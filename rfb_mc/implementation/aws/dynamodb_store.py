from ast import literal_eval
from collections import Counter
from typing import TypedDict, Optional, Literal, Dict, Any, Iterable, Tuple
import uuid
from rfb_mc.store import StoreBase, StoreData
from rfb_mc.types import RfBmcTask, RfBmcResult, Params


def v1_encode_rf_bmc_task(task: RfBmcTask) -> str:
    return repr(tuple(task))


def v1_decode_rf_bmc_task(task: str) -> RfBmcTask:
    return RfBmcTask(*literal_eval(task))


def v1_encode_rf_bmc_result(result: RfBmcResult) -> str:
    return repr(tuple(result))


def v1_decode_rf_bmc_result(result: str) -> RfBmcResult:
    return RfBmcResult(*literal_eval(result))


DynamodbV1RfBmcResultsMap = Dict[str, Dict[str, int]]


def v1_encode_rf_bmc_results_map(
    rf_bmc_results_map: Dict[RfBmcTask, Counter[RfBmcResult]],
) -> DynamodbV1RfBmcResultsMap:
    return {
        v1_encode_rf_bmc_task(task): {
            v1_encode_rf_bmc_result(result): rf_bmc_results_map[task][result]
            for result in rf_bmc_results_map[task]
        }
        for task in rf_bmc_results_map
    }


def v1_decode_rf_bmc_results_map(
    rf_bmc_results_map: DynamodbV1RfBmcResultsMap,
) -> Dict[RfBmcTask, Counter[RfBmcResult]]:
    return {
        v1_decode_rf_bmc_task(task): Counter({
            v1_decode_rf_bmc_result(result): rf_bmc_results_map[task][result]
            for result in rf_bmc_results_map[task]
        })
        for task in rf_bmc_results_map
    }


class DynamodbV1Params(TypedDict):
    bit_width_counter: Dict[int, int]


def v1_encode_params(params: Params) -> DynamodbV1Params:
    return {
        "bit_width_counter": dict(params.bit_width_counter)
    }


def v1_decode_params(params: DynamodbV1Params) -> Params:
    return Params(
        bit_width_counter=Counter(params["bit_width_counter"])
    )


class DynamodbV1StoreData(TypedDict):
    id: str
    version: Literal[1]
    params: DynamodbV1Params
    rf_bmc_results_map: Dict[str, Dict[str, int]]


def v1_encode_store_data(ident: str, data: StoreData) -> DynamodbV1StoreData:
    return DynamodbV1StoreData(
        id=ident,
        version=1,
        params=v1_encode_params(data.params),
        rf_bmc_results_map=v1_encode_rf_bmc_results_map(
            data.rf_bmc_results_map,
        )
    )


def v1_decode_store_data(data: DynamodbV1StoreData) -> StoreData:
    return StoreData(
        params=v1_decode_params(data["params"]),
        rf_bmc_results_map=v1_decode_rf_bmc_results_map(data["rf_bmc_results_map"])
    )


def decode_store_data(item: Any) -> Tuple[int, StoreData]:
    """
    Decodes a database item of any known version,
    returns the version it was encoded in and the interpreted store data
    """

    if item["version"] == 1:
        typed_item: DynamodbV1StoreData = item
        return item["version"], v1_decode_store_data(typed_item)
    else:
        raise ValueError(f"Unexpected version \"{item['version']}\" in store data entry")


class DynamodbStore(StoreBase):
    VERSION = 1

    def __init__(self, table, ident: str):
        """
        Initializes a dynamodb store, requires the identifier to point to
        an existing store data entry. It modifies the data format if the version is
        different as otherwise update methods will throw.
        """

        super().__init__(
            DynamodbStore.get_and_correct_store_data_entry(table, ident)
        )

        self.table = table
        self.ident = ident

    def sync(self):
        data = self.get_store_data_entry(self.table, self.ident)

        with self.data_lock:
            self.data = data

    def _add_rf_bmc_results(self, task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]]):
        task_results = list(task_results)

        # if no results are available only the synchronization needs to be performed
        if len(task_results) == 0:
            self.sync()
            return

        # update expression will increment and create the necessary counters

        task_results_increments = Counter(task_results)

        update_expression = ""
        expression_attribute_names = {}
        expression_attribute_values = {
            "version": DynamodbStore.VERSION,
            "empty_map": {},
            "zero": 0,
        }

        tasks = tuple(set([task for task, _ in task_results]))

        for idx, task in enumerate(tasks):
            update_expression += f"SET rf_bmc_results_map.#task_{idx} " \
                                 f"= if_not_exists(rf_bmc_results_map.#task_{idx}, :empty_map), "

            expression_attribute_names[f"task_{idx}"] = v1_encode_rf_bmc_task(task)

            results = tuple(set([
                task_result for task_result in task_results if task_result[0] == task
            ]))

            for jdx, result in enumerate(results):
                update_expression += f"SET rf_bmc_results_map.#task_{idx}.#task_{idx}_result_{jdx}" \
                                     f" = if_not_exists(" \
                                     f"rf_bmc_results_map.#task_{idx}.#task_{idx}_result_{jdx}, :zero), "

                update_expression += f"ADD rf_bmc_results_map.#task_{idx}.#task_{idx}_result_{jdx} " \
                                     f":inc_task_{idx}_result_{jdx}, "

                expression_attribute_values[f"inc_task_{idx}_result_{jdx}"] = task_results_increments[(task, result)]
                expression_attribute_names[f"task_{idx}_result_{jdx}"] = v1_encode_rf_bmc_result(result)

        # increments the necessary counters and retrieves the previous store data that was stored
        response = self.table.put_item(
            Key={"id": self.ident},
            UpdateExpression=update_expression,
            ConditionExpression="attribute_exists(id) AND version = :version",
            ExpressionAttirbuteValues=expression_attribute_values,
            ExpressionAttributeNames=expression_attribute_names,
            ReturnValues="ALL_OLD"
        )

        # data object that was previously stored in the data entry before increment updates where performed
        data = decode_store_data(response.Attributes)[1]

        # update the store data according to database updates
        for task, result in task_results:
            if task not in data.rf_bmc_results_map:
                data.rf_bmc_results_map[task] = Counter[RfBmcResult]()

            data.rf_bmc_results_map[task][result] += 1

        # write the synchronized update back to memory
        with self.data_lock:
            self.data = data

    @classmethod
    def get_and_correct_store_data_entry(
        cls,
        table,
        ident: str,
    ) -> StoreData:
        """
        Retrieves the store data and updates the data format if the version is
        different.
        """

        version, data = DynamodbStore.get_store_data_entry(table, ident)

        # ensures the data format is correct in order for class method to
        # update the data correctly
        if version != cls.VERSION:
            cls.replace_store_data_entry(table, ident, data)

        return data

    @staticmethod
    def get_store_data_entry(
        table,
        ident: str,
    ) -> (int, StoreData):
        """
        Retrieves the store data entry with the given identifier from
        the table and decodes it.
        """

        item: Any = table.get_item(
            Key={
                "id": ident,
            }
        ).Item

        return decode_store_data(item)

    @staticmethod
    def replace_store_data_entry(
        table,
        ident: str,
        store: StoreData,
    ):
        """
        Removes the store entry and then puts the provided data in the entry.
        """

        table.delete_item(
            Key={
                "id": ident,
            },
        )

        item: DynamodbV1StoreData = v1_encode_store_data(ident, store)

        table.put_item(
            Item=item
        )

    @staticmethod
    def create_store_data_entry(
        table,
        params: Params,
        ident: Optional[str] = None,
    ) -> str:
        ident = ident if ident is not None else uuid.uuid4()

        item: DynamodbV1StoreData = DynamodbV1StoreData(
            id=ident,
            version=1,
            params=v1_encode_params(params),
            rf_bmc_results_map={},
        )

        table.put_item(
            Item=item,
            ConditionExpression="attribute_not_exists(id)",
        )

        return ident
