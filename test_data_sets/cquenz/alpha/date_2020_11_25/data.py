import os

code_dir = os.path.dirname(__file__)

with open(os.path.join(code_dir, "constraint_assertions.txt"), "r") as f:
    const_assertions = str(f.read())

with open(os.path.join(code_dir, "feature_and_element_assertions.txt"), "r") as f:
    fe_assertions = str(f.read())

with open(os.path.join(code_dir, "conf_knowledge_event.txt"), "r") as f:
    exec("conf_knowledge_event = " + str(f.read()))

ck_data = {
    "ck": conf_knowledge_event,
    "const_assertions": const_assertions,
    "fe_assertions": fe_assertions,
}
