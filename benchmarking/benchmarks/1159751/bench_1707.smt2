(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T4_88 () (_ BitVec 32))
(declare-fun T1_88 () (_ BitVec 8))
(declare-fun T1_89 () (_ BitVec 8))
(declare-fun T1_90 () (_ BitVec 8))
(declare-fun T1_91 () (_ BitVec 8))
(assert (let ((?v_2 ((_ extract 7 0) (bvashr T4_88 ((_ zero_extend 24) (_ bv24 8))))) (?v_1 ((_ extract 7 0) (bvashr T4_88 ((_ zero_extend 24) (_ bv8 8))))) (?v_0 ((_ extract 7 0) (bvashr T4_88 ((_ zero_extend 24) (_ bv16 8)))))) (and true (= T4_88 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_91) (_ bv8 32)) ((_ zero_extend 24) T1_90)) (_ bv8 32)) ((_ zero_extend 24) T1_89)) (_ bv8 32)) ((_ zero_extend 24) T1_88))) (bvult ?v_2 (_ bv65 8)) (bvule ?v_0 (_ bv90 8)) (bvule (_ bv65 8) ?v_0) (bvult ?v_0 (_ bv97 8)) (bvule ?v_1 (_ bv90 8)) (bvule (_ bv65 8) ?v_1) (bvult ?v_1 (_ bv97 8)) (bvule T1_88 (_ bv90 8)) (bvule (_ bv65 8) T1_88) (bvult T1_88 (_ bv97 8)) (bvult (_ bv57 8) T1_88) (bvule (_ bv48 8) T1_88) (bvult ?v_2 (_ bv97 8)))))
(check-sat)
(exit)
