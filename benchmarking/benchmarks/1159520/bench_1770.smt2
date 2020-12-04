(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_20 () (_ BitVec 8))
(declare-fun T4_20 () (_ BitVec 32))
(declare-fun T1_21 () (_ BitVec 8))
(declare-fun T1_22 () (_ BitVec 8))
(declare-fun T1_23 () (_ BitVec 8))
(assert (let ((?v_1 ((_ extract 7 0) (bvashr T4_20 ((_ zero_extend 24) (_ bv8 8))))) (?v_0 ((_ extract 7 0) (bvashr T4_20 ((_ zero_extend 24) (_ bv16 8)))))) (and true (= T4_20 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_23) (_ bv8 32)) ((_ zero_extend 24) T1_22)) (_ bv8 32)) ((_ zero_extend 24) T1_21)) (_ bv8 32)) ((_ zero_extend 24) T1_20))) (bvult ((_ extract 7 0) (bvashr T4_20 ((_ zero_extend 24) (_ bv24 8)))) (_ bv48 8)) (bvule ?v_0 (_ bv122 8)) (bvule (_ bv97 8) ?v_0) (bvult (_ bv57 8) ?v_0) (bvule (_ bv48 8) ?v_0) (bvule ?v_1 (_ bv122 8)) (bvule (_ bv97 8) ?v_1) (bvult (_ bv57 8) ?v_1) (bvule (_ bv48 8) ?v_1) (bvule T1_20 (_ bv122 8)) (bvule (_ bv97 8) T1_20) (bvult (_ bv57 8) T1_20) (bvule (_ bv48 8) T1_20))))
(check-sat)
(exit)
