(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T4_212 () (_ BitVec 32))
(declare-fun T1_212 () (_ BitVec 8))
(declare-fun T1_213 () (_ BitVec 8))
(declare-fun T1_214 () (_ BitVec 8))
(declare-fun T1_215 () (_ BitVec 8))
(assert (let ((?v_0 ((_ extract 7 0) (bvashr T4_212 ((_ zero_extend 24) (_ bv8 8)))))) (and true (= T4_212 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_215) (_ bv8 32)) ((_ zero_extend 24) T1_214)) (_ bv8 32)) ((_ zero_extend 24) T1_213)) (_ bv8 32)) ((_ zero_extend 24) T1_212))) (bvult (_ bv90 8) ?v_0) (bvule T1_212 (_ bv90 8)) (bvule (_ bv65 8) T1_212) (bvult T1_212 (_ bv97 8)) (bvule (_ bv65 8) ?v_0) (bvult ?v_0 (_ bv97 8)))))
(check-sat)
(exit)
