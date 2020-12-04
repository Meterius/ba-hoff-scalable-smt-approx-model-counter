(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T4_216 () (_ BitVec 32))
(declare-fun T1_216 () (_ BitVec 8))
(declare-fun T1_217 () (_ BitVec 8))
(declare-fun T1_218 () (_ BitVec 8))
(declare-fun T1_219 () (_ BitVec 8))
(assert (and true (= T4_216 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_219) (_ bv8 32)) ((_ zero_extend 24) T1_218)) (_ bv8 32)) ((_ zero_extend 24) T1_217)) (_ bv8 32)) ((_ zero_extend 24) T1_216))) (= T4_216 (_ bv0 32))))
(check-sat)
(exit)
