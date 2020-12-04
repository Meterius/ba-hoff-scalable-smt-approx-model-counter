(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T4_168 () (_ BitVec 32))
(declare-fun T1_168 () (_ BitVec 8))
(declare-fun T1_169 () (_ BitVec 8))
(declare-fun T1_170 () (_ BitVec 8))
(declare-fun T1_171 () (_ BitVec 8))
(assert (and true (= T4_168 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_171) (_ bv8 32)) ((_ zero_extend 24) T1_170)) (_ bv8 32)) ((_ zero_extend 24) T1_169)) (_ bv8 32)) ((_ zero_extend 24) T1_168))) (= T4_168 (_ bv0 32))))
(check-sat)
(exit)
