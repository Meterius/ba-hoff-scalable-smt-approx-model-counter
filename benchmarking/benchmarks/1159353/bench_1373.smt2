(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_2036 () (_ BitVec 8))
(declare-fun T4_2036 () (_ BitVec 32))
(declare-fun T1_2037 () (_ BitVec 8))
(declare-fun T1_2038 () (_ BitVec 8))
(declare-fun T1_2039 () (_ BitVec 8))
(assert (and true (= T4_2036 (bvor (bvshl (bvor (bvshl (bvor (bvshl ((_ zero_extend 24) T1_2039) (_ bv8 32)) ((_ zero_extend 24) T1_2038)) (_ bv8 32)) ((_ zero_extend 24) T1_2037)) (_ bv8 32)) ((_ zero_extend 24) T1_2036))) (= T4_2036 (_ bv1414087753 32)) (bvule T1_2036 (_ bv90 8)) (bvule (_ bv65 8) T1_2036)))
(check-sat)
(exit)
