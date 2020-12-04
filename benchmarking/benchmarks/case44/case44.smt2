(set-logic QF_BV)
(declare-fun clock_1 () (_ BitVec 1))
(declare-fun clock_2 () (_ BitVec 1))
(declare-fun clock_3 () (_ BitVec 1))
(declare-fun eql_1 () (_ BitVec 1))
(declare-fun eql_2 () (_ BitVec 1))
(declare-fun reset_1 () (_ BitVec 1))
(declare-fun reset_2 () (_ BitVec 1))
(declare-fun reset_3 () (_ BitVec 1))
(declare-fun state_2 () (_ BitVec 4))
(declare-fun uscite_1 () (_ BitVec 4))
(declare-fun uscite_0 () (_ BitVec 4))
(define-fun $e1 () (_ BitVec 4) (_ bv0 4))
(define-fun $e2 () (_ BitVec 4) (_ bv14 4))
(define-fun $e3 () (_ BitVec 4) (_ bv10 4))
(define-fun $e4 () (_ BitVec 4) (_ bv2 4))
(define-fun $e5 () (_ BitVec 4) (_ bv12 4))
(define-fun $e6 () (_ BitVec 4) (_ bv4 4))
(define-fun $e7 () (_ BitVec 4) (_ bv6 4))
(define-fun $e8 () (_ BitVec 1) (ite (= reset_1 reset_2) #b1 #b0))
(define-fun $e9 () (_ BitVec 1) (ite (= clock_1 clock_2) #b1 #b0))
(define-fun $e10 () (_ BitVec 1) (bvand $e8 $e9))
(define-fun $e11 () (_ BitVec 1) (ite (= uscite_0 $e1) #b1 #b0))
(define-fun $e12 () (_ BitVec 1) (bvand clock_1 (bvnot $e9)))
(define-fun $e13 () (_ BitVec 1) (ite (= reset_2 reset_3) #b1 #b0))
(define-fun $e14 () (_ BitVec 1) (ite (= clock_2 clock_3) #b1 #b0))
(define-fun $e15 () (_ BitVec 1) (bvand $e13 $e14))
(define-fun $e16 () (_ BitVec 1) (bvand clock_2 (bvnot $e14)))
(define-fun $e17 () (_ BitVec 1) (ite (= state_2 $e1) #b1 #b0))
(define-fun $e18 () (_ BitVec 1) (ite (= state_2 (bvnot $e2)) #b1 #b0))
(define-fun $e19 () (_ BitVec 1) (ite (= state_2 (bvnot $e3)) #b1 #b0))
(define-fun $e20 () (_ BitVec 1) (ite (= state_2 $e4) #b1 #b0))
(define-fun $e21 () (_ BitVec 1) (ite (= state_2 (bvnot $e5)) #b1 #b0))
(define-fun $e22 () (_ BitVec 1) (ite (= state_2 $e6) #b1 #b0))
(define-fun $e23 () (_ BitVec 1) (ite (= state_2 $e7) #b1 #b0))
(define-fun $e24 () (_ BitVec 1) (bvand (bvnot $e16) $e17))
(define-fun $e25 () (_ BitVec 1) (bvand (bvnot reset_2) (bvnot $e24)))
(define-fun $e26 () (_ BitVec 1) (bvand $e15 (bvnot $e17)))
(define-fun $e27 () (_ BitVec 1) (bvand (bvnot $e15) $e25))
(define-fun $e28 () (_ BitVec 1) (bvand (bvnot $e26) (bvnot $e27)))
(define-fun $e29 () (_ BitVec 1) (ite (= uscite_0 (bvnot $e2)) #b1 #b0))
(define-fun $e30 () (_ BitVec 1) (bvand eql_2 $e23))
(define-fun $e31 () (_ BitVec 1) (bvand (bvnot $e18) (bvnot $e23)))
(define-fun $e32 () (_ BitVec 1) (bvand (bvnot $e30) (bvnot $e31)))
(define-fun $e33 () (_ BitVec 1) (bvand (bvnot $e22) $e32))
(define-fun $e34 () (_ BitVec 1) (bvand eql_2 $e21))
(define-fun $e35 () (_ BitVec 1) (bvand (bvnot $e21) (bvnot $e33)))
(define-fun $e36 () (_ BitVec 1) (bvand (bvnot $e34) (bvnot $e35)))
(define-fun $e37 () (_ BitVec 1) (bvand (bvnot $e20) $e36))
(define-fun $e38 () (_ BitVec 1) (bvand eql_2 $e19))
(define-fun $e39 () (_ BitVec 1) (bvand (bvnot $e19) (bvnot $e37)))
(define-fun $e40 () (_ BitVec 1) (bvand (bvnot $e38) (bvnot $e39)))
(define-fun $e41 () (_ BitVec 1) (bvand (bvnot $e18) $e40))
(define-fun $e42 () (_ BitVec 1) (bvand (bvnot $e17) (bvnot $e41)))
(define-fun $e43 () (_ BitVec 1) (bvand $e16 $e42))
(define-fun $e44 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e18)))
(define-fun $e45 () (_ BitVec 1) (bvand (bvnot $e43) (bvnot $e44)))
(define-fun $e46 () (_ BitVec 1) (bvand (bvnot reset_2) $e45))
(define-fun $e47 () (_ BitVec 1) (bvand $e15 (bvnot $e18)))
(define-fun $e48 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e46)))
(define-fun $e49 () (_ BitVec 1) (bvand (bvnot $e47) (bvnot $e48)))
(define-fun $e50 () (_ BitVec 1) (bvand eql_1 (bvnot $e11)))
(define-fun $e51 () (_ BitVec 1) (bvand (bvnot eql_1) (bvnot $e29)))
(define-fun $e52 () (_ BitVec 1) (bvand (bvnot $e50) (bvnot $e51)))
(define-fun $e53 () (_ BitVec 1) (bvand (bvnot eql_2) $e18))
(define-fun $e54 () (_ BitVec 1) (bvand (bvnot $e17) $e53))
(define-fun $e55 () (_ BitVec 1) (bvand $e16 (bvnot $e54)))
(define-fun $e56 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e19)))
(define-fun $e57 () (_ BitVec 1) (bvand (bvnot $e55) (bvnot $e56)))
(define-fun $e58 () (_ BitVec 1) (bvand (bvnot reset_2) $e57))
(define-fun $e59 () (_ BitVec 1) (bvand $e15 (bvnot $e19)))
(define-fun $e60 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e58)))
(define-fun $e61 () (_ BitVec 1) (bvand (bvnot $e59) (bvnot $e60)))
(define-fun $e62 () (_ BitVec 1) (bvand eql_2 $e20))
(define-fun $e63 () (_ BitVec 1) (bvand (bvnot $e19) $e62))
(define-fun $e64 () (_ BitVec 1) (bvand (bvnot $e18) (bvnot $e63)))
(define-fun $e65 () (_ BitVec 1) (bvand (bvnot $e53) (bvnot $e64)))
(define-fun $e66 () (_ BitVec 1) (bvand (bvnot $e17) $e65))
(define-fun $e67 () (_ BitVec 1) (bvand $e16 (bvnot $e66)))
(define-fun $e68 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e20)))
(define-fun $e69 () (_ BitVec 1) (bvand (bvnot $e67) (bvnot $e68)))
(define-fun $e70 () (_ BitVec 1) (bvand (bvnot reset_2) $e69))
(define-fun $e71 () (_ BitVec 1) (bvand $e15 (bvnot $e20)))
(define-fun $e72 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e70)))
(define-fun $e73 () (_ BitVec 1) (bvand (bvnot $e71) (bvnot $e72)))
(define-fun $e74 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e34)))
(define-fun $e75 () (_ BitVec 1) (bvand (bvnot $e62) (bvnot $e74)))
(define-fun $e76 () (_ BitVec 1) (bvand (bvnot $e19) $e75))
(define-fun $e77 () (_ BitVec 1) (bvand (bvnot $e18) $e76))
(define-fun $e78 () (_ BitVec 1) (bvand (bvnot $e17) $e77))
(define-fun $e79 () (_ BitVec 1) (bvand $e16 (bvnot $e78)))
(define-fun $e80 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e21)))
(define-fun $e81 () (_ BitVec 1) (bvand (bvnot $e79) (bvnot $e80)))
(define-fun $e82 () (_ BitVec 1) (bvand (bvnot reset_2) $e81))
(define-fun $e83 () (_ BitVec 1) (bvand $e15 (bvnot $e21)))
(define-fun $e84 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e82)))
(define-fun $e85 () (_ BitVec 1) (bvand (bvnot $e83) (bvnot $e84)))
(define-fun $e86 () (_ BitVec 1) (bvand eql_2 $e22))
(define-fun $e87 () (_ BitVec 1) (bvand (bvnot $e21) $e86))
(define-fun $e88 () (_ BitVec 1) (bvand (bvnot $e20) $e87))
(define-fun $e89 () (_ BitVec 1) (bvand (bvnot eql_2) $e19))
(define-fun $e90 () (_ BitVec 1) (bvand (bvnot $e19) (bvnot $e88)))
(define-fun $e91 () (_ BitVec 1) (bvand (bvnot $e89) (bvnot $e90)))
(define-fun $e92 () (_ BitVec 1) (bvand (bvnot $e18) $e91))
(define-fun $e93 () (_ BitVec 1) (bvand (bvnot $e17) $e92))
(define-fun $e94 () (_ BitVec 1) (bvand $e16 (bvnot $e93)))
(define-fun $e95 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e22)))
(define-fun $e96 () (_ BitVec 1) (bvand (bvnot $e94) (bvnot $e95)))
(define-fun $e97 () (_ BitVec 1) (bvand (bvnot reset_2) $e96))
(define-fun $e98 () (_ BitVec 1) (bvand $e15 (bvnot $e22)))
(define-fun $e99 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e97)))
(define-fun $e100 () (_ BitVec 1) (bvand (bvnot $e98) (bvnot $e99)))
(define-fun $e101 () (_ BitVec 1) (ite (= uscite_0 (bvnot $e5)) #b1 #b0))
(define-fun $e102 () (_ BitVec 1) (bvand (bvnot eql_1) (bvnot $e101)))
(define-fun $e103 () (_ BitVec 1) (bvand (bvnot $e50) (bvnot $e102)))
(define-fun $e104 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e30)))
(define-fun $e105 () (_ BitVec 1) (bvand (bvnot $e86) (bvnot $e104)))
(define-fun $e106 () (_ BitVec 1) (bvand (bvnot $e21) $e105))
(define-fun $e107 () (_ BitVec 1) (bvand (bvnot $e20) $e106))
(define-fun $e108 () (_ BitVec 1) (bvand (bvnot $e19) $e107))
(define-fun $e109 () (_ BitVec 1) (bvand (bvnot $e18) $e108))
(define-fun $e110 () (_ BitVec 1) (bvand (bvnot $e17) $e109))
(define-fun $e111 () (_ BitVec 1) (bvand $e16 (bvnot $e110)))
(define-fun $e112 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e23)))
(define-fun $e113 () (_ BitVec 1) (bvand (bvnot $e111) (bvnot $e112)))
(define-fun $e114 () (_ BitVec 1) (bvand (bvnot reset_2) $e113))
(define-fun $e115 () (_ BitVec 1) (bvand $e15 (bvnot $e23)))
(define-fun $e116 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e114)))
(define-fun $e117 () (_ BitVec 1) (bvand (bvnot $e115) (bvnot $e116)))
(define-fun $e118 () (_ BitVec 1) (bvand eql_1 (bvnot $e101)))
(define-fun $e119 () (_ BitVec 1) (bvand (bvnot $e51) (bvnot $e118)))
(define-fun $e120 () (_ BitVec 1) (ite (= uscite_1 uscite_0) #b1 #b0))
(define-fun $e121 () (_ BitVec 1) (bvand $e117 (bvnot $e119)))
(define-fun $e122 () (_ BitVec 1) (bvand (bvnot $e117) (bvnot $e120)))
(define-fun $e123 () (_ BitVec 1) (bvand (bvnot $e121) (bvnot $e122)))
(define-fun $e124 () (_ BitVec 1) (bvand $e100 (bvnot $e103)))
(define-fun $e125 () (_ BitVec 1) (bvand (bvnot $e100) (bvnot $e123)))
(define-fun $e126 () (_ BitVec 1) (bvand (bvnot $e124) (bvnot $e125)))
(define-fun $e127 () (_ BitVec 1) (bvand (bvnot $e29) $e85))
(define-fun $e128 () (_ BitVec 1) (bvand (bvnot $e85) (bvnot $e126)))
(define-fun $e129 () (_ BitVec 1) (bvand (bvnot $e127) (bvnot $e128)))
(define-fun $e130 () (_ BitVec 1) (bvand (bvnot $e52) $e73))
(define-fun $e131 () (_ BitVec 1) (bvand (bvnot $e73) (bvnot $e129)))
(define-fun $e132 () (_ BitVec 1) (bvand (bvnot $e130) (bvnot $e131)))
(define-fun $e133 () (_ BitVec 1) (bvand (bvnot $e52) $e61))
(define-fun $e134 () (_ BitVec 1) (bvand (bvnot $e61) (bvnot $e132)))
(define-fun $e135 () (_ BitVec 1) (bvand (bvnot $e133) (bvnot $e134)))
(define-fun $e136 () (_ BitVec 1) (bvand $e49 (bvnot $e52)))
(define-fun $e137 () (_ BitVec 1) (bvand (bvnot $e49) (bvnot $e135)))
(define-fun $e138 () (_ BitVec 1) (bvand (bvnot $e136) (bvnot $e137)))
(define-fun $e139 () (_ BitVec 1) (bvand $e28 (bvnot $e29)))
(define-fun $e140 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e138)))
(define-fun $e141 () (_ BitVec 1) (bvand (bvnot $e139) (bvnot $e140)))
(define-fun $e142 () (_ BitVec 1) (bvand $e12 (bvnot $e141)))
(define-fun $e143 () (_ BitVec 1) (bvand (bvnot $e12) (bvnot $e120)))
(define-fun $e144 () (_ BitVec 1) (bvand (bvnot $e142) (bvnot $e143)))
(define-fun $e145 () (_ BitVec 1) (bvand reset_1 (bvnot $e11)))
(define-fun $e146 () (_ BitVec 1) (bvand (bvnot reset_1) (bvnot $e144)))
(define-fun $e147 () (_ BitVec 1) (bvand $e10 (bvnot $e120)))
(define-fun $e148 () (_ BitVec 1) (bvand (bvnot $e10) $e145))
(assert (not (= (bvnot $e147) #b0)))
(assert (not (= (bvnot $e148) #b0)))
(assert (not (= (bvnot $e146) #b0)))
(check-sat)
(exit)
