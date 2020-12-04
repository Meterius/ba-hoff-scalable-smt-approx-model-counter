(set-logic QF_BV)
(declare-fun CLOCK_1 () (_ BitVec 1))
(declare-fun CLOCK_2 () (_ BitVec 1))
(declare-fun CLOCK_3 () (_ BitVec 1))
(declare-fun autoname_1 () (_ BitVec 4))
(declare-fun autoname_2 () (_ BitVec 1))
(declare-fun autoname_3 () (_ BitVec 1))
(declare-fun autoname_4 () (_ BitVec 5))
(declare-fun autoname_5 () (_ BitVec 1))
(declare-fun autoname_6 () (_ BitVec 1))
(declare-fun autoname_7 () (_ BitVec 1))
(declare-fun autoname_8 () (_ BitVec 1))
(declare-fun dual_2 () (_ BitVec 1))
(declare-fun jumper_2 () (_ BitVec 5))
(declare-fun local_dtack_1 () (_ BitVec 1))
(declare-fun local_dtack_0 () (_ BitVec 1))
(declare-fun reset_1 () (_ BitVec 1))
(declare-fun reset_2 () (_ BitVec 1))
(declare-fun reset_3 () (_ BitVec 1))
(declare-fun vme_iack_in_1 () (_ BitVec 1))
(declare-fun vme_iack_in_2 () (_ BitVec 1))
(define-fun $e1 () (_ BitVec 4) (_ bv0 4))
(define-fun $e2 () (_ BitVec 4) (_ bv14 4))
(define-fun $e3 () (_ BitVec 4) (_ bv2 4))
(define-fun $e4 () (_ BitVec 4) (_ bv12 4))
(define-fun $e5 () (_ BitVec 4) (_ bv4 4))
(define-fun $e6 () (_ BitVec 4) (_ bv10 4))
(define-fun $e7 () (_ BitVec 4) (_ bv6 4))
(define-fun $e8 () (_ BitVec 4) (_ bv8 4))
(define-fun $e9 () (_ BitVec 1) (ite (= CLOCK_1 CLOCK_2) #b1 #b0))
(define-fun $e10 () (_ BitVec 1) (ite (= reset_1 reset_2) #b1 #b0))
(define-fun $e11 () (_ BitVec 1) (bvand $e9 $e10))
(define-fun $e12 () (_ BitVec 1) (bvand CLOCK_1 (bvnot $e9)))
(define-fun $e13 () (_ BitVec 1) (ite (= CLOCK_2 CLOCK_3) #b1 #b0))
(define-fun $e14 () (_ BitVec 1) (ite (= reset_2 reset_3) #b1 #b0))
(define-fun $e15 () (_ BitVec 1) (bvand $e13 $e14))
(define-fun $e16 () (_ BitVec 1) (bvand CLOCK_2 (bvnot $e13)))
(define-fun $e17 () (_ BitVec 1) (ite (= autoname_1 $e1) #b1 #b0))
(define-fun $e18 () (_ BitVec 1) (bvand (bvnot autoname_2) (bvnot autoname_3)))
(define-fun $e19 () (_ BitVec 1) (bvand vme_iack_in_2 (bvnot $e18)))
(define-fun $e20 () (_ BitVec 1) (ite (= autoname_1 (bvnot $e2)) #b1 #b0))
(define-fun $e21 () (_ BitVec 1) (bvand (bvnot autoname_2) (bvnot vme_iack_in_2)))
(define-fun $e22 () (_ BitVec 1) (bvand dual_2 $e21))
(define-fun $e23 () (_ BitVec 1) (bvand vme_iack_in_2 $e18))
(define-fun $e24 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e23)))
(define-fun $e25 () (_ BitVec 1) (ite (= autoname_1 $e3) #b1 #b0))
(define-fun $e26 () (_ BitVec 1) (ite (= autoname_1 (bvnot $e4)) #b1 #b0))
(define-fun $e27 () (_ BitVec 1) (ite (= autoname_1 $e5) #b1 #b0))
(define-fun $e28 () (_ BitVec 1) (ite (= autoname_1 (bvnot $e6)) #b1 #b0))
(define-fun $e29 () (_ BitVec 1) (bvand autoname_2 autoname_3))
(define-fun $e30 () (_ BitVec 1) (ite (= autoname_1 $e7) #b1 #b0))
(define-fun $e31 () (_ BitVec 1) (ite (= autoname_1 (bvnot $e8)) #b1 #b0))
(define-fun $e32 () (_ BitVec 1) (ite (= autoname_1 $e8) #b1 #b0))
(define-fun $e33 () (_ BitVec 1) (ite (= autoname_1 (bvnot $e7)) #b1 #b0))
(define-fun $e34 () (_ BitVec 1) (bvand $e21 $e33))
(define-fun $e35 () (_ BitVec 1) (bvand (bvnot $e32) (bvnot $e34)))
(define-fun $e36 () (_ BitVec 1) (bvand (bvnot $e31) $e35))
(define-fun $e37 () (_ BitVec 1) (bvand (bvnot $e30) $e36))
(define-fun $e38 () (_ BitVec 1) (bvand $e28 (bvnot $e29)))
(define-fun $e39 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e37)))
(define-fun $e40 () (_ BitVec 1) (bvand (bvnot $e38) (bvnot $e39)))
(define-fun $e41 () (_ BitVec 1) (bvand (bvnot $e27) $e40))
(define-fun $e42 () (_ BitVec 1) (bvand (bvnot $e26) $e41))
(define-fun $e43 () (_ BitVec 1) (bvand (bvnot $e25) $e42))
(define-fun $e44 () (_ BitVec 1) (bvand $e20 (bvnot $e24)))
(define-fun $e45 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e43)))
(define-fun $e46 () (_ BitVec 1) (bvand (bvnot $e44) (bvnot $e45)))
(define-fun $e47 () (_ BitVec 1) (bvand $e17 (bvnot $e19)))
(define-fun $e48 () (_ BitVec 1) (bvand (bvnot $e17) (bvnot $e46)))
(define-fun $e49 () (_ BitVec 1) (bvand (bvnot $e47) (bvnot $e48)))
(define-fun $e50 () (_ BitVec 1) (bvand $e16 (bvnot $e49)))
(define-fun $e51 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e17)))
(define-fun $e52 () (_ BitVec 1) (bvand (bvnot $e50) (bvnot $e51)))
(define-fun $e53 () (_ BitVec 1) (bvand reset_2 (bvnot $e52)))
(define-fun $e54 () (_ BitVec 1) (bvand $e15 (bvnot $e17)))
(define-fun $e55 () (_ BitVec 1) (bvand (bvnot $e15) $e53))
(define-fun $e56 () (_ BitVec 1) (bvand (bvnot $e54) (bvnot $e55)))
(define-fun $e57 () (_ BitVec 1) (bvand $e16 (bvnot $e47)))
(define-fun $e58 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e20)))
(define-fun $e59 () (_ BitVec 1) (bvand (bvnot $e57) (bvnot $e58)))
(define-fun $e60 () (_ BitVec 1) (bvand reset_2 $e59))
(define-fun $e61 () (_ BitVec 1) (bvand $e15 (bvnot $e20)))
(define-fun $e62 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e60)))
(define-fun $e63 () (_ BitVec 1) (bvand (bvnot $e61) (bvnot $e62)))
(define-fun $e64 () (_ BitVec 1) (ite (= local_dtack_1 local_dtack_0) #b1 #b0))
(define-fun $e65 () (_ BitVec 1) (ite (= autoname_4 jumper_2) #b1 #b0))
(define-fun $e66 () (_ BitVec 1) (bvand (bvnot autoname_5) autoname_6))
(define-fun $e67 () (_ BitVec 1) (bvand $e65 (bvnot $e66)))
(define-fun $e68 () (_ BitVec 1) (bvand $e23 $e67))
(define-fun $e69 () (_ BitVec 1) (bvand (bvnot $e22) $e68))
(define-fun $e70 () (_ BitVec 1) (bvand $e20 $e69))
(define-fun $e71 () (_ BitVec 1) (bvand (bvnot $e17) $e70))
(define-fun $e72 () (_ BitVec 1) (bvand $e16 (bvnot $e71)))
(define-fun $e73 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e25)))
(define-fun $e74 () (_ BitVec 1) (bvand (bvnot $e72) (bvnot $e73)))
(define-fun $e75 () (_ BitVec 1) (bvand reset_2 $e74))
(define-fun $e76 () (_ BitVec 1) (bvand $e15 (bvnot $e25)))
(define-fun $e77 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e75)))
(define-fun $e78 () (_ BitVec 1) (bvand (bvnot $e76) (bvnot $e77)))
(define-fun $e79 () (_ BitVec 1) (bvand $e16 (bvnot $e25)))
(define-fun $e80 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e26)))
(define-fun $e81 () (_ BitVec 1) (bvand (bvnot $e79) (bvnot $e80)))
(define-fun $e82 () (_ BitVec 1) (bvand reset_2 $e81))
(define-fun $e83 () (_ BitVec 1) (bvand $e15 (bvnot $e26)))
(define-fun $e84 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e82)))
(define-fun $e85 () (_ BitVec 1) (bvand (bvnot $e83) (bvnot $e84)))
(define-fun $e86 () (_ BitVec 1) (bvand $e16 (bvnot $e26)))
(define-fun $e87 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e27)))
(define-fun $e88 () (_ BitVec 1) (bvand (bvnot $e86) (bvnot $e87)))
(define-fun $e89 () (_ BitVec 1) (bvand reset_2 $e88))
(define-fun $e90 () (_ BitVec 1) (bvand $e15 (bvnot $e27)))
(define-fun $e91 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e89)))
(define-fun $e92 () (_ BitVec 1) (bvand (bvnot $e90) (bvnot $e91)))
(define-fun $e93 () (_ BitVec 1) (bvand $e23 (bvnot $e67)))
(define-fun $e94 () (_ BitVec 1) (bvand (bvnot $e22) $e93))
(define-fun $e95 () (_ BitVec 1) (bvand (bvnot $e27) (bvnot $e38)))
(define-fun $e96 () (_ BitVec 1) (bvand (bvnot $e26) (bvnot $e95)))
(define-fun $e97 () (_ BitVec 1) (bvand (bvnot $e25) $e96))
(define-fun $e98 () (_ BitVec 1) (bvand $e20 (bvnot $e94)))
(define-fun $e99 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e97)))
(define-fun $e100 () (_ BitVec 1) (bvand (bvnot $e98) (bvnot $e99)))
(define-fun $e101 () (_ BitVec 1) (bvand (bvnot $e17) $e100))
(define-fun $e102 () (_ BitVec 1) (bvand $e16 (bvnot $e101)))
(define-fun $e103 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e28)))
(define-fun $e104 () (_ BitVec 1) (bvand (bvnot $e102) (bvnot $e103)))
(define-fun $e105 () (_ BitVec 1) (bvand reset_2 $e104))
(define-fun $e106 () (_ BitVec 1) (bvand $e15 (bvnot $e28)))
(define-fun $e107 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e105)))
(define-fun $e108 () (_ BitVec 1) (bvand (bvnot $e106) (bvnot $e107)))
(define-fun $e109 () (_ BitVec 1) (bvand autoname_7 autoname_8))
(define-fun $e110 () (_ BitVec 1) (bvand (bvnot local_dtack_0) $e109))
(define-fun $e111 () (_ BitVec 1) (bvand (bvnot $e64) (bvnot $e109)))
(define-fun $e112 () (_ BitVec 1) (bvand (bvnot $e110) (bvnot $e111)))
(define-fun $e113 () (_ BitVec 1) (bvand $e20 $e22))
(define-fun $e114 () (_ BitVec 1) (bvand (bvnot $e17) $e113))
(define-fun $e115 () (_ BitVec 1) (bvand $e16 (bvnot $e114)))
(define-fun $e116 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e30)))
(define-fun $e117 () (_ BitVec 1) (bvand (bvnot $e115) (bvnot $e116)))
(define-fun $e118 () (_ BitVec 1) (bvand reset_2 $e117))
(define-fun $e119 () (_ BitVec 1) (bvand $e15 (bvnot $e30)))
(define-fun $e120 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e118)))
(define-fun $e121 () (_ BitVec 1) (bvand (bvnot $e119) (bvnot $e120)))
(define-fun $e122 () (_ BitVec 1) (bvand $e16 (bvnot $e30)))
(define-fun $e123 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e31)))
(define-fun $e124 () (_ BitVec 1) (bvand (bvnot $e122) (bvnot $e123)))
(define-fun $e125 () (_ BitVec 1) (bvand reset_2 $e124))
(define-fun $e126 () (_ BitVec 1) (bvand $e15 (bvnot $e31)))
(define-fun $e127 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e125)))
(define-fun $e128 () (_ BitVec 1) (bvand (bvnot $e126) (bvnot $e127)))
(define-fun $e129 () (_ BitVec 1) (bvand $e16 (bvnot $e31)))
(define-fun $e130 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e32)))
(define-fun $e131 () (_ BitVec 1) (bvand (bvnot $e129) (bvnot $e130)))
(define-fun $e132 () (_ BitVec 1) (bvand reset_2 $e131))
(define-fun $e133 () (_ BitVec 1) (bvand $e15 (bvnot $e32)))
(define-fun $e134 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e132)))
(define-fun $e135 () (_ BitVec 1) (bvand (bvnot $e133) (bvnot $e134)))
(define-fun $e136 () (_ BitVec 1) (bvand (bvnot $e31) (bvnot $e35)))
(define-fun $e137 () (_ BitVec 1) (bvand (bvnot $e30) $e136))
(define-fun $e138 () (_ BitVec 1) (bvand (bvnot $e28) $e137))
(define-fun $e139 () (_ BitVec 1) (bvand (bvnot $e27) $e138))
(define-fun $e140 () (_ BitVec 1) (bvand (bvnot $e26) $e139))
(define-fun $e141 () (_ BitVec 1) (bvand (bvnot $e25) $e140))
(define-fun $e142 () (_ BitVec 1) (bvand (bvnot $e20) $e141))
(define-fun $e143 () (_ BitVec 1) (bvand (bvnot $e17) $e142))
(define-fun $e144 () (_ BitVec 1) (bvand $e16 (bvnot $e143)))
(define-fun $e145 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e33)))
(define-fun $e146 () (_ BitVec 1) (bvand (bvnot $e144) (bvnot $e145)))
(define-fun $e147 () (_ BitVec 1) (bvand reset_2 $e146))
(define-fun $e148 () (_ BitVec 1) (bvand $e15 (bvnot $e33)))
(define-fun $e149 () (_ BitVec 1) (bvand (bvnot $e15) (bvnot $e147)))
(define-fun $e150 () (_ BitVec 1) (bvand (bvnot $e148) (bvnot $e149)))
(define-fun $e151 () (_ BitVec 1) (bvand (bvnot autoname_7) (bvnot vme_iack_in_1)))
(define-fun $e152 () (_ BitVec 1) (bvand (bvnot $e64) $e151))
(define-fun $e153 () (_ BitVec 1) (bvand (bvnot local_dtack_0) (bvnot $e151)))
(define-fun $e154 () (_ BitVec 1) (bvand (bvnot $e152) (bvnot $e153)))
(define-fun $e155 () (_ BitVec 1) (bvand $e150 (bvnot $e154)))
(define-fun $e156 () (_ BitVec 1) (bvand (bvnot local_dtack_0) (bvnot $e150)))
(define-fun $e157 () (_ BitVec 1) (bvand (bvnot $e155) (bvnot $e156)))
(define-fun $e158 () (_ BitVec 1) (bvand local_dtack_0 $e135))
(define-fun $e159 () (_ BitVec 1) (bvand (bvnot $e135) (bvnot $e157)))
(define-fun $e160 () (_ BitVec 1) (bvand (bvnot $e158) (bvnot $e159)))
(define-fun $e161 () (_ BitVec 1) (bvand (bvnot $e64) $e128))
(define-fun $e162 () (_ BitVec 1) (bvand (bvnot $e128) (bvnot $e160)))
(define-fun $e163 () (_ BitVec 1) (bvand (bvnot $e161) (bvnot $e162)))
(define-fun $e164 () (_ BitVec 1) (bvand (bvnot $e64) $e121))
(define-fun $e165 () (_ BitVec 1) (bvand (bvnot $e121) (bvnot $e163)))
(define-fun $e166 () (_ BitVec 1) (bvand (bvnot $e164) (bvnot $e165)))
(define-fun $e167 () (_ BitVec 1) (bvand $e108 (bvnot $e112)))
(define-fun $e168 () (_ BitVec 1) (bvand (bvnot $e108) (bvnot $e166)))
(define-fun $e169 () (_ BitVec 1) (bvand (bvnot $e167) (bvnot $e168)))
(define-fun $e170 () (_ BitVec 1) (bvand local_dtack_0 $e92))
(define-fun $e171 () (_ BitVec 1) (bvand (bvnot $e92) (bvnot $e169)))
(define-fun $e172 () (_ BitVec 1) (bvand (bvnot $e170) (bvnot $e171)))
(define-fun $e173 () (_ BitVec 1) (bvand (bvnot $e64) $e85))
(define-fun $e174 () (_ BitVec 1) (bvand (bvnot $e85) (bvnot $e172)))
(define-fun $e175 () (_ BitVec 1) (bvand (bvnot $e173) (bvnot $e174)))
(define-fun $e176 () (_ BitVec 1) (bvand (bvnot $e64) $e78))
(define-fun $e177 () (_ BitVec 1) (bvand (bvnot $e78) (bvnot $e175)))
(define-fun $e178 () (_ BitVec 1) (bvand (bvnot $e176) (bvnot $e177)))
(define-fun $e179 () (_ BitVec 1) (bvand $e63 (bvnot $e64)))
(define-fun $e180 () (_ BitVec 1) (bvand (bvnot $e63) (bvnot $e178)))
(define-fun $e181 () (_ BitVec 1) (bvand (bvnot $e179) (bvnot $e180)))
(define-fun $e182 () (_ BitVec 1) (bvand (bvnot local_dtack_0) $e56))
(define-fun $e183 () (_ BitVec 1) (bvand (bvnot $e56) (bvnot $e181)))
(define-fun $e184 () (_ BitVec 1) (bvand (bvnot $e182) (bvnot $e183)))
(define-fun $e185 () (_ BitVec 1) (bvand $e12 (bvnot $e184)))
(define-fun $e186 () (_ BitVec 1) (bvand (bvnot $e12) (bvnot $e64)))
(define-fun $e187 () (_ BitVec 1) (bvand (bvnot $e185) (bvnot $e186)))
(define-fun $e188 () (_ BitVec 1) (bvand reset_1 (bvnot $e187)))
(define-fun $e189 () (_ BitVec 1) (bvand (bvnot local_dtack_0) (bvnot reset_1)))
(define-fun $e190 () (_ BitVec 1) (bvand (bvnot $e188) (bvnot $e189)))
(define-fun $e191 () (_ BitVec 1) (bvand $e11 (bvnot $e64)))
(define-fun $e192 () (_ BitVec 1) (bvand (bvnot $e11) (bvnot $e190)))
(assert (not (= (bvnot $e191) #b0)))
(assert (not (= (bvnot $e192) #b0)))
(check-sat)
(exit)
