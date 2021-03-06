(set-logic QF_BV)
(declare-fun autoname_1 () (_ BitVec 1))
(declare-fun autoname_2 () (_ BitVec 1))
(declare-fun b_sysres_0 () (_ BitVec 1))
(declare-fun b_sysres_1 () (_ BitVec 1))
(declare-fun state0 () (_ BitVec 4))
(declare-fun mvme_dtack_0 () (_ BitVec 1))
(declare-fun mvme_dtack_1 () (_ BitVec 1))
(declare-fun power_on_rst_0 () (_ BitVec 1))
(declare-fun power_on_rst_1 () (_ BitVec 1))
(declare-fun reset_0 () (_ BitVec 1))
(declare-fun sig_local_dtack_0 () (_ BitVec 1))
(declare-fun vme_dtack_0 () (_ BitVec 1))
(declare-fun vme_dtack_1 () (_ BitVec 1))
(declare-fun vme_iack_in_1 () (_ BitVec 1))
(define-fun $e1 () (_ BitVec 4) (_ bv0 4))
(define-fun $e2 () (_ BitVec 4) (_ bv14 4))
(define-fun $e3 () (_ BitVec 4) (_ bv2 4))
(define-fun $e4 () (_ BitVec 4) (_ bv12 4))
(define-fun $e5 () (_ BitVec 4) (_ bv4 4))
(define-fun $e6 () (_ BitVec 4) (_ bv10 4))
(define-fun $e7 () (_ BitVec 4) (_ bv6 4))
(define-fun $e8 () (_ BitVec 4) (_ bv8 4))
(define-fun $e9 () (_ BitVec 1) (ite (= power_on_rst_0 power_on_rst_1) #b1 #b0))
(define-fun $e10 () (_ BitVec 1) (ite (= b_sysres_0 b_sysres_1) #b1 #b0))
(define-fun $e11 () (_ BitVec 1) (bvand $e9 $e10))
(define-fun $e12 () (_ BitVec 1) (bvand b_sysres_1 power_on_rst_1))
(define-fun $e13 () (_ BitVec 1) (bvand reset_0 $e12))
(define-fun $e14 () (_ BitVec 1) (bvand (bvnot reset_0) (bvnot $e12)))
(define-fun $e15 () (_ BitVec 1) (bvand (bvnot $e13) (bvnot $e14)))
(define-fun $e16 () (_ BitVec 1) (bvand (bvnot $e11) $e15))
(define-fun $e17 () (_ BitVec 1) (bvand reset_0 $e11))
(define-fun $e18 () (_ BitVec 1) (bvand (bvnot $e11) $e12))
(define-fun $e19 () (_ BitVec 1) (bvand (bvnot $e17) (bvnot $e18)))
(define-fun $e20 () (_ BitVec 1) (ite (= state0 $e1) #b1 #b0))
(define-fun $e21 () (_ BitVec 1) (ite (= state0 (bvnot $e2)) #b1 #b0))
(define-fun $e22 () (_ BitVec 1) (ite (= state0 $e3) #b1 #b0))
(define-fun $e23 () (_ BitVec 1) (ite (= state0 (bvnot $e4)) #b1 #b0))
(define-fun $e24 () (_ BitVec 1) (ite (= state0 $e5) #b1 #b0))
(define-fun $e25 () (_ BitVec 1) (ite (= state0 (bvnot $e6)) #b1 #b0))
(define-fun $e26 () (_ BitVec 1) (bvand autoname_1 autoname_2))
(define-fun $e27 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) (bvnot $e26)))
(define-fun $e28 () (_ BitVec 1) (ite (= state0 $e7) #b1 #b0))
(define-fun $e29 () (_ BitVec 1) (ite (= state0 (bvnot $e8)) #b1 #b0))
(define-fun $e30 () (_ BitVec 1) (ite (= state0 $e8) #b1 #b0))
(define-fun $e31 () (_ BitVec 1) (ite (= state0 (bvnot $e7)) #b1 #b0))
(define-fun $e32 () (_ BitVec 1) (bvand (bvnot autoname_1) (bvnot vme_iack_in_1)))
(define-fun $e33 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e32))
(define-fun $e34 () (_ BitVec 1) (bvand $e31 $e33))
(define-fun $e35 () (_ BitVec 1) (bvand (bvnot $e30) (bvnot $e34)))
(define-fun $e36 () (_ BitVec 1) (bvand sig_local_dtack_0 $e29))
(define-fun $e37 () (_ BitVec 1) (bvand (bvnot $e29) $e35))
(define-fun $e38 () (_ BitVec 1) (bvand (bvnot $e36) (bvnot $e37)))
(define-fun $e39 () (_ BitVec 1) (bvand sig_local_dtack_0 $e28))
(define-fun $e40 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e38)))
(define-fun $e41 () (_ BitVec 1) (bvand (bvnot $e39) (bvnot $e40)))
(define-fun $e42 () (_ BitVec 1) (bvand $e25 (bvnot $e27)))
(define-fun $e43 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e41)))
(define-fun $e44 () (_ BitVec 1) (bvand (bvnot $e42) (bvnot $e43)))
(define-fun $e45 () (_ BitVec 1) (bvand (bvnot $e24) (bvnot $e44)))
(define-fun $e46 () (_ BitVec 1) (bvand sig_local_dtack_0 $e23))
(define-fun $e47 () (_ BitVec 1) (bvand (bvnot $e23) $e45))
(define-fun $e48 () (_ BitVec 1) (bvand (bvnot $e46) (bvnot $e47)))
(define-fun $e49 () (_ BitVec 1) (bvand sig_local_dtack_0 $e22))
(define-fun $e50 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e48)))
(define-fun $e51 () (_ BitVec 1) (bvand (bvnot $e49) (bvnot $e50)))
(define-fun $e52 () (_ BitVec 1) (bvand sig_local_dtack_0 $e21))
(define-fun $e53 () (_ BitVec 1) (bvand (bvnot $e21) (bvnot $e51)))
(define-fun $e54 () (_ BitVec 1) (bvand (bvnot $e52) (bvnot $e53)))
(define-fun $e55 () (_ BitVec 1) (bvand (bvnot $e20) $e54))
(define-fun $e56 () (_ BitVec 1) (bvand reset_0 $e55))
(define-fun $e57 () (_ BitVec 1) (bvand (bvnot $e19) $e56))
(define-fun $e58 () (_ BitVec 1) (bvand $e16 (bvnot $e57)))
(define-fun $e59 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e56)))
(define-fun $e60 () (_ BitVec 1) (bvand (bvnot $e58) (bvnot $e59)))
(define-fun $e61 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e26))
(define-fun $e62 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) (bvnot $e32)))
(define-fun $e63 () (_ BitVec 1) (bvand $e31 (bvnot $e62)))
(define-fun $e64 () (_ BitVec 1) (bvand sig_local_dtack_0 (bvnot $e31)))
(define-fun $e65 () (_ BitVec 1) (bvand (bvnot $e63) (bvnot $e64)))
(define-fun $e66 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e30))
(define-fun $e67 () (_ BitVec 1) (bvand (bvnot $e30) (bvnot $e65)))
(define-fun $e68 () (_ BitVec 1) (bvand (bvnot $e66) (bvnot $e67)))
(define-fun $e69 () (_ BitVec 1) (bvand (bvnot $e29) $e68))
(define-fun $e70 () (_ BitVec 1) (bvand (bvnot $e28) $e69))
(define-fun $e71 () (_ BitVec 1) (bvand $e25 (bvnot $e61)))
(define-fun $e72 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e70)))
(define-fun $e73 () (_ BitVec 1) (bvand (bvnot $e71) (bvnot $e72)))
(define-fun $e74 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e24))
(define-fun $e75 () (_ BitVec 1) (bvand (bvnot $e24) (bvnot $e73)))
(define-fun $e76 () (_ BitVec 1) (bvand (bvnot $e74) (bvnot $e75)))
(define-fun $e77 () (_ BitVec 1) (bvand (bvnot $e23) $e76))
(define-fun $e78 () (_ BitVec 1) (bvand (bvnot $e22) $e77))
(define-fun $e79 () (_ BitVec 1) (bvand (bvnot $e21) $e78))
(define-fun $e80 () (_ BitVec 1) (bvand sig_local_dtack_0 $e20))
(define-fun $e81 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e79)))
(define-fun $e82 () (_ BitVec 1) (bvand (bvnot $e80) (bvnot $e81)))
(define-fun $e83 () (_ BitVec 1) (bvand reset_0 (bvnot $e82)))
(define-fun $e84 () (_ BitVec 1) (bvand (bvnot reset_0) sig_local_dtack_0))
(define-fun $e85 () (_ BitVec 1) (bvand (bvnot $e83) (bvnot $e84)))
(define-fun $e86 () (_ BitVec 1) (bvand sig_local_dtack_0 $e19))
(define-fun $e87 () (_ BitVec 1) (bvand (bvnot $e19) (bvnot $e85)))
(define-fun $e88 () (_ BitVec 1) (bvand (bvnot $e86) (bvnot $e87)))
(define-fun $e89 () (_ BitVec 1) (bvand $e16 (bvnot $e88)))
(define-fun $e90 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e29))
(define-fun $e91 () (_ BitVec 1) (bvand (bvnot $e29) (bvnot $e35)))
(define-fun $e92 () (_ BitVec 1) (bvand (bvnot $e90) (bvnot $e91)))
(define-fun $e93 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e28))
(define-fun $e94 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e92)))
(define-fun $e95 () (_ BitVec 1) (bvand (bvnot $e93) (bvnot $e94)))
(define-fun $e96 () (_ BitVec 1) (bvand $e25 $e27))
(define-fun $e97 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e95)))
(define-fun $e98 () (_ BitVec 1) (bvand (bvnot $e96) (bvnot $e97)))
(define-fun $e99 () (_ BitVec 1) (bvand (bvnot $e24) $e98))
(define-fun $e100 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e23))
(define-fun $e101 () (_ BitVec 1) (bvand (bvnot $e23) (bvnot $e99)))
(define-fun $e102 () (_ BitVec 1) (bvand (bvnot $e100) (bvnot $e101)))
(define-fun $e103 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e22))
(define-fun $e104 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e102)))
(define-fun $e105 () (_ BitVec 1) (bvand (bvnot $e103) (bvnot $e104)))
(define-fun $e106 () (_ BitVec 1) (bvand (bvnot sig_local_dtack_0) $e21))
(define-fun $e107 () (_ BitVec 1) (bvand (bvnot $e21) (bvnot $e105)))
(define-fun $e108 () (_ BitVec 1) (bvand (bvnot $e106) (bvnot $e107)))
(define-fun $e109 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e108)))
(define-fun $e110 () (_ BitVec 1) (bvand reset_0 $e109))
(define-fun $e111 () (_ BitVec 1) (bvand (bvnot $e19) $e110))
(define-fun $e112 () (_ BitVec 1) (bvand $e16 $e111))
(define-fun $e113 () (_ BitVec 1) (bvand (bvnot $e16) $e110))
(define-fun $e114 () (_ BitVec 1) (bvand (bvnot $e112) (bvnot $e113)))
(define-fun $e115 () (_ BitVec 1) (bvand reset_0 $e33))
(define-fun $e116 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e115)))
(define-fun $e117 () (_ BitVec 1) (bvand reset_0 (bvnot $e62)))
(define-fun $e118 () (_ BitVec 1) (bvand (bvnot $e84) (bvnot $e117)))
(define-fun $e119 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e118)))
(define-fun $e120 () (_ BitVec 1) (bvand (bvnot $e89) (bvnot $e119)))
(define-fun $e121 () (_ BitVec 1) (bvand $e32 (bvnot $e120)))
(define-fun $e122 () (_ BitVec 1) (bvand (bvnot $e19) $e115))
(define-fun $e123 () (_ BitVec 1) (bvand $e16 (bvnot $e122)))
(define-fun $e124 () (_ BitVec 1) (bvand (bvnot $e116) (bvnot $e123)))
(define-fun $e125 () (_ BitVec 1) (bvand (bvnot $e32) (bvnot $e124)))
(define-fun $e126 () (_ BitVec 1) (bvand (bvnot $e121) (bvnot $e125)))
(define-fun $e127 () (_ BitVec 1) (bvand $e31 (bvnot $e126)))
(define-fun $e128 () (_ BitVec 1) (bvand (bvnot $e31) (bvnot $e60)))
(define-fun $e129 () (_ BitVec 1) (bvand (bvnot $e127) (bvnot $e128)))
(define-fun $e130 () (_ BitVec 1) (bvand reset_0 (bvnot $e19)))
(define-fun $e131 () (_ BitVec 1) (bvand $e16 $e130))
(define-fun $e132 () (_ BitVec 1) (bvand reset_0 (bvnot $e16)))
(define-fun $e133 () (_ BitVec 1) (bvand (bvnot $e131) (bvnot $e132)))
(define-fun $e134 () (_ BitVec 1) (bvand $e30 (bvnot $e133)))
(define-fun $e135 () (_ BitVec 1) (bvand (bvnot $e30) (bvnot $e129)))
(define-fun $e136 () (_ BitVec 1) (bvand (bvnot $e134) (bvnot $e135)))
(define-fun $e137 () (_ BitVec 1) (bvand (bvnot reset_0) (bvnot sig_local_dtack_0)))
(define-fun $e138 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e137)))
(define-fun $e139 () (_ BitVec 1) (bvand (bvnot $e19) (bvnot $e137)))
(define-fun $e140 () (_ BitVec 1) (bvand (bvnot $e86) (bvnot $e139)))
(define-fun $e141 () (_ BitVec 1) (bvand $e16 (bvnot $e140)))
(define-fun $e142 () (_ BitVec 1) (bvand (bvnot $e138) (bvnot $e141)))
(define-fun $e143 () (_ BitVec 1) (bvand $e29 (bvnot $e142)))
(define-fun $e144 () (_ BitVec 1) (bvand (bvnot $e29) (bvnot $e136)))
(define-fun $e145 () (_ BitVec 1) (bvand (bvnot $e143) (bvnot $e144)))
(define-fun $e146 () (_ BitVec 1) (bvand $e28 (bvnot $e142)))
(define-fun $e147 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e145)))
(define-fun $e148 () (_ BitVec 1) (bvand (bvnot $e146) (bvnot $e147)))
(define-fun $e149 () (_ BitVec 1) (bvand reset_0 $e27))
(define-fun $e150 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e149)))
(define-fun $e151 () (_ BitVec 1) (bvand (bvnot $e19) $e149))
(define-fun $e152 () (_ BitVec 1) (bvand $e16 (bvnot $e151)))
(define-fun $e153 () (_ BitVec 1) (bvand (bvnot $e150) (bvnot $e152)))
(define-fun $e154 () (_ BitVec 1) (bvand $e26 (bvnot $e153)))
(define-fun $e155 () (_ BitVec 1) (bvand reset_0 (bvnot $e61)))
(define-fun $e156 () (_ BitVec 1) (bvand (bvnot $e84) (bvnot $e155)))
(define-fun $e157 () (_ BitVec 1) (bvand (bvnot $e16) (bvnot $e156)))
(define-fun $e158 () (_ BitVec 1) (bvand (bvnot $e89) (bvnot $e157)))
(define-fun $e159 () (_ BitVec 1) (bvand (bvnot $e26) (bvnot $e158)))
(define-fun $e160 () (_ BitVec 1) (bvand (bvnot $e154) (bvnot $e159)))
(define-fun $e161 () (_ BitVec 1) (bvand $e25 (bvnot $e160)))
(define-fun $e162 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e148)))
(define-fun $e163 () (_ BitVec 1) (bvand (bvnot $e161) (bvnot $e162)))
(define-fun $e164 () (_ BitVec 1) (bvand $e24 (bvnot $e133)))
(define-fun $e165 () (_ BitVec 1) (bvand (bvnot $e24) (bvnot $e163)))
(define-fun $e166 () (_ BitVec 1) (bvand (bvnot $e164) (bvnot $e165)))
(define-fun $e167 () (_ BitVec 1) (bvand $e23 (bvnot $e142)))
(define-fun $e168 () (_ BitVec 1) (bvand (bvnot $e23) (bvnot $e166)))
(define-fun $e169 () (_ BitVec 1) (bvand (bvnot $e167) (bvnot $e168)))
(define-fun $e170 () (_ BitVec 1) (bvand $e22 (bvnot $e142)))
(define-fun $e171 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e169)))
(define-fun $e172 () (_ BitVec 1) (bvand (bvnot $e170) (bvnot $e171)))
(define-fun $e173 () (_ BitVec 1) (bvand $e21 (bvnot $e142)))
(define-fun $e174 () (_ BitVec 1) (bvand (bvnot $e21) (bvnot $e172)))
(define-fun $e175 () (_ BitVec 1) (bvand (bvnot $e173) (bvnot $e174)))
(define-fun $e176 () (_ BitVec 1) (bvand (bvnot $e20) $e175))
(define-fun $e177 () (_ BitVec 1) (bvand reset_0 (bvnot $e176)))
(define-fun $e178 () (_ BitVec 1) (bvand (bvnot reset_0) (bvnot $e60)))
(define-fun $e179 () (_ BitVec 1) (bvand (bvnot $e177) (bvnot $e178)))
(define-fun $e180 () (_ BitVec 1) (bvand mvme_dtack_1 $e114))
(define-fun $e181 () (_ BitVec 1) (ite (= vme_dtack_1 $e180) #b1 #b0))
(define-fun $e182 () (_ BitVec 1) (bvand mvme_dtack_1 (bvnot $e110)))
(define-fun $e183 () (_ BitVec 1) (ite (= vme_dtack_1 $e182) #b1 #b0))
(define-fun $e184 () (_ BitVec 1) (ite (= mvme_dtack_0 mvme_dtack_1) #b1 #b0))
(define-fun $e185 () (_ BitVec 1) (bvand mvme_dtack_1 sig_local_dtack_0))
(define-fun $e186 () (_ BitVec 1) (ite (= vme_dtack_1 $e185) #b1 #b0))
(define-fun $e187 () (_ BitVec 1) (ite (= vme_dtack_0 vme_dtack_1) #b1 #b0))
(define-fun $e188 () (_ BitVec 1) (bvand $e184 (bvnot $e187)))
(define-fun $e189 () (_ BitVec 1) (bvand (bvnot $e184) (bvnot $e186)))
(define-fun $e190 () (_ BitVec 1) (bvand (bvnot $e188) (bvnot $e189)))
(define-fun $e191 () (_ BitVec 1) (bvand $e85 (bvnot $e183)))
(define-fun $e192 () (_ BitVec 1) (bvand (bvnot $e85) (bvnot $e190)))
(define-fun $e193 () (_ BitVec 1) (bvand (bvnot $e191) (bvnot $e192)))
(define-fun $e194 () (_ BitVec 1) (bvand $e179 (bvnot $e181)))
(define-fun $e195 () (_ BitVec 1) (bvand (bvnot $e179) (bvnot $e193)))
(assert (not (= (bvnot $e194) #b0)))
(assert (not (= (bvnot $e195) #b0)))
(check-sat)
(exit)
