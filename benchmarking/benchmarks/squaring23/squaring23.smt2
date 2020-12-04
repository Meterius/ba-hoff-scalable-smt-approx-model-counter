(set-logic QF_BV)
(declare-fun clk_0 () (_ BitVec 1))
(declare-fun clk_1 () (_ BitVec 1))
(declare-fun clk_2 () (_ BitVec 1))
(declare-fun count1_0 () (_ BitVec 16))
(declare-fun count1_1 () (_ BitVec 16))
(declare-fun count1_2 () (_ BitVec 16))
(declare-fun flashclock1_1 () (_ BitVec 1))
(declare-fun flashclock1_2 () (_ BitVec 1))
(declare-fun rst_0 () (_ BitVec 1))
(declare-fun rst_1 () (_ BitVec 1))
(declare-fun rst_2 () (_ BitVec 1))
(declare-fun sflashclock1_0 () (_ BitVec 1))
(declare-fun sflashclock1_1 () (_ BitVec 1))
(declare-fun sflashclock1_2 () (_ BitVec 1))
(define-fun $e1 () (_ BitVec 16) (_ bv0 16))
(define-fun $e2 () (_ BitVec 1) (bvand (bvnot flashclock1_1) (bvnot sflashclock1_1)))
(define-fun $e3 () (_ BitVec 1) (bvand flashclock1_1 sflashclock1_1))
(define-fun $e4 () (_ BitVec 1) (bvand (bvnot $e2) (bvnot $e3)))
(define-fun $e5 () (_ BitVec 1) (bvand (bvnot clk_0) (bvnot clk_1)))
(define-fun $e6 () (_ BitVec 1) (bvand clk_0 clk_1))
(define-fun $e7 () (_ BitVec 1) (bvand (bvnot $e5) (bvnot $e6)))
(define-fun $e8 () (_ BitVec 1) (bvand (bvnot rst_0) (bvnot rst_1)))
(define-fun $e9 () (_ BitVec 1) (bvand rst_0 rst_1))
(define-fun $e10 () (_ BitVec 1) (bvand (bvnot $e8) (bvnot $e9)))
(define-fun $e11 () (_ BitVec 16) (bvmul count1_1 (bvnot $e1)))
(define-fun $e12 () (_ BitVec 16) (bvadd count1_0 $e11))
(define-fun $e13 () (_ BitVec 1) (ite (= $e1 $e12) #b1 #b0))
(define-fun $e14 () (_ BitVec 1) (bvand (bvnot sflashclock1_0) (bvnot sflashclock1_1)))
(define-fun $e15 () (_ BitVec 1) (bvand sflashclock1_0 sflashclock1_1))
(define-fun $e16 () (_ BitVec 1) (bvand (bvnot $e14) (bvnot $e15)))
(define-fun $e17 () (_ BitVec 1) (bvand (bvnot flashclock1_2) (bvnot sflashclock1_2)))
(define-fun $e18 () (_ BitVec 1) (bvand flashclock1_2 sflashclock1_2))
(define-fun $e19 () (_ BitVec 1) (bvand (bvnot $e17) (bvnot $e18)))
(define-fun $e20 () (_ BitVec 1) (bvand (bvnot clk_1) (bvnot clk_2)))
(define-fun $e21 () (_ BitVec 1) (bvand clk_1 clk_2))
(define-fun $e22 () (_ BitVec 1) (bvand (bvnot $e20) (bvnot $e21)))
(define-fun $e23 () (_ BitVec 1) (bvand (bvnot rst_1) (bvnot rst_2)))
(define-fun $e24 () (_ BitVec 1) (bvand rst_1 rst_2))
(define-fun $e25 () (_ BitVec 1) (bvand (bvnot $e23) (bvnot $e24)))
(define-fun $e26 () (_ BitVec 16) (bvmul count1_2 (bvnot $e1)))
(define-fun $e27 () (_ BitVec 16) (bvadd count1_1 $e26))
(define-fun $e28 () (_ BitVec 1) (ite (= $e1 $e27) #b1 #b0))
(define-fun $e29 () (_ BitVec 1) (bvand (bvnot sflashclock1_1) (bvnot sflashclock1_2)))
(define-fun $e30 () (_ BitVec 1) (bvand sflashclock1_1 sflashclock1_2))
(define-fun $e31 () (_ BitVec 1) (bvand (bvnot $e29) (bvnot $e30)))
(define-fun $e32 () (_ BitVec 1) (bvand $e28 (bvnot $e31)))
(define-fun $e33 () (_ BitVec 1) (bvand sflashclock1_2 $e28))
(define-fun $e34 () (_ BitVec 1) (bvand rst_2 (bvnot $e33)))
(define-fun $e35 () (_ BitVec 1) (bvand (bvnot rst_2) (bvnot $e32)))
(define-fun $e36 () (_ BitVec 1) (bvand (bvnot $e34) (bvnot $e35)))
(define-fun $e37 () (_ BitVec 1) (bvand $e25 (bvnot $e36)))
(define-fun $e38 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e32)))
(define-fun $e39 () (_ BitVec 1) (bvand (bvnot $e37) (bvnot $e38)))
(define-fun $e40 () (_ BitVec 1) (bvand (bvnot clk_2) (bvnot $e31)))
(define-fun $e41 () (_ BitVec 1) (ite (= count1_1 (bvnot $e1)) #b1 #b0))
(define-fun $e42 () (_ BitVec 1) (ite (= count1_2 $e1) #b1 #b0))
(define-fun $e43 () (_ BitVec 1) (bvand $e31 $e42))
(define-fun $e44 () (_ BitVec 1) (ite (= (bvnot $e1) $e27) #b1 #b0))
(define-fun $e45 () (_ BitVec 1) (bvand (bvnot $e31) $e44))
(define-fun $e46 () (_ BitVec 1) (bvand $e41 (bvnot $e43)))
(define-fun $e47 () (_ BitVec 1) (bvand (bvnot $e41) (bvnot $e45)))
(define-fun $e48 () (_ BitVec 1) (bvand (bvnot $e46) (bvnot $e47)))
(define-fun $e49 () (_ BitVec 1) (bvand clk_2 $e48))
(define-fun $e50 () (_ BitVec 1) (bvand $e28 (bvnot $e40)))
(define-fun $e51 () (_ BitVec 1) (bvand (bvnot $e28) (bvnot $e49)))
(define-fun $e52 () (_ BitVec 1) (bvand (bvnot $e50) (bvnot $e51)))
(define-fun $e53 () (_ BitVec 1) (bvand (bvnot rst_2) (bvnot $e52)))
(define-fun $e54 () (_ BitVec 1) (bvand (bvnot $e34) (bvnot $e53)))
(define-fun $e55 () (_ BitVec 1) (bvand $e22 (bvnot $e54)))
(define-fun $e56 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e39)))
(define-fun $e57 () (_ BitVec 1) (bvand (bvnot $e55) (bvnot $e56)))
(define-fun $e58 () (_ BitVec 1) (bvand (bvnot $e19) $e57))
(define-fun $e59 () (_ BitVec 1) (bvand (bvnot $e16) $e58))
(define-fun $e60 () (_ BitVec 1) (bvand $e13 $e59))
(define-fun $e61 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e32)))
(define-fun $e62 () (_ BitVec 1) (bvand (bvnot $e55) (bvnot $e61)))
(define-fun $e63 () (_ BitVec 1) (bvand (bvnot $e19) $e62))
(define-fun $e64 () (_ BitVec 1) (bvand sflashclock1_1 $e63))
(define-fun $e65 () (_ BitVec 1) (bvand $e13 $e64))
(define-fun $e66 () (_ BitVec 1) (bvand $e25 (bvnot $e33)))
(define-fun $e67 () (_ BitVec 1) (bvand (bvnot $e38) (bvnot $e66)))
(define-fun $e68 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e67)))
(define-fun $e69 () (_ BitVec 1) (bvand (bvnot $e55) (bvnot $e68)))
(define-fun $e70 () (_ BitVec 1) (bvand (bvnot $e19) $e69))
(define-fun $e71 () (_ BitVec 1) (bvand (bvnot $e16) $e70))
(define-fun $e72 () (_ BitVec 1) (bvand $e13 $e71))
(define-fun $e73 () (_ BitVec 1) (bvand rst_1 (bvnot $e65)))
(define-fun $e74 () (_ BitVec 1) (bvand (bvnot rst_1) (bvnot $e72)))
(define-fun $e75 () (_ BitVec 1) (bvand (bvnot $e73) (bvnot $e74)))
(define-fun $e76 () (_ BitVec 1) (bvand $e10 (bvnot $e75)))
(define-fun $e77 () (_ BitVec 1) (bvand (bvnot $e10) (bvnot $e60)))
(define-fun $e78 () (_ BitVec 1) (bvand (bvnot $e76) (bvnot $e77)))
(define-fun $e79 () (_ BitVec 1) (bvand (bvnot $e28) $e48))
(define-fun $e80 () (_ BitVec 1) (bvand (bvnot rst_2) (bvnot $e79)))
(define-fun $e81 () (_ BitVec 1) (bvand (bvnot $e34) (bvnot $e80)))
(define-fun $e82 () (_ BitVec 1) (bvand $e22 (bvnot $e81)))
(define-fun $e83 () (_ BitVec 1) (bvand (bvnot $e68) (bvnot $e82)))
(define-fun $e84 () (_ BitVec 1) (bvand (bvnot $e19) $e83))
(define-fun $e85 () (_ BitVec 1) (bvand (bvnot $e16) $e84))
(define-fun $e86 () (_ BitVec 1) (bvand (bvnot clk_1) $e85))
(define-fun $e87 () (_ BitVec 1) (ite (= count1_0 (bvnot $e1)) #b1 #b0))
(define-fun $e88 () (_ BitVec 1) (ite (= count1_1 $e1) #b1 #b0))
(define-fun $e89 () (_ BitVec 1) (bvand $e22 (bvnot $e36)))
(define-fun $e90 () (_ BitVec 1) (bvand (bvnot $e68) (bvnot $e89)))
(define-fun $e91 () (_ BitVec 1) (bvand (bvnot $e19) $e90))
(define-fun $e92 () (_ BitVec 1) (ite (= $e1 $e26) #b1 #b0))
(define-fun $e93 () (_ BitVec 1) (bvand (bvnot $e31) $e92))
(define-fun $e94 () (_ BitVec 1) (bvand (bvnot $e25) (bvnot $e93)))
(define-fun $e95 () (_ BitVec 1) (bvand sflashclock1_2 $e92))
(define-fun $e96 () (_ BitVec 1) (bvand $e25 (bvnot $e95)))
(define-fun $e97 () (_ BitVec 1) (bvand (bvnot $e94) (bvnot $e96)))
(define-fun $e98 () (_ BitVec 1) (bvand (bvnot $e22) (bvnot $e97)))
(define-fun $e99 () (_ BitVec 1) (bvand rst_2 (bvnot $e95)))
(define-fun $e100 () (_ BitVec 1) (bvand (bvnot rst_2) (bvnot $e93)))
(define-fun $e101 () (_ BitVec 1) (bvand (bvnot $e99) (bvnot $e100)))
(define-fun $e102 () (_ BitVec 1) (bvand $e22 (bvnot $e101)))
(define-fun $e103 () (_ BitVec 1) (bvand (bvnot $e98) (bvnot $e102)))
(define-fun $e104 () (_ BitVec 1) (bvand (bvnot $e19) $e103))
(define-fun $e105 () (_ BitVec 1) (bvand $e16 $e104))
(define-fun $e106 () (_ BitVec 1) (bvand $e88 $e105))
(define-fun $e107 () (_ BitVec 1) (ite (= (bvnot $e1) $e12) #b1 #b0))
(define-fun $e108 () (_ BitVec 1) (bvand (bvnot $e16) $e91))
(define-fun $e109 () (_ BitVec 1) (bvand $e107 $e108))
(define-fun $e110 () (_ BitVec 1) (bvand $e87 (bvnot $e106)))
(define-fun $e111 () (_ BitVec 1) (bvand (bvnot $e87) (bvnot $e109)))
(define-fun $e112 () (_ BitVec 1) (bvand (bvnot $e110) (bvnot $e111)))
(define-fun $e113 () (_ BitVec 1) (bvand clk_1 $e112))
(define-fun $e114 () (_ BitVec 1) (bvand $e13 (bvnot $e86)))
(define-fun $e115 () (_ BitVec 1) (bvand (bvnot $e13) (bvnot $e113)))
(define-fun $e116 () (_ BitVec 1) (bvand (bvnot $e114) (bvnot $e115)))
(define-fun $e117 () (_ BitVec 1) (bvand (bvnot rst_1) (bvnot $e116)))
(define-fun $e118 () (_ BitVec 1) (bvand (bvnot $e73) (bvnot $e117)))
(define-fun $e119 () (_ BitVec 1) (bvand $e7 (bvnot $e118)))
(define-fun $e120 () (_ BitVec 1) (bvand (bvnot $e7) (bvnot $e78)))
(assert (not (= (bvnot $e119) #b0)))
(assert (not (= (bvnot $e120) #b0)))
(assert (not (= (bvnot $e4) #b0)))
(check-sat)
(exit)
