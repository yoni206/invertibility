
(set-option :produce-models true)
(declare-fun certora_certoraAssumet1_1 () (_ BitVec 256))
(declare-fun b_0 () (_ BitVec 256))
(declare-fun certoraTPos_1 () Bool)
(declare-fun certoraAssume_1 () Bool)
(declare-fun certora_ct2_1 () (_ BitVec 256))
(declare-fun certoraDivisionByZero_1 () Bool)
(declare-fun certoraAssert_1_1 () Bool)
(declare-fun OK_0_0_0_0_0_0_0 () Bool)

(assert (not (=> (= OK_0_0_0_0_0_0_0 (=> (= certora_certoraAssumet1_1 b_0) (=> (= certoraTPos_1 (= certora_certoraAssumet1_1 (_ bv0 256))) (=> (= certoraAssume_1 (not certoraTPos_1)) (=> certoraAssume_1 (=> (= certora_ct2_1 b_0) (=> (= certoraDivisionByZero_1 (= certora_ct2_1 (_ bv0 256))) (and (not certoraDivisionByZero_1) (=> (= certoraAssert_1_1 true) (and certoraAssert_1_1 true)))))))))) OK_0_0_0_0_0_0_0)))
(check-sat)
(get-model)
