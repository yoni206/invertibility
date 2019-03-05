
(set-option :produce-models true)
(declare-fun certoraAssert_0_1 () Bool)
(declare-fun OK_0_0_0_0_0_0_0 () Bool)

(assert (not (=> (= OK_0_0_0_0_0_0_0 (=> (= certoraAssert_0_1 true) (and certoraAssert_0_1 true))) OK_0_0_0_0_0_0_0)))
(check-sat)
(get-model)
