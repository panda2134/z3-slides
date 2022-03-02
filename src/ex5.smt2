(declare-fun f (Bool Bool) Bool)

(assert (= (f false false) false))
(assert (= (f false true) true))
(assert (= (f true false) true))
(assert (= (f true true) false))
(check-sat)
(get-model)