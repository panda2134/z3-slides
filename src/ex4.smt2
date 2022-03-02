(declare-const x Int)

(assert (= (mod x 3) 2))
(assert (= (mod x 5) 3))
(assert (= (mod x 7) 2))
(assert (> x 0))

(check-sat)
(get-model)