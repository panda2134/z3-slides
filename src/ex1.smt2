(declare-const x Real)
(declare-const y Real)
(assert
 (= (+ (* 2 x) y) 5))
(assert
 (= (+ x y) 3))
(check-sat)
(get-model)