(declare-const x Int)
(assert (>= (^ x 2) 5))
(assert (< (^ x 3) 30))
(check-sat)