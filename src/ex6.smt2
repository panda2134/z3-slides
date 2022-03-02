(declare-const left (_ BitVec 32))
(declare-const right (_ BitVec 32))
(declare-const mid (_ BitVec 32))
(declare-const left_1 Int) (declare-const right_1 Int)
(declare-const mid_1 Int)
(assert (bvsle #x00000000 left))  ; $0 \le left \le right$
(assert (bvsle #x00000000 right))
(assert (bvsle left right))
(assert (= left_1 (bv2int left))) ; arbitrary precision
(assert (= right_1 (bv2int right)))
(assert (= mid (bvsdiv (bvadd left right) #x00000002)))
(assert (= mid_1 (div (+ left_1 right_1) 2)))
(assert (not (= (bv2int mid) mid_1))); mid is wrong
(check-sat) (get-model)