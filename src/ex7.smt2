(declare-const A (Array Int Real))
(declare-const B (Array Int Real))
(assert (= (store A 1 3.14) B)) ; $B \gets A[1 \mapsto 3.14]$
(assert (= (select B 1) 3.14)) ; assert: $B[1] = 3.14$
(assert (= (select B 2) 6.28)) ; assert: $B[2] = 6.28$
(check-sat); find viable $A$ and $B$
(get-model)