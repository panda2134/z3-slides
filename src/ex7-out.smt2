((define-fun A () (Array Int Real) ; const array of $6.28$
   ((as const (Array Int Real)) (/ 157.0 25.0)))
 (define-fun B () (Array Int Real)
   (store ((as const (Array Int Real)) ; const array of $6.28$
     (/ 157.0 25.0)) 1 (/ 157.0 50.0))))
     ; store $3.14$ to position $1$