; --------
; sat
; result of get-model: $f(x, y) := (\neg x \land y) \lor (x \land \neg y)$
( (define-fun f ((x!0 Bool) (x!1 Bool)) Bool
    (or (and (not x!0) x!1) (and x!0 (not x!1)))) )