(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

(assert (let ((A (implies p q))
              (B (implies q r))
              (C (implies p r)))
             (not (implies A (implies B C)))))

(check-sat)