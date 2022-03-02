(assert
  (not (exists ((i Int) (j Int)) 
               (and (< i j) (> (select A i) (select A j))))
))