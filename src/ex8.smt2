(assert
  (not (exists ((i Int) (j Int)) 
               (> (select A i) (select A j)))
))