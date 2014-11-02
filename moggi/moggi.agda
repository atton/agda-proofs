module moggi where


postulate A : Set
postulate A1 : Set
postulate A2 : Set

postulate x : A
postulate e1 : A1
--postulate f : A1 -> A2

data _==_ : {A : Set} -> A -> A -> Set where
  refl  : {x : A} -> x == x
  sym   : {x y : A} -> x == y -> y == x
  trans : {x y z : A} -> x == y -> y == z -> x == z
  congr : {x y : A1} -> (f : A1 -> A2) -> x == y -> 
            f x == f y

record Term (A : Set) : Set where
  field
    type : A
    var  : A -> (A -> A)
    f    : A1 -> A2
    eq   : (g1 : A1 -> A2) -> (g2 : A1 -> A2) -> g1 == g2

