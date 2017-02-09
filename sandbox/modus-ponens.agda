module modus-ponens where

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst < a , _ > = a

snd : {A B : Set} -> A × B -> B
snd < _ , b > = b

f : {A B C : Set} -> (A -> B) × (B -> C) -> (A -> C)
f = (\p x -> snd p ((fst p) x))
