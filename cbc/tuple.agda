module tuple where

open import Level



_×_ : {l : Level} -> Set l -> Set l -> Set (suc l)
_×_ {l} U V = {X : Set  l} -> (U -> V -> X) -> X

<_,_> : {l : Level} {A B : Set l} -> A -> B -> A × B
<_,_> {l} {A} {B} a b = \{X : Set l} -> \(x : A -> B -> X) -> x a b


CodeSegment : {l : Level} -> Set l -> Set l -> Set l -> Set l -> Set (suc l)
CodeSegment A B C D  = (A × B) -> (C × D)


data Nat : Set where
  O : Nat
  S : Nat -> Nat

data Unit : Set where
  unit : Unit


fst : {l : Level} {A B : Set l} -> A × B  -> A
fst x = x (\a b -> a)

snd : {l : Level} {A B : Set l} -> A × B -> B
snd x = x (\a b -> b)



plus1 : CodeSegment Nat Unit Nat Unit
plus1 a = < (S (fst a)) , unit >


twice' : Nat -> Nat
twice' O     = O
twice' (S n) = (S (S (twice' n)))

twice : CodeSegment Nat Unit Nat Unit
twice a = < (twice' (fst a)) , unit >


_∘_ : {l : Level} {A B C D E F : Set l} -> CodeSegment C D E F -> CodeSegment A B C D -> CodeSegment A B E F
_∘_ cs2 cs1 x = cs2 (cs1 x)


hoge : CodeSegment Nat Unit Nat Unit
hoge = ((plus1 ∘ twice) ∘ twice)
