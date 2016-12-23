module InferenceTypeComposition where

open import Relation.Binary.PropositionalEquality

infixl 30 _+++_
-- _+++_ : {A B C : Set} {equiv : B ≡ B} -> (A -> B) -> (B -> C) -> (A -> C)
_+++_ : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
_+++_ f g = \x -> g (f x)

comp-sample : {A B C D : Set} -> (A -> B) -> (B -> C) -> (C -> D) -> (A -> D)
comp-sample f g h = f +++ g +++ h
