open import systemT
open import Relation.Binary.PropositionalEquality

module boolean where

_and_ : Bool -> Bool -> Bool
T and b = b
F and _ = F

_or_ : Bool -> Bool -> Bool
T or _ = T
F or b = b

not : Bool -> Bool
not T = F
not F = T

De-Morgan's-laws : (a b : Bool) -> (not a) and (not b) ≡ not (a or b)
De-Morgan's-laws T T = refl
De-Morgan's-laws T F = refl
De-Morgan's-laws F T = refl
De-Morgan's-laws F F = refl
