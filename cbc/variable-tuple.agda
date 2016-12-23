module variable-tuple where

open import Data.Nat hiding (_<_ ; _>_)
open import Data.String
open import Data.List
open import Data.Unit
open import Data.Product
open import Function using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality
open import Level hiding (zero)

data Format : Set₁ where
  FEnd : Format
  FSet : Set -> Format -> Format

<> : Format
<> = FEnd

infix  51 _>
_> : (Format -> Format) -> Format
_> f = f FEnd

infixl 52 _||_
_||_ : (Format -> Format) -> Set -> (Format -> Format)
_||_ f1 s = f1 ∘ (FSet s)

infix 53 <_
<_ : Set -> Format -> Format
<_ s = FSet s


unit : Format
unit = <>

single : Format
single = < ℕ  >

double : Format
double = < String || ℕ  >

triple : Format
triple = < String || ℕ  || (List ℕ) >

