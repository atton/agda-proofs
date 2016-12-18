module variable-tuple where

open import Data.Nat hiding (_<_ ; _>_)
open import Data.String
open import Data.List
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

data Format : Set₁ where
  FEnd : Format
  FSet : Set -> Format -> Format

<> : Format
<> = FEnd

{-
  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≅⟨_⟩_ : ∀ (x {y z} : A) → x ≅ y → y ≡ z → x ≡ z
  _ ≅⟨ x≅y ⟩ y≡z = trans (H.≅-to-≡ x≅y) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl
-}

infix  51 _>
_> : (Format -> Format) -> Format
_> f = f FEnd

infixl 52 _||_
_||_ : (Format -> Format) -> Set -> (Format -> Format)
_||_ f1 s = f1 ∘ (FSet s)

infix 54 <_
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
