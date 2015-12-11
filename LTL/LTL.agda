-- Principles of Model Checking

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module LTL where

-- Syntax Definition (p227)

data AP : Set where

data LTL : Set  where
  true     : LTL
  ap       : AP -> LTL
  _and_    : LTL -> LTL -> LTL
  not      : LTL -> LTL
  next     : LTL -> LTL
  _until_  : LTL -> LTL -> LTL


_or_ : LTL -> LTL -> LTL
a or b = not ((not a) and (not b))

_implies_ : LTL -> LTL -> LTL
a implies b = (not a) or b

_equiv_ : LTL -> LTL -> LTL
a equiv b = (a implies b) and (b implies a)

_xor_  : LTL -> LTL -> LTL
a xor b = (a and (not b)) or (b and (not a))

eventually : LTL -> LTL
eventually a = true until a

always : LTL -> LTL
always a = not (eventually (not a))

-- Equivalences (p244)

next-duality-law : (a : LTL) -> not (next a) ≡ next (not a)
next-duality-law true = begin
  not (next true)
  ≡⟨ {!!} ⟩
  next (not true)
  ∎
next-duality-law (ap x) = begin
  not (next (ap x))
  ≡⟨ {!!} ⟩
  next (not (ap x))
  ∎
next-duality-law (a and b) = begin
  not (next (a and b))
  ≡⟨ {!!} ⟩
  next (not (a and b))
  ∎
next-duality-law (not a) = {!!}
next-duality-law (next a) = {!!}
next-duality-law (a until b) = {!!}

eventually-duality-law : (a : LTL) -> not (eventually a) ≡ always (not a)
eventually-duality-law true = {!!}
eventually-duality-law (ap x) = {!!}
eventually-duality-law (a and b) = {!!}
eventually-duality-law (not a) = {!!}
eventually-duality-law (next a) = {!!}
eventually-duality-law (a until b) = {!!}