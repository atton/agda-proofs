open import Level
open import Data.Maybe
open import Function using (id)
open import Relation.Binary.PropositionalEquality

module maybe-subtype (A : Set)  where


record Context : Set where

open import subtype Context as N


record Meta (A : Set) : Set where
  field
    context   : Context
    maybeElem : Maybe A


