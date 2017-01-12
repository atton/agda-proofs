module maybe-subtype (A : Set) where

open import Level
open import Function using (id)
open import Relation.Binary.PropositionalEquality

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A


record Context (A : Set) : Set where
  field
    maybeElem : Maybe A

open import subtype (Context A) as N


record Meta (A : Set) : Set where
  field
    context : Context A


open import subtype (Meta A) as M

instance
  MetaIsMetaDataSegment : M.DataSegment (Meta A)
  MetaIsMetaDataSegment = record {get = (\mc -> mc) ; set = (\_ mc -> mc)}
  ContextIsMetaDataSegment : M.DataSegment (Context A)
  ContextIsMetaDataSegment = record {get = Meta.context ; set = (\mc c -> record mc {context = c})}

