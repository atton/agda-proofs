module maybe-subtype-sample (A : Set) where

open import Level
open import Function using (id)
open import Relation.Binary.PropositionalEquality



open import maybe-subtype A
open import subtype (Context A) as M
open import subtype A as N

return : {_ : Context A} {_ : Meta (Context A)} {{_ : N.DataSegment A}} {{_ : M.DataSegment A}} -> A -> Meta A
return {c} {mc} {{nd}} {{md}} a = record {context = record {maybeElem = just a}}

fmap' : {B : Set} {{_ : M.DataSegment (Context A)}} {{_ : M.DataSegment (Context B)}} -> (A -> B) -> Context A -> Context B
fmap' f record { maybeElem = (just x) } = record {maybeElem = just (f x)}
fmap' f record { maybeElem = nothing }  = record {maybeElem = nothing}



fmap : {c : Context A} {B : Set}
       {{_ : N.DataSegment A}} {{_ : N.DataSegment B}} {{_ : M.DataSegment (Context A)}} {{_ : M.DataSegment (Context B)}}
      -> N.CodeSegment A B -> M.CodeSegment (Context A) (Context B)
fmap  {c} {B} {{na}} {{nb}} {{ma}} {{mb}} (N.cs f) = M.cs {{ma}} (fmap' {B} {{ma}} {{mb}} f)





