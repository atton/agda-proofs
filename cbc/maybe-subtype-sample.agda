module maybe-subtype-sample (A : Set) where

open import Level
open import Data.Maybe
open import Function using (id)
open import Relation.Binary.PropositionalEquality

open import maybe-subtype A
open import subtype A as N
open import subtype (Meta A) as M

instance
  MetaIsMetaDataSegment : {{_ : M.DataSegment A}} -> M.DataSegment (Meta A)
  MetaIsMetaDataSegment    = record {get = (\mc -> mc) ; set = (\_ mc -> mc)}
  ContextIsMetaDataSegment : M.DataSegment (Context)
  ContextIsMetaDataSegment = record {get = Meta.context ; set = (\mc c -> record mc {context = c})}





return : {X : Set} {_ : Context} {_ : Meta A} {{_ : N.DataSegment X}} {{_ : M.DataSegment X}} -> X -> Meta X
return {c} {mc} {{nd}} {{md}} a = record {context = record {} ; maybeElem = just a}


fmap' : {B : Set} -> (A -> B) -> Meta A -> Meta B
fmap' f record { maybeElem = (just x) } = record {maybeElem = just (f x)}
fmap' f record { maybeElem = nothing }  = record {maybeElem = nothing}


fmap : {c : Context} {B : Set}
       {{_ : M.DataSegment A}} {{_ : M.DataSegment B}} {{_ : M.DataSegment (Meta A)}}{{_ : M.DataSegment (Meta B)}}
      -> M.CodeSegment A B -> M.CodeSegment (Meta A) (Meta B)
fmap  {c} {B} {{na}} {{nb}} {{ma}}  (N.cs f) = M.cs {{ma}} (fmap' {B} f)


liftMeta : {B : Set} {{_ : M.DataSegment A}} {{_ : M.DataSegment B}} -> N.CodeSegment A B -> M.CodeSegment A B
liftMeta (N.cs f) = M.cs f


fmap-preserve-id : {x : Meta A} {{nx : N.DataSegment A }}{{mx : M.DataSegment A}} {{mmx : M.DataSegment (Meta A)}}
                 -> M.exec {{mmx}} {{mmx}} (fmap {{mx}} {{mx}} {{mmx}} {{mmx}} (M.cs id)) x ≡ M.exec (liftMeta (N.cs id)) x
fmap-preserve-id = {!!}


