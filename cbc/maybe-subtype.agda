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

return : {_ : Context A} {_ : Meta (Context A)} {{_ : N.DataSegment A}} {{_ : M.DataSegment A}} -> A -> Meta A
return {c} {mc} {{nd}} {{md}} a = record {context = record {maybeElem = just a}}

fmap' : {B : Set} {{_ : M.DataSegment (Context A)}} {{_ : M.DataSegment (Context B)}} -> (A -> B) -> Context A -> Context B
fmap' f record { maybeElem = (just x) } = record {maybeElem = just (f x)}
fmap' f record { maybeElem = nothing }  = record {maybeElem = nothing}



fmap : {c : Context A} {B : Set}
       {{_ : N.DataSegment A}} {{_ : N.DataSegment B}} {{_ : M.DataSegment (Context A)}} {{_ : M.DataSegment (Context B)}}
      -> N.CodeSegment A B -> M.CodeSegment (Context A) (Context B)
fmap  {c} {B} {{na}} {{nb}} {{ma}} {{mb}} (N.cs f) = M.cs {{ma}} (fmap' {B} {{ma}} {{mb}} f)



open ≡-Reasoning

exec-id : (x : Meta A) -> M.exec (M.cs {zero} {zero} {Context A} id) x ≡ x
exec-id record { context = context } = refl


maybe-preserve-id : {{na : N.DataSegment A}} {{ma : M.DataSegment A}} {{mx : M.DataSegment (Context A)}}
                  -> (x : Context A)
                  -> M.exec {{mx}} {{mx}} (fmap {x} {{na}}{{na}}{{mx}}{{mx}} (N.cs id)) (record {context = x})
                     ≡
                     M.exec {{mx}} {{mx}} (M.cs {{mx}} {{mx}} id) (record {context = x})

maybe-preserve-id {{na}} {{ma}} {{mx}} record { maybeElem = nothing }  = begin
  M.exec {{mx}} {{mx}} (fmap {record { maybeElem = nothing }} {{na}}{{na}}{{mx}}{{mx}} (N.cs id)) (record {context = record { maybeElem = nothing }})
  ≡⟨ refl ⟩
  M.DataSegment.set mx (record { context = record { maybeElem = nothing } }) ((fmap' {{mx}} {{mx}} id) (M.DataSegment.get mx (record { context = record { maybeElem = nothing } })))
  ≡⟨ {!!} ⟩
  record {context = record { maybeElem = nothing }}
  ≡⟨ sym (exec-id (record {context = record {maybeElem = nothing}})) ⟩
  M.exec {{mx}} {{mx}} (M.cs {{mx}} {{mx}} id) (record {context = record { maybeElem = nothing }})
  ∎
maybe-preserve-id record { maybeElem = (just x) } = {!!}
                     {-
maybe-preserve-id {{na}} {{ma}} {{mx}} record { maybeElem = nothing }  = begin
  M.exec (fmap {record {maybeElem = nothing}} (N.cs id)) record {context = record { maybeElem = nothing}}
  ≡⟨ refl ⟩
  M.exec  (M.cs (fmap' id)) record {context = record {maybeElem = nothing}}
  ≡⟨ refl ⟩
  M.DataSegment.set mx (record { context = record { maybeElem = nothing } }) ((fmap' id) (M.DataSegment.get mx (record { context = record { maybeElem = nothing } })))
  ≡⟨ {!!} ⟩
  record { context = record { maybeElem = nothing }}
  ≡⟨ {!!} ⟩
  M.exec {zero} {zero} {A} {A} (M.cs id) (record { context = record { maybeElem = nothing } })
  ∎
maybe-preserve-id record { maybeElem = (just x) } = {!!}


-}
