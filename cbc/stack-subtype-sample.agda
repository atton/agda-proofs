module stack-subtype-sample where

open import Function
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import stack-subtype ℕ  as S
open import subtype Context  as N
open import subtype Meta     as M


record Num : Set where
  field
    num : ℕ

instance
  NumIsNormalDataSegment : N.DataSegment Num
  NumIsNormalDataSegment = record { get = (\c -> record { num = Context.n c})
                                  ; set = (\c n -> record c {n = Num.num n})}
  NumIsMetaDataSegment : M.DataSegment Num
  NumIsMetaDataSegment = record { get = (\m -> record {num = Context.n (Meta.context m)})
                                ; set = (\m n -> record m {context = record (Meta.context m) {n = Num.num n}})}


plus3 : Num -> Num
plus3 record { num = n } = record {num = n + 3}

plus3CS : N.CodeSegment Num Num
plus3CS = N.cs plus3



plus5AndPushWithPlus3 : {mc : Meta} {{_ : N.DataSegment Num}}
               -> M.CodeSegment Num (Meta)
plus5AndPushWithPlus3 {mc} {{nn}} = M.cs (\n -> record {context = con n ; nextCS = (liftContext {{nn}} {{nn}} plus3CS) ; stack = st} )
  where
    co    = Meta.context mc
    con : Num -> Context
    con record { num = num } = N.DataSegment.set nn co record {num = num + 5}
    st    = Meta.stack mc




push-sample : {{_ : N.DataSegment Num}} {{_ : M.DataSegment Num}} ->  Meta
push-sample {{nd}} {{md}} = M.exec {{md}} (plus5AndPushWithPlus3 {mc} {{nd}}) mc
  where
    con  = record { n = 4 ; element = just 0}
    code = N.cs (\c -> c)
    mc   = record {context = con ; stack = emptySingleLinkedStack ; nextCS = code}


push-sample-equiv : push-sample ≡ record { nextCS  = liftContext plus3CS
                                          ; stack   = record { top = nothing}
                                          ; context = record { n = 9} }
push-sample-equiv = refl


pushed-sample : {m : Meta} {{_ : N.DataSegment Num}} {{_ : M.DataSegment Num}} ->  Meta
pushed-sample {m} {{nd}} {{md}} = M.exec {{md}} (M.csComp {m} {{md}} pushSingleLinkedStackCS (plus5AndPushWithPlus3 {mc} {{nd}})) mc
  where
    con  = record { n = 4 ; element = just 0}
    code = N.cs (\c -> c)
    mc   = record {context = con ; stack = emptySingleLinkedStack ; nextCS = code}



pushed-sample-equiv : {m : Meta} ->
                      pushed-sample {m} ≡ record { nextCS  = liftContext plus3CS
                                                  ; stack   = record { top = just (cons 0 nothing) }
                                                  ; context = record { n   = 12} }
pushed-sample-equiv = refl



pushNum : N.CodeSegment Context Context
pushNum = N.cs pn
  where
    pn : Context -> Context
    pn record { n = n } = record { n = n  ; element = just n}

n-push : {{_ : N.DataSegment Num}} -> Meta -> Meta
n-push {{x}} record { context = record { n = zero    ; element = el } ; stack = st ; nextCS = code} =
  M.exec pushSingleLinkedStackCS record { context = record { n = zero ; element = el }
                                        ; stack   = st ; nextCS  = code}
n-push {{x}} record { context = record { n = (suc n) ; element = el } ; stack = st ; nextCS = code} =
  n-push {{x}} record {context = record {n = n ; element = e} ; stack = s ; nextCS = c}
    where
      pushedMeta = M.exec pushSingleLinkedStackCS record { context = record { n = (suc n) ; element = el}
                                                         ; stack = st ; nextCS = code}
      e = Context.element (Meta.context pushedMeta)
      s = Meta.stack pushedMeta
      c = Meta.nextCS pushedMeta



n-push-cs : M.CodeSegment Meta Meta
n-push-cs = M.cs n-push


initMeta : ℕ -> N.CodeSegment Context Context -> Meta
initMeta n code = record { context = record { n = n ; element = nothing}
                         ; stack   = emptySingleLinkedStack
                         ; nextCS  = code
                         }

n-push-cs-exec = M.exec n-push-cs (initMeta 4 pushNum)


n-push-cs-exec-equiv : n-push-cs-exec ≡ record { nextCS  = {!!}
                                                ; context = {!!}
                                                ; stack   = record { top = {!!} }}
n-push-cs-exec-equiv = refl
