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
    pn record { n = n } = record { n = pred n  ; element = just n}


pushOnce : Meta -> Meta
pushOnce m = M.exec pushSingleLinkedStackCS m

n-push : {m : Meta} {{_ : M.DataSegment Meta}} (n : ℕ) -> M.CodeSegment Meta Meta
n-push {{mm}} (zero)  = M.cs {{mm}} {{mm}} pushOnce
n-push {m} {{mm}} (suc n)        = M.csComp {m} {{mm}} {{mm}} {{mm}} {{mm}} (n-push {m} {{mm}} n) (M.cs {{mm}} {{mm}} pushOnce)

popOnce : Meta -> Meta
popOnce m = M.exec popSingleLinkedStackCS m

n-pop : {m : Meta} {{_ : M.DataSegment Meta}} (n : ℕ) -> M.CodeSegment Meta Meta
n-pop {{mm}} (zero)      = M.cs {{mm}} {{mm}} popOnce
n-pop {m} {{mm}} (suc n) = M.csComp {m} {{mm}} {{mm}} {{mm}} {{mm}} (n-pop {m} {{mm}} n) (M.cs {{mm}} {{mm}} popOnce)




initMeta : ℕ -> N.CodeSegment Context Context -> Meta
initMeta n code = record { context = record { n = n ; element = nothing}
                         ; stack   = emptySingleLinkedStack
                         ; nextCS  = code
                         }

n-push-cs-exec = M.exec (n-push {meta} 2) meta
  where
    meta = (initMeta 5 pushNum)


n-push-cs-exec-equiv : n-push-cs-exec ≡ record { nextCS  = pushNum
                                                ; context = record {n = 2 ; element = just 3}
                                                ; stack   = record {top = just (cons 4 (just (cons 5 nothing)))}}
n-push-cs-exec-equiv = refl


n-pop-cs-exec = M.exec (n-pop {meta} 3) meta
  where
    meta = record { nextCS  = N.cs id
                  ; context = record { n = 0 ; element = nothing}
                  ; stack   = record {top = just (cons 9 (just (cons 8 (just (cons 7 (just (cons 6 (just (cons 5 nothing)))))))))}
                  }

n-pop-cs-exec-equiv : n-pop-cs-exec ≡ record { nextCS  = N.cs id
                                              ; context = record { n = 0 ; element = just 6}
                                              ; stack   = record { top = just (cons 5 nothing)}
                                              }

n-pop-cs-exec-equiv = refl
