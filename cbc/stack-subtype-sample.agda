module stack-subtype-sample where

open import Level renaming (suc to S ; zero to O)
open import Function
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import stack-subtype ℕ 
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
n-push {{mm}} (zero)      = M.cs {{mm}} {{mm}} id
n-push {m} {{mm}} (suc n) = M.csComp {m} {{mm}} {{mm}} {{mm}} {{mm}} (n-push {m} {{mm}} n) (M.cs {{mm}} {{mm}} pushOnce)

popOnce : Meta -> Meta
popOnce m = M.exec popSingleLinkedStackCS m

n-pop : {m : Meta} {{_ : M.DataSegment Meta}} (n : ℕ) -> M.CodeSegment Meta Meta
n-pop {{mm}} (zero)      = M.cs {{mm}} {{mm}} id
n-pop {m} {{mm}} (suc n) = M.csComp {m} {{mm}} {{mm}} {{mm}} {{mm}} (n-pop {m} {{mm}} n) (M.cs {{mm}} {{mm}} popOnce)




initMeta : ℕ  -> Maybe ℕ -> N.CodeSegment Context Context -> Meta
initMeta n mn code = record { context = record { n = n ; element = mn}
                         ; stack   = emptySingleLinkedStack
                         ; nextCS  = code
                         }

n-push-cs-exec = M.exec (n-push {meta} 3) meta
  where
    meta = (initMeta 5 (just 9) pushNum)


n-push-cs-exec-equiv : n-push-cs-exec ≡ record { nextCS  = pushNum
                                                ; context = record {n = 2 ; element = just 3}
                                                ; stack   = record {top = just (cons 4 (just (cons 5 (just (cons 9 nothing)))))}}
n-push-cs-exec-equiv = refl


n-pop-cs-exec = M.exec (n-pop {meta} 4) meta
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


open ≡-Reasoning

{-
comp-id-type : {m : Meta} {{mm : M.DataSegment Meta}} (f : M.CodeSegment Meta Meta) -> Set₁
comp-id-type {m} {{mm}} f = M.csComp {m} {{mm}} {{mm}} {{mm}} {{mm}} f (M.cs {S O} {S O} {Meta} {Meta} {{mm}}{{mm}} id) ≡ f

comp-id : {m : Meta} (f : M.CodeSegment Meta Meta) -> comp-id-type {m} f
comp-id (M.cs f) = refl

n-pop-pop-once-n-push :(n : ℕ) (m : Meta) ->
    M.exec (M.csComp {m} (M.csComp {m} (n-pop {m} n) (M.cs popOnce)) (n-push {m} (suc n))) m
    ≡
    M.exec (M.csComp {m} (n-pop {m} n) (n-push {m} n)) m
n-pop-pop-once-n-push zero m    = begin
  M.exec (M.csComp {m} (M.csComp {m} (n-pop {m} zero) (M.cs popOnce)) (n-push {m} (suc zero))) m
  ≡⟨ refl ⟩
   M.exec (M.csComp {m} (M.csComp {m} (M.cs {S O} {S O} {Meta} {Meta} id) (M.cs popOnce)) (n-push {m} (suc zero))) m
  ≡⟨ {!!} ⟩
  M.exec (M.csComp {m} (M.cs popOnce) (n-push {m} (suc zero))) m
  ≡⟨ {!!} ⟩
  M.exec (M.csComp {m} (n-pop {m} zero) (n-push {m} zero)) m
  ∎
n-pop-pop-once-n-push (suc n) m = {!!} 
-}




id-meta : Context -> Meta
id-meta c = record { context = c ; nextCS = (N.cs id) ; stack = record {top = nothing}}


push-pop : (c : Context) -> M.exec (M.csComp {id-meta c} (M.cs popOnce) (M.cs pushOnce)) (id-meta c) ≡ id-meta c
push-pop record { n = n ; element = (just x) } = refl
push-pop record { n = n ; element = nothing }  = refl
{-
n-pop-pop-once-n-push : (n : ℕ) (c : Context) ->
    M.exec (M.csComp {id-meta c}  (M.csComp {id-meta c} (n-pop {id-meta c} n) (M.cs popOnce)) (n-push {id-meta c} (suc n))) (id-meta c)
    ≡                                                                                                                
    M.exec (M.csComp {id-meta c} (n-pop {id-meta c} n) (n-push {id-meta c} n)) (id-meta c)
n-pop-pop-once-n-push zero    c = begin
  M.exec (M.csComp {id-meta c} (M.csComp {id-meta c}(n-pop {id-meta c} zero) (M.cs popOnce)) (n-push {id-meta c} (suc zero))) (id-meta c)
  ≡⟨ refl ⟩
  M.exec (M.csComp {id-meta c} (M.csComp {id-meta c} (M.cs {S O} {S O} {Meta} {Meta} id) (M.cs popOnce)) (n-push {id-meta c} (suc zero))) (id-meta c)
  ≡⟨ refl ⟩
  M.exec (M.csComp {id-meta c} (M.cs popOnce) (n-push {id-meta c} (suc zero))) (id-meta c)
  ≡⟨ refl ⟩
  M.exec (M.csComp {id-meta c} (M.cs popOnce) (M.cs pushOnce)) (id-meta c)
  ≡⟨ push-pop c ⟩
  id-meta c
  ≡⟨ refl ⟩
  M.exec (M.csComp {id-meta c} (n-pop {id-meta c} zero) (n-push {id-meta c} zero)) (id-meta c)
  ∎
n-pop-pop-once-n-push (suc n) c = begin
  M.exec (M.csComp (M.csComp (n-pop (suc n)) (M.cs popOnce)) (n-push (suc (suc n)))) (id-meta c)
  ≡⟨ cong (\f -> M.exec f (id-meta c)) (sym (M.comp-associative (n-push (suc (suc n))) (M.cs popOnce) (n-pop (suc n)))) ⟩
  M.exec (M.csComp (n-pop (suc n)) (M.csComp (M.cs popOnce) (n-push (suc (suc n))))) (id-meta c)
  ≡⟨ {!!} ⟩
  M.exec (M.csComp (n-pop (suc n)) (n-push (suc n))) (id-meta c)
  ∎
-}

exec-comp : (f g : M.CodeSegment Meta Meta) (m : Meta) -> M.exec (M.csComp {m} f g) m ≡ M.exec f (M.exec g m)
exec-comp (M.cs x) (M.cs _) m = refl



n-push-pop :  (n : ℕ) (c : Context) ->
  (M.exec (M.csComp {id-meta c} (M.cs popOnce) (n-push {id-meta c} (suc n))) (id-meta c)) ≡ M.exec (n-push {id-meta c} n) (id-meta c)
n-push-pop zero c    = push-pop c
n-push-pop (suc n) record {n = num ; element = nothing} = begin
  M.exec (M.csComp (M.cs popOnce) (n-push (suc (suc n)))) (id-meta record {n = num ; element = nothing})
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (M.csComp (n-push (suc n)) (M.cs pushOnce))) (id-meta record {n = num ; element = nothing})
  ≡⟨ cong (\f -> M.exec f (id-meta record {n = num ; element = nothing})) (M.comp-associative (M.cs pushOnce) (n-push (suc n)) (M.cs popOnce) ) ⟩
  M.exec (M.csComp (M.csComp (M.cs popOnce) (n-push (suc n))) (M.cs pushOnce)) (id-meta record {n = num ; element = nothing})
  ≡⟨ exec-comp (M.csComp (M.cs popOnce) (n-push (suc n))) (M.cs pushOnce) (id-meta record {n = num ; element = nothing})  ⟩
  M.exec (M.csComp (M.cs popOnce) (n-push (suc n))) (M.exec (M.cs pushOnce) (id-meta record {n = num ; element = nothing}))
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (M.csComp (n-push n) (M.cs pushOnce))) (M.exec (M.cs pushOnce) (id-meta record {n = num ; element = nothing}))
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (M.csComp (n-push n) (M.cs pushOnce))) (id-meta record {n = num ; element = nothing})
  ≡⟨ cong (\f -> M.exec f (id-meta record {n = num ; element = nothing})) (M.comp-associative (M.cs pushOnce) (n-push n) (M.cs popOnce)) ⟩
  M.exec (M.csComp (M.csComp (M.cs popOnce) (n-push n)) (M.cs pushOnce)) (id-meta record {n = num ; element = nothing})
  ≡⟨ exec-comp (M.csComp (M.cs popOnce) (n-push n)) (M.cs pushOnce) (id-meta record {n = num ; element = nothing }) ⟩
  M.exec (M.csComp (M.cs popOnce) (n-push n)) (M.exec (M.cs pushOnce) (id-meta record {n = num ; element = nothing}))
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (n-push n)) (id-meta record {n = num ; element = nothing})
  ≡⟨ {!!} ⟩
  M.exec (n-push (suc n)) (id-meta record {n = num ; element = nothing})
  ∎
n-push-pop (suc n) record {n = num ; element = just x} = begin
  M.exec (M.csComp (M.cs popOnce) (n-push (suc (suc n)))) (id-meta record {n = num ; element = just x})
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (M.csComp (n-push (suc n)) (M.cs pushOnce))) (id-meta record {n = num ; element = just x})
  ≡⟨ cong (\f -> M.exec f (id-meta record {n = num ; element = just x})) (M.comp-associative (M.cs pushOnce) (n-push (suc n)) (M.cs popOnce) ) ⟩
  M.exec (M.csComp (M.csComp (M.cs popOnce) (n-push (suc n))) (M.cs pushOnce)) (id-meta record {n = num ; element = just x})
  ≡⟨ exec-comp (M.csComp (M.cs popOnce) (n-push (suc n))) (M.cs pushOnce) (id-meta record {n = num ; element = just x})  ⟩
  M.exec (M.csComp (M.cs popOnce) (n-push (suc n))) (M.exec (M.cs pushOnce) (id-meta record {n = num ; element = just x}))
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.cs popOnce) (M.csComp (n-push n) (M.cs pushOnce))) (M.exec (M.cs pushOnce) (id-meta record {n = num ; element = just x}))
  ≡⟨ {!!} ⟩
  M.exec (n-push (suc n)) (id-meta record {n = num ; element = just x})
  ∎


n-push-pop-equiv : {c : Context} -> (n : ℕ )
                 -> M.exec (M.csComp {id-meta c} (n-pop {id-meta c} n) (n-push {id-meta c} n)) (id-meta c) ≡ (id-meta c)
n-push-pop-equiv           zero  = refl
n-push-pop-equiv {c} (suc n) = begin
  M.exec (M.csComp (n-pop (suc n)) (n-push (suc n))) (id-meta c)
  ≡⟨ refl ⟩
  M.exec (M.csComp (M.csComp (n-pop n) (M.cs popOnce)) (n-push (suc n))) (id-meta c)
  ≡⟨ cong (\f -> M.exec f (id-meta c)) (sym (M.comp-associative (n-push (suc n)) (M.cs popOnce) (n-pop n)))  ⟩
  M.exec (M.csComp (n-pop n) (M.csComp (M.cs popOnce) (n-push (suc n)))) (id-meta c)
  ≡⟨ exec-comp (n-pop n) (M.csComp (M.cs popOnce) (n-push (suc n)))  (id-meta c) ⟩
  M.exec (n-pop n) (M.exec (M.csComp (M.cs popOnce) (n-push (suc n))) (id-meta c))
  ≡⟨ cong (\x -> M.exec (n-pop n) x) (n-push-pop n c ) ⟩
  M.exec (n-pop n) (M.exec (n-push {id-meta c} n) (id-meta c))
  ≡⟨ sym (exec-comp (n-pop n) (n-push n) (id-meta c)) ⟩
  M.exec (M.csComp (n-pop n) (n-push n)) (id-meta c)
  ≡⟨ n-push-pop-equiv n ⟩
  id-meta c
  ∎
