module stack-subtype-sample where

open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import stack-subtype ℕ  as S
open import subtype Context as N
open import subtype (MetaContext Context) as M


record Num : Set where
  field
    num : ℕ

instance
  NumIsNormalDataSegment : N.DataSegment Num
  NumIsNormalDataSegment = record { get = (\c -> record { num = Context.n c})
                                  ; set = (\c n -> record c {n = Num.num n})}
  NumIsMetaDataSegment : M.DataSegment Num
  NumIsMetaDataSegment = record { get = (\m -> record {num = Context.n (MetaContext.context m)})
                                ; set = (\m n -> record m {context = record (MetaContext.context m) {n = Num.num n}})}


plus3 : Num -> Num
plus3 record { num = n } = record {num = n + 3}

plus3CS : N.CodeSegment Num Num
plus3CS = N.cs plus3


setNext : {X Y : Set} {{x : N.DataSegment X}} {{y : N.DataSegment Y}}
        -> (N.CodeSegment X Y) -> M.CodeSegment (MetaContext Context) (MetaContext Context)
setNext c = M.cs (\mc -> record mc {nextCS = liftContext c})

setElement : ℕ -> M.CodeSegment (MetaContext Context) (MetaContext Context)
setElement x = M.cs (\mc -> record mc {context = record (MetaContext.context mc) {element = just x}})



plus5AndPushWithPlus3 : {mc : MetaContext Context} {{_ : N.DataSegment Num}}
               -> M.CodeSegment Num (MetaContext Context)
plus5AndPushWithPlus3 {mc} {{nn}} = M.cs (\n -> record {context = con n ; nextCS = (liftContext {{nn}} {{nn}} plus3CS) ; stack = st} )
  where
    co    = MetaContext.context mc
    con : Num -> Context
    con record { num = num } = N.DataSegment.set nn co record {num = num + 5}
    st    = MetaContext.stack mc




push-sample : {{_ : N.DataSegment Num}} {{_ : M.DataSegment Num}} ->  MetaContext Context
push-sample {{nd}} {{md}} = M.exec {{md}} (plus5AndPushWithPlus3 {mc} {{nd}}) mc
  where
    con  = record { n = 4 ; element = just 0}
    code = N.cs (\c -> c)
    mc   = record {context = con ; stack = emptySingleLinkedStack ; nextCS = code}


push-sample-equiv : push-sample ≡ record { nextCS  = liftContext plus3CS
                                          ; stack   = record { top = nothing}
                                          ; context = record { n = 9} }
push-sample-equiv = refl


pushed-sample : {m : MetaContext Context} {{_ : N.DataSegment Num}} {{_ : M.DataSegment Num}} ->  MetaContext Context
pushed-sample {m} {{nd}} {{md}} = M.exec {{md}} (M.csComp {m} {{md}} pushSingleLinkedStackCS (plus5AndPushWithPlus3 {mc} {{nd}})) mc
  where
    con  = record { n = 4 ; element = just 0}
    code = N.cs (\c -> c)
    mc   = record {context = con ; stack = emptySingleLinkedStack ; nextCS = code}



pushed-sample-equiv : {m : MetaContext Context} -> pushed-sample {m} ≡ record { nextCS  = liftContext plus3CS
                                                                               ; stack   = record { top = just (cons 0 nothing) }
                                                                               ; context = record { n   = 12} }
pushed-sample-equiv = refl


