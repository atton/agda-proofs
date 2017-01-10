open import Level
open import Relation.Binary.PropositionalEquality

module subtype (Context : Set) where


record DataSegment (A : Set) : Set where
  field
    get : Context -> A
    set : Context -> A -> Context
open DataSegment

data CodeSegment (A B : Set) : Set where
  cs : {{_ : DataSegment A}} {{_ : DataSegment B}} -> (A -> B) -> CodeSegment A B


exec : {I O : Set} {{_ : DataSegment I}} {{_ : DataSegment O}} -> CodeSegment I O -> Context -> Context
exec {l} {{i}} {{o}}  (cs b) c = set o c (b (get i c))


comp : {con : Context} -> {A B C D : Set} {{_ : DataSegment A}} {{_ : DataSegment B}} {{_ : DataSegment C}} {{_ : DataSegment D}}
       -> (C -> D) -> (A -> B) -> A -> D
comp {con} {{i}} {{io}} {{oi}} {{o}} g f x = g (get oi (set io con (f x)))

csComp : {con : Context} {A B C D : Set}
         {{_ : DataSegment A}} {{_ : DataSegment B}} {{_ : DataSegment C}} {{_ : DataSegment D}}
       -> CodeSegment C D -> CodeSegment A B -> CodeSegment A D
csComp {con} {A} {B} {C} {D} {{da}} {{db}} {{dc}} {{dd}} (cs g) (cs f)
      = cs {{da}} {{dd}} (comp {con} {{da}} {{db}} {{dc}} {{dd}} g f)



comp-associative : {A B C D E F : Set} {con : Context}
                   {{da : DataSegment A}} {{db : DataSegment B}} {{dc : DataSegment C}}
                   {{dd : DataSegment D}} {{de : DataSegment E}} {{df : DataSegment F}}
                   -> (a : CodeSegment A B) (b : CodeSegment C D) (c : CodeSegment E F)
                   -> csComp {con} c (csComp {con} b a)  ≡ csComp {con} (csComp {con} c b) a
comp-associative (cs _) (cs _) (cs _) = refl
