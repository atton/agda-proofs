module named-product where


open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (_++_ ; show)
open import Data.List
open import Relation.Binary.PropositionalEquality




record Context : Set where
  field
    cycle : ℕ
    led   : String
    signature : String

record Datum (A : Set) : Set where
  field 
    get : Context -> A
    set : Context -> A -> Context
open Datum

record LoopCounter : Set where
  field
    count : ℕ
    name  : String

record SignatureWithNum : Set where
  field
    signature : String
    num       : ℕ

instance
  contextHasLoopCounter : Datum LoopCounter
  contextHasLoopCounter = record {get = (\c   -> record {count = Context.cycle c ;
                                                         name  = Context.led   c });
                                  set = (\c l -> record {cycle     = LoopCounter.count l;
                                                         led       = LoopCounter.name  l;
                                                         signature = Context.signature c})}
  contextHasSignatureWithNum : Datum SignatureWithNum
  contextHasSignatureWithNum = record {get = (\c -> record { signature = Context.signature c
                                                           ; num       = Context.cycle     c})
                                      ;set = (\c s -> record { cycle = SignatureWithNum.num s
                                                             ; led    = Context.led c
                                                             ; signature = SignatureWithNum.signature s})
                                      }


inc :  LoopCounter -> LoopCounter
inc  l = record l {count = suc (LoopCounter.count l)}

firstContext : Context
firstContext = record { cycle = 3 ; led = "q" ; signature = "aaa" }


incContextCycle : {{_ : Datum LoopCounter }} -> Context -> Context
incContextCycle {{l}} c = Datum.set l c (inc (Datum.get l c))


equiv : incContextCycle firstContext ≡ record { cycle = 4 ; led = "q" ; signature = "aaa" }
equiv = refl


data CodeSegment (A B : Set) : (List Set) -> Set where
  cs : {l : List Set} {{_ : Datum A}} {{_ : Datum B}} -> (A -> B) -> CodeSegment A B (B ∷ A ∷ l)

BasicCS : Set -> Set -> Set
BasicCS A B = CodeSegment A B (A ∷ B ∷ [])

  

exec : {I O : Set} -> {l : List Set} {{_ : Datum I}} {{_ : Datum O}} -> CodeSegment I O l -> Context -> Context
exec {l} {{i}} {{o}}  (cs b) c = Datum.set o c (b (get i c))


comp : {con : Context} -> {A B C D : Set} {{_ : Datum A}} {{_ : Datum B}} {{_ : Datum C}} {{_ : Datum D}}
       -> (C -> D) -> (A -> B) -> A -> D
comp {con} {{i}} {{io}} {{oi}} {{o}} g f x = g (get oi (set io con (f x)))
                                         
                                           
csInc : BasicCS LoopCounter LoopCounter
csInc = cs inc
                                       



equiv-exec : {l : List Set} -> incContextCycle firstContext ≡ exec csInc firstContext
equiv-exec = refl


csComp : {con : Context} {A B C D : Set} {{_ : Datum A}} {{_ : Datum B}} {{_ : Datum C}} {{_ : Datum D}} {l ll : List Set}
       -> CodeSegment C D (D ∷ C ∷ l) -> CodeSegment A B (B ∷ A ∷ ll) -> CodeSegment A D (D ∷ A ∷ C ∷ B ∷ (l ++ ll))
csComp {con} {A} {B} {C} {D} {{da}} {{db}} {{dc}} {{dd}} {l} {ll} (cs g) (cs f)
      = cs {l = (C ∷ B ∷ (l ++ ll))} {{da}} {{dd}} (comp {con} {{da}} {{db}} {{dc}} {{dd}} g f)


comp-sample : {c : Context} -> CodeSegment LoopCounter LoopCounter (LoopCounter ∷ LoopCounter ∷ LoopCounter ∷ LoopCounter ∷ [])
comp-sample {c} = (csComp {c} csInc csInc)


apply-sample : Context
apply-sample = exec (comp-sample {firstContext}) firstContext



updateSignature : SignatureWithNum -> SignatureWithNum
updateSignature record { signature = signature ; num = num } = record { signature = (Data.String._++_) signature (show num ) ; num = num}


csUpdateSignature : BasicCS SignatureWithNum SignatureWithNum
csUpdateSignature = cs updateSignature



comp-sample-2 : {c : Context} -> CodeSegment LoopCounter SignatureWithNum (SignatureWithNum ∷ LoopCounter ∷ SignatureWithNum ∷ LoopCounter ∷ [])
comp-sample-2 {c} = csComp {c} csUpdateSignature  csInc

apply-sample-2 : Context
apply-sample-2 = exec (comp-sample-2 {firstContext}) firstContext
