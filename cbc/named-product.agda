module named-product where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (_++_ ; show ; toList ; fromList)
open import Data.List
open import Data.AVL.Sets
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


data CodeSegment (A B : Set) : Set where
  cs : {{_ : Datum A}} {{_ : Datum B}} -> (A -> B) -> CodeSegment A B

BasicCS :  Set -> Set -> Set
BasicCS A B = CodeSegment  A B
  

exec : {I O : Set} {{_ : Datum I}} {{_ : Datum O}} -> CodeSegment I O -> Context -> Context
exec {l} {{i}} {{o}}  (cs b) c = Datum.set o c (b (get i c))


comp : {con : Context} -> {A B C D : Set} {{_ : Datum A}} {{_ : Datum B}} {{_ : Datum C}} {{_ : Datum D}}
       -> (C -> D) -> (A -> B) -> A -> D
comp {con} {{i}} {{io}} {{oi}} {{o}} g f x = g (get oi (set io con (f x)))
                                         
                                           
csInc : BasicCS LoopCounter LoopCounter
csInc = cs inc
                                       


equiv-exec : {l : List Set} -> incContextCycle firstContext ≡ exec csInc firstContext
equiv-exec = refl


csComp : {con : Context} {A B C D : Set} {{_ : Datum A}} {{_ : Datum B}} {{_ : Datum C}} {{_ : Datum D}}
       -> CodeSegment C D -> CodeSegment A B -> CodeSegment A D
csComp {con} {A} {B} {C} {D} {{da}} {{db}} {{dc}} {{dd}} (cs g) (cs f)
      = cs {{da}} {{dd}} (comp {con} {{da}} {{db}} {{dc}} {{dd}} g f)

comp-sample : {c : Context} -> CodeSegment LoopCounter LoopCounter
comp-sample {c}  = (csComp {c} csInc csInc)


apply-sample : Context
apply-sample = exec (comp-sample {firstContext}) firstContext



updateSignature : SignatureWithNum -> SignatureWithNum
updateSignature record { signature = signature ; num = num } = record { signature = (Data.String._++_) signature (show num ) ; num = num}


csUpdateSignature : BasicCS SignatureWithNum SignatureWithNum
csUpdateSignature = cs updateSignature



comp-sample-2 : {c : Context} -> CodeSegment LoopCounter SignatureWithNum
comp-sample-2 {c}  = csComp {c}  csUpdateSignature  csInc

apply-sample-2 : Context
apply-sample-2 = exec (comp-sample-2 {firstContext}) firstContext



comp-associative : {A B C D E F : Set} {con : Context}
                   {{da : Datum A}} {{db : Datum B}} {{dc : Datum C}} {{dd : Datum D}} {{de : Datum E}} {{df : Datum F}}
                   -> (a : CodeSegment A B) (b : CodeSegment C D) (c : CodeSegment E F)
                   -> csComp {con} c (csComp {con} b a)  ≡ csComp {con} (csComp {con} c b) a
comp-associative (cs _) (cs _) (cs _) = refl
