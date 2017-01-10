module subtype-sample where

open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (_++_ ; show ; toList ; fromList)
open import Data.List
open import Relation.Binary.PropositionalEquality



record Context : Set where
  field
    cycle : ℕ
    led   : String
    signature : String
    
open import subtype Context


record LoopCounter : Set where
  field
    count : ℕ
    name  : String

record SignatureWithNum : Set where
  field
    signature : String
    num       : ℕ

instance
  contextHasLoopCounter : DataSegment LoopCounter
  contextHasLoopCounter = record {get = (\c   -> record {count = Context.cycle c ;
                                                         name  = Context.led   c });
                                  set = (\c l -> record {cycle     = LoopCounter.count l;
                                                         led       = LoopCounter.name  l;
                                                         signature = Context.signature c})}
  contextHasSignatureWithNum : DataSegment SignatureWithNum
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


incContextCycle : {{_ : DataSegment LoopCounter }} -> Context -> Context
incContextCycle {{l}} c = DataSegment.set l c (inc (DataSegment.get l c))


equiv : incContextCycle firstContext ≡ record { cycle = 4 ; led = "q" ; signature = "aaa" }
equiv = refl


csInc : CodeSegment LoopCounter LoopCounter
csInc = cs inc



equiv-exec : {l : List Set} -> incContextCycle firstContext ≡ exec csInc firstContext
equiv-exec = refl

comp-sample : {c : Context} -> CodeSegment LoopCounter LoopCounter
comp-sample {c}  = (csComp {c} csInc csInc)


apply-sample : Context
apply-sample = exec (comp-sample {firstContext}) firstContext



updateSignature : SignatureWithNum -> SignatureWithNum
updateSignature record { signature = signature ; num = num } = record { signature = (Data.String._++_) signature (show num ) ; num = num}


csUpdateSignature : CodeSegment SignatureWithNum SignatureWithNum
csUpdateSignature = cs updateSignature



comp-sample-2 : {c : Context} -> CodeSegment LoopCounter SignatureWithNum
comp-sample-2 {c}  = csComp {c}  csUpdateSignature  csInc

apply-sample-2 : Context
apply-sample-2 = exec (comp-sample-2 {firstContext}) firstContext

