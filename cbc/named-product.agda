module named-product where

open import Function
open import Data.Bool
open import Data.Nat
open import Data.String
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
  cs : {l : List Set} {{_ : Datum A}} {{_ : Datum B}} -> (A -> B) -> CodeSegment A B (A ∷ (B ∷ l))
  

exec : {I O : Set} -> {l : List Set} {{_ : Datum I}} {{_ : Datum O}} -> CodeSegment I O l  -> Context -> Context
exec {{i}} {{o}} (cs b) c = Datum.set o c (b (Datum.get i c))


equiv-exec : {l : List Set} ->  incContextCycle firstContext ≡ exec (cs {l = l} inc) firstContext
equiv-exec = refl

{-


InputIsHead : {n : ℕ} {I O : Set} {l : Vec Set (suc (suc n))} -> (cs : CodeSegment I O l) -> I ≡ head l
InputIsHead (cs _) = refl

OutputIsLast : {n : ℕ} {I O : Set} {l : Vec Set (suc (suc n))} -> (cs : CodeSegment I O l) -> O ≡ last l
OutputIsLast {_} {_} {_} {l} (cs x) = {!!}

-}
  


--yoyo : DataSegment
--yoyo = record { name = "yoyo" ; ds = [ Yo ]}
