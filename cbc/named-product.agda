module named-product where

open import Function
open import Data.Nat
open import Data.String
open import Data.Vec
open import Relation.Binary.PropositionalEquality



record DataSegment (n : ℕ) : Set₁ where
  field
    name : String
    ds   : Vec (Set -> Set) (suc n)

ids : {A : Set} {n : ℕ} -> DataSegment n -> Set
ids {a} {zero}  record { name = name ; ds = (x ∷ []) } = x a
ids {a} {suc n} record { name = name ; ds = (x ∷ ds) } = x a -> ids {a} {n} record { name = name ; ds = ds }


record _<<<_ (A : Set) (B : Set) : Set where
  field 
    get : B -> A
    set : B -> A -> B

open _<<<_


record LoopCounter : Set where
  field
    count : ℕ
    name  : String

record Context : Set where
  field
    cycle : ℕ
    led   : String
    signature : String


instance
  contextHasLoopCounter : LoopCounter <<< Context
  contextHasLoopCounter = record {get = (\c   -> record {count = Context.cycle c ;
                                                         name  = Context.led   c });
                                  set = (\c l -> record {cycle     = LoopCounter.count l;
                                                         led       = LoopCounter.name  l;
                                                         signature = Context.signature c})
                                  }


inc :  LoopCounter -> LoopCounter
inc  l = record l {count = suc (LoopCounter.count l)}

firstContext : Context
firstContext = record { cycle = 3 ; led = "q" ; signature = "aaa" }

incContextCycle : {{_ : LoopCounter <<< Context }} -> Context -> Context
incContextCycle {{l}} c = set l c (inc (get l c))


equiv : incContextCycle firstContext ≡ record { cycle = 4 ; led = "q" ; signature = "aaa" }
equiv = refl



--data CodeSegment (n m : ℕ) : Set₁ where
--  cs : (i : DataSegment n) -> (o : DataSegment m) -> CodeSegment n m



--yoyo : DataSegment
--yoyo = record { name = "yoyo" ; ds = [ Yo ]}
