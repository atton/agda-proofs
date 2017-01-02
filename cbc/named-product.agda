module named-product where

open import Data.Nat
open import Data.String
open import Data.Vec

record DataSegment (n : ℕ) : Set₁ where
  field
    name : String
    ds   : Vec (Set -> Set) (suc n)

ids : {A : Set} {n : ℕ} -> DataSegment n -> Set
ids {a} {zero}  record { name = name ; ds = (x ∷ []) } = x a
ids {a} {suc n} record { name = name ; ds = (x ∷ ds) } = x a -> ids {a} {n} record { name = name ; ds = ds }

record LoopCounter (A : Set) : Set where
  field
    counter : ℕ
    name    : String


record Context : Set where
  field
    cycle : ℕ
    led   : String
    signature : String

instance
  contextHasLoopCounter : {A : Set} -> Context -> LoopCounter Context
  contextHasLoopCounter c = record { counter = Context.cycle c ; name = Context.led c}

inc : {A :  Set} -> LoopCounter A -> LoopCounter A
inc c = record c { counter =  (LoopCounter.counter c) + 1}

firstContext : Context
firstContext = record { cycle = 3 ; led = "q" ; signature = "aaa" }

incContextCycle : {{_ : Context -> LoopCounter Context}} -> Context -> Context
incContextCycle {{lp}} c = record c { cycle = incrementedCycle }
  where
    incrementedCycle = LoopCounter.counter (inc (lp c))






--data CodeSegment (n m : ℕ) : Set₁ where
--  cs : (i : DataSegment n) -> (o : DataSegment m) -> CodeSegment n m



--yoyo : DataSegment
--yoyo = record { name = "yoyo" ; ds = [ Yo ]}
