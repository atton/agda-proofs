module subtype where

open import Level
open import Function
open import Data.Nat hiding (_⊔_)
open import Data.Bool

data DataSegment  (X : Set -> Set) : Set₁  where
  ds : {x : Set} -> X x -> DataSegment X


record DS1 (A : Set) : Set where
  field
    counter : A -> ℕ

record DS2 (A : Set) : Set where
  field
    useSum : A -> Bool

record Context : Set where
  field
    loopCounter : ℕ
    flag        : Bool

instance
  ds1 : DS1 Context
  ds1 = record {counter = Context.loopCounter}

hoge :  Context -> {{ins : DS1 Context}} -> DataSegment DS1
hoge _ {{i}}  = ds i



data CodeSegment (I O : (Set -> Set)) : Set₁ where
  cs : (DataSegment I -> DataSegment O) -> CodeSegment I O
