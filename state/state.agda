open import Relation.Binary.PropositionalEquality
open import Level
open ≡-Reasoning

{-
Haskell Definition
newtype State s a = State { runState :: s -> (a, s) }

instance Monad (State s) where
  return a = State $ \s -> (a, s)
  m >>= k  = State $ \s -> let
    (a, s') = runState m s
    in runState (k a) s'
-}

module state where

record Product {l ll : Level} (A : Set l) (B : Set ll) : Set (suc (l ⊔ ll)) where 
  constructor <_,_>
  field
    first  : A
    second : B
open Product

product-create : {l ll : Level} {A : Set l} {B : Set ll} -> A -> B -> Product A B
product-create a b = < a , b >


record State {l ll : Level} (S : Set l) (A : Set ll) : Set (suc (l ⊔ ll)) where
  field
    runState : S -> Product A S
open State

state : {l ll : Level} {S : Set l} {A : Set ll} -> (S -> Product A S) -> State S A
state f = record {runState = f}

return : {l ll : Level} {S : Set l} {A : Set ll} -> A -> State S A
return a = state (\s -> < a , s > )


_>>=_ : {l ll lll : Level} {S : Set l} {A : Set ll} {B : Set lll} -> State S A -> (A -> State S B) -> State S B
m >>= k = {!!}