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

record Product {l : Level} (A B : Set l) : Set (suc l) where 
  constructor <_,_>
  field
    first  : A
    second : B
open Product

record State {l : Level} (S A : Set l) : Set (suc l) where
  field
    runState : S -> Product A S
open State

state : {l : Level} {S A : Set l} -> (S -> Product A S) -> State S A
state f = record {runState = f}

return : {l : Level} {S A : Set l}  -> A -> State S A
return a = state (\s -> < a , s > )

_>>=_ : {l : Level} {S A B : Set l} -> State S A -> (A -> State S B) -> State S B
m  >>= k =  state (\s -> (State.runState (k (Product.first (State.runState m s))) (Product.second (State.runState m s))))