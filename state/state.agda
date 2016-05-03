open import Relation.Binary.PropositionalEquality
open import Level
open ≡-Reasoning


module state where

record Product {l : Level} (A B : Set l) : Set (suc l) where 
  constructor <_,_>
  field
    first  : A
    second : B
open Product

id : {l : Level} {A : Set l} -> A -> A
id a = a


infixr 10 _∘_
_∘_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘ f = \a -> g (f a)

{-
Haskell Definition
newtype State s a = State { runState :: s -> (a, s) }

instance Monad (State s) where
  return a = State $ \s -> (a, s)
  m >>= k  = State $ \s -> let
    (a, s') = runState m s
    in runState (k a) s'
-}


record State {l : Level} (S A : Set l) : Set (suc l) where
  field
    runState : S -> Product A S
open State

state : {l : Level} {S A : Set l} -> (S -> Product A S) -> State S A
state f = record {runState = f}

return : {l : Level} {S A : Set l} -> A -> State S A
return a = state (\s -> < a , s > )

_>>=_ : {l : Level} {S A B : Set l} -> State S A -> (A -> State S B) -> State S B
m  >>= k =  state (\s -> (runState (k (first (runState m s))) (second (runState m s))))

{- fmap definitions in Haskell
instance Functor (State s) where
    fmap f m = State $ \s -> let
        (a, s') = runState m s
        in (f a, s')
-}

fmap : {l : Level} {S A B : Set l} -> (A -> B) -> (State S A) -> (State S B)
fmap f m = state (\s -> < (f (first ((runState m) s))), (second ((runState m) s)) >)

-- proofs

fmap-id : {l : Level} {A S : Set l} {s : State S A} -> fmap id s ≡ id s
fmap-id = refl

fmap-comp : {l : Level} {S A B C : Set l} {g : B -> C} {f : A -> B} {s : State S A} ->  ((fmap g) ∘ (fmap f)) s ≡ fmap (g ∘ f) s
fmap-comp {_}{_}{_}{_}{_}{g}{f}{s} = refl 
