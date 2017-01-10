open import Level
open import Data.Maybe
open import Data.Product
open import Data.Nat

module stack-subtype (A : Set) where

-- data definitions

data Element (a : Set) : Set where
  cons : a -> Maybe (Element a) -> Element a

datum : {a : Set} -> Element a -> a
datum (cons a _) = a

next : {a : Set} -> Element a -> Maybe (Element a)
next (cons _ n) = n

record SingleLinkedStack (a : Set) : Set where
  field
    top : Maybe (Element a)
open SingleLinkedStack

record Context : Set where
  field
    stack   : SingleLinkedStack A
    element : Maybe A
    n       : ℕ 

open import subtype Context

instance
  yo : DataSegment Context
  yo = record {get = (\x -> x) ; set = (\_ c -> c)}



-- definition based from Gears(209:5708390a9d88) src/parallel_execution

emptySingleLinkedStack : SingleLinkedStack A
emptySingleLinkedStack = record {top = nothing}

pushSingleLinkedStack : Context -> Context
pushSingleLinkedStack c = record c { stack = (push c) ; element = nothing}
  where
    push : Context -> SingleLinkedStack A
    push record { stack = stack ; element = nothing }  = stack
    push record { stack = stack ; element = (just x) } = stack1
      where
        el = cons x (top stack)
        stack1 = record {top = just el}

popSingleLinkedStack : Context -> Context
popSingleLinkedStack c = record c {element = (elem c) ; stack =  (popdStack c)}
  where
    elem : Context -> Maybe A
    elem record { stack = record { top = (just (cons x _)) } } = just x
    elem record { stack = record { top = nothing } }           = nothing
    popdStack : Context -> SingleLinkedStack A
    popdStack record { stack = record { top = (just (cons _ s)) } } = record { top = s }
    popdStack record { stack = record { top = nothing } }           = record { top = nothing }

-- sample


pushCS = cs pushSingleLinkedStack
popCS  = cs popSingleLinkedStack


-- stack
record Stack {X Y : Set} (stackImpl : Set -> Set) : Set where
  field
    stack : stackImpl A
    push  : {{_ : DataSegment X}} {{_ : DataSegment Y}} -> CodeSegment X Y
    pop   : {{_ : DataSegment X}} {{_ : DataSegment Y}} -> CodeSegment X Y

