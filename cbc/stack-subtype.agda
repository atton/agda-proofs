open import Level hiding (lift)
open import Data.Maybe
open import Data.Product
open import Data.Nat hiding (suc)

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
    -- fields for stack
    element : Maybe A
    stack   : SingleLinkedStack A
    -- fields for data segments
    n       : ℕ



open import subtype Context as N

instance
  ContextIsDataSegment : N.DataSegment Context
  ContextIsDataSegment = record {get = (\c -> c) ; set = (\_ c -> c)}


record Meta  : Set₁ where
  field
    context : Context
    nextCS  : N.CodeSegment Context Context

    

open import subtype Meta as M

instance
  MetaIncludeContext : M.DataSegment Context
  MetaIncludeContext = record { get = Meta.context
                              ; set = (\m c -> record m {context = c}) }

  MetaIsMetaDataSegment : M.DataSegment Meta
  MetaIsMetaDataSegment  = record { get = (\m -> m) ; set = (\_ m -> m) }


liftMeta : {X Y : Set} {{_ : M.DataSegment X}} {{_ : M.DataSegment Y}} -> N.CodeSegment X Y -> M.CodeSegment X Y
liftMeta (N.cs f) = M.cs f

liftContext : {X Y : Set} {{_ : N.DataSegment X}} {{_ : N.DataSegment Y}} -> N.CodeSegment X Y -> N.CodeSegment Context Context
liftContext {{x}} {{y}} (N.cs f) = N.cs (\c -> N.DataSegment.set y c (f (N.DataSegment.get x c)))
 
-- definition based from Gears(209:5708390a9d88) src/parallel_execution

emptySingleLinkedStack : SingleLinkedStack A
emptySingleLinkedStack = record {top = nothing}


pushSingleLinkedStack : Meta -> Meta
pushSingleLinkedStack m = M.exec (liftMeta n) (record m {context = record c {stack = (push s e)}})
  where
    c = (Meta.context m)
    n = Meta.nextCS     m
    e = Context.element c
    s = Context.stack   c
    push : SingleLinkedStack A -> Maybe A -> SingleLinkedStack A
    push s nothing  = s
    push s (just x) = record {top = just (cons x (top s))}


popSingleLinkedStack : Meta -> Meta
popSingleLinkedStack m = M.exec (liftMeta n) (record m { context = record c { stack = (st c) ; element = (elem c)}})
  where
    n = Meta.nextCS m
    c = Meta.context m
    elem : Context -> Maybe A
    elem record {stack = record { top = (just (cons x _)) }} = just x
    elem record {stack = record { top = nothing } }          = nothing
    st : Context -> SingleLinkedStack A
    st record {stack = record { top = (just (cons _ s)) }} = record {top = s}
    st record {stack = record { top = nothing } }          = record {top = nothing}


pushSingleLinkedStackCS : M.CodeSegment Meta Meta
pushSingleLinkedStackCS = M.cs pushSingleLinkedStack

popSingleLinkedStackCS : M.CodeSegment Meta Meta
popSingleLinkedStackCS = M.cs popSingleLinkedStack


-- for sample

firstContext : Context
firstContext = record {stack = emptySingleLinkedStack ; element = nothing ; n = 0}


firstMeta : Meta 
firstMeta = record {nextCS = (N.cs (\m -> m)) ; context = firstContext}

