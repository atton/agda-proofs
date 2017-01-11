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
    element : Maybe A
    n       : ℕ


open import subtype Context as N

instance
  ContextIsDataSegment : N.DataSegment Context
  ContextIsDataSegment = record {get = (\c -> c) ; set = (\_ c -> c)}


record MetaContext (X : Set) {{_ : N.DataSegment X}} : Set₁ where
  field
    context : Context
    stack   : SingleLinkedStack A
    nextCS  : N.CodeSegment X X




open import subtype (MetaContext Context) as M

instance
  MetaContextIncludeContext : M.DataSegment Context
  MetaContextIncludeContext = record { get = MetaContext.context
                                     ; set = (\m c -> record m {context = c}) }

  MetaContextIsMetaDataSegment : M.DataSegment (MetaContext Context)
  MetaContextIsMetaDataSegment  = record { get = (\m -> m) ; set = (\_ m -> m) }


liftMeta : {X Y : Set} {{_ : M.DataSegment X}} {{_ : M.DataSegment Y}} -> N.CodeSegment X Y -> M.CodeSegment X Y
liftMeta (N.cs f) = M.cs f

liftContext : {X Y : Set} {{_ : N.DataSegment X}} {{_ : N.DataSegment Y}} -> N.CodeSegment X Y -> N.CodeSegment Context Context
liftContext {{x}} {{y}} (N.cs f) = N.cs (\c -> N.DataSegment.set y c (f (N.DataSegment.get x c)))
 
-- definition based from Gears(209:5708390a9d88) src/parallel_execution

emptySingleLinkedStack : SingleLinkedStack A
emptySingleLinkedStack = record {top = nothing}


pushSingleLinkedStack :  MetaContext Context -> MetaContext Context
pushSingleLinkedStack m = M.exec (liftMeta n) (record m {stack = (push s e) })
  where
    n = MetaContext.nextCS m
    e = Context.element (MetaContext.context m)
    s = MetaContext.stack   m
    push : SingleLinkedStack A -> Maybe A -> SingleLinkedStack A
    push s nothing  = s
    push s (just x) = record {top = just (cons x (top s))}



popSingleLinkedStack : MetaContext Context -> MetaContext Context
popSingleLinkedStack m = M.exec (liftMeta n) (record m {stack = (st m) ; context = record con {element = (elem m)}})
  where
    n = MetaContext.nextCS m
    con  = MetaContext.context m
    elem : MetaContext Context -> Maybe A
    elem record {stack = record { top = (just (cons x _)) }} = just x
    elem record {stack = record { top = nothing           }} = nothing
    st : MetaContext Context -> SingleLinkedStack A
    st record {stack = record { top = (just (cons _ s)) }} = record {top = s}
    st record {stack = record { top = nothing           }} = record {top = nothing}
    
pushSingleLinkedStackCS : M.CodeSegment (MetaContext Context) (MetaContext Context)
pushSingleLinkedStackCS = M.cs pushSingleLinkedStack

popSingleLinkedStackCS : M.CodeSegment (MetaContext Context) (MetaContext Context)
popSingleLinkedStackCS = M.cs popSingleLinkedStack





-- sample

record Num : Set where
  field
    num : ℕ

instance
  NumIsNormalDataSegment : N.DataSegment Num
  NumIsNormalDataSegment = record { get = (\c -> record { num = Context.n c})
                                  ; set = (\c n -> record c {n = Num.num n})}


plus3 : Num -> Num
plus3 record { num = n } = record {num = n + 3}

plus3CS : N.CodeSegment Num Num
plus3CS = N.cs plus3


setNext : {X Y : Set} {{x : N.DataSegment X}} {{y : N.DataSegment Y}}
        -> (N.CodeSegment X Y) -> M.CodeSegment (MetaContext Context) (MetaContext Context)
setNext c = M.cs (\mc -> record mc {nextCS = liftContext c})





pushPlus3CS : {mc : MetaContext Context} -> M.CodeSegment (MetaContext Context) (MetaContext Context)
pushPlus3CS {mc} = M.csComp {mc} pushSingleLinkedStackCS (setNext plus3CS)
