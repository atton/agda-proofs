module atton-master-meta-sample where

open import Data.Nat
open import Data.Unit
open import Function
Int = ℕ

record Context : Set where
  field
    a  : Int
    b  : Int
    c  : Int

open import subtype Context as N

record Meta : Set where 
  field
    context : Context
    c'      : Int
    next    : N.CodeSegment Context Context

open import subtype Meta as M

instance
  _ : N.DataSegment Context
  _ = record { get = id ; set = (\_ c -> c) }
  _ : M.DataSegment Context
  _ = record { get = (\m -> Meta.context m)  ;
               set = (\m c -> record m {context = c}) }
  _ : M.DataSegment Meta
  _ = record { get = id ; set = (\_ m -> m) }


liftContext : {X Y : Set} {{_ : N.DataSegment X}} {{_ : N.DataSegment Y}} -> N.CodeSegment X Y -> N.CodeSegment Context Context
liftContext {{x}} {{y}} (N.cs f) = N.cs (\c -> N.DataSegment.set y c (f (N.DataSegment.get x c)))

liftMeta : {X Y : Set} {{_ : M.DataSegment X}} {{_ : M.DataSegment Y}} -> N.CodeSegment X Y -> M.CodeSegment X Y
liftMeta (N.cs f) = M.cs f


gotoMeta : {I O : Set} {{_ : N.DataSegment I}} {{_ : N.DataSegment O}} -> M.CodeSegment Meta Meta -> N.CodeSegment I O -> Meta -> Meta
gotoMeta mCode code m = M.exec mCode (record m {next = (liftContext code)})

push : M.CodeSegment Meta Meta
push = M.cs (\m -> M.exec (liftMeta (Meta.next m)) (record m {c' = Context.c (Meta.context m)}))


record ds0 : Set where
  field
    a : Int
    b : Int

record ds1 : Set where
  field
    c : Int

instance
  _ : N.DataSegment ds0
  _ = record { set = (\c d -> record c {a = (ds0.a d) ; b = (ds0.b d)})
             ; get = (\c ->   record { a = (Context.a c) ; b = (Context.b c)})}
  _ : N.DataSegment ds1
  _ = record { set = (\c d -> record c {c = (ds1.c d)})
             ; get = (\c ->   record { c = (Context.c c)})}

cs2 : N.CodeSegment ds1 ds1
cs2 = N.cs id

cs1 : N.CodeSegment ds1 ds1
cs1 = N.cs (\d -> N.goto cs2 d)

cs0 : N.CodeSegment ds0 ds1
cs0 = N.cs (\d -> N.goto cs1 (record {c = (ds0.a d) + (ds0.b d)}))


main : Meta
main = gotoMeta push cs0 (record {context = (record {a = 100 ; b = 50 ; c = 70}) ; c' = 0 ; next = (N.cs id)})
-- record {context = record {a = 100 ; b = 50 ; c = 150} ; c' = 70 ; next = (N.cs id)}
