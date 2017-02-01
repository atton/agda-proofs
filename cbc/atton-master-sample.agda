module atton-master-sample where

open import Data.Nat
open import Data.Unit
open import Function
Int = ℕ

record Context : Set where
  field
    a : Int
    b : Int
    c : Int


open import subtype Context



record ds0 : Set where
  field
    a : Int
    b : Int

record ds1 : Set where
  field
    c : Int

instance
  _ : DataSegment ds0
  _ = record { set = (\c d -> record c {a = (ds0.a d) ; b = (ds0.b d)})
             ; get = (\c ->   record { a = (Context.a c) ; b = (Context.b c)})}
  _ : DataSegment ds1
  _ = record { set = (\c d -> record c {c = (ds1.c d)})
             ; get = (\c ->   record { c = (Context.c c)})}

cs2 : {{_ : DataSegment ds1}} -> CodeSegment ds1 ds1
cs2 {{d}} = cs {{d}}{{d}} id

cs1 : CodeSegment ds1 ds1
cs1 = cs (\d -> goto cs2 d)

cs0 : {{_ : DataSegment ds0}} {{_ : DataSegment ds1}} -> CodeSegment ds0 ds1
cs0 {{d0}}{{d1}} = cs {{d0}}{{d1}} (\d -> goto {{d1}} {{d1}} cs1 (record {c = (ds0.a d) + (ds0.b d)}))

main : ds1
main = goto cs0 (record {a = 100 ; b = 50})
