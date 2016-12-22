module variable-tuple where

open import Data.Nat hiding (_<_ ; _>_)
open import Data.String
open import Data.List
open import Data.Unit
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

data Format : Set₁ where
  FEnd : Format
  FSet : Set -> Format -> Format

<> : Format
<> = FEnd

infix  51 _>
_> : (Format -> Format) -> Format
_> f = f FEnd

infixl 52 _||_
_||_ : (Format -> Format) -> Set -> (Format -> Format)
_||_ f1 s = f1 ∘ (FSet s)

infix 53 <_
<_ : Set -> Format -> Format
<_ s = FSet s


unit : Format
unit = <>

single : Format
single = < ℕ  >

double : Format
double = < String || ℕ  >

triple : Format
triple = < String || ℕ  || (List ℕ) >


record CodeSegment : Set₁ where
  field
    IDS : Format
    ODS : Format

cs : Format -> Format -> CodeSegment
cs i o = record { IDS = i ; ODS = o }


csDouble : CodeSegment
csDouble = cs double double


ods : CodeSegment -> Set
ods record { ODS = i } = ods' i
  where
    ods' : Format -> Set
    ods' FEnd         = ⊤
    ods' (FSet s o) = s × (ods' o)

ods-double : ods csDouble
ods-double = "hoge" , zero , tt



ids : {A : Set} ->  CodeSegment -> Set
ids {A} record {IDS = IDS} = ids' IDS
  where
    ids' : Format -> Set
    ids' FEnd       = A
    ids' (FSet x f) = x -> (ids' f)


ids-double : {A : Set} {a : A} -> ids {A} csDouble
ids-double {_} {a}  =  \(s : String) -> \(n : ℕ) -> a


executeCS : (cs : CodeSegment) -> Set
executeCS c = ids {ods c} c


_◎_ : {c1ods c2ids : Format} -> {equiv : c1ods ≡ c2ids} -> CodeSegment -> CodeSegment -> CodeSegment
record {IDS = i} ◎ (record {ODS = o}) = cs i o


compose-cs : CodeSegment
compose-cs = _◎_ {double} {double} {refl} csDouble csDouble



