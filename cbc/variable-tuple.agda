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


DataSegment : {A : Set} -> Format -> Set
DataSegment {A} FEnd       = A
DataSegment {A} (FSet x f) = x -> (DataSegment {A} f)


data CodeSegment : Set₁ where
  cs : Format -> Format -> CodeSegment

csDouble : CodeSegment
csDouble = cs double double

ods : CodeSegment -> Set
ods (cs ids FEnd)         = ⊤
ods (cs ids (FSet s f))   = s × (ods (cs ids f))

ods-double : ods csDouble
ods-double = "hoge" , zero , tt


ids : {A : Set} -> CodeSegment ->  Set
ids {A} (cs i o) = DataSegment {A} i

ids-double : {A : Set} {a : A} -> ids {A} csDouble
ids-double {_} {a}  =  \(s : String) -> \(n : ℕ) -> a


executeCS : (cs : CodeSegment) -> Set
executeCS c = ids {ods c} c

