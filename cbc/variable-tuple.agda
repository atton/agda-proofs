module variable-tuple where

open import Data.Nat hiding (_<_ ; _>_)
open import Data.String
open import Data.List
open import Data.Unit
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Level hiding (zero)

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

data CodeSegment (A B : Set₁) : Set₁ where
--  cs : A -> B -> (A -> B) -> CodeSegment A B
  cs : A -> B  -> CodeSegment A B

id : {l : Level} {A : Set l} -> A -> A
id a = a

CommonCodeSegment : Set₁
CommonCodeSegment = CodeSegment Format Format

csDouble : CommonCodeSegment
csDouble = cs double double


ods : CommonCodeSegment -> Set
ods (cs i FEnd)       = ⊤
ods (cs i (FSet s o)) = s × (ods (cs i o))


ods-double : ods csDouble
ods-double = "hoge" , zero , tt


ids : {A : Set} -> CommonCodeSegment -> Set
ids {A} (cs FEnd o)       = A
ids {A} (cs (FSet s i) o) = s -> (ids {A} (cs i o))


ids-double : {A : Set} {a : A} -> ids {A} csDouble
ids-double {_} {a}  =  \(s : String) -> \(n : ℕ) -> a



executeCS : (cs : CommonCodeSegment) -> Set
executeCS c = ids {ods c} c


infixr 30  _◎_
_◎_ : {A B C : Set₁} -> CodeSegment A B -> CodeSegment B C -> CodeSegment A C
(cs i _) ◎ (cs _ o) = cs i o


◎-double : CommonCodeSegment 
◎-double = csDouble ◎ (cs (< String || ℕ >) <>) ◎ (cs <> triple)
-- ◎-double = csDouble ◎ (cs (< String || ℕ >) <>) ◎ (cs double triple) -- ...
