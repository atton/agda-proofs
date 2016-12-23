module variable-tuple where

open import Data.Nat hiding (_<_ ; _>_)
open import Data.String
open import Data.List
open import Data.Unit
open import Data.Product
open import Function using (_∘_ ; id)
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

data CodeSegment (I O : Set) : Set₁ where
  cs : (I -> O) -> CodeSegment I O


twiceWithName : (String × ℕ ) -> (String × ℕ )
twiceWithName (s , n) = s , twice n
  where
    twice : ℕ -> ℕ
    twice zero        = zero
    twice (ℕ.suc n₁) = (ℕ.suc (ℕ.suc (twice n₁)))

csDouble : CodeSegment (String × ℕ) (String × ℕ)
csDouble = cs twiceWithName


ods : {I O : Set} -> CodeSegment I O -> Set
ods {i} {o} c = o

ods-double : ods csDouble
ods-double = "hoge" , zero


ids : {I O : Set} -> CodeSegment I O -> Set
ids {i} {o} c = i

ids-double : ids csDouble
ids-double = "fuga" , 3

--ids-double : {A : Set} {a : A} -> ids csDouble
--ids-double {_} {a}  =  \(s : String) -> \(n : ℕ) -> a



executeCS : {A B : Set} ->  CodeSegment A B -> (A -> B)
executeCS (cs b) = b



infixr 30  _◎_
_◎_ : {A B C : Set} -> CodeSegment A B -> CodeSegment B C -> CodeSegment A C
(cs b1) ◎ (cs b2) = cs (b2 ∘ b1)




◎-double : CodeSegment (String × ℕ) (String × ℕ )
--◎-double = csDouble ◎ csDouble ◎ csDouble  -- ok
◎-double = csDouble ◎ (cs (\s -> tt)) ◎ (cs (\t -> ("yo" , 100))) -- ok
--◎-double = csDouble ◎ (cs (\s -> tt)) ◎ csDouble  -- ng (valid type check)


