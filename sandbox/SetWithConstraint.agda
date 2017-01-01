module SetWithConstraint where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Data.AVL 
open import Data.AVL.Sets (Relation.Binary.StrictTotalOrder.isStrictTotalOrder Data.Nat.Properties.strictTotalOrder) as S

yo : ⟨Set⟩
yo = S.empty

empty-set : (length (S.toList  S.empty)) ≡ zero
empty-set  = refl

empty-set+1 : length (S.toList (S.insert 100 S.empty)) ≡ 1
empty-set+1 = refl

open ≡-Reasoning

non-empty-set+1 : (a : ℕ ) (s : ⟨Set⟩) {notElem : (a S.∈? s) ≡ false} -> length (S.toList (S.insert a s)) ≡ suc (length (S.toList s))
non-empty-set+1 a (tree (Indexed.leaf l<u))         = refl
non-empty-set+1 a (tree (Indexed.node (proj₃ , proj₄) x x₁ Height-invariants.∼+)) = {!!}
non-empty-set+1 a (tree (Indexed.node (proj₃ , proj₄) x x₁ Height-invariants.∼0)) = {!!}
non-empty-set+1 a (tree (Indexed.node (proj₃ , proj₄) x x₁ Height-invariants.∼-)) = {!!}

