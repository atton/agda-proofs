module SetWithConstraint where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Maybe


data MySet (A : Set) : Set where
  empty : MySet A
  cons  : (String × A) -> MySet A -> MySet A

elem : {A : Set} -> String -> MySet A -> Bool
elem a empty              = false
elem a (cons (k , v) s)   = elem' (a == k) a (k , v) s
  where
    elem' : {A : Set} -> Bool -> String -> (String × A) -> MySet A -> Bool
    elem' false a p s  = elem a s
    elem' true  _ _ _  = true


insert' : {A : Set} -> Bool -> (String × A) -> MySet A -> MySet A
insert' false p s  = cons p s
insert' true  _ s  = s

insert : {A : Set} -> (String × A) -> MySet A -> MySet A
insert (k , v) empty = cons (k , v) empty
insert (k , v) s     = insert' (elem k s) (k , v) s

       
length : {A : Set} -> MySet A -> ℕ
length empty      = 0
length (cons _ s) = suc (length s)

head : {A : Set} -> MySet A -> Maybe (String × A)
head empty      = nothing
head (cons x _) = just x



empty-length : {A : Set} -> (length {A} empty) ≡ 0
empty-length = refl

empty-insert-length : (s : MySet ℕ) -> length (insert ("a" , 100) empty) ≡ 1
empty-insert-length s = refl

open ≡-Reasoning

insert-length : (k : String) (n : ℕ )(s : MySet ℕ) {nonElem : elem k s ≡ false} -> length (insert (k , n) s) ≡ suc (length s)
insert-length k n empty              = refl
insert-length k n (cons (ks , vs) s) {nonElem} = begin
  length (insert (k , n) (cons (ks , vs) s))
  ≡⟨ refl ⟩
  length (insert' (elem k (cons (ks , vs) s)) (k , n) (cons (ks , vs) s))
  ≡⟨ cong (\e -> length (insert' e (k , n) (cons (ks , vs) s))) nonElem  ⟩
  length (insert' false (k , n) (cons (ks , vs) s))
  ≡⟨ refl ⟩
  suc (suc (length s))
  ∎
  
insert-length-exists : (k : String) (n : ℕ )(s : MySet ℕ) {hasKey : elem k s ≡ true} {nonEmpty : s ≢ empty}
                       -> length (insert (k , n) s) ≡ (length s)
insert-length-exists _ _ empty  {nonEmpty = n}   = ⊥-elim (n refl)
insert-length-exists k n (cons x s) {hasKey = h} = begin
  length (insert (k , n) (cons x s))
  ≡⟨ refl ⟩
  length (insert' (elem k (cons x s)) (k , n) (cons x s))
  ≡⟨ cong (\e -> length (insert' e (k , n) (cons x s))) h ⟩
  length (insert' true (k , n) (cons x s))
  ≡⟨ refl ⟩
  length (cons x s)
  ∎
