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

insert : {A : Set} -> (String × A) -> MySet A -> MySet A
insert (k , v) empty        = cons (k , v) empty
insert (k , v) (cons (sk , sv) s) with (k == sk)
...                                  | true  = cons (sk , sv) s
...                                  | false = cons (sk , sv) (insert (k , v) s)
       
length : {A : Set} -> MySet A -> ℕ
length empty      = 0
length (cons _ s) = suc (length s)

elem : {A : Set} -> String -> MySet A -> Bool
elem a empty      = false
elem a (cons (k , v) s) with a == k
...                      | true  = true
...                      | false = elem a s

head : {A : Set} -> MySet A -> Maybe (String × A)
head empty      = nothing
head (cons x _) = just x



empty-length : {A : Set} -> (length {A} empty) ≡ 0
empty-length = refl

empty-insert-length : (s : MySet ℕ) -> length (insert ("a" , 100) empty) ≡ 1
empty-insert-length s = refl

open ≡-Reasoning

expand-non-elem : (k : String) (s : MySet ℕ) -> (nonElem : elem k s ≡ false) -> (just k ≢ (Data.Maybe.map proj₁ (head s)))
expand-non-elem k empty nonElem      = {!!}
expand-non-elem k (cons x s) nonElem = {!!}


insert-length : (k : String) (n : ℕ )(s : MySet ℕ) {nonElem : elem k s ≡ false} -> length (insert (k , n) s) ≡ suc (length s)
insert-length k n empty              = refl
insert-length k n (cons (ks , vs) s) {nonElem} = begin
  length (insert (k , n) (cons (ks , vs) s))
  ≡⟨ {!!} ⟩
  suc (suc (length s))
  ∎
