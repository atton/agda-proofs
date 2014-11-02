open import systemT
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module int where

double : Int -> Int
double O = O
double (S n) = S (S (double n))


infixl 30 _+_
_+_ : Int -> Int -> Int
n + O     = n
n + (S m) = S (n + m)

left-add-zero : (n : Int) -> O + n ≡ n
left-add-zero O     = refl
left-add-zero (S n) = cong S (left-add-zero n)

left-add-one : (n : Int) -> (S n) ≡ S O + n
left-add-one    O  = refl
left-add-one (S n) = cong S (left-add-one n)

left-increment : (n m : Int) -> (S n) + m ≡ S (n + m)
left-increment  n    O  = refl
left-increment  n (S m) = cong S (left-increment n m)

sum-sym : (x : Int) (y : Int) -> x + y ≡ y + x
sum-sym    O     O  = refl
sum-sym    O  (S y) = cong S (sum-sym O y)
sum-sym (S x)    O  = cong S (sum-sym x O)
sum-sym (S x) (S y) = begin
    (S x) + (S y)
  ≡⟨ refl ⟩
    S ((S x) + y)
  ≡⟨ cong S (sum-sym (S x) y) ⟩
    S (y + (S x))
  ≡⟨ (sym (left-increment y (S x))) ⟩
    (S y) + (S x)
  ∎

sum-assoc : (x y z : Int) -> x + (y + z) ≡ (x + y) + z
sum-assoc    O     O     O   = refl
sum-assoc    O     O  (S z)  = cong S (sum-assoc O O z)
sum-assoc    O  (S y)    O   = refl
sum-assoc    O  (S y) (S z)  = cong S (sum-assoc O (S y) z)
sum-assoc (S x)    O     O   = refl
sum-assoc (S x)    O  (S z)  = cong S (sum-assoc (S x) O z)
sum-assoc (S x) (S y)    O   = refl
sum-assoc (S x) (S y) (S z)  = cong S (sum-assoc (S x) (S y) z)


infixl 40 _*_
_*_ : Int -> Int -> Int
n *    O  = O
n * (S O) = n
n * (S m) = n + (n * m)

right-mult-zero : (n : Int) -> n * O ≡ O
right-mult-zero n = refl

right-mult-one : (n : Int) -> n * (S O) ≡ n
right-mult-one n = refl

right-mult-distr-one : (n m : Int) -> n * (S m) ≡ n + (n * m)
right-mult-distr-one    O     O  = refl
right-mult-distr-one    O  (S m) = refl
right-mult-distr-one (S n)    O  = refl
right-mult-distr-one (S n) (S m) = refl


left-mult-zero : (n : Int) -> O * n ≡ O
left-mult-zero O     = refl
left-mult-zero (S n) = begin
    O * (S n)
  ≡⟨ right-mult-distr-one O n ⟩
    O + (O * n)
  ≡⟨ sum-sym O (O * n) ⟩
    (O * n) + O
  ≡⟨ refl ⟩
    (O * n)
  ≡⟨ left-mult-zero n ⟩
    O
  ∎

left-mult-one : (n : Int) -> (S O) * n ≡ n
left-mult-one    O  = refl
left-mult-one (S n) = begin
    (S O) * S n
  ≡⟨ right-mult-distr-one (S O) n ⟩
    (S O) + ((S O) * n)
  ≡⟨ cong (_+_ (S O)) (left-mult-one n) ⟩
    (S O) + n
  ≡⟨ sum-sym (S O) n ⟩
    n + (S O)
  ≡⟨ refl ⟩
    S n
  ∎


left-mult-distr-one : (n m : Int) -> (S n) * m ≡ m + (n * m)
left-mult-distr-one    O     O  = refl
left-mult-distr-one    O  (S m) = begin
    (S O) * S m
  ≡⟨ left-mult-one (S m) ⟩
    S m
  ≡⟨ refl ⟩
    S m + O
  ≡⟨ cong (_+_ (S m)) (sym (left-mult-zero (S m))) ⟩
    S m + (O * S m)
  ∎
left-mult-distr-one (S n)    O  = refl
left-mult-distr-one (S n) (S m) = begin
    S (S n) * S m
  ≡⟨ right-mult-distr-one (S (S n)) m ⟩
    (S (S n)) + ((S (S n)) * m)
  ≡⟨ cong (\x -> (S (S n)) + x) (left-mult-distr-one (S n) m) ⟩
    S (S n) + (m + S n * m)
  ≡⟨ cong (\x -> x + (m + S n * m)) (left-add-one (S n)) ⟩
    (S O) + (S n) + (m + S n * m)
  ≡⟨ sum-assoc ((S O) + (S n)) m (S n * m)  ⟩
    (S O) + (S n) + m + S n * m
  ≡⟨ cong (\x -> x + m + S n * m) (sum-sym (S O) (S n)) ⟩
    ((((S n) + (S O)) + m) + S n * m)
  ≡⟨ cong (\x -> x + (S n * m)) (sym (sum-assoc (S n) (S O) m))⟩
    (((S n) + ((S O) + m)) + S n * m)
  ≡⟨ cong (\x -> (S n + x + S n * m)) (sym (left-add-one m)) ⟩
    ((S n) + (S m) + S n * m)
  ≡⟨ cong (\x -> x + (S n * m)) (sum-sym (S n) (S m)) ⟩
    (S m) + (S n) + (S n * m)
  ≡⟨ sym (sum-assoc (S m) (S n) (S n * m)) ⟩
    (S m) + ((S n) + ((S n) * m))
  ≡⟨ cong (\x -> (S m) + x ) (sym (right-mult-distr-one (S n) m )) ⟩
    S m + S n * S m
  ∎


mult-sym : (n m : Int) -> n * m ≡ m * n
mult-sym n O     = begin
    n * O
  ≡⟨ refl ⟩
    O
  ≡⟨ sym (left-mult-zero n) ⟩
    O * n
  ∎
mult-sym n (S m) = begin
    n * (S m)
  ≡⟨ right-mult-distr-one n m ⟩
    n + (n * m)
  ≡⟨ cong (\x -> n + x ) (mult-sym n m) ⟩
    n + (m * n)
  ≡⟨ sym (left-mult-distr-one m n)  ⟩
    (S m) * n
  ∎
