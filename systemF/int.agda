module int where

open import Relation.Binary.PropositionalEquality
open import Level
open import systemF

-- define values

one : {l : Level} {U : Set l} -> Int {l} {U}
one = S O

two : {l : Level} {U : Set l} -> Int {l} {U}
two = S (S O)

three : {l : Level} {U : Set l} -> Int {l} {U}
three = S (S (S O))

four : {l : Level} {U : Set l} -> Int {l} {U}
four = S (S (S (S O)))

five : {l : Level} {U : Set l} -> Int {l} {U}
five = S (S (S (S (S O))))

six : {l : Level} {U : Set l} -> Int {l} {U}
six =  S (S (S (S (S (S O)))))

seven : {l : Level} {U : Set l} -> Int {l} {U}
seven = S (S (S (S (S (S (S O))))))

eight : {l : Level} {U : Set l} -> Int {l} {U}
eight = S (S (S (S (S (S (S (S O)))))))

nine : {l : Level} {U : Set l} -> Int {l} {U}
nine = S (S (S (S (S (S (S (S (S O))))))))

ten : {l : Level} {U : Set l} -> Int {l} {U}
ten = S (S (S (S (S (S (S (S (S O))))))))


-- add

add : {l : Level} {U : Set l} -> Int -> Int -> Int
add {l} {U} a b = \(x : U) -> \(y : (U -> U)) -> a (b x y) y

add-r : {l : Level} {U : Set l} -> Int -> Int -> Int {{!!}} {{!!}}
add-r {l} {U} a b = \z -> \s -> (R (R z (\x -> \_ -> s x) a) (\x -> \_ -> s x) b)

lemma-same-add : {l : Level} {U : Set l} -> add ≡ add-r {_} {U}
lemma-same-add = refl

lemma-add-zero-zero : {l : Level} {U : Set l} -> add O O ≡ O {_} {U}
lemma-add-zero-zero = refl

lemma-add-one-two : {l : Level} {U : Set l} -> add one two ≡ three {_} {U}
lemma-add-one-two = refl

--lemma-add-swap : {l : Level} {U : Set l} {a b : Int}  -> add a b ≡ add b a
--lemma-add-swap = refl
