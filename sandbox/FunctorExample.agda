open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


module FunctorExample where

id : {l : Level} {A : Set l} -> A -> A
id x = x

_∙_ : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} -> (B -> C) -> (A -> B) -> (A -> C)
f ∙ g = \x -> f (g x)



record Functor {l : Level} (F : Set l -> Set (suc l)) : (Set (suc l)) where
  field
    fmap : ∀{A B} -> (A -> B) -> (F A) -> (F B)
  field
    preserve-id : ∀{A} (Fa : F A) → fmap id Fa ≡ id Fa
    covariant : ∀{A B C} (f : A → B) → (g : B → C) → (x : F A)
      → fmap (g ∙ f) x ≡ fmap g (fmap f x)

data List {l : Level} (A : Set l) : (Set (suc l)) where
  nil  : List A
  cons : A -> List A -> List A

list-fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> List A -> List B
list-fmap f nil         = nil
list-fmap f (cons x xs) = cons (f x) (list-fmap f xs)

list-preserve-id : {l : Level} {A : Set l} -> (xs : List A) -> list-fmap id xs ≡ id xs
list-preserve-id nil = refl
list-preserve-id (cons x xs) = cong (\li -> cons x li) (list-preserve-id xs)

list-covariant : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                 (f : A -> B) → (g : B -> C) → (x : List A) → list-fmap (g ∙ f) x ≡ list-fmap g (list-fmap f x)
list-covariant f g nil         = refl
list-covariant f g (cons x xs) = cong (\li -> cons (g (f x)) li) (list-covariant f g xs)


list-is-functor : {l : Level} -> Functor List
list-is-functor {l} = record { fmap        = list-fmap ;
                               preserve-id = list-preserve-id ;
                               covariant   = list-covariant {l}}

--open module FunctorWithImplicits {l ll : Level} {F : Set l -> Set ll} {{functorT : Functor F}} = Functor functorT


--hoge : ∀{F A} {{Functor F}} -> (Fa : F A) -> Functor.fmap id Fa ≡ id Fa
--hoge = {!!}


{-
record NaturalTransformation {l ll : Level} (F G : Set l -> Set ll) : Set (suc (l ⊔ ll)) where
  field
    natural : {A : Set l}  -> F A -> G A
  field
    lemma : ∀{f } {x : Functor F} -> natural (fmap f x) ≡ f (natural x)
-}
