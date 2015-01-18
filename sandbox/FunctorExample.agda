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

fmap-to-nest-list : {l ll : Level} {A : Set l} {B : Set l} {fl : {l' : Level} -> Functor {l'} List}
                    -> (A -> B) -> (List (List A)) -> (List (List B))
fmap-to-nest-list {_} {_} {_} {_} {fl} f xs = Functor.fmap fl (Functor.fmap fl f)  xs

data Identity {l : Level} (A : Set l) : Set (suc l) where
  identity : A -> Identity A

identity-fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> Identity A -> Identity B
identity-fmap f (identity a) = identity (f a)

identity-preserve-id : {l : Level} {A : Set l} -> (x : Identity A) -> identity-fmap id x ≡ id x
identity-preserve-id (identity x) = refl 

identity-covariant : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                 (f : A -> B) → (g : B -> C) → (x : Identity A) → identity-fmap (g ∙ f) x ≡ identity-fmap g (identity-fmap f x)
identity-covariant f g (identity x) = refl

identity-is-functor : {l : Level} -> Functor Identity
identity-is-functor {l} = record { fmap        = identity-fmap {l};
                                   preserve-id = identity-preserve-id ;
                                   covariant   = identity-covariant }




record NaturalTransformation {l ll : Level} (F G : Set l -> Set (suc l))
                                            (functorF : Functor F)
                                            (functorG : Functor G) : Set (suc (l ⊔ ll)) where
  field
    natural-transformation : {A : Set l}  -> F A -> G A
  field
    commute : ∀ {A B} -> (function : A -> B) -> (x : F A) ->
              natural-transformation (Functor.fmap functorF function x) ≡  Functor.fmap functorG function (natural-transformation x)

tail : {l : Level} {A : Set l} -> List A -> List A
tail nil         = nil
tail (cons _ xs) = xs

tail-commute : {l ll : Level} {A : Set l} {B : Set ll} -> (f : A -> B) -> (xs : List A) -> 
               tail (list-fmap f xs) ≡ list-fmap f (tail xs)
tail-commute f nil = refl
tail-commute f (cons x xs) = refl 

tail-is-natural-transformation : {l ll : Level} -> NaturalTransformation  {l} {ll} List List list-is-functor list-is-functor
tail-is-natural-transformation = record { natural-transformation = tail;
                                          commute                = tail-commute} 
