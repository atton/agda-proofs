open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


module FunctorExample where

id : {l : Level} {A : Set l} -> A -> A
id x = x

_∙_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
f ∙ g = \x -> f (g x)

record Functor {l : Level} {A : Set l} (F : {l' : Level} -> Set l' -> Set l') : Set (suc l) where
  field
    fmap : {A B : Set l} -> (A -> B) -> (F A) -> (F B)
  field
    preserve-id : {A : Set l} (x : F A) → fmap id x ≡ id x
    covariant   : {A B C : Set l} (f : A -> B) -> (g : B -> C) -> (x : F A)
                    -> fmap (g ∙ f) x ≡ ((fmap g) ∙ (fmap f)) x
open Functor



data List {l : Level} (A : Set l) : (Set l) where
  nil  : List A
  cons : A -> List A -> List A

list-fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> List A -> List B
list-fmap f nil         = nil
list-fmap f (cons x xs) = cons (f x) (list-fmap f xs)

list-preserve-id : {l : Level} {A : Set l} -> (xs : List A) -> list-fmap id xs ≡ id xs
list-preserve-id nil = refl
list-preserve-id (cons x xs) = cong (\li -> cons x li) (list-preserve-id xs)

list-covariant : {l : Level} {A B C : Set l} ->
                 (f : A -> B) → (g : B -> C) → (x : List A) → list-fmap (g ∙ f) x ≡ list-fmap g (list-fmap f x)
list-covariant f g nil         = refl
list-covariant f g (cons x xs) = cong (\li -> cons (g (f x)) li) (list-covariant f g xs)


list-is-functor : {l : Level} {A : Set l}-> Functor {l} {A} List
list-is-functor = record { fmap        = list-fmap ;
                           preserve-id = list-preserve-id ;
                           covariant   = list-covariant}

fmap-to-nest-list : {l : Level} {A B : Set l} 
                    -> (A -> B) -> (List (List A)) -> (List (List B))
fmap-to-nest-list {l} {A} {B} f xs = Functor.fmap (list-is-functor {l} {List A}) (Functor.fmap {l} {A} list-is-functor f)  xs

data Identity {l : Level} (A : Set l) : Set l where
  identity : A -> Identity A

identity-fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> Identity A -> Identity B
identity-fmap f (identity a) = identity (f a)

identity-preserve-id : {l : Level} {A : Set l} -> (x : Identity A) -> identity-fmap id x ≡ id x
identity-preserve-id (identity x) = refl 

identity-covariant : {l : Level} {A B C : Set l}
                 (f : A -> B) → (g : B -> C) → (x : Identity A) → identity-fmap (g ∙ f) x ≡ identity-fmap g (identity-fmap f x)
identity-covariant f g (identity x) = refl

identity-is-functor : {l : Level} {A : Set l} -> Functor {l} {A} Identity
identity-is-functor {l} = record { fmap        = identity-fmap {l};
                                   preserve-id = identity-preserve-id ;
                                   covariant   = identity-covariant }




record NaturalTransformation {l : Level} (F G : {l' : Level} -> Set l' -> Set l')
                                         {fmapF : {A B : Set l} -> (A -> B) -> (F A) -> (F B)}
                                         {fmapG : {A B : Set l} -> (A -> B) -> (G A) -> (G B)}
                                         (natural-transformation : {A : Set l}  -> F A -> G A)
                             : Set (suc l) where
  field
    commute : {A B : Set l} -> (f : A -> B) -> (x : F A) ->
              natural-transformation (fmapF f x) ≡  fmapG f (natural-transformation x)
open NaturalTransformation

tail : {l : Level} {A : Set l} -> List A -> List A
tail nil         = nil
tail (cons _ xs) = xs

tail-commute : {l : Level} {A B : Set l} -> (f : A -> B) -> (xs : List A) -> 
               tail (list-fmap f xs) ≡ list-fmap f (tail xs)
tail-commute f nil = refl
tail-commute f (cons x xs) = refl 


tail-is-natural-transformation : {l : Level} -> NaturalTransformation List List {list-fmap} {list-fmap {l}} tail
tail-is-natural-transformation = record { commute                = tail-commute} 


append : {l : Level} {A : Set l} -> List A -> List A -> List A
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

append-with-fmap : {l : Level} {A B : Set l} -> (f : A -> B) -> (xs : List A) -> (ys : List A) ->
  append (list-fmap f xs) (list-fmap f ys) ≡  list-fmap f (append xs ys)
append-with-fmap f nil ys         = refl
append-with-fmap f (cons x xs) ys = begin 
  append (list-fmap f (cons x xs)) (list-fmap f ys)     ≡⟨ refl ⟩
  append (cons (f x) (list-fmap f xs)) (list-fmap f ys) ≡⟨ refl ⟩
  cons (f x) (append (list-fmap f xs) (list-fmap f ys)) ≡⟨ cong (\li -> cons (f x) li) (append-with-fmap f xs ys) ⟩
  list-fmap f (append (cons x xs) ys)                   ∎
                   


concat : {l : Level} {A : Set l} -> List (List A) -> List A
concat nil         = nil
concat (cons x xs) = append x (concat xs)

concat-commute :  {l : Level} {A B : Set l} -> (f : A -> B) -> (xs : List (List A)) ->
               concat ((list-fmap ∙ list-fmap) f xs) ≡ list-fmap  f (concat xs)
concat-commute f nil         = refl
concat-commute f (cons x xs) = begin
  concat ((list-fmap ∙ list-fmap) f (cons x xs))                 ≡⟨ refl ⟩
  concat (cons (list-fmap f x) ((list-fmap ∙ list-fmap) f xs))   ≡⟨ refl ⟩
  append (list-fmap f x) (concat ((list-fmap ∙ list-fmap) f xs)) ≡⟨ cong (\li -> append (list-fmap f x) li) (concat-commute f xs) ⟩
  append (list-fmap f x) (list-fmap f (concat xs))               ≡⟨ append-with-fmap f x (concat xs) ⟩
  list-fmap f (append x (concat xs)) ≡⟨ refl ⟩
  list-fmap f (concat (cons x xs))
  ∎

concat-is-natural-transformation : {l : Level} -> NaturalTransformation (\A -> List (List A)) List
                                   {list-fmap ∙ list-fmap} {list-fmap {l}} concat
concat-is-natural-transformation = record {commute = concat-commute}