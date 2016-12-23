module stack-product where

open import product
open import Data.Product
open import Function using (id)
open import Relation.Binary.PropositionalEquality

-- definition based from Gears(209:5708390a9d88) src/parallel_execution
goto = executeCS

data Bool : Set where
  True  : Bool
  False : Bool

data Maybe (a : Set) : Set  where
  Nothing : Maybe a
  Just    : a -> Maybe a


record Stack {a t : Set} (stackImpl : Set) : Set  where
  field
    stack : stackImpl
    push : CodeSegment (stackImpl × a × (CodeSegment stackImpl t)) t
    pop  : CodeSegment (stackImpl × (CodeSegment (stackImpl × Maybe a) t)) t


data Element (a : Set) : Set where
  cons : a -> Maybe (Element a) -> Element a

datum : {a : Set} -> Element a -> a
datum (cons a _) = a

next : {a : Set} -> Element a -> Maybe (Element a)
next (cons _ n) = n

record SingleLinkedStack (a : Set) : Set where
  field
    top : Maybe (Element a)
open SingleLinkedStack

emptySingleLinkedStack : {a : Set} -> SingleLinkedStack a
emptySingleLinkedStack = record {top = Nothing}




pushSingleLinkedStack : {a t : Set} -> CodeSegment ((SingleLinkedStack a) × a × (CodeSegment (SingleLinkedStack a) t)) t
pushSingleLinkedStack = cs push
  where
    push : {a t : Set} -> ((SingleLinkedStack a) × a × (CodeSegment (SingleLinkedStack a) t)) -> t
    push (stack , datum , next) = goto next stack1
      where
        element = cons datum (top stack)
        stack1  = record {top = Just element}

popSingleLinkedStack : {a t : Set} -> CodeSegment (SingleLinkedStack a × (CodeSegment (SingleLinkedStack a × Maybe a) t))  t
popSingleLinkedStack = cs pop
  where
    pop : {a t : Set} -> (SingleLinkedStack a × (CodeSegment (SingleLinkedStack a × Maybe a) t)) -> t
    pop (record { top = Nothing } , nextCS) = goto nextCS (emptySingleLinkedStack , Nothing) 
    pop (record { top = Just x } , nextCS)  = goto nextCS (stack1 , (Just datum1))
      where
        datum1 = datum x
        stack1 = record { top = (next x) }





createSingleLinkedStack : {a b : Set} -> Stack {a} {b} (SingleLinkedStack a)
createSingleLinkedStack = record { stack = emptySingleLinkedStack
                                 ; push = pushSingleLinkedStack
                                 ; pop  = popSingleLinkedStack
                                 }




test01 : {a : Set} -> CodeSegment (SingleLinkedStack a × Maybe a) Bool
test01 = cs test01'
  where
    test01' : {a : Set} -> (SingleLinkedStack a × Maybe a) -> Bool
    test01' (record { top = Nothing } , _) = False
    test01' (record { top = Just x } ,  _)  = True


test02 : {a : Set} -> CodeSegment (SingleLinkedStack a) (SingleLinkedStack a × Maybe a)
test02 = cs test02'
  where
    test02' : {a : Set} -> SingleLinkedStack a -> (SingleLinkedStack a × Maybe a)
    test02' stack = goto popSingleLinkedStack (stack , (cs id))


test03 : {a : Set} -> CodeSegment a (SingleLinkedStack a)
test03  = cs test03'
  where
    test03' : {a : Set} -> a -> SingleLinkedStack a
    test03' a = goto pushSingleLinkedStack (emptySingleLinkedStack , a , (cs id))


lemma : {A : Set} {a : A} -> goto (test03 ◎ test02 ◎ test01) a ≡ False
lemma = refl




{-

n-push : {A : Set} {a : A} -> Nat -> SingleLinkedStack A -> SingleLinkedStack A
n-push zero s            = s
n-push {A} {a} (suc n) s = pushSingleLinkedStack (n-push {A} {a} n s) a (\s -> s)

n-pop : {A : Set} {a : A} -> Nat -> SingleLinkedStack A -> SingleLinkedStack A
n-pop zero    s         = s
n-pop {A} {a} (suc n) s = popSingleLinkedStack (n-pop {A} {a} n s) (\s _ -> s)

open ≡-Reasoning

push-pop-equiv : {A : Set} {a : A} (s : SingleLinkedStack A) -> popSingleLinkedStack (pushSingleLinkedStack s a (\s -> s)) (\s _ -> s) ≡ s
push-pop-equiv s = refl

push-and-n-pop : {A : Set} {a : A} (n : Nat) (s : SingleLinkedStack A) -> n-pop {A} {a} (suc n) (pushSingleLinkedStack s a id) ≡ n-pop {A} {a} n s
push-and-n-pop zero s            = refl
push-and-n-pop {A} {a} (suc n) s = begin
  n-pop (suc (suc n)) (pushSingleLinkedStack s a id)
  ≡⟨ refl ⟩
  popSingleLinkedStack (n-pop (suc n) (pushSingleLinkedStack s a id)) (\s _ -> s)
  ≡⟨ cong (\s -> popSingleLinkedStack s (\s _ -> s)) (push-and-n-pop n s) ⟩
  popSingleLinkedStack (n-pop n s) (\s _ -> s)
  ≡⟨ refl ⟩
  n-pop (suc n) s
  ∎


n-push-pop-equiv : {A : Set} {a : A} (n : Nat) (s : SingleLinkedStack A) -> (n-pop {A} {a} n (n-push {A} {a} n s)) ≡ s
n-push-pop-equiv zero s            = refl
n-push-pop-equiv {A} {a} (suc n) s = begin
  n-pop (suc n) (n-push (suc n) s)
  ≡⟨ refl ⟩
  n-pop (suc n) (pushSingleLinkedStack (n-push n s) a (\s -> s))
  ≡⟨ push-and-n-pop n (n-push n s)  ⟩
  n-pop n (n-push n s)
  ≡⟨ n-push-pop-equiv n s ⟩
  s
  ∎


n-push-pop-equiv-empty : {A : Set} {a : A} -> (n : Nat) -> n-pop {A} {a} n (n-push {A} {a} n emptySingleLinkedStack)  ≡ emptySingleLinkedStack
n-push-pop-equiv-empty n = n-push-pop-equiv n emptySingleLinkedStack
-}

