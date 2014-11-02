open import Level
open import Relation.Binary.PropositionalEquality

module systemF where

-- Bool

Bool = \{l : Level} -> {X : Set l} -> X -> X -> X

T : Bool
T = \{X : Set} -> \(x : X) -> \y -> x

F : Bool
F = \{X : Set} -> \x -> \(y : X) -> y

not : Bool -> Bool
not b =  \{X : Set} -> \(x : X) -> \(y : X) -> b y x

D : {X : Set} -> (U V : X) -> Bool -> X
D {X} u v bool = bool {X} u v

lemma-bool-t : {X : Set} -> {u v : X} -> D {X} u v T ≡ u
lemma-bool-t = refl

lemma-bool-f : {X : Set} -> {u v : X} -> D {X} u v F ≡ v
lemma-bool-f = refl

lemma-bool-not-D : {X : Set} {u v : X} {b : Bool} -> D u v b ≡ D v u (not b)
lemma-bool-not-D = refl

-- Product

_×_ : ∀ {l ll} -> Set l -> Set ll -> {lll : Level} -> Set (suc lll ⊔ (ll ⊔ l))
_×_ {l} {ll} U V {lll} = {X : Set lll} -> (U -> V -> X) -> X

<_,_> : ∀{l ll lll} -> {U : Set l} -> {V : Set ll} -> U -> V -> (U × V)
<_,_> {l} {ll} {lll} {U} {V} u v = \{X : Set lll} -> \(x : U -> V -> X) -> x u v

π1 : ∀{l ll} -> {U : Set l} -> {V : Set ll} -> (U × V) -> U
π1  {l} {ll} {U} {V} t = t {U} \(x : U) -> \(y : V) -> x

π2 : ∀{l ll} ->  {U : Set l} -> {V : Set ll} -> (U × V) -> V
π2  {l} {ll} {U} {V} t = t {V} \(x : U) -> \(y : V) -> y

lemma-product : {l ll : Level} {U V : Set l} -> U -> V -> (U × V) {ll}
lemma-product u v = < u , v >

lemma-product-pi1 : {l : Level} {U V : Set l} -> {u : U} -> {v : V} -> π1 (< u , v >) ≡ u
lemma-product-pi1 = refl

lemma-product-pi2 : {l : Level} {U V : Set l} -> {u : U} -> {v : V} -> π2 (< u , v >) ≡ v
lemma-product-pi2 = refl

lemma-product-rebuild : {l : Level} {U V X : Set l} {u : U} {v : V} -> < π1 < u , v > , π2 < u , v > > {X} ≡ < u , v > {X}
lemma-product-rebuild = refl

-- Empty


-- Sum

_+_ : {l : Level} ->  Set l -> Set l -> Set (suc l)
_+_ {l} U V = {X : Set  l} -> (U -> X) -> (V -> X) -> X

ι1 :  {l : Level} {U V : Set l} -> U -> (U + V)
ι1  {l} {U} {V} u =  \{X : Set l} -> \(x : U -> X) -> \(y : V -> X) -> x u

ι2 : {l : Level} {U V : Set l} -> V -> (U + V)
ι2  {l} {U} {V} v =  \{X : Set l} -> \(x : U -> X) -> \(y : V -> X) -> y v

δ : {l : Level} -> {U V : Set l} -> {X : Set l} -> (U -> X) -> (V -> X) -> (U + V) -> X
δ {l} {U} {V} {X} u v t = t {X} u v

lemma-sum-iota1 : {l : Level} {U V X R : Set l} -> {u : U} -> {ux : (U -> X)} -> {vx : (V -> X)} -> δ ux vx (ι1 u) ≡ ux u
lemma-sum-iota1 = refl

lemma-sum-iota2 : {l : Level} {U V X R : Set l} -> {v : V} -> {ux : (U -> X)} -> {vx : (V -> X)} -> δ ux vx (ι2 v) ≡ vx v
lemma-sum-iota2 = refl


-- Existential

data V {l} (X : Set l) : Set l
  where
    v : X -> V X

Σ_,_ : {l : Level} (X : Set l) -> V X -> Set (suc l)
Σ_,_ {l} U u = {Y : Set l} -> ({X : Set l} -> (V X) -> Y) -> Y

⟨_,_⟩ : {l : Level} (U : Set l) -> (u : V U) -> Σ U , u
⟨_,_⟩ {l} U u = \{Y : Set l} -> \(x : {X : Set l} -> (V X) -> Y) -> x {U} u

∇_,_,_ :  {l : Level} {W : Set l} -> (X : Set l) -> { u : V X } -> X -> W -> Σ X , u  -> W
∇_,_,_ {l} {W} X {u} x w t = t {W} (\{X : Set l} -> \(x : V X) -> w)

{-
  lemma-nabla on proofs and types
  (∇ X , x , w ) ⟨ U , u ⟩ ≡ w
  w[U/X][u/x^[U/X]]
-}

lemma-nabla : {l : Level} {X W : Set l} -> {x : X} -> {w : W} -> (∇_,_,_ {l} {W} X {v x} x w) ⟨ X , (v x) ⟩ ≡ w
lemma-nabla = refl


-- Int

Int : ∀{l} -> {X : Set l} -> Set l
Int {l} {X} = X -> (X -> X) -> X

O : {l : Level} -> {X : Set l} -> Int
O {l} {X} =  \(x : X) -> \(y : X -> X) -> x

S : ∀ {l X}  -> Int {l} {X} -> Int
S {l} {X} t = \(x : X) -> \(y : X -> X) -> y (t x y)

It : ∀{l} {U : Set l} -> (u : U) -> (U -> U) -> Int -> U
It {l} {U} u f t = t u f

lemma-it-o : {l : Level} {U : Set l} -> {u : U} -> {f : U -> U} -> It u f O ≡ u
lemma-it-o = refl

lemma-it-s-o : {l : Level} {U : Set l} -> {u : U} -> {f : U -> U} -> {t : Int} -> It u f (S t) ≡ f (It u f t)
lemma-it-s-o = refl

g : ∀{l ll U X} -> {f : U -> Int {l} {X} -> U} -> (U × Int) {l}-> (U × Int) {ll}
g {l} {ll} {U} {X} {f} = \x -> < (f (π1 x) (π2 x)) , S (π2 x) >

lemma-g : ∀{l ll U X Y} {u : U} {n : Int} {f : U -> Int {l} {X} -> U} -> g {l} {ll} {U} {X} {f} < u , n > ≡  < f u n , S n > {Y}
lemma-g = refl

lemma-it-n : ∀{l ll U X Y} {u : U} {n : Int {l} {X}} {f : U -> Int {l} {X} -> U} -> (g {l} {ll} {U} {X} {f} < u , n >) ≡ < f u n , S n > {Y}
lemma-it-n = refl

R : ∀{l U X} -> (u : U) -> (U -> Int {_} {X} -> U) -> Int -> U
R  {l} {U} {X} u f t = π1 {l} (It {_} {U × Int} < u , O > (g {f = f}) t)

lemma-R-O : ∀{l U X} {u : U} {f : (U -> Int {l} {X} -> U)} -> R u f O ≡ u
lemma-R-O = refl


-- lemma-R-n : {l : Level} {U : Set l} {u : U} {f : (U -> Int -> U)} {n : Int} -> R u f (S n) ≡ f (R u f n) (n < u , O > (g {l} {U} {f}) (↑ n ->  π2 < u , n > ))

-- not finished Proof lemma-R-n
-- If applied g for Int. I think Int has type of (Int {?} {U × Int}).
--lemma-R-n : ∀{u f}{n : Int} -> R u f (S n) ≡ f (R u f n) n
--lemma-R-n = refl

-- Proofs And Types Style lemma-R-n
--lemma-R-n : {l : Level} {U : Set l} {u : U} {f : (U -> Int -> U)} {n : Int} -> R u f (S n) ≡ f (R u f n) n
-- n in (S n) and (R u f n) has (U × Int), but last n has Int.
-- regenerate same (n : Int) by used g, <_,_>
-- NOTE : Proofs And Types say "equation for recursion is satisfied by values only"


-- List

List : {l ll : Level} -> (U : Set l) -> Set (l ⊔ (suc ll))
List {l} {ll} U =  {X : Set ll} -> X -> (U -> X -> X) -> X

nil : {l : Level} {U : Set l} {ll : Level} -> List U
nil {l} {U} {ll} = \{X : Set ll} -> \(x : X) -> \(y : U -> X -> X) -> x

cons : {l : Level} {U : Set l} {ll : Level}-> U -> List U -> List U
cons {l} {U} {ll} u t = \{X : Set ll} -> \(x : X) -> \(y : U -> X -> X) -> y u (t {X} x y)

ListIt : {l : Level} {U : Set l} {ll : Level} {W : Set ll} -> W -> (U -> W -> W) -> List U -> W
ListIt {l} {U} {ll} {W} w f t = t {W} w f

-- (u1 u2 nil)
lemma-list : {l : Level} {U X : Set l} {u1 u2 : U} {x : X} {y : U -> X -> X} -> (cons u1 (cons u2 nil)) x y ≡ y u1 (y u2 x)
lemma-list = refl

lemma-list-it-nil : {l : Level} {U W : Set l} {w : W} {f : U -> W -> W} -> ListIt w f nil ≡ w
lemma-list-it-nil = refl

lemma-list-it-cons : {l : Level} {U W : Set l} {u : U} {w : W} {f : U -> W -> W} {t : List U} -> ListIt w f (cons u t) ≡ f u (ListIt w f t)
lemma-list-it-cons = refl

-- cannot proove gerenal list ...?

--lemma-list-nil-cons : {l ll : Level} {U : Set l} {t : List {l} {ll} U} -> (ListIt {l} {U} {(l ⊔ (suc ll))} {List {l} {ll} U} (nil {l} {U} {ll}) (cons {l} {U} {ll}) t) ≡ t
--lemma-list-nil-cons = refl


-- lemma-list-nil-cons for concrete list. has yellow.

--elem2-list : {l ll : Level} {U : Set l} {u1 u2 : U} -> List {l} {ll} U
--elem2-list {l} {ll} {U} {u1} {u2} = cons u1 (cons u2 nil)

--lemma-list-nil-cons-val : {l ll : Level} {U : Set l} -> (ListIt {l} {U} {(l ⊔ (suc ll))} {List {l} {ll} U} (nil {l} {U} {ll}) (cons {l} {U} {ll}) elem2-list) ≡ elem2-list
--lemma-list-nil-cons-val = refl


-- Binary Tree

data BinTree {l : Level} : Set (suc l) where
  leaf   : BinTree
  couple : BinTree -> BinTree -> BinTree

BinTreeIt : {l : Level} -> {W : Set l} -> W -> (W -> W -> W) -> BinTree {l} -> W
BinTreeIt w f (couple left right) = f (BinTreeIt w f left) (BinTreeIt w f right)
BinTreeIt w f leaf = w


lemma-binary-tree-it-leaf : {l : Level} {W : Set l} {w : W} {f : W -> W -> W} -> BinTreeIt w f leaf ≡ w
lemma-binary-tree-it-leaf = refl

lemma-binary-tree-it-tree : {l : Level} {W : Set l} {w : W} {f : W -> W -> W} {u v : BinTree} -> BinTreeIt w f (couple u v)  ≡ f (BinTreeIt w f u) (BinTreeIt w f v)
lemma-binary-tree-it-tree = refl


-- Tree

Tree : {l : Level} -> (U : Set l) -> Set (suc l)
Tree {l} U = {X : Set l} -> X -> ((U -> X) -> X) -> X

Leaf : {l : Level} {U : Set l} -> Tree U
Leaf {l} {U} = \{X : Set l} -> \(x : X) -> \(y : (U -> X) -> X) -> x

collect : {l : Level} {U : Set l} -> (U -> Tree U) -> Tree U
collect {l} {U} f = \{X : Set l} -> \(x : X) -> \(y  : ((U -> X) -> X)) -> y (\(z : U) -> f z {X} x y)

TreeIt : {l : Level} {U W : Set l} -> W -> ((U -> W) -> W) -> Tree U -> W
TreeIt {l} {U} {W} w h t = t {W} w h

lemma-tree-it-nil : {l : Level} {U W : Set l} {w : W} {h : (U -> W) -> W} -> TreeIt {l} {U} {W} w h Leaf ≡ w
lemma-tree-it-nil = refl

lemma-tree-it-collect : {l : Level} {U W : Set l} {w : W} {h : (U -> W) -> W} {f : U -> Tree U} -> (TreeIt w h (collect f)) ≡ (h (\(x : U) -> TreeIt w h (f x)))
lemma-tree-it-collect = refl


