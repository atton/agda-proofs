module systemT where

data Bool : Set where
  T : Bool
  F : Bool

data Int : Set where
  O : Int
  S : Int -> Int

R : {U : Set} -> U -> (U -> (Int -> U)) -> Int -> U
R u v O = u
R u v (S t) = v (R u v t) t

D : {U : Set} -> U -> U -> Bool -> U
D u v F = v
D u v T = u