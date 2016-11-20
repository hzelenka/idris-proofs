module Combinatorics

import Functions

%default total

fac : Nat -> Nat
fac Z = S Z
fac (S n) = (S n) * fac n

data Permutation : Type -> Nat -> Type where
  Nil  : Permutation a 0
  (:-) : Permutation a n -> Permutation a (S n)

--data Combination : Type -> Nat -> Type where
