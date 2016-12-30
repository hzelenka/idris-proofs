module Combinatorics

import Foundations.Functions
import Foundations.Cardinality

||| Cardinality of (a, b) is that of a times that of b
product_card : (a : Type) ->
               (b : Type) ->
               (m : Nat) ->
               (n : Nat) ->
               a ~= m ->
               b ~= n ->
               (a, b) ~= m * n

||| Cardinality of Either a b is that of a plus that of b
coproduct_card : (a : Type) ->
                 (b : Type) ->
                 (m : Nat) ->
                 (n : Nat) ->
                 a ~= m ->
                 b ~= n ->
                 Either a b ~= m + n

||| Factorial function
fac : Nat -> Nat
fac Z = S Z
fac (S n) = (S n) * fac n

mutual
  data Permute : Type ->
                 Nat ->
                 Type where
    Nil  : Permute a 0
    Cons : (x : a) ->
           (p : Permute a n) ->
           NotElem x p ->
           Permute a (S n)

  head : Permute a (S n) -> a
  head (Cons x _ _) = x

  tail : Permute a (S n) -> Permute a n
  tail (Cons _ p _) = p

  data NotElem : a ->
                 Permute a n ->
                 Type where
    NotHere : (x : a) ->
              NotElem x Nil
    NotThere : (x : a) ->
               (ys : Permute a (S n)) ->
               Not (x = head ys) ->
               NotElem x (tail ys) ->
               NotElem x ys

permutation_fac : (a : Type) ->
                  (n : Nat) ->
                  a ~= n ->
                  Permute a n ~= fac n