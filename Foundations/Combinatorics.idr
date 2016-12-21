module Combinatorics

import Data.Fin
import Foundations.Functions

%default total

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
permutation_fac a Z (Equi a Z bij) =
  Equi (Permute a 0) 1 (\x => FZ ** Bij _ inj srj) where
  inj = Inj _ (\x, y, _ => case x of Nil => case y of Nil => Refl)
  srj = Srj _ (\z => case z of FZ => (Nil ** Refl))
permutation_fac a (S k) equi_a =
  let rec = (\b, equi_b => permutation_fac b k equi_b)
  in ?perm_hole_3
