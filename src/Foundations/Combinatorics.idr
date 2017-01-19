module Combinatorics

import Data.Fin
import Foundations.Functions
import Foundations.Cardinality

{-mult_lemma : (n : Nat) ->
             (m : Nat) ->
             (S n * S m = S n + m + n * m)
mult_lemma Z _ = Refl
mult_lemma (S k) Z = rewrite multOneRightNeutral k in
                     rewrite plusZeroRightNeutral k in
                     rewrite multZeroRightZero k in
                     rewrite plusZeroRightNeutral k in
                     Refl
                     mult_lemma (S k) (S j) = ?mult_lemma_hole_5 -}

||| Cardinality of (a, b) is that of a times that of b
product_card : (a : Type) ->
               (b : Type) ->
               (m : Nat) ->
               (n : Nat) ->
               a ~= m ->
               b ~= n ->
               (a, b) ~= m * n
product_card a b Z _ (Absurd a a_absurd) _ = Absurd _ (\t => a_absurd (fst t))
product_card a b m Z _ (Absurd b b_absurd) =
  rewrite multZeroRightZero m in Absurd _ (\t => b_absurd (snd t))
product_card a b (S k) (S j) (Finite a k (f ** Bij f f_inj f_srj))
                             (Finite b j (g ** Bij g g_inj g_srj)) =
  Finite (a, b) _ (h ** Bij h h_inj h_srj) where
    h : (a, b) -> Fin ((S k) * (S j))
    h_inj = ?hinjhole
    h_srj = ?hsrjhole

weakenN_to_weaken : (n : Nat) ->
                    (m : Nat) ->
                    (x : Fin m) ->
                    weakenN (S m) x = weakenN m (weaken x)
weakenN_to_weaken n (S k) FZ = ?weakentoweakenhole_1
weakenN_to_weaken n (S k) (FS x) = ?weakenntoweakenhole_2

||| Cardinality of Either a b is that of a plus that of b
coproduct_card : (a : Type) ->
                 (b : Type) ->
                 (m : Nat) ->
                 (n : Nat) ->
                 a ~= m ->
                 b ~= n ->
                 Either a b ~= m + n
coproduct_card a b Z Z (Absurd a a_contra) (Absurd b b_contra) =
  Absurd (Either a b) (\e => case e of Left l => a_contra l
                                       Right r => b_contra r)
coproduct_card a b Z (S k) (Absurd a a_contra)
                           (Finite b k (g ** Bij g g_inj g_srj)) =
  Finite (Either a b) k (h ** Bij h h_inj h_srj) where
    h : Either a b -> Fin (S k)
    h (Right r) = g r
    h_inj : (x : Either a b) -> (y : Either a b) -> h x = h y -> x = y
    h_inj (Right x) (Right y) h_eq = cong $ g_inj x y h_eq
    h_srj : (z : Fin (S k)) -> (x : Either a b ** h x = z)
    h_srj z = let (g_val ** g_prf) = g_srj z
              in (Right g_val ** g_prf)
coproduct_card a b (S j) Z (Finite a j (f ** Bij f f_inj f_srj))
                           (Absurd b b_contra) =
  rewrite plusZeroRightNeutral j in
  Finite (Either a b) j (h ** Bij h h_inj h_srj) where
    h : Either a b -> Fin (S j)
    h (Left l) = f l
    h_inj : (x : Either a b) -> (y : Either a b) -> h x = h y -> x = y
    h_inj (Left x) (Left y) h_eq = cong $ f_inj x y h_eq
    h_srj : (z : Fin (S j)) -> (x : Either a b ** h x = z)
    h_srj z = let (f_val ** f_prf) = f_srj z
              in (Left f_val ** f_prf)
coproduct_card a b (S j) (S k) (Finite a j (f ** Bij f f_inj f_srj))
                               (Finite b k (g ** Bij g g_inj g_srj)) =
  Finite (Either a b) (j + S k) (h ** Bij h h_inj h_srj) where
    h : Either a b -> Fin (S j + S k)
    h (Left l) = weakenN (S k) $ f l
    h (Right r) = shift (S j) $ g r
    h_left_not_h_right : (x : a) -> (y : b) -> h (Left x) = h (Right y) -> Void
    h_left_not_h_right l r h_eq with (f l)
      | FZ = absurd $ FZNotFS h_eq
      | FS l' = let (rec_val ** rec_prf) = f_srj (weaken l')
                in ?fs_hole
    h_inj : (x : Either a b) -> (y : Either a b) -> h x = h y -> x = y
    h_inj (Left l1) (Left l2) h_eq = cong $ f_inj l1 l2 ?hinjhole_3
    h_inj (Left l) (Right r) h_eq = ?hinjhole_4
    h_inj (Right r) (Left l) h_eq = ?hinjhole_1
    h_inj (Right r1) (Right r2) h_eq = cong $ g_inj r1 r2 ?hinjhole_5
    h_srj : (z : Fin (S j + S k)) -> (x : Either a b ** h x = z)
    h_srj = ?hsrjhole

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
