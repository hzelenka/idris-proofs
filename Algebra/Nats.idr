module Nats

import Algebra.Groups
import Algebra.Cyclics
import Data.Fin

%default total
%access public export

succ_lte_zero : LTE (S n) Z ->
                Void
succ_lte_zero LTEZero impossible
succ_lte_zero (LTESucc _) impossible

lte_succ_void_eq : (n : Nat) ->
                   (m : Nat) ->
                   (LTE n (S m)) ->
                   (LTE n m -> Void) ->
                   n = S m
lte_succ_void_eq Z m lte lte_void = absurd $ lte_void LTEZero
lte_succ_void_eq (S Z) Z lte lte_void = Refl
lte_succ_void_eq (S (S n)) Z lte lte_void =
  absurd $ succNotLTEzero $ fromLteSucc lte
lte_succ_void_eq (S k) (S j) lte lte_void with (fromLteSucc lte)
  | prf = cong $ lte_succ_void_eq k j prf (lte_void . LTESucc)

-- This proof is admittedly rather unsightly. I may prettify it eventually.
division_algorithm : (a : Nat) ->
                     (b : Nat) ->
                     (q : Nat ** r : Nat ** (b = q * (S a) + r, LTE r a))
division_algorithm a Z = (0 ** 0 ** (Refl, LTEZero))
division_algorithm Z b = (b ** Z ** (b_eq, LTEZero)) where
  b_eq = rewrite (multOneRightNeutral b) in
         rewrite (plusZeroRightNeutral b) in Refl
division_algorithm (S k) (S j) with (division_algorithm (S k) j)
  | (q ** r ** (eq_prf, lte_prf)) with (isLTE r k)
    | Yes prf = (q ** S r ** (j_eq, (LTESucc prf))) where
      j_eq = rewrite (sym (plusSuccRightSucc (mult q (S (S k))) r)) in
             rewrite eq_prf in Refl
    | No contra = (S q ** Z ** (s_j_eq,LTEZero)) where
      s_j_eq = let s_k_eq_r = sym (lte_succ_void_eq r k lte_prf contra)
                   s_s_k_eq_s_r = cong {f=S} s_k_eq_r in
               rewrite (plusZeroRightNeutral (plus k (mult q (S (S k))))) in
               rewrite (plusCommutative k (mult q (S (S k)))) in
               rewrite (plusSuccRightSucc (mult q (S (S k))) k) in
               rewrite s_k_eq_r in
               rewrite (sym s_s_k_eq_s_r) in
               rewrite (sym eq_prf) in Refl
