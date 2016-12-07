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
-- Note that the successor of a ends up being used to avoid zero
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
               rewrite (sym eq_prf) in
               Refl

quotient : Nat -> Nat -> Nat
quotient a b = fst $ division_algorithm a b

remainder : Nat -> Nat -> Nat
remainder a b = fst $ snd $ division_algorithm a b

nat_to_fin : (n : Nat) ->
             (m : Nat) ->
             LT n m ->
             Fin m
nat_to_fin _ Z lt_proof = absurd lt_proof
nat_to_fin Z (S j) lt_proof = FZ
nat_to_fin (S k) (S j) lt_proof = let lt_proof' = fromLteSucc lt_proof
                                   in shift (S Z) $ nat_to_fin k j lt_proof'

-- Use the division algorithm to add two Fin n's
fin_add : {n : Nat} ->
          Fin n ->
          Fin n ->
          Fin n
fin_add {n=Z} x y = FinZElim x
fin_add {n=S k} x y =
  let x' = finToNat x
      y' = finToNat y
      (_ ** r ** (_, lte_prf)) = division_algorithm k (x' + y')
  in nat_to_fin r (S k) (LTESucc lte_prf)

-- Will probably need to use a view later to satisfy the totality checker
fin_neg : {n : Nat} ->
          Fin n ->
          Fin n
fin_neg {n=Z} x = FinZElim x
fin_neg {n=S k} FZ = FZ
fin_neg {n=S (S k)} (FS FZ) = last
fin_neg {n=S (S k)} (FS j) = assert_total $ pred $ fin_neg $ weaken j

using (n : Nat)
  implementation Group (Fin (S n)) where
    (<+>) = fin_add
    zero = FZ
    neg = fin_neg
    associativity x y z = ?assoc_hole
    identity x = ?id_hole
    inverse {n} x with (division_algorithm n (finToNat x + finToNat (fin_neg x)))
      | (q ** r ** (eq_prf, lte_prf)) = ?inv_hole
