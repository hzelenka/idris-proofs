module Nats

import Algebra.Groups
import Algebra.Cyclics
import Data.Fin

%default total
%access public export

data FinLTE : (x : Fin n) ->
              (y : Fin n) ->
              Type where
  FinLTEZero : FinLTE FZ right
  FinLTESucc : FinLTE left right -> FinLTE (FS left) (FS right)

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

division_algorithm : (a : Nat) -> -- S a will be used to avoid division by zero
                     (b : Nat) ->
                     (q : Nat ** r : Nat ** (b = q * (S a) + r, LTE r a))
-- Case 1: The dividend is equal to zero. Let the quotient and remainder both
-- be zero. Zero times the divisor plus zero is equal to zero, so the first
-- condition holds. Also, zero is less than or equal to zero, so the second
-- condition holds.
division_algorithm a Z = (0 ** 0 ** (Refl, LTEZero))
-- Case 2: The divisor is equal to one. Let the quotient equal the dividend
-- and the remainder equal zero. One times the dividend plus zero is equal to
-- the dividend by additive and multiplicative identity, so the first condition
-- holds. Also, zero is less than or equal to zero, so the second condition
-- also holds.
division_algorithm Z b = (b ** Z ** (b_eq, LTEZero)) where
  b_eq = rewrite (multOneRightNeutral b) in
         rewrite (plusZeroRightNeutral b) in Refl
-- Case 3: Neither the dividend nor the divisor equals zero. Then both are the
-- successor of another natural number, say k and j. Apply induction on the
-- divisor with Case 1 as the base case. For the inductive case, assume the
-- division algorithm holds for the divisor and the pred of the dividend.
division_algorithm (S k) (S j) with (division_algorithm (S k) j)
  | (q ** r ** (eq_prf, lte_prf)) with (isLTE r k)
    -- Subcase 1: The remainder in the preceding case was less than or equal to
    -- the predecessor of the divisor. Let the quotient equal the previous
    -- quotient and the remainder equal the succ of the previous remainder. The
    -- quotient times the divisor plus the new remainder may be algebraically
    -- shown to equal the new dividend, so the first condition holds. Also, the
    -- second condition holds bc succ preserves LTE.
    | Yes prf = (q ** S r ** (j_eq, (LTESucc prf))) where
      j_eq = rewrite (sym (plusSuccRightSucc (mult q (S (S k))) r)) in
             rewrite eq_prf in Refl
    -- Subcase 2: The previous remainder was not less than or equal to the pred
    -- of the divisor. Then it must equal the divisor, because otherwise we
    -- would have that the remainder exceeded the divisor, violating that the
    -- division algorithm held. Let the quotient equal the successor of the
    -- previous quotient and the remainder equal zero. We have:
    --                  j = q * (S k) + r
    -- and we need to show that
    --                  S j = (S q) * (S k)
    -- But we know that r = S k, so we can simplify the former to
    --                  S j = q * (S k) + (S k)
    -- which clearly reduces to what we were trying to prove. As for the latter
    -- condition, it is clearly satisfied because our remainder of zero is LTE
    -- to everything.
    | No contra = (S q ** Z ** (s_j_eq, LTEZero)) where
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

sum_zero : (x : Nat) ->
           (y : Nat) ->
           (x + y = Z) ->
           (x = 0, y = 0)
sum_zero Z Z eq_prf = (Refl, Refl)
sum_zero Z (S k) eq_prf = absurd $ SIsNotZ eq_prf
sum_zero (S k) y eq_prf = absurd $ SIsNotZ eq_prf

product_zero : (x : Nat) ->
               (y : Nat) ->
               (x * y = 0) ->
               Either (x = 0) (y = 0)
product_zero Z y eq_prf = Left Refl
product_zero (S k) Z eq_prf = Right Refl
product_zero (S k) (S j) eq_prf = absurd $ SIsNotZ eq_prf

lte_z_z : (x : Nat) ->
          LTE x Z ->
          x = 0
lte_z_z Z lte_prf = Refl
lte_z_z (S k) lte_prf = absurd lte_prf

-- Below two may be needed later
apply_f_eq : f = g ->
             x = y ->
             f x = f y
apply_f_eq eq_1 eq_2 = rewrite eq_1 in rewrite eq_2 in Refl

tuple_eq : w = x ->
           y = z ->
           (w, y) = (x, z)
tuple_eq eq_1 eq_2 = rewrite eq_1 in rewrite eq_2 in Refl

-- Very much a work in progress. I got most of the cases to work w/ quotient,
-- remainder functions in last type of proof, but not the last =/
partial
division_alg_unique : (a : Nat) ->
                      (b : Nat) ->
                      (q : Nat) ->
                      (r : Nat) ->
                      (eq_prf : b = q * (S a) + r) ->
                      (lte_prf : LTE r a) ->
                      (q ** r ** (eq_prf, lte_prf)) = division_algorithm a b
division_alg_unique a Z q r eq_prf lte_prf with (division_algorithm a Z)
  | (q' ** r' ** (eq_prf', lte_prf')) =
    let (mult_q_prf, r_prf) = sum_zero (q * (S a)) r (sym eq_prf)
        (mult_q_prf', r_prf') = sum_zero (q' * (S a)) r' (sym eq_prf') in
    case (product_zero q (S a) mult_q_prf, product_zero q' (S a) mult_q_prf') of
        (Left prf_1, Left prf_2) =>
          ?exact
        (_, Right prf_2) => absurd $ SIsNotZ prf_2
        (Right prf_1, _) => absurd $ SIsNotZ prf_1
division_alg_unique Z b q r eq_prf lte_prf with (division_algorithm Z b)
  | (q' ** r' ** (eq_prf', lte_prf'))
    with (lte_z_z r lte_prf, lte_z_z r' lte_prf')
    | (r_z, r_z') = ?div_hole --(trans left_eq right_eq, trans r_z (sym r_z')) where
      {- s_z : S r = 1
      s_z = cong r_z
      s_z' : S r' = 1
      s_z' = cong r_z'
      left_eq : q = b
      left_eq = rewrite sym (multOneRightNeutral q) in
                rewrite sym (plusZeroRightNeutral (mult q 1)) in
                rewrite sym r_z in
                rewrite s_z in
                sym eq_prf
      right_eq : b = q'
      right_eq = rewrite sym (multOneRightNeutral q') in
                 rewrite sym (plusZeroRightNeutral (mult q' 1)) in
                 rewrite sym r_z' in
                 rewrite s_z' in
                 eq_prf'
                 division_algorithm_unique (S j) (S k) q r eq_prf lte_prf = ?unique_hole_3 -}

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

fin_assoc : (x : Fin (S n)) ->
            (y : Fin (S n)) ->
            (z : Fin (S n)) ->
            fin_add (fin_add x y) z = fin_add x (fin_add y z)

fin_id : (x : Fin (S n)) ->
         (fin_add x FZ = x, fin_add FZ x = x)
fin_id x with (fin_add x FZ, fin_add FZ x)
  | (left_prf, right_prf) = (?l_hole, ?r_hole)

using (n : Nat)
  implementation Group (Fin (S n)) where
    (<+>) = fin_add
    zero = FZ
    neg = fin_neg
    associativity x y z = fin_assoc x y z
    identity x = fin_id x
    inverse {n} x with (division_algorithm n (finToNat x + finToNat (fin_neg x)))
      | (q ** r ** (eq_prf, lte_prf)) = ?inv_hole
