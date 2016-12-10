module Nats

import Algebra.Groups

%default total
%access public export

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

cancel_mult : (x : Nat) ->
              (y : Nat) ->
              (z : Nat) ->
              x * (S z) = y * (S z) ->
              x = y
cancel_mult x y Z eq_prf =
  rewrite sym (multOneRightNeutral y) in
  rewrite sym (multOneRightNeutral x) in
  eq_prf
cancel_mult Z y (S k) eq_prf with (product_zero _ _ (sym eq_prf))
  | Left y_z      = sym y_z
  | Right s_s_k_z = absurd $ SIsNotZ s_s_k_z
cancel_mult (S j) Z (S k) eq_prf = absurd $ SIsNotZ eq_prf
cancel_mult (S j) (S i) (S k) eq_prf =
  cong $
  cancel_mult _ _ _ $
  plusLeftCancel _ _ _ $
  succInjective _ _ $
  succInjective _ _ $
  eq_prf

-- Yo dawg I heard you liked with blocks
division_alg_unique : (a : Nat) ->
                      (b : Nat) ->
                      (q : Nat) ->
                      (r : Nat) ->
                      (eq_prf : b = q * (S a) + r) ->
                      (lte_prf : LTE r a) ->
                      (q = quotient a b, r = remainder a b)
division_alg_unique a Z q r eq_prf lte_prf with (division_algorithm a Z)
  | (q' ** r' ** (eq_prf', lte_prf')) =
    let (mult_q_prf, r_zero) = sum_zero (q * (S a)) r (sym eq_prf) in
    case product_zero _ _ mult_q_prf of
         Left q_zero => (q_zero, r_zero)
         Right q_succ => absurd $ SIsNotZ q_succ
division_alg_unique Z b q r eq_prf lte_prf with (division_algorithm Z b)
  | (q' ** r' ** (eq_prf', lte_prf'))
    with (lte_z_z r lte_prf, lte_z_z r' lte_prf')
    | (r_z, r_z') = (trans left_eq right_eq, trans r_z (sym r_z')) where
      s_z : S r = 1
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
-- These two cases will be merged later
division_alg_unique k (S j) q Z eq_prf lte_prf
  with (division_algorithm k (S j))
  | (q' ** r' ** (eq_prf', lte_prf'))
    with (division_alg_unique k j q k (believe_me k) (believe_me k))
    | (q_unique, r_unique) with (division_algorithm k j)
      | (q'' ** r'' ** (eq_prf'', lte_prf'')) with (decEq q q', decEq 0 r')
        | (Yes q_prf, Yes r_prf)     = (q_prf, r_prf)
        | (Yes q_prf, No r_contra)   =
          absurd $
          r_contra $
          plusLeftCancel (q' * S k) Z r' $
          replace {P=(\val => val * S k + Z = q' * S k + r')} q_prf $
          trans (sym eq_prf) eq_prf'
        | (No q_contra, Yes r_prf)   =
          absurd $
          q_contra $
          cancel_mult q q' k $
          plusRightCancel (q * S k) (q' * S k) Z $
          replace {P=(\val => q * S k + Z = q' * S k + val)} (sym r_prf) $
          trans (sym eq_prf) eq_prf'
        | (No q_contra, No r_contra) = ?r_zero_hole_4
division_alg_unique k (S j) q (S r) eq_prf lte_prf
  with (division_algorithm k (S j))
  | (q' ** r' ** (eq_prf', lte_prf'))
    with (division_alg_unique k j q r (believe_me k) (believe_me k))
    | (q_unique, r_unique) with (division_algorithm k j)
      | (q'' ** r'' ** (eq_prf'', lte_prf'')) with (decEq q q', decEq (S r) r')
        | (Yes q_prf, Yes r_prf)     = (q_prf, r_prf)
        | (Yes q_prf, No r_contra)   =
          absurd $
          r_contra $
          plusLeftCancel (q' * S k) (S r) r' $
          replace {P=(\val => val * S k + S r = q' * S k + r')} q_prf $
          trans (sym eq_prf) eq_prf'
        | (No q_contra, Yes r_prf)   =
          absurd $
          q_contra $
          cancel_mult q q' k $
          plusRightCancel (q * S k) (q' * S k) (S r) $
          replace {P=(\val => q * S k + S r = q' * S k + val)} (sym r_prf) $
          trans (sym eq_prf) eq_prf'
        | (No q_contra, No r_contra) = ?dec_eq_hole_4

