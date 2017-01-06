module DivisionAlgorithm

%default total
%access public export

lte_successor : (m : Nat) ->
                (n : Nat) ->
                (LTE m n -> Void) ->
                LTE m (S n) ->
                m = S n
lte_successor Z n lte_contra lte_prf = absurd $ lte_contra LTEZero
lte_successor (S Z) Z lte_contra lte_prf = Refl
lte_successor (S k) (S j) lte_contra lte_prf =
  let rec = lte_successor k j (\x => lte_contra (LTESucc x))
                              (fromLteSucc lte_prf)
  in cong rec

division_algorithm : (a : Nat) -> -- S a will be used to avoid division by zero
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
    | No contra = (S q ** Z ** (s_j_eq, LTEZero)) where
      s_j_eq = let s_k_eq_r = sym (lte_successor r k contra lte_prf)
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

not_succ_lte : (m : Nat) ->
               LTE (S m) m ->
               Void
not_succ_lte Z prf = absurd prf
not_succ_lte (S k) prf = not_succ_lte k $ fromLteSucc prf

not_succ_eq : (m : Nat) ->
              m = S m ->
              Void
not_succ_eq Z eq = absurd $ SIsNotZ $ sym eq
not_succ_eq (S k) eq = not_succ_eq k $ succInjective _ _ eq

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
division_alg_unique (S k) (S j) Z Z eq_prf lte_prf = absurd $ SIsNotZ eq_prf
division_alg_unique (S k) (S j) (S q) Z eq_prf lte_prf = exact where
  eq_rec : j = q * (S (S k)) + S k
  eq_rec = rewrite sym (plusSuccRightSucc (q * (S (S k))) k) in
           rewrite plusCommutative (q * (S (S k))) k in
           rewrite sym (plusZeroRightNeutral (k + q * (S (S k)))) in
           succInjective _ _ eq_prf
  exact with (division_alg_unique (S k) j q (S k) eq_rec (lteRefl))
    | (q_eq, r_eq) with (division_algorithm (S k) j)
      | (q' ** r' ** (eq_prf', lte_prf')) with (isLTE r' k)
        | Yes prf = absurd $ not_succ_lte k $ rewrite r_eq in prf
        | No contra = (cong q_eq, Refl)
division_alg_unique (S k) (S j) q (S r) eq_prf lte_prf
  with (division_alg_unique (S k) j q r
          (succInjective _ _ (trans eq_prf (sym (plusSuccRightSucc
            (q*(S (S k))) r))))
          (lteSuccLeft lte_prf))
    | (q_eq, r_eq) with (division_algorithm (S k) j)
      | (q' ** r' ** (eq_prf', lte_prf')) with (isLTE r' k)
        | Yes prf = (q_eq, cong r_eq)
        | No contra = absurd (not_succ_lte (S k) lte_k) where
          r_s_k' : r' = S k
          r_s_k' = lte_successor r' k contra lte_prf'
          r_s_k : r = S k
          r_s_k = trans r_eq r_s_k'
          lte_k : LTE (S (S k)) (S k)
          lte_k = replace {P=\val => LTE (S val) (S k)} r_s_k lte_prf
