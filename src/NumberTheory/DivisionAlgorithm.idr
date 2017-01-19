module DivisionAlgorithm

%default total
%access public export

lteSuccEq : (m : Nat) ->
            (n : Nat) ->
            (LTE m n -> Void) ->
            LTE m (S n) ->
            m = S n
lteSuccEq Z n lte_contra lte_prf = absurd $ lte_contra LTEZero
lteSuccEq (S Z) Z lte_contra lte_prf = Refl
lteSuccEq (S k) (S j) lte_contra lte_prf =
  let rec = lteSuccEq k j (\x => lte_contra (LTESucc x))
                              (fromLteSucc lte_prf)
  in cong rec

divisionAlgorithm : (a : Nat) -> -- S a will be used to avoid division by zero
                    (b : Nat) ->
                    (q : Nat ** r : Nat ** (b = q * (S a) + r, LTE r a))
divisionAlgorithm a Z = (0 ** 0 ** (Refl, LTEZero))
divisionAlgorithm Z b = (b ** Z ** (b_eq, LTEZero)) where
  b_eq = rewrite (multOneRightNeutral b) in
         rewrite (plusZeroRightNeutral b) in Refl
divisionAlgorithm (S k) (S j) with (divisionAlgorithm (S k) j)
  | (q ** r ** (eq_prf, lte_prf)) with (isLTE r k)
    | Yes prf = (q ** S r ** (j_eq, (LTESucc prf))) where
      j_eq = rewrite (sym (plusSuccRightSucc (mult q (S (S k))) r)) in
             rewrite eq_prf in Refl
    | No contra = (S q ** Z ** (s_j_eq, LTEZero)) where
      s_j_eq = let s_k_eq_r = sym (lteSuccEq r k contra lte_prf)
                   s_s_k_eq_s_r = cong {f=S} s_k_eq_r in
               rewrite (plusZeroRightNeutral (plus k (mult q (S (S k))))) in
               rewrite (plusCommutative k (mult q (S (S k)))) in
               rewrite (plusSuccRightSucc (mult q (S (S k))) k) in
               rewrite s_k_eq_r in
               rewrite (sym s_s_k_eq_s_r) in
               rewrite (sym eq_prf) in
               Refl

quotient : Nat -> Nat -> Nat
quotient a b = fst $ divisionAlgorithm a b

remainder : Nat -> Nat -> Nat
remainder a b = fst $ snd $ divisionAlgorithm a b

sumZ : (x : Nat) ->
       (y : Nat) ->
       (x + y = Z) ->
       (x = 0, y = 0)
sumZ Z Z eq_prf = (Refl, Refl)
sumZ Z (S k) eq_prf = absurd $ SIsNotZ eq_prf
sumZ (S k) y eq_prf = absurd $ SIsNotZ eq_prf

productZ : (x : Nat) ->
           (y : Nat) ->
           (x * y = 0) ->
           Either (x = 0) (y = 0)
productZ Z y eq_prf = Left Refl
productZ (S k) Z eq_prf = Right Refl
productZ (S k) (S j) eq_prf = absurd $ SIsNotZ eq_prf

lteZZ : (x : Nat) ->
        LTE x Z ->
        x = 0
lteZZ Z lte_prf = Refl
lteZZ (S k) lte_prf = absurd lte_prf

notSuccLTE : (m : Nat) ->
             LTE (S m) m ->
             Void
notSuccLTE Z prf = absurd prf
notSuccLTE (S k) prf = notSuccLTE k $ fromLteSucc prf

notSuccEq : (m : Nat) ->
            m = S m ->
            Void
notSuccEq Z eq = absurd $ SIsNotZ $ sym eq
notSuccEq (S k) eq = notSuccEq k $ succInjective _ _ eq

divAlgUniq : (a : Nat) ->
             (b : Nat) ->
             (q : Nat) ->
             (r : Nat) ->
             (eq_prf : b = q * (S a) + r) ->
             (lte_prf : LTE r a) ->
             (q = quotient a b, r = remainder a b)
divAlgUniq a Z q r eq_prf lte_prf with (divisionAlgorithm a Z)
  | (q' ** r' ** (eq_prf', lte_prf')) =
    let (mult_q_prf, r_zero) = sumZ (q * (S a)) r (sym eq_prf) in
    case productZ _ _ mult_q_prf of
         Left q_zero => (q_zero, r_zero)
         Right q_succ => absurd $ SIsNotZ q_succ
divAlgUniq Z b q r eq_prf lte_prf with (divisionAlgorithm Z b)
  | (q' ** r' ** (eq_prf', lte_prf'))
    with (lteZZ r lte_prf, lteZZ r' lte_prf')
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
divAlgUniq (S k) (S j) Z Z eq_prf lte_prf = absurd $ SIsNotZ eq_prf
divAlgUniq (S k) (S j) (S q) Z eq_prf lte_prf = exact where
  eq_rec : j = q * (S (S k)) + S k
  eq_rec = rewrite sym (plusSuccRightSucc (q * (S (S k))) k) in
           rewrite plusCommutative (q * (S (S k))) k in
           rewrite sym (plusZeroRightNeutral (k + q * (S (S k)))) in
           succInjective _ _ eq_prf
  exact with (divAlgUniq (S k) j q (S k) eq_rec (lteRefl))
    | (q_eq, r_eq) with (divisionAlgorithm (S k) j)
      | (q' ** r' ** (eq_prf', lte_prf')) with (isLTE r' k)
        | Yes prf = absurd $ notSuccLTE k $ rewrite r_eq in prf
        | No contra = (cong q_eq, Refl)
divAlgUniq (S k) (S j) q (S r) eq_prf lte_prf
  with (divAlgUniq (S k) j q r
          (succInjective _ _ (trans eq_prf (sym (plusSuccRightSucc
            (q*(S (S k))) r))))
          (lteSuccLeft lte_prf))
    | (q_eq, r_eq) with (divisionAlgorithm (S k) j)
      | (q' ** r' ** (eq_prf', lte_prf')) with (isLTE r' k)
        | Yes prf = (q_eq, cong r_eq)
        | No contra = absurd (notSuccLTE (S k) lte_k) where
          r_s_k' : r' = S k
          r_s_k' = lteSuccEq r' k contra lte_prf'
          r_s_k : r = S k
          r_s_k = trans r_eq r_s_k'
          lte_k : LTE (S (S k)) (S k)
          lte_k = replace {P=\val => LTE (S val) (S k)} r_s_k lte_prf
