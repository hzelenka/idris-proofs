module Primes

import NumberTheory.DivisionAlgorithm

%default total
%access public export

infixl 2 //
||| Data type expressing that a number divides another number
data (//) : Nat ->
            Nat ->
            Type where
  Divides : (m : Nat) ->
            (n : Nat) ->
            (k : Nat) ->
            S m * k = n ->
            S m // n

using (m : Nat)
  implementation Uninhabited (Z // m) where
    uninhabited divides_prf impossible

get_k : m // n -> Nat
get_k (Divides _ _ k _) = k

||| If m divides n, k is the quotient and zero is the remainder
divides_quo_rem : (m : Nat) ->
                  (n : Nat) ->
                  (prf : S m // n) ->
                  (quotient m n = get_k prf, remainder m n = Z)
divides_quo_rem m n (Divides m n k eq_prf) =
  (\(a,b) => (sym a, sym b)) $
  division_alg_unique m n k Z exact LTEZero where
    exact : n = k * S m + 0
    exact = rewrite plusZeroRightNeutral (k * S m) in
            rewrite multCommutative k (S m) in
            sym eq_prf

||| divides_quo_rem in reverse
quo_rem_divides : (m : Nat) ->
                  (n : Nat) ->
                  remainder m n = Z ->
                  S m // n
quo_rem_divides m n rem_prf with (division_algorithm m n)
  | (q ** Z ** (eq_prf, lte_prf)) = Divides m n q exact where
    lemma : q + q * m = q * S m + 0
    lemma = rewrite plusZeroRightNeutral (q * S m) in
            sym $ multRightSuccPlus q m
    exact : (S m) * q = n
    exact = rewrite multCommutative m q in
            trans lemma (sym eq_prf)
  | (q ** S k ** (eq_prf, lte_prf)) = absurd $ SIsNotZ rem_prf

||| Whether m divides n is decidable
dec_divides : (m : Nat) ->
              (n : Nat) ->
              Dec (m // n)
dec_divides Z n = No absurd
dec_divides (S m) n with (decEq (remainder m n) Z)
  | Yes eq = Yes $ quo_rem_divides m n eq
  | No ineq = No $ (\div_prf => ineq (snd (divides_quo_rem m n div_prf)))

||| Multiplication by a natural number greater than zero preserves reflexivity
lte_mult : (m : Nat) ->
           (n : Nat) ->
           LTE m (m * S n)
lte_mult m Z = rewrite multOneRightNeutral m in lteRefl
lte_mult m (S k) =
  let rec = lte_mult m k in
  lteTransitive rec $
  rewrite multRightSuccPlus m (S k) in
  rewrite plusCommutative m (m * (S k)) in
  lteAddRight $ m * S k

||| Can't have two numbers both less than one another
two_ltes_contra : (m : Nat) ->
                  (n : Nat) ->
                  LTE (S m) n ->
                  LTE n m ->
                  Void
two_ltes_contra Z (S k) lte_1 lte_2 = absurd lte_2
two_ltes_contra (S k) n lte_1 lte_2 =
  absurd $ not_succ_lte (S k) $ lteTransitive lte_1 lte_2

||| A divisor of a number must be less than the number it divides
only_lte_divides : (m : Nat) ->
                   (n : Nat) ->
                   GT m n ->
                   Not (S m // S n)
only_lte_divides Z _ gt_prf (Divides _ _ _ _) impossible
only_lte_divides (S j) n gt_prf (Divides _ _ Z k_prf) =
  absurd $ SIsNotZ $ trans (sym k_prf) $ multZeroRightZero j
only_lte_divides (S j) n gt_prf (Divides _ _ (S k) k_prf) =
  two_ltes_contra j n exact $ fromLteSucc gt_prf where
    exact : LTE (S j) n
    exact = ?exacthole $
            succInjective _ _ k_prf

data Prime : Nat ->
             Type where
  IsPrime : (n : Nat) ->
            ((m : Nat) ->
             LT m n ->
             Not (m // n)) ->
            Prime n
