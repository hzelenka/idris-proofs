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
            (S m) * k = n ->
            m // n

get_k : m // n -> Nat
get_k (Divides _ _ k _) = k

divides_quo_rem : (m : Nat) ->
                  (n : Nat) ->
                  (prf : m // n) ->
                  (quotient m n = get_k prf, remainder m n = Z)
divides_quo_rem m n (Divides _ _ k div) = exact where 
  eq_prf : n = k * (S m) + 0
  eq_prf = sym $
           rewrite plusZeroRightNeutral (k * (S m)) in
           rewrite multCommutative k (S m) in
           div
  exact = (\(a,b) => (sym a, sym b)) $
          division_alg_unique m n k Z eq_prf LTEZero

quo_rem_divides : (m : Nat) ->
                  (n : Nat) ->
                  remainder m n = Z ->
                  m // n
quo_rem_divides m n rem_prf with (division_algorithm m n)
  | (q ** Z ** (eq_prf, lte_prf)) = Divides m n q exact where
    exact : (S m) * q = n
    exact = rewrite multCommutative (S m) q in
            rewrite sym (plusZeroRightNeutral (q * (S m))) in
            sym eq_prf
  | (q ** S k ** (eq_prf, lte_prf)) = absurd $ SIsNotZ rem_prf

||| Whether m divides n is decidable
dec_divides : (m : Nat) ->
              (n : Nat) ->
              Dec (m // n)
dec_divides m n with (decEq (remainder m n) Z)
  | Yes eq = Yes $ quo_rem_divides m n eq
  | No ineq = No $ (\div_prf => ineq (snd (divides_quo_rem m n div_prf)))

data Prime : Nat ->
             Type where
  IsPrime : (n : Nat) ->
            ((m : Nat) ->
             LT (S m) n ->
             Not (m // n)) ->
            Prime n
