module Primes

import NumberTheory.DivisionAlgorithm

%default total
%access public export

infixl 2 //
||| Data type expressing that a number divides another number
data (//) : Nat ->
            Nat ->
            Type where
  Divides : (m, n, k : Nat) ->
            S m * k = n ->
            S m // n

using (m : Nat)
  implementation Uninhabited (Z // m) where
    uninhabited divides_prf impossible

||| Every nonzero Nat divides zero
dividesZero : (m : Nat) ->
              S m // Z
dividesZero m = Divides m Z Z $ multZeroRightZero m

get_k : m // n -> Nat
get_k (Divides _ _ k _) = k

kNotZ : (m, n : Nat) ->
        (prf : S m // S n) ->
        (l : Nat ** get_k prf = S l)
kNotZ m n (Divides m (S n) Z eq) =
  let eq' = trans (sym eq) (multZeroRightZero m)
  in absurd $ SIsNotZ eq'
kNotZ m n (Divides m (S n) (S k) eq) = (k ** Refl)

kDivides : (m, n : Nat) ->
           (prf : S m // n) ->
           get_k prf // n
kDivides m Z (Divides m Z Z eq) = ?kdivhole_3
kDivides m Z (Divides m Z (S k) eq) = absurd $ SIsNotZ eq
kDivides m (S j) (Divides m (S j) k eq) = ?kdivhole_2

||| If m divides n, k is the quotient and zero is the remainder
dividesQuoRem : (m : Nat) ->
                (n : Nat) ->
                (prf : S m // n) ->
                (quotient m n = get_k prf, remainder m n = Z)
dividesQuoRem m n (Divides m n k eq_prf) =
  (\(a,b) => (sym a, sym b)) $
  divAlgUniq m n k Z exact LTEZero where
    exact : n = k * S m + 0
    exact = rewrite plusZeroRightNeutral (k * S m) in
            rewrite multCommutative k (S m) in
            sym eq_prf

||| dividesQuoRem in reverse
quoRemDivides : (m : Nat) ->
                (n : Nat) ->
                remainder m n = Z ->
                S m // n
quoRemDivides m n rem_prf with (divisionAlgorithm m n)
  | (q ** Z ** (eq_prf, lte_prf)) = Divides m n q exact where
    lemma : q + q * m = q * S m + 0
    lemma = rewrite plusZeroRightNeutral (q * S m) in
            sym $ multRightSuccPlus q m
    exact : (S m) * q = n
    exact = rewrite multCommutative m q in
            trans lemma (sym eq_prf)
  | (q ** S k ** (eq_prf, lte_prf)) = absurd $ SIsNotZ rem_prf

||| Whether m divides n is decidable
decDivides : (m : Nat) ->
             (n : Nat) ->
             Dec (m // n)
decDivides Z n = No absurd
decDivides (S m) n with (decEq (remainder m n) Z)
  | Yes eq = Yes $ quoRemDivides m n eq
  | No ineq = No $ (\div_prf => ineq (snd (dividesQuoRem m n div_prf)))

||| Multiplication by a natural number greater than zero preserves reflexivity
lteMult : (m : Nat) ->
          (n : Nat) ->
          LTE m (m * S n)
lteMult m Z = rewrite multOneRightNeutral m in lteRefl
lteMult m (S k) =
  let rec = lteMult m k in
  lteTransitive rec $
  rewrite multRightSuccPlus m (S k) in
  rewrite plusCommutative m (m * (S k)) in
  lteAddRight $ m * S k

||| Can't have two numbers both less than one another
twoLTEsContra : (m : Nat) ->
                (n : Nat) ->
                LTE (S m) n ->
                LTE n m ->
                Void
twoLTEsContra Z (S k) lte_1 lte_2 = absurd lte_2
twoLTEsContra (S k) n lte_1 lte_2 =
  absurd $ notSuccLTE (S k) $ lteTransitive lte_1 lte_2

||| Multiplying by a nonzero Nat and adding another Nat gives a larger number
multAddLTE : (m, n, l, o : Nat) ->
              m + (S n) * l = o ->
              LTE l o
multAddLTE Z n l o eq =
  rewrite sym eq in rewrite multCommutative (S n) l in lteMult l n
multAddLTE (S k) n l Z eq = absurd $ SIsNotZ eq
multAddLTE (S k) n l (S j) eq =
  let rec = multAddLTE k n l j (succInjective _ _ eq) in lteSuccRight rec

||| A divisor of a number must be less than the number it divides
onlyLteDivides : (m : Nat) ->
                 (n : Nat) ->
                 GT m n ->
                 Not (S m // S n)
onlyLteDivides Z _ gt_prf (Divides _ _ _ _) impossible
onlyLteDivides (S j) n gt_prf (Divides _ _ Z k_prf) =
  absurd $ SIsNotZ $ trans (sym k_prf) $ multZeroRightZero j
onlyLteDivides (S j) n gt_prf (Divides _ _ (S k) k_prf) =
  twoLTEsContra j n exact $ fromLteSucc gt_prf where
    exact : LTE (S j) n
    exact = multAddLTE k k (S j) n $
            replace {P=\val => k + val = n} (sym (multRightSuccPlus (S k) j)) $
            replace {P=\val => k + S (k + val) = n} (multCommutative j (S k)) $
            succInjective (k + (S k + j * S k)) n k_prf

data Prime : Nat ->
             Type where
  Prm : (n : Nat) ->
        ((m : Nat) ->
         LT m n ->
         Not (S (S m) // S (S n))) ->
        Prime (S (S n))

zeroNotPrime : Not (Prime Z)
zeroNotPrime prf impossible

oneNotPrime : Not (Prime (S Z))
oneNotPrime prf impossible

decPrime : (m : Nat) ->
           Dec $ Prime m
decPrime Z = No zeroNotPrime
decPrime (S Z) = No oneNotPrime
decPrime (S (S k)) = ?decprimehole_4

data Composite : Nat ->
                 Type where
  Cms : (n : Nat) ->
        (m : Nat ** S (S m) // n) ->
        Composite n
