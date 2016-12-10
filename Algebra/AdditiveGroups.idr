module AdditiveGroups

import Algebra.Groups
import Algebra.Cyclics
import Algebra.DivisionAlgorithm
import Data.Fin

nat_to_fin : (n : Nat) ->
             (m : Nat) ->
             LTE n m ->
             Fin (S m)
nat_to_fin _ Z _ = FZ
nat_to_fin Z _ _ = FZ
nat_to_fin (S j) (S k) lte_prf =
  let rec = nat_to_fin j k (fromLteSucc lte_prf)
  in shift (S Z) rec

-- Conversion always sends Z to FZ
nat_to_fin_z_fz : nat_to_fin Z m lte_prf = FZ
nat_to_fin_z_fz {m = Z} {lte_prf = lte_prf} = Refl
nat_to_fin_z_fz {m = (S k)} {lte_prf = lte_prf} = Refl

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
  in nat_to_fin r k lte_prf

-- Will probably need to use a view later to satisfy the totality checker
fin_neg : {n : Nat} ->
          Fin n ->
          Fin n
fin_neg {n=Z} x = FinZElim x
fin_neg {n=S k} FZ = FZ
fin_neg {n=S (S k)} (FS FZ) = last
fin_neg {n=S (S k)} (FS j) = assert_total $ pred $ fin_neg $ weaken j

fin_assoc : (x : Fin n) ->
            (y : Fin n) ->
            (z : Fin n) ->
            fin_add (fin_add x y) z = fin_add x (fin_add y z) 
fin_assoc {n=Z} x _ _ = FinZElim x
fin_assoc {n=S k} x y z = ?assoc_hole

fin_id : (x : Fin (S n)) ->
         (fin_add x FZ = x, fin_add FZ x = x)
fin_id x with (fin_add x FZ, fin_add FZ x)
  | (left_prf, right_prf) = (?l_hole, ?r_hole)

{- using (n : Nat)
  implementation Group (Fin (S n)) where
    (<+>) = ?fin_add
    zero = FZ
    neg = fin_neg
    associativity x y z = fin_assoc x y z
    identity x = fin_id x
    inverse {n} x with (division_algorithm n (finToNat x + finToNat (fin_neg x)))
    | (q ** r ** (eq_prf, lte_prf)) = ?inv_hole -}
