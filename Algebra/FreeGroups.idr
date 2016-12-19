module FreeGroups

import Data.Vect
%hide Data.Vect.take

%default total
%access public export

-- Data.Vect.take forces the vector to be of the form n + m
-- My version instead takes a witness to LTE n m
take : (n : Nat) ->
       (m : Nat) ->
       Vect m a ->
       LTE n m ->
       Vect n a
take Z Z [] lte = []
take (S k) Z [] lte = absurd lte
take Z (S j) (x :: xs) lte = []
take (S k) (S j) (x :: xs) lte = x :: rec where
  rec : Vect k a
  rec = take k j xs $ fromLteSucc lte

-- Take zero is always the empty vector
take_z_nil : (xs : Vect m a) ->
             take Z m xs LTEZero = Nil
take_z_nil {m = Z} [] = Refl
take_z_nil {m = (S k)} (x :: xs) = Refl

-- Predicate that a vector is contained (in order!) in another vector
data Subvect : Vect k a ->
               Vect j a ->
               Type where
  SubvHere : (xs : Vect k a) ->
             (ys : Vect j a) ->
             {auto lte_prf : LTE k j} ->
             xs = take k j ys lte_prf ->
             Subvect xs ys
  SubvThere : (xs : Vect k a) ->
              (ys : Vect j a) ->
              (later : Subvect xs ys) ->
              Subvect xs (y :: ys)

-- The empty vector is always a subvector
trivial_subv : (xs : Vect m a) ->
               Subvect [] xs
trivial_subv xs = SubvHere [] xs $ sym $ take_z_nil xs

-- No nontrivial vector is a subvector of the empty vector
implementation Uninhabited (Subvect (x :: xs) []) where
  uninhabited (SubvHere {lte_prf} {k=S len} {j=Z} _ _ _) = absurd lte_prf

-- If the heads and tails are equal, the resulting vector is equal
parallel_cons : (x, y : a) ->
                (xs, ys : Vect k a) ->
                x = y ->
                xs = ys ->
                x :: xs = y :: ys
parallel_cons x y xs ys eq_1 eq_2 =
  replace {P=(\val => x :: xs = val :: ys)} eq_1 $
  cong {f=(\zs => x :: zs)} eq_2

-- If the vectors are equal, the heads are equal
heads_eq : (xs : Vect k a) ->
           (ys : Vect k a) ->
           x :: xs = y :: ys ->
           x = y
heads_eq xs ys eq = cong {f=head} eq

-- If the vectors are equal, the tails are equal
tails_eq : (xs : Vect k a) ->
           (ys : Vect k a) ->
           x :: xs = y :: ys ->
           xs = ys
tails_eq xs ys eq = cong {f=tail} eq

-- Determine if the first vector is a prefix of the second
check_prefix : DecEq a =>
               (xs : Vect k a) ->
               (ys : Vect j a) ->
               Dec (lte_prf : LTE k j ** xs = take k j ys lte_prf)
check_prefix [] ys = Yes (LTEZero ** sym (take_z_nil ys))
check_prefix (x :: xs) [] = No (\(lte_prf ** _) => absurd lte_prf)
check_prefix (x :: xs) (y :: ys) with (decEq x y)
  | Yes prf with (check_prefix xs ys)
    | Yes (lte_prf ** eq_prf) = Yes (LTESucc lte_prf ** eq_prf') where
      eq_prf' = parallel_cons _ _ _ _ prf eq_prf
    | No contra' = No (\(lte_prf ** eq_prf) =>
                        contra' (fromLteSucc lte_prf ** tails_eq _ _ eq_prf))
  | No contra = No (\(_ ** eq_prf) => contra (heads_eq _ _ eq_prf))

-- Determine if the first vector is anywhere in the second vector
check_subvect : DecEq a =>
                (xs : Vect k a) ->
                (ys : Vect j a) ->
                Dec (Subvect xs ys)
check_subvect {k = Z} {j = j} [] ys = Yes $ trivial_subv ys
check_subvect {k = (S len)} {j = Z} (x :: xs) [] = No (\prf => absurd prf)
check_subvect {k = (S len)} {j = (S k)} (x :: xs) (y :: ys)
  with (check_prefix (x :: xs) (y :: ys))
  | Yes (lte_prf ** eq_prf) = Yes $ SubvHere _ _ eq_prf
  | No contra with (check_subvect (x :: xs) ys)
    | Yes prf = Yes $ SubvThere _ _ prf
    | No contra' = No subv_contra where
      subv_contra (SubvHere _ _ {lte_prf} prf) = contra (lte_prf ** prf)
      subv_contra (SubvThere _ _ later) = contra' later

||| Vector with a guarantee that certain sequences do not appear
data Word : (a : Type) ->
            (axioms : ((n : Nat) ->
                       Vect (S n) a ->
                       Maybe a)) ->
            Type where
  ||| Empty word
  Empty : Word a axioms
  ||| Nonempty word w/o the sequences
  MkWord : (ys : Vect (S m) a) ->
           (axioms : ((n : Nat) ->
                      Vect (S n) a ->
                      Maybe a)) ->
           ((xs : Vect (S k) a) ->
            axioms k xs = Just _ ->
            Subvect xs ys ->
            Void) ->
            Word a axioms
