module Cardinality

import Data.Fin
import Foundations.Functions
import Foundations.Composition

%default total
%access public export

infixl 2 ~=
||| Data type for having a particular cardinality
data (~=) : Type -> Nat -> Type where
  ||| Cardinality of the empty set
  Absurd : (a : Type) ->
           Not a ->
           a ~= 0
  ||| Can be put into correspondence with some Fin (S n)
  Finite : (a : Type) ->
           (n : Nat) ->
           (bij : (f : (a -> Fin (S n)) ** Bijective f)) ->
           (~=) a (S n)

||| Has cardinality of the natural numbers
Aleph : Type -> Type
Aleph a = (f : (a -> Nat) ** Bijective f)

||| Convert a Nat to Fin (S m), where m is some greater quantity
nat_to_fin : (n : Nat) ->
             (m : Nat) ->
             LTE n m ->
             Fin (S m)
nat_to_fin _ Z _ = FZ
nat_to_fin Z _ _ = FZ
nat_to_fin (S j) (S k) lte_prf =
  let rec = nat_to_fin j k (fromLteSucc lte_prf)
  in shift (S Z) rec

bij_fin_one : (m : Nat) ->
              (f : Fin (S Z) -> Fin m) ->
              Bijective f ->
              m = S Z
bij_fin_one Z f (Bij f f_inj f_srj) = absurd $ f FZ
bij_fin_one (S Z) f (Bij f f_inj f_srj) = Refl
bij_fin_one (S (S k)) f (Bij f f_inj f_srj) = exact where
  step_1 : f FZ = FZ
  step_1 = let (fz ** fz_eq) = f_srj FZ in case fz of FZ => fz_eq
  step_2 : f FZ = FS FZ
  step_2 = let (fz ** fz_eq) = f_srj (FS FZ) in case fz of FZ => fz_eq
  exact = absurd $ FZNotFS $ trans (sym step_1) step_2

private
restrict_bij_fz_fixed : (m : Nat) ->
                        (n : Nat) ->
                        (f : (Fin (S m) -> Fin (S n))) ->
                        f FZ = FZ ->
                        Bijective f ->
                        (g : (Fin m -> Fin n) ** Bijective g)
restrict_bij_fz_fixed m n f f_of_fz (Bij f f_inj f_srj) =
  (g ** Bij g g_inj g_srj) where
    g_lemma : (x : Fin m) -> (y : Fin n ** f (FS x) = FS y)
    g_lemma x with (f (FS x))
      | FZ = case decEq FZ (FS x) of Yes eq => absurd $ FZNotFS eq
      | FS y = (y ** Refl)
    g : Fin m -> Fin n
    g x = fst $ g_lemma x
    from_lemma : (x : Fin m) -> f (FS x) = FS (g x)
    from_lemma x = snd $ g_lemma x
    g_inj : (x : Fin m) -> (y : Fin m) -> g x = g y -> x = y
    g_inj x y g_eq = FSinjective $ f_inj (FS x) (FS y) exact where
      exact = rewrite from_lemma x in rewrite from_lemma y in cong g_eq
    g_srj : (z : Fin n) -> (x : Fin m ** g x = z)
    g_srj z = let (f_val ** f_prf) = f_srj (FS z)
              in case decEq f_val FZ of 
                      Yes eq => absurd $ FZNotFS $ trans (trans (sym f_of_fz)
                                (cong (sym eq))) f_prf
                      No ineq => let FS x = f_val
                                     exact = trans (sym (from_lemma x)) f_prf
                                 in (x ** FSinjective exact)

private
restrict_bij_fz_not_fixed : (m : Nat) ->
                            (n : Nat) ->
                            (f : (Fin (S m) -> Fin (S n))) ->
                            (w : Fin n) ->
                            f FZ = FS w ->
                            Bijective f ->
                            (g : (Fin m -> Fin n) ** Bijective g)
restrict_bij_fz_not_fixed m n f w f_of_fz (Bij f f_inj f_srj) =
  (g ** Bij g g_inj g_srj) where
    preimage_fz : (preim : Fin m ** f (FS preim) = FZ)
    preimage_fz = case f_srj FZ of (FZ ** im_prf) => absurd $ FZNotFS $ trans
                                                     (sym im_prf) f_of_fz
                                   (FS preim ** im_prf) => (preim ** im_prf)
    preimage_fz_val : Fin m
    preimage_fz_val = fst preimage_fz
    preimage_fz_prf : f (FS preimage_fz_val) = FZ
    preimage_fz_prf = snd preimage_fz
    g : Fin m -> Fin n
    g x with (decEq x preimage_fz_val)
      | Yes eq = w
      | No ineq = case f (FS x) of FS y => y
    g_of_preimage : g preimage_fz_val = w
    g_of_preimage with (decEq preimage_fz_val preimage_fz_val)
      | Yes Refl = Refl
    g_not_preimage : (x : Fin m) ->
                     Not (x = preimage_fz_val) ->
                     FS (g x) = f (FS x)
    g_not_preimage x ineq with (decEq x preimage_fz_val)
      | No ineq' with (f (FS x))
        | FS y = Refl
    g_inj : (xx : Fin m) -> (yy : Fin m) -> g xx = g yy -> xx = yy
    g_inj xx yy g_eq with (decEq xx preimage_fz_val, decEq yy preimage_fz_val)
      | (Yes x_eq, Yes y_eq)  = ?yesyeshole
      | (No x_ineq, No y_ineq) impossible -- = ?nonohole -- Idris does not complain if I mark
                                           -- this case impossible, which must
                                           -- indicate I screwed up somewhere
    g_srj : (z : Fin n) -> (x : Fin m ** g x = z)
    g_srj z with (decEq w z)
      | Yes eq = (preimage_fz_val ** trans g_of_preimage eq)
      | No ineq = let (FS f_val ** f_prf) = f_srj (FS z)
                  in case decEq f_val preimage_fz_val of
                          Yes eq' => absurd $ FZNotFS $
                                     trans (sym preimage_fz_prf) $
                                     rewrite (sym eq') in f_prf
                          No ineq' => (f_val ** FSinjective (trans
                                      (g_not_preimage f_val ineq') f_prf))

||| Restrict a bijection from Fin (S n) to Fin (S m)
restrict_bij : (m : Nat) ->
               (n : Nat) ->
               (f : (Fin (S m) -> Fin (S n))) ->
               Bijective f ->
               (g : (Fin m -> Fin n) ** Bijective g)
restrict_bij m n f f_bij with (decEq (f FZ) FZ)
  | Yes eq = restrict_bij_fz_fixed m n f eq f_bij
  | No ineq with (f FZ)
    | FS x = case decEq (f FZ) (FS x) of Yes f_fs_x =>
                  restrict_bij_fz_not_fixed m n f x f_fs_x f_bij

||| If there is a bijection between two Fin data types, they are the same Fin
bij_fins : (n : Nat) ->
           (m : Nat) ->
           (f : Fin (S n) -> Fin (S m)) ->
           Bijective f ->
           n = m
bij_fins Z Z _ _ = Refl
bij_fins Z (S m) f (Bij _ f_inj f_srj) with (f_srj FZ, f_srj (FS FZ))
  | ((FZ ** prf_1), (FZ ** prf_2)) = absurd $ FZNotFS $ trans (sym prf_1) prf_2
bij_fins (S n) Z f (Bij _ f_inj f_srj) =
  case decEq (f FZ) (f (FS FZ)) of Yes eq => absurd $ FZNotFS $ f_inj _ _ eq
bij_fins (S n) (S m) f bij =
  let (g ** g_prf) = restrict_bij _ _ f bij in cong $ bij_fins _ _ g g_prf

||| Between two equipotent sets, injection and surjection correspond
fin_inj_srj : (a : Type) ->
              (b : Type) ->
              (n : Nat) ->
              a ~= S n ->
              b ~= S n ->
              (f : a -> b) ->
              Injective f <-> Surjective f

||| A data type can only have one cardinality
cardinality_unique : (a : Type) ->
                     (n : Nat) ->
                     (m : Nat) ->
                     a ~= S n ->
                     a ~= S m ->
                     n = m
cardinality_unique a n m (Finite _ _ (f ** f_prf)) (Finite _ _ g_sigma) =
  let (h ** h_prf) = g_sigma ~.~ (bij_inv f f_prf)
  in bij_fins n m h h_prf
