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

||| Maybe applied to a finite set has cardinality one greater
s_fin_maybe_fin : (n : Nat) ->
                  Maybe (Fin n) ~= S n
s_fin_maybe_fin Z = Finite _ _ (f ** Bij _ f_inj f_srj) where
  f : Maybe (Fin 0) -> Fin 1
  f Nothing = FZ
  f_inj Nothing Nothing _ = Refl
  f_srj FZ = (Nothing ** Refl)
s_fin_maybe_fin (S k) = Finite _ _ (f ** Bij _ f_inj f_srj) where
  f : Maybe (Fin n) -> Fin (S n)
  f Nothing = FZ
  f (Just n) = FS n
  f_inj Nothing Nothing eq = Refl
  f_inj Nothing (Just x) eq = absurd $ FZNotFS eq
  f_inj (Just x) Nothing eq = absurd $ FZNotFS $ sym eq
  f_inj (Just x) (Just y) eq = cong $ FSInjective _ _ eq
  f_srj FZ = (Nothing ** Refl)
  f_srj (FS x) = (Just x ** Refl)

-- Very much a work in progress from here on out
-- Many functions are mostly holes!

data IsLast : Fin (S n) ->
              Type where
  ItIsLast : (x : Fin (S n)) ->
             x = last {n} ->
             IsLast x

both_last : (x : Fin (S n)) ->
            (y : Fin (S n)) ->
            IsLast x ->
            IsLast y ->
            x = y
both_last x y (ItIsLast x x_prf) (ItIsLast y y_prf) = trans x_prf $ sym y_prf

is_it_last : (x : Fin (S n)) ->
             Dec (IsLast x)
is_it_last x with (decEq x last)
  | Yes prf = Yes $ ItIsLast x prf
  | No contra = No (\(ItIsLast _ eq) => contra eq)

cant_strengthen_last : (n : Nat) ->
                       (x : Fin (S n)) ->
                       IsLast x ->
                       strengthen x = Left x
cant_strengthen_last Z FZ (ItIsLast FZ prf) = Refl
cant_strengthen_last (S k) FZ (ItIsLast FZ prf) = absurd $ FZNotFS prf
cant_strengthen_last (S k) (FS x) (ItIsLast (FS x) prf) =
  trans exact $ sym $ cong {f=Left} prf where
    exact : strengthen (FS x) = Left (FS last)
    exact = let rec = cant_strengthen_last k x $ ItIsLast x $ FSinjective prf
            in ?exact_hole

weaken_inj : (x : Fin n) ->
             (y : Fin n) ->
             weaken x = weaken y ->
             x = y
weaken_inj FZ FZ _ = Refl
weaken_inj (FS x) FZ eq = absurd $ FZNotFS $ sym eq
weaken_inj FZ (FS y) eq = absurd $ FZNotFS eq
weaken_inj (FS x) (FS y) eq = cong $ weaken_inj x y $ FSInjective _ _ eq

strengthen_fz_left : Left (FZ {k=Z}) = strengthen (FZ {k=Z})
strengthen_fz_left = Refl

strengthen_fz_right : (j : Nat) ->
                      Right (FZ {k=j}) = strengthen (FZ {k=S j})
strengthen_fz_right j = Refl

strengthen_fs_left : (n : Nat) ->
                     (x : Fin (S n)) ->
                     IsLast (FS x) ->
                     Left (FS x) = strengthen (FS x)
strengthen_fs_left n x (ItIsLast (FS x) prf) = ?strengthen_fs_left_hole

strengthen_fz_not_fs : (n : Nat) ->
                       strengthen (FZ {k=n}) = strengthen (FS x) ->
                       Void
strengthen_fz_not_fs Z eq = absurd $ FZNotFS $ leftInjective eq
strengthen_fz_not_fs {x=FZ} (S k) eq = ?str_hole
strengthen_fz_not_fs {x=FS k} (S j) eq = ?str_hole_2
{-strengthen_fz_not_fs {x} (S k) eq with (strengthen (FS x))
  | (Left l) = absurd $ leftNotRight $ sym eq
  | (Right FZ) = ?absurd_hole
  | (Right (FS y)) = absurd $ FZNotFS $ rightInjective eq -}

remove_fs_strengthen : (x : Fin (S n)) ->
                       (y : Fin (S n)) ->
                       strengthen (FS x) = strengthen (FS y) ->
                       strengthen x = strengthen y
remove_fs_strengthen FZ FZ _ = Refl
remove_fs_strengthen {n} FZ (FS x) eq = ?rem_hole_2
remove_fs_strengthen (FS x) FZ eq = ?rem_hole_1
remove_fs_strengthen (FS x) (FS y) eq = ?rem_hole_3

strengthen_inj : (x : Fin (S n)) ->
                 (y : Fin (S n)) ->
                 strengthen x = strengthen y ->
                 x = y
strengthen_inj FZ FZ _ = Refl
strengthen_inj {n} FZ (FS x) eq = ?str_inj_hole--absurd $ strengthen_fz_not_fs n eq
strengthen_inj {n} (FS x) FZ eq = absurd $ strengthen_fz_not_fs n $ sym eq
strengthen_inj {n=S k} (FS x) (FS y) eq =
  cong $ strengthen_inj x y $ remove_fs_strengthen _ _ eq

||| Restrict a bijection from Fin (S n) to Fin (S m)
rec_bij : (f : (Fin (S n) -> Fin (S m))) ->
          Bijective f ->
          (g : (Fin n -> Fin m) ** Bijective g)
{-rec_bij {n} {m} f (Bij _ f_inj f_srj) with (is_it_last (f last))
  | Yes (ItIsLast _ eq) = (g ** Bij g g_inj g_srj) where
    g : Fin n -> Fin m
    g x with (strengthen (f (weaken x)))
      | Left y = ?left_hole
      | Right y = y
    g_inj : (x : Fin n) -> (y : Fin n) -> g x = g y -> x = y
    g_inj x y eq' = weaken_inj _ _ $ f_inj (weaken x) (weaken y) ?g_inj_hole-- $ strengthen_inj _ _ eq'
    g_srj z = ?gsrj_hole_2
  | No contra = (g ** Bij g g_inj g_srj) where
    g : Fin n -> Fin m
    g_inj = ?ginj_hole_1
    g_srj = ?gsrj_hole_2 -}

||| If there is a bijectiom between two Fin data types, they are the same Fin
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
  let (g ** g_prf) = rec_bij f bij in cong $ bij_fins _ _ g g_prf

||| Between two equipotent sets, injection and surjection correspond
finite_sets_inj_srj : (a : Type) ->
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

||| Cardinality of (a, b) is that of a times that of b
product_card : (a : Type) ->
               (b : Type) ->
               (m : Nat) ->
               (n : Nat) ->
               a ~= m ->
               b ~= n ->
               (a, b) ~= m * n

||| Cardinality of Either a b is that of a plus that of b
coproduct_card : (a : Type) ->
                 (b : Type) ->
                 (m : Nat) ->
                 (n : Nat) ->
                 a ~= m ->
                 b ~= n ->
                 Either a b ~= m + n

||| Factorial function
fac : Nat -> Nat
fac Z = S Z
fac (S n) = (S n) * fac n

mutual
  data Permute : Type ->
                 Nat ->
                 Type where
    Nil  : Permute a 0
    Cons : (x : a) ->
           (p : Permute a n) ->
           NotElem x p ->
           Permute a (S n)

  head : Permute a (S n) -> a
  head (Cons x _ _) = x

  tail : Permute a (S n) -> Permute a n
  tail (Cons _ p _) = p

  data NotElem : a ->
                 Permute a n ->
                 Type where
    NotHere : (x : a) ->
              NotElem x Nil
    NotThere : (x : a) ->
               (ys : Permute a (S n)) ->
               Not (x = head ys) ->
               NotElem x (tail ys) ->
               NotElem x ys

permutation_fac : (a : Type) ->
                  (n : Nat) ->
                  a ~= n ->
                  Permute a n ~= fac n
