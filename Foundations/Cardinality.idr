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

-- The proofs up to bij_fin_one probably won't end up being necessary
-- I'm keeping them around just in case

||| Predicate expressing that a Fin is the largest element in its type
data IsLast : Fin (S n) ->
              Type where
  ItIsLast : (x : Fin (S n)) ->
             x = last {n} ->
             IsLast x

||| If IsLast applies to two members of a Fin, they are in fact the same
both_last : (x : Fin (S n)) ->
            (y : Fin (S n)) ->
            IsLast x ->
            IsLast y ->
            x = y
both_last x y (ItIsLast x x_prf) (ItIsLast y y_prf) = trans x_prf $ sym y_prf

||| Covering function to determine if a Fin is the last
is_it_last : (x : Fin (S n)) ->
             Dec (IsLast x)
is_it_last x with (decEq x last)
  | Yes prf = Yes $ ItIsLast x prf
  | No contra = No (\(ItIsLast _ eq) => contra eq)

||| If some x is the last element of a Fin, so is FS applied to x
fs_last_is_last : (x : Fin (S n)) ->
                  IsLast x ->
                  IsLast (FS x)
fs_last_is_last x (ItIsLast x x_eq) = ItIsLast (FS x) $ cong x_eq

||| If FS x is the last element of a fin, so is x
rem_fs_last_is_last : (x : Fin (S n)) ->
                      IsLast (FS x) ->
                      IsLast x
rem_fs_last_is_last x (ItIsLast (FS x) x_eq) = ItIsLast x $ FSinjective x_eq

||| Except for Fin 1, last takes the form of FS x
last_is_fs : (k : Nat) ->
             (x : Fin (S k) ** last {n=S k} = FS x)
last_is_fs Z = (FZ ** Refl)
last_is_fs (S k) = let (rec_val ** rec_prf) = last_is_fs k
                   in (FS rec_val ** cong rec_prf)

||| Weakening a Fin never results in the last element
weaken_not_last : (x : Fin (S n)) ->
                  Not (IsLast (weaken x))
weaken_not_last FZ (ItIsLast FZ last_eq) = absurd $ FZNotFS last_eq
weaken_not_last {n = S k} (FS x) last_prf = weaken_not_last x $
  rem_fs_last_is_last _ last_prf

||| The weaken function is injective
weaken_inj : (x : Fin n) ->
             (y : Fin n) ->
             weaken x = weaken y ->
             x = y
weaken_inj FZ FZ _ = Refl
weaken_inj (FS x) FZ eq = absurd $ FZNotFS $ sym eq
weaken_inj FZ (FS y) eq = absurd $ FZNotFS eq
weaken_inj (FS x) (FS y) eq = cong $ weaken_inj x y $ FSInjective _ _ eq

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

||| Restrict a bijection from Fin (S n) to Fin (S m)
restrict_bij : (n : Nat) ->
               (m : Nat) ->
               (f : (Fin (S n) -> Fin (S m))) ->
               Bijective f ->
               (g : (Fin n -> Fin m) ** Bijective g)
restrict_bij Z Z f f_bij = (g ** Bij g g_inj g_srj) where
  g : Fin Z -> Fin Z
  g x impossible
  g_inj x y impossible
  g_srj z impossible
restrict_bij Z (S j) f f_bij = absurd $ SIsNotZ $ succInjective (S j) Z $
                               bij_fin_one (S (S j)) f f_bij
restrict_bij (S j) Z f f_bij = let (f_inv ** f_prf) = bij_inv f f_bij
                               in absurd $ SIsNotZ $ succInjective (S j) Z $
                                  bij_fin_one (S (S j)) f_inv f_prf
restrict_bij (S j) (S k) f (Bij f f_inj f_srj) with (decEq (f FZ) FZ)
  | Yes eq = (g ** Bij g g_inj g_srj) where
    lemma_f_fs : (x : Fin (S j)) -> (y : Fin (S k) ** f (FS x) = FS y)
    lemma_f_fs x with (f (FS x))
      | FZ with (decEq FZ (FS x))
        | Yes eq' = absurd $ FZNotFS eq'
      | FS x' = (x' ** Refl)
    g : Fin (S j) -> Fin (S k)
    g x = fst $ lemma_f_fs x
    from_lemma : (x : Fin (S j)) -> f (FS x) = FS (g x)
    from_lemma x = snd $ lemma_f_fs x
    g_inj : (x : Fin (S j)) -> (y : Fin (S j)) -> g x = g y -> x = y
    g_inj x y g_eq = FSinjective $ f_inj (FS x) (FS y) $ exact where
      exact = rewrite from_lemma x in rewrite from_lemma y in cong g_eq
    g_srj : (z : Fin (S k)) -> (x : Fin (S j) ** g x = z)
    g_srj z =
      let (f_val ** f_prf) = f_srj (FS z)
      in case decEq f_val FZ of
              Yes eq' => absurd $ FZNotFS $ trans (trans (sym eq)
                         (cong (sym eq'))) f_prf
              No ineq' => let FS x = f_val
                              exact = trans (sym (from_lemma x)) f_prf
                          in (x ** FSinjective exact)
  | No ineq = ?no_hole

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
fin_inj_srj a b n (Finite _ _ (g ** Bij g g_inj g_srj))
                  (Finite _ _ (h ** Bij h h_inj h_srj)) f = (fwd, bwd) where
  fwd (Inj _ f_inj) = (Srj _ f_srj) where
    f_srj z = ?f_srj_hole_fins
  bwd (Srj _ f_srj) = ?bwd_hole

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
