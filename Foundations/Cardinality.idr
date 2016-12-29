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
  | No ineq with (f FZ)
    | FS x = (g ** Bij g g_inj g_srj) where
      preimage_fz : (preim : Fin (S j) ** f (FS preim) = FZ)
      preimage_fz = case f_srj FZ of (FS preim ** im_prf) => (preim ** im_prf)
      preimage_fz_val : Fin (S j)
      preimage_fz_val = fst preimage_fz
      preimage_fz_prf : f (FS preimage_fz_val) = FZ
      preimage_fz_prf = snd preimage_fz
      g : Fin (S j) -> Fin (S k)
      g f1 with (decEq f1 preimage_fz_val)
        | Yes eq' = x
        | No ineq' = case f (FS f1) of FS f2 => f2
      g_of_preimage : g preimage_fz_val = x
      g_of_preimage with (decEq preimage_fz_val preimage_fz_val)
        | Yes eq' = Refl
      g_not_preimage : (y : Fin (S j)) ->
                       Not (y = preimage_fz_val) ->
                       FS (g y) = f (FS y)
      g_not_preimage y ineq with (decEq y preimage_fz_val)
        | No ineq' with (f (FS y))
          | FS f2 = Refl
      not_z_not_preimage : (val : Fin (S j)) ->
                           Not (g val = FZ) ->
                           Not (val = preimage_fz_val)
      g_inj : (xx : Fin (S j)) -> (y : Fin (S j)) -> g xx = g y -> xx = y
      g_inj x' y' g_eq with (decEq x' preimage_fz_val)
        | Yes eq' = ?show_just_preimage_to_x
        | No ineq' = ?no_ineq_hole
      g_srj : (z : Fin (S k)) -> (x : Fin (S j) ** g x = z)
      g_srj z with (decEq x z)
        | Yes eq' = (preimage_fz_val ** trans g_of_preimage eq')
        | No ineq' = let (FS f_val ** f_prf) = f_srj (FS z)
                     in case decEq f_val preimage_fz_val of
                             Yes eq'' => absurd $ FZNotFS $
                                         trans (sym preimage_fz_prf) $
                                         rewrite (sym eq'') in f_prf
                             No ineq'' => (f_val ** FSinjective (trans
                                          (g_not_preimage f_val ineq'') f_prf))

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
