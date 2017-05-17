module Valleys

%default total

data Decreasing : (Nat -> Nat) -> Type where
  Decr : (f : Nat -> Nat) ->
         ((m, n : Nat) ->
          LTE m n ->
          LTE (f n) (f m)) ->
         Decreasing f

||| Valley m f n means there exists a valley of length m in f ending at n
data Valley : Nat -> (Nat -> Nat) -> Nat -> Type where
  ||| There is trivially a valley of length 1 at any point
  ValZ : (f : Nat -> Nat) ->
         (n : Nat) ->
         Valley (S Z) f n
  ||| If a valley of length m ends at n, and f (S n) = f n, there is also a
  ||| valley of length (S m) ending at (S n)
  ValS : (v : Valley m f n) ->
         f (S n) = f n ->
         Valley (S m) f (S n)

lteZeroIsZero : (m : Nat) ->
                LTE m Z ->
                m = Z
lteZeroIsZero Z prf = Refl

valleyFromZ : (f : Nat -> Nat) ->
              Decreasing f ->
              f Z = Z ->
              (m : Nat) ->
              Valley (S m) f m
valleyFromZ f _ eq Z = ValZ f Z
valleyFromZ f (Decr f decr_prf) eq (S k) = ValS rec f_Sk_eq_f_k where
  rec = valleyFromZ f (Decr f decr_prf) eq k
  f_Sk_eq_f_k : f (S k) = f k
  f_Sk_eq_f_k with (k)
    | Z = trans (lteZeroIsZero (f 1) (rewrite sym eq in ?ltehole)) $ sym eq
    | S k' = trans f_S_S_k_Z (sym f_S_k_Z) where
      f_S_S_k_Z : f (S (S k')) = Z
      f_S_S_k_Z = lteZeroIsZero (f (S (S k'))) $
                  rewrite sym eq in decr_prf 0 (S (S k')) LTEZero
      f_S_k_Z : f (S k') = Z
      f_S_k_Z = lteZeroIsZero (f (S k')) $
                rewrite sym eq in decr_prf 0 (S k') LTEZero

shiftValley : (f : Nat -> Nat) ->
              (m, n, p : Nat) ->
              Valley m ((p+) . f) n ->
              Valley m f (p+n)
shiftValley f m n Z valley = valley
shiftValley f (S Z) n (S k) (ValZ _ _) = ValZ f $ S (k + n)
shiftValley f (S m) (S n) (S k) (ValS valley eq) =
 let rec = shiftValley f m n (S k) valley in
        ?shiftvalley_2 $ ValS rec ?eqhole

alwaysExistsValley' : (f : Nat -> Nat) ->
                      Decreasing f ->
                      (m : Nat) ->
                      (f_Z : Nat ** f Z = f_Z) ->
                      (n : Nat ** Valley (S m) f n)
alwaysExistsValley' f decr m (Z ** z_prf) = (m ** valleyFromZ f decr z_prf m)
alwaysExistsValley' f decr Z (S k ** s_k_prf) = (Z ** ValZ f Z)
alwaysExistsValley' f decr (S j) (S k ** s_k_prf)
  with (alwaysExistsValley' f decr j (S k ** s_k_prf))
    | (n ** valley_n) with (decEq (f (S n)) (f n))
      | Yes prf = (S n ** ValS valley_n prf)
      | No contra = let Decr f decr_prf = decr
                    in ?valleyhole

alwaysExistsValley : (f : Nat -> Nat) ->
                     Decreasing f ->
                     (m : Nat) ->
                     (n : Nat ** Valley (S m) f n)
alwaysExistsValley f decr m = alwaysExistsValley' f decr m $ (f 0 ** Refl)
