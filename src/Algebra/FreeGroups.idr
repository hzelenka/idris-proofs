module FreeGroups

import Data.Vect
import Algebra.Groups

%default total
%access public export

infixl 6 <>
interface DecEq a => Invertible a where
  (<>) : a -> a -> a
  inv : a -> a
  inv_inv : (x : a) ->
            x = inv (inv x)

dec_inv : Invertible a =>
          (x : a) ->
          (x' : a) ->
          Dec (x' = inv x)
dec_inv x x' = decEq x' (inv x)

mutual
  data Word : (a : Type) ->
              Type where
    WNil : Invertible a =>
          Word a
    WCons : Invertible a =>
           (w : a) ->
           (ws : Word a) ->
           (prf : Either (head ws = Nothing) (Not (head ws = Just (inv w)))) ->
           Word a

  head : Word a -> Maybe a
  head WNil = Nothing
  head (WCons w _ _) = Just w

implementation Foldable Word where
  foldr f acc WNil = acc
  foldr f acc (WCons w ws _) = f w $ foldr f acc ws
  foldl f acc WNil = acc
  foldl f acc (WCons w ws _) = foldl f (f acc w) ws

tail : Word a -> Word a
tail WNil = WNil
tail (WCons _ ws _) = ws

length : Word a -> Nat
length WNil = Z
length (WCons _ ws _) = S $ length ws

cons_helper : Invertible a =>
              (w : a) ->
              (ws : Word a) ->
              Maybe (Either (head ws = Nothing) (Not (head ws = Just (inv w))))
cons_helper w WNil = Just $ Left Refl
cons_helper {a} w (WCons x ws w_prf) with (dec_inv w x)
  | Yes prf = Nothing
  | No contra = Just $ Right (\eq => contra (justInjective eq))

-- Infix word construction; adjacent inverses are removed
wappend : Invertible a => a -> Word a -> Word a
wappend w WNil = WCons w WNil (Left Refl)
wappend w ws with (cons_helper w ws)
  | Nothing = tail ws
  | Just prf = WCons w ws prf

rewrite_wappend : Invertible a =>
                  (ws : Word a) ->
                  ws = foldr FreeGroups.wappend WNil ws
rewrite_wappend {a} WNil = Refl
rewrite_wappend {a} (WCons w ws prf) = let rec = rewrite_wappend ws in
  trans eq (cong {f=wappend w} rec) where
    eq = case prf of (Left l) => ?eq_hole_1
                     (Right r) => ?eq_hole_2

-- Like wappend, adjacent inverses are removed
wconcat : Invertible a => Word a -> Word a -> Word a
wconcat WNil ms = ms
wconcat ws WNil = ws
wconcat (WCons w WNil prf) ms = w `wappend` ms
wconcat (WCons w ws prf) ms = w `wappend` (ws `wconcat` ms)

wconcat_id : Invertible a =>
             (ws : Word a) ->
             (ws `wconcat` WNil = ws,
              WNil `wconcat` ws = ws)
wconcat_id ws = (left_prf ws, Refl) where
  left_prf WNil = Refl
  left_prf (WCons _ _ _) = Refl

-- Invert a word
winv : Invertible a => Word a -> Word a
winv WNil = WNil
winv (WCons w WNil _) = WCons (inv w) WNil (Left Refl)
winv (WCons w ws prf) = (winv ws) `wconcat` (WCons (inv w) WNil (Left Refl))

winv_wnil_wnil : Invertible a =>
                 winv (WNil {a}) = WNil
winv_wnil_wnil = Refl

winv_is_inv : Invertible a =>
              (ws : Word a) ->
              (ws `wconcat` (winv ws) = WNil,
               (winv ws) `wconcat` ws = WNil)
winv_is_inv {a} WNil = (Refl, Refl)
winv_is_inv {a} (WCons w ws prf) = (left_prf, right_prf) where
  left_prf = let rec = fst (winv_is_inv ws)
             in ?left_hole
  right_prf = ?right_hole
