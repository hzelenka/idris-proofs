module Groups

import Foundations.Functions

%default total
%access public export
%hide Prelude.Algebra.(<+>)

interface Group a where
  (<+>) : a -> a -> a
  zero : a
  neg : a -> a
  associativity : (x : a) ->
                  (y : a) ->
                  (z : a) ->
                  (x <+> y) <+> z = x <+> (y <+> z)
  identity : (x : a) ->
             (x <+> zero = x,
              zero <+> x = x)
  inverse : (x : a) ->
             (x <+> (neg x) = zero,
              (neg x) <+> x = zero)

-- The identity element in a group is unique
id_unique : Group a =>
            (z' : a) ->
            ((x : a) ->
             (x <+> z' = x,
              z' <+> x = x)) ->
            Groups.zero = z'
id_unique z' prf = trans (sym eq_1) eq_2 where
  eq_1 : Groups.zero <+> z' = Groups.zero
  eq_1 = fst $ prf zero
  eq_2 : Groups.zero <+> z' = z'
  eq_2 = snd $ identity z'

lassoc : Group a =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         (x <+> y) <+> z = x <+> (y <+> z)
lassoc x y z = associativity x y z

rassoc : Group a =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         x <+> (y <+> z) = (x <+> y) <+> z
rassoc x y z = sym $ associativity x y z

-- Possible to eliminate elements on the left
cancel_left : Group a =>
              (x : a) ->
              (y : a) ->
              (z : a) ->
              x <+> y = x <+> z ->
              y = z
cancel_left x y z xy_eq_xz =
  let left     = lassoc (neg x) x y
      right    = lassoc (neg x) x z
      elim_inv = sym $ snd $ inverse x
      elim_e_l = sym $ snd $ identity y
      elim_e_r = sym $ snd $ identity z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      cong xy_eq_xz

-- Also possible to eliminate elements on the right
cancel_right : Group a =>
               (x : a) ->
               (y : a) ->
               (z : a) ->
               y <+> x = z <+> x ->
               y = z
cancel_right x y z yx_eq_zx =
  let left     = rassoc y x (neg x)
      right    = rassoc z x (neg x)
      elim_inv = sym $ fst $ inverse x
      elim_e_l = sym $ fst $ identity y
      elim_e_r = sym $ fst $ identity z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      apply_cong where
  apply_cong = (cong {f=(\val => val <+> (neg x))} yx_eq_zx)

-- Inverse of some given element in a group is unique
neg_unique : Group a =>
             (x : a) ->
             (x' : a) ->
             (x <+> x' = Groups.zero,
              x' <+> x = Groups.zero) ->
             x' = neg x
neg_unique x x' neg_prf =
  cancel_left x x' (neg x) $ trans left_eq right_eq where
    left_eq : x <+> x' = Groups.zero
    left_eq = fst neg_prf
    right_eq : Groups.zero = x <+> (neg x)
    right_eq = sym $ fst $ inverse x

-- The inverse of the inverse of an element is the element
double_neg : Group a =>
             (x : a) ->
             x = neg (neg x)
double_neg x = let elims = inverse x
               in neg_unique (neg x) x (snd elims, fst elims)

-- If x is the inverse of y, then y is the inverse of x
neg_sym : Group a =>
          (x : a) ->
          (x' : a) ->
          neg x = x' ->
          x = neg x'
neg_sym x _ prf = rewrite double_neg x in cong prf

interface Group a => AbelianGroup a where
  commutativity : (x : a) ->
                  (y : a) ->
                  x <+> y = y <+> x
