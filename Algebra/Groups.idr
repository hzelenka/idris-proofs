module Groups

import Foundations.Functions

%default total
%access public export
%hide Prelude.Algebra.(<+>)

infixl 6 <+>
||| Set coupled with an associative binary option with an identity and inverses
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

||| Group with added requirement of commutativity
interface Group a => AbelianGroup a where
  commutativity : (x : a) ->
                  (y : a) ->
                  x <+> y = y <+> x

||| Synonym for fst . identity
leftId : Group a => (x : a) -> x <+> Groups.zero = x
leftId x = fst $ identity x

||| Synonym for snd . identity
rightId : Group a => (x : a) -> Groups.zero <+> x = x
rightId x = snd $ identity x

||| Synonym for fst . inverse
leftInv : Group a => (x : a) -> x <+> neg x = Groups.zero
leftInv x = fst $ inverse x

||| Synonym for snd . inverse
rightInv : Group a => (x : a) -> neg x <+> x = Groups.zero
rightInv x = snd $ inverse x

infixr 8 <^>
||| Apply the group operation an arbitrary number of times
(<^>) : Group a => a -> Nat -> a
_ <^> Z = zero
x <^> (S k) = x <+> (x <^> k)

||| Powers of the identity are always equal to the identity
powerOfZero : Group a =>
              (n : Nat) ->
              (zero {a}) <^> n = zero {a}
powerOfZero Z = Refl
powerOfZero {a} (S k) = rewrite powerOfZero {a} k in leftId zero

||| The identity element in a group is unique
idUniq : Group a =>
         (z' : a) ->
         ((x : a) ->
          (x <+> z' = x,
           z' <+> x = x)) ->
         Groups.zero = z'
idUniq z' prf = trans (sym (fst (prf zero))) $ rightId z'

||| Rewrite left associativity to right associativity
lassoc : Group a =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         (x <+> y) <+> z = x <+> (y <+> z)
lassoc x y z = associativity x y z

||| Rewrite right associativity to left associativity
rassoc : Group a =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         x <+> (y <+> z) = (x <+> y) <+> z
rassoc x y z = sym $ associativity x y z

||| Eliminate an element left-operated on both sides of an equality
cancelLeft : Group a =>
             (x : a) ->
             (y : a) ->
             (z : a) ->
             x <+> y = x <+> z ->
             y = z
cancelLeft x y z xy_eq_xz =
  let left     = lassoc (neg x) x y
      right    = lassoc (neg x) x z
      elim_inv = sym $ rightInv x
      elim_e_l = sym $ rightId y
      elim_e_r = sym $ rightId z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      cong xy_eq_xz

||| Eliminate an element right-operated on both sides of an equality
cancelRight : Group a =>
              (x : a) ->
              (y : a) ->
              (z : a) ->
              y <+> x = z <+> x ->
              y = z
cancelRight x y z yx_eq_zx =
  let left     = rassoc y x (neg x)
      right    = rassoc z x (neg x)
      elim_inv = sym $ leftInv x
      elim_e_l = sym $ leftId y
      elim_e_r = sym $ leftId z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      apply_cong where
  apply_cong = (cong {f=(\val => val <+> (neg x))} yx_eq_zx)

||| Operate two equalities together
operateEq : Group a =>
             (w : a) ->
             (x : a) ->
             (y : a) ->
             (z : a) ->
             w = x ->
             y = z ->
             w <+> y = x <+> z
operateEq w x y z w_eq_x y_eq_z =
  let wy_eq_xy = cong {f=(<+> y)} w_eq_x
      xy_eq_xz = cong {f=(x <+>)} y_eq_z
  in trans wy_eq_xy xy_eq_xz

||| Inverse of some given element in a group is unique
negUniq : Group a =>
          (x : a) ->
          (x' : a) ->
          (x <+> x' = Groups.zero,
           x' <+> x = Groups.zero) ->
          x' = neg x
negUniq x x' neg_prf = 
  cancelLeft x x' (neg x) $ trans (fst neg_prf) $ sym $ leftInv x

||| Negating an element is involutive
doubleNeg : Group a =>
            (x : a) ->
            x = neg (neg x)
doubleNeg x = negUniq (neg x) x $ swap $ inverse x

||| Negating an element is injective
negInjective : Group a =>
               (x : a) ->
               (y : a) ->
               neg x = neg y ->
               x = y
negInjective x y eq = trans (trans (doubleNeg x) (cong eq)) $ sym $ doubleNeg y

||| If x is the inverse of y, then y is the inverse of x
negSym : Group a =>
         (x : a) ->
         (x' : a) ->
         neg x = x' ->
         x = neg x'
negSym x x' prf = rewrite doubleNeg x in cong prf

||| If an element and the inverse of another element sum to the identity, they
||| are in fact the same element
opZeroEq : Group a =>
           (x : a) ->
           (y : a) ->
           x <+> (neg y) = Groups.zero ->
           (neg y) <+> x = Groups.zero ->
           x = y
opZeroEq x y left_eq right_eq =
  negInjective x y $ sym $ negUniq x (neg y) (left_eq, right_eq)

||| Like opZeroEq, but assumes Abelian and demands only one equality
opZeroEqAb : AbelianGroup a =>
             (x : a) ->
             (y : a) ->
             Either (x <+> (neg y) = Groups.zero)
                    ((neg y) <+> x = Groups.zero)  ->
             x = y
opZeroEqAb x y (Left eq) = let eq' = trans (commutativity (neg y) x) eq
                           in opZeroEq x y eq eq'
opZeroEqAb x y (Right eq) = let eq' = trans (commutativity x (neg y)) eq
                            in opZeroEq x y eq' eq
