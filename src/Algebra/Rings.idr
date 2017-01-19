module Rings

import Foundations.Utilities
import Foundations.Functions
import Algebra.Groups

%default total
%access public export

infixl 8 <#>
||| Abelian group enhanced with a second operation that is associative and
||| distributive over the original
interface AbelianGroup a => Ring a where
  (<#>) : a -> a -> a
  mult_associativity : (x, y, z : a) ->
                       (x <#> y) <#> z = x <#> (y <#> z)
  distributivity : (x, y, z : a) ->
                   (x <#> (y <+> z) = x <#> y <+> x <#> z,
                    (y <+> z) <#> x = y <#> x <+> z <#> x)

||| Added operation is commutative
interface Ring a => CommutativeRing a where
  multComm : (x, y : a) ->
             x <#> y = y <#> x

||| Synonym for fst . distributivity
distrLeft : Ring a => 
            (x, y, z : a) -> 
            x <#> (y <+> z) = x <#> y <+> x <#> z
distrLeft x y z = fst $ distributivity x y z

||| Synonym for snd . distributivity
distrRight : Ring a => 
             (x, y, z : a) -> 
             (y <+> z) <#> x = y <#> x <+> z <#> x
distrRight x y z = snd $ distributivity x y z

||| Multiply two equalities together
multEq : Ring a =>
         (w, x, y, z : a) ->
         w = x ->
         y = z ->
         w <#> y = x <#> z
multEq w x y z w_eq_x y_eq_z =
  let wy_eq_xy = cong {f=(<#> y)} w_eq_x
      xy_eq_xz = cong {f=(x <#>)} y_eq_z
  in trans wy_eq_xy xy_eq_xz

||| Left-multiplication by zero yields zero with any element
timesZeroLeft : Ring a =>
                (x : a) ->
                Groups.zero <#> x = Groups.zero
timesZeroLeft x = cancelLeft _ _ _ $
                  sym (distrRight x x zero) $=
                  cong {f=(<#> x)} (leftId x) $=
                  sym (leftId (x <#> x))

||| Right-multiplication by zero yields zero with any element
timesZeroRight : Ring a =>
                 (x : a) ->
                 x <#> Groups.zero = Groups.zero
timesZeroRight x = cancelRight _ _ _ $
                   sym (distrLeft x zero x) $=
                   cong {f=(x <#>)} (rightId x) $=
                   sym (rightId (x <#> x))

||| Pull an inverse out on the left side
multNegLeft : Ring a =>
              (x, y : a) ->
              neg x <#> y = neg $ x <#> y
multNegLeft x y = negUniq _ _ (exact, trans (commutativity _ _) exact) where
    exact : x <#> y <+> neg x <#> y = Groups.zero
    exact = sym (distrRight y x (neg x)) $=
            rewrite fst (inverse x) in timesZeroLeft y

||| Pull an inverse out on the right side
multNegRight : Ring a =>
               (x, y : a) ->
               x <#> neg y = neg $ x <#> y
multNegRight x y = negUniq _ _ (exact, trans (commutativity _ _) exact) where
  exact : x <#> y <+> x <#> neg y = Groups.zero
  exact = sym (fst (distributivity x y (neg y))) $=
          rewrite leftInv y in timesZeroRight x

||| Cancel the negatives in a product
multNegNeg : Ring a =>
             (x, y : a) ->
             neg x <#> neg y = x <#> y
multNegNeg x y = rewrite multNegLeft x (neg y) in
                 rewrite multNegRight x y in
                 sym $ doubleNeg $ x <#> y

||| Special case of binomial coefficient expansion
multSumSum : Ring a =>
             (w, x, y, z : a) ->
             (w <+> x) <#> (y <+> z) =
             w <#> y <+> w <#> z <+> x <#> y <+> x <#> z
multSumSum w x y z =
  distrLeft (w <+> x) y z $=
  cong {f=(<+> ((w <+> x) <#> z))} (distrRight y w x) $=
  cong {f=((w <#> y <+> x <#> y) <+>)} (distrRight z w x) $=
  ?multsumsumhole

||| Simple predicate that an element in a ring is not the additive identity
Nonzero : Group a => a -> Type
Nonzero x = Not (x = zero)

||| Some nonzero element yields zero when multiplied by another nonzero element
data DivisorOfZero : Ring a =>
                     a ->
                     Type where
  ||| Given x <#> y = zero with x and y nonzero, x is a divisor of zero
  LDiv : Ring a => 
         (x : a) ->
         Nonzero x ->
         (y : a) ->
         Nonzero y ->
         x <#> y = Groups.zero ->
         DivisorOfZero x
  ||| Given x <#> y = zero with x and y nonzero, y is a divisor of zero
  RDiv : Ring a =>
         (x : a) ->
         Nonzero x ->
         (y : a) ->
         Nonzero y ->
         x <#> y = Groups.zero ->
         DivisorOfZero y

||| Get the proof of being nonzero out of a divisor of zero
divZeroNotZero : Ring a => (x : a) -> DivisorOfZero x -> Nonzero x
divZeroNotZero x (LDiv x prf _ _ _) = prf
divZeroNotZero x (RDiv _ _ x prf _) = prf

||| Predicate that a ring has no divisors of zero
NoDivisorsOfZero : Ring a => Type
NoDivisorsOfZero {a} = (x : a) -> DivisorOfZero x -> Void

||| Predicate that a ring allows <#> cancellation of nonzero elements
CancellationProperty : Ring a => Type
CancellationProperty {a} = (x : a) ->
                           Nonzero x ->
                           (y : a) ->
                           (z : a) ->
                           Either (x <#> y = x <#> z) (y <#> x = z <#> x) ->
                           y = z

||| If a product is zero in a ring with no divisors of zero, one of the
||| arguments must be itself zero
noDivsZeroTimesZero : Ring a =>
                      NoDivisorsOfZero {a} ->
                      (x, y : a) ->
                      x <#> y = Groups.zero ->
                      Either (x = Groups.zero) (y = Groups.zero)
noDivsZeroTimesZero no_divs x y eq = ?nodivhole -- I suspect this is unprovable
                                                -- constructively

||| Can cancel multiplication by nonzeros iff there are no divisors of zero
divsZeroCancelMult : Ring a =>
                     NoDivisorsOfZero {a} <-> CancellationProperty {a}
divsZeroCancelMult {a} = (fwd, bwd) where
  fwd : NoDivisorsOfZero {a} -> CancellationProperty {a}
  fwd no_divs x nonzero y z (Left eq) = opZeroEqAb y z (Left step3) where
    step1 : x <#> y <+> neg (x <#> z) = Groups.zero
    step1 = cong {f=(<+> neg (x <#> z))} eq $= leftInv (x <#> z)
    step2 : x <#> (y <+> neg z) = Groups.zero
    step2 = distrLeft x y (neg z) $= rewrite multNegRight x z in step1
    step3 : y <+> neg z = Groups.zero
    step3 with (noDivsZeroTimesZero no_divs x (y <+> neg z) step2)
      | Left x_zero = absurd $ nonzero x_zero
      | Right exact = exact
  fwd no_divs x nonzero y z (Right eq) = ?fwdhole_2 where
    step1 : y <#> x <+> neg (z <#> x) = Groups.zero
    step1 = cong {f=(<+> neg (z <#> x))} eq $= leftInv (z <#> x)
    step2 : (y <+> neg z) <#> x = Groups.zero
    step2 = distrRight x y (neg z) $= rewrite multNegLeft z x in step1
    step3 : y <+> neg z = Groups.zero
    step3 with (noDivsZeroTimesZero no_divs (y <+> neg z) x step2)
      | Left exact   = exact
      | Right x_zero = absurd $ nonzero x_zero
  bwd : CancellationProperty {a} -> NoDivisorsOfZero {a}
  bwd cancel x (LDiv x x_nonzero y y_nonzero eq) =
    absurd $ y_nonzero $
    cancel x x_nonzero y zero $
    Left $ eq $= sym (timesZeroRight x)
  bwd cancel x (RDiv y y_nonzero x x_nonzero eq) =
    absurd $ x_nonzero $
    cancel y y_nonzero x zero $
    Left $ eq $= sym (timesZeroRight y)
