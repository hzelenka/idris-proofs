module Rings

import Foundations.Functions
import Algebra.Groups

%default total
%access public export
%hide Prelude.Applicative.(<*>)

interface AbelianGroup a => Ring a where
  (<*>) : a -> a -> a
  mult_associativity : (x : a) ->
                       (y : a) ->
                       (z : a) ->
                       (x <*> y) <*> z = x <*> (y <*> z)
  distributivity : (x : a) ->
                   (y : a) ->
                   (z : a) ->
                   (x <*> (y <+> z) = (x <*> y) <+> (x <*> z),
                    (y <+> z) <*> x = (y <*> x) <+> (z <*> x))

||| In every ring, multiplication by zero yields zero with any element
timesZeroZero : Ring a =>
                (x : a) ->
                (Groups.zero <*> x = Groups.zero,
                 x <*> Groups.zero = Groups.zero)
timesZeroZero x = (lmult, rmult) where
  lmult = cancelLeft _ _ _ exact where
    exact : (x <*> x) <+> (Groups.zero <*> x) = (x <*> x) <+> Groups.zero
    exact = trans (sym (snd (distributivity x x zero))) $
            trans (cong {f=(<*> x)} (fst (identity x))) $
            sym $ fst $ identity $ x <*> x
  rmult = cancelRight _ _ _ exact where
    exact : (x <*> Groups.zero) <+> (x <*> x) = Groups.zero <+> (x <*> x)
    exact = trans (sym (fst (distributivity x zero x))) $
            trans (cong {f=(x <*>)} (snd (identity x))) $
            sym $ snd $ identity $ x <*> x

||| Pull an inverse out on the left side
multNegLeft : Ring a =>
              (x : a) ->
              (y : a) ->
              neg x <*> y = neg $ x <*> y
multNegLeft x y = negUniq _ _ (exact, trans (commutativity _ _) exact) where
    exact : (x <*> y) <+> (neg x <*> y) = Groups.zero
    exact = trans (sym (snd (distributivity y x (neg x)))) $
            rewrite fst (inverse x) in fst $ timesZeroZero y

||| Pull an inverse out on the right side
multNegRight : Ring a =>
               (x : a) ->
               (y : a) ->
               x <*> neg y = neg $ x <*> y
multNegRight x y = negUniq _ _ (exact, trans (commutativity _ _) exact) where
  exact : (x <*> y) <+> (x <*> neg y) = Groups.zero
  exact = trans (sym (fst (distributivity x y (neg y)))) $
          rewrite (fst (inverse y)) in snd $ timesZeroZero x

||| Simple predicate that an element in a ring is not the additive identity
Nonzero : Group a => a -> Type
Nonzero x = Not (x = zero)

||| Some nonzero element yields zero when multiplied by another nonzero element
data DivisorOfZero : Ring a =>
                     a ->
                     Type where
  ||| Given x <*> y = zero with x and y nonzero, x is a divisor of zero
  LDiv : Ring a => 
         (x : a) ->
         Nonzero x ->
         (y : a) ->
         Nonzero y ->
         x <*> y = Groups.zero ->
         DivisorOfZero x
  ||| Given x <*> y = zero with x and y nonzero, y is a divisor of zero
  RDiv : Ring a =>
         (x : a) ->
         Nonzero x ->
         (y : a) ->
         Nonzero y ->
         x <*> y = Groups.zero ->
         DivisorOfZero y

||| Get the proof of being nonzero out of a divisor of zero
divZeroNotZero : Ring a => (x : a) -> DivisorOfZero x -> Nonzero x
divZeroNotZero x (LDiv x prf _ _ _) = prf
divZeroNotZero x (RDiv _ _ x prf _) = prf

||| Predicate that a ring has no divisors of zero
NoDivisorsOfZero : Ring a => Type
NoDivisorsOfZero {a} = (x : a) -> DivisorOfZero x -> Void

||| Predicate that a ring allows <*> cancellation of nonzero elements
CancellationProperty : Ring a => Type
CancellationProperty {a} = (x : a) ->
                           Nonzero x ->
                           (y : a) ->
                           (z : a) ->
                           Either (x <*> y = x <*> z) (y <*> x = z <*> x) ->
                           y = z

||| Can cancel multiplication by nonzeros iff there are no divisors of zero
divsZeroCancelMult : Ring a =>
                     NoDivisorsOfZero {a} <-> CancellationProperty {a}
divsZeroCancelMult {a} = (fwd, bwd) where
  fwd : NoDivisorsOfZero {a} -> CancellationProperty {a}
  fwd no_divs x nonzero y z (Left eq) = ?fwdhole_1 where
    step1 : (x <*> y) <+> neg (x <*> z) = Groups.zero
    step1 = trans (cong {f=(<+> neg (x <*> z))} eq) $ fst $ inverse $ x <*> z
    step2 : x <*> (y <+> neg z) = Groups.zero
  fwd no_divs x nonzero y z (Right eq) = ?fwdhole_2
  bwd : CancellationProperty {a} -> NoDivisorsOfZero {a}
  bwd cancel x (LDiv x x_nonzero y y_nonzero eq) =
    absurd $ y_nonzero $
    cancel x x_nonzero y zero $
    Left $ trans eq $ sym $ snd $ timesZeroZero x
  bwd cancel x (RDiv y y_nonzero x x_nonzero eq) =
    absurd $ x_nonzero $
    cancel y y_nonzero x zero $
    Left $ trans eq $ sym $ snd $ timesZeroZero y

interface Ring a => IntegralDomain a where                    
  one : a
  ml_commutativity : (x : a) ->
                     (y : a) ->
                     x <*> y = y <*> x
  ml_identity : (x : a) ->
                (x <*> one = x,
                one <*> x = x)
  no_divs_zero : (x : a) ->
                 (y : a) ->
                 x <*> y = zero ->
                 Either (x = Groups.zero) (y = Groups.zero)
