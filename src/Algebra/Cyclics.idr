module Cyclics

import Foundations.Functions
import Foundations.Utilities
import Algebra.Groups
import Algebra.Homomorphisms
import Data.ZZ

%default total
%access public export

implementation Group ZZ where
  (<+>) = (+)
  zero = Pos Z
  neg = negate
  associativity x y z = sym $ plusAssociativeZ x y z
  identity x = (plusZeroRightNeutralZ x, plusZeroLeftNeutralZ x)
  inverse x = (plusNegateInverseLZ x, plusNegateInverseRZ x)

interface Group a => CyclicGroup a where
  imOfZZ : (hom : (ZZ -> a) ** (Homomorphism hom, Surjective hom))

||| Get the generator of a cyclic group
gen : CyclicGroup a => a
gen {a} = fst imOfZZ 1

plusZZPosSucc : (m : Nat) ->
                plusZ (Pos 1) (Pos m) = Pos (S m)
plusZZPosSucc Z = Refl
plusZZPosSucc (S k) = Refl

sumOnes : (m : Nat) ->
          (n : Nat ** 1 <^> n = Pos m)
sumOnes Z = (Z ** Refl)
sumOnes (S k) = let (n' ** rec_prf) = sumOnes k
                in (S n' ** rewrite rec_prf in Refl)

negSuccs : (m, n : Nat) ->
           NegS m = NegS n ->
           NegS (S m) = NegS (S n)
negSuccs m n eq = rewrite negSInjective eq in Refl

negNegIsNeg : (m, n : Nat) ->
              (s : Nat ** plusZ (NegS m) (NegS n) = NegS s)
negNegIsNeg Z k = (S k ** Refl)
negNegIsNeg (S k) j = let (s ** rec) = negNegIsNeg k j
                      in (S s ** negSuccs _ _ rec)

||| In a cyclic group, every element can be written as a power of the generator
cyclicGrpPowGen : CyclicGroup a =>
                  (x : a) ->
                  (n : Nat ** gen {a} <^> n = x)
cyclicGrpPowGen {a} x with (imOfZZ {a})
  | (hom ** (Hom hom prs, Srj hom srj_prf)) with (srj_prf x)
    | (Pos k ** preim_prf) = let (n ** n_prf) = sumOnes k in
                                 rewrite sym preim_prf in
                                 rewrite sym n_prf in
                                 (n ** sym (homPow hom (Hom hom prs) (Pos 1) n))
    | (NegS k ** preim_prf) with (srj_prf (neg x))
      | (Pos k' ** preim_prf') =
        let (n ** n_prf) = sumOnes k' in
        (n ** rewrite sym (homPow hom (Hom hom prs) (Pos 1) n) in
              rewrite n_prf in ?pospreimhole)
      | (NegS k' ** preim_prf') = ?negpreimhole
