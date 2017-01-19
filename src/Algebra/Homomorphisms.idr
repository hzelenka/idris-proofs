module Homomorphisms

import Algebra.Groups
import Foundations.Functions

%default total
%access public export

||| Function between two groups preserving group structure
data Homomorphism : (Group a, Group b) =>
                    (hom : a -> b) ->
                    Type where
  Hom : (Group a, Group b) =>
        (hom : a -> b) ->
        (preservation : (x : a) ->
                        (y : a) ->
                        hom (x <+> y) = hom x <+> hom y) ->
        Homomorphism hom

||| Bijective homomorphism
data Isomorphism : (Group a, Group b) =>
                   (iso : a -> b) ->
                   Type where
  Iso : (Group a, Group b) =>
        (iso : a -> b) ->
        Homomorphism iso ->
        Bijective iso ->
        Isomorphism iso

||| Set of all elements mapped to the identity by a homomorphism
data Kernel : (Group a, Group b) =>
              (a -> b) ->
              (x : a) ->
              Type where
  Kern : (Group a, Group b) =>
         (x : a) ->
         (hom : (a -> b)) ->
         Homomorphism hom ->
         hom x = Groups.zero ->
         Kernel hom x

||| Every homomorphism sends the identity element to its counterpart
zeroToZero : (Group a, Group b) =>
             (hom : a -> b) ->
             Homomorphism hom ->
             hom Groups.zero = Groups.zero
zeroToZero {a} {b} hom (Hom _ prs) = sym step_5 where
  step_1 : hom (zero {a}) = hom (zero {a} <+> zero {a})
  step_1 = cong {f=hom} $ sym $ leftId _
  step_2 : hom (zero {a} <+> zero {a}) = hom (zero {a}) <+> hom (zero {a})
  step_2 = prs _ _
  step_3 : hom (zero {a}) = hom (zero {a}) <+> hom (zero {a})
  step_3 = trans step_1 step_2
  step_4 : zero {a=b} <+> hom (zero {a}) = hom (zero {a}) <+> hom (zero {a})
  step_4 = trans (rightId _) step_3
  --step_5 : Groups.zero = hom Groups.zero
  step_5 = cancelRight _ _ _ step_4

||| Zero is in the kernel of every homomorphism
zeroInKernel : (Group a, Group b) =>
               (hom : (a -> b)) ->
               Homomorphism hom ->
               Kernel hom Groups.zero
zeroInKernel hom hom_prf = Kern _ _ hom_prf $ zeroToZero hom hom_prf

||| Homomorphisms preserve inverses
homNeg : (Group a, Group b) =>
         (hom : (a -> b)) ->
         Homomorphism hom ->
         (x : a) ->
         hom (neg x) = neg (hom x)
homNeg hom (Hom _ prs) x = negUniq _ _ (left, right) where
  left : hom x <+> hom (neg x) = Groups.zero
  left = rewrite sym (zeroToZero hom (Hom hom prs)) in
         rewrite sym (prs x (neg x)) in
         rewrite leftInv x in
         Refl
  right : hom (neg x) <+> hom x = Groups.zero
  right = rewrite sym (zeroToZero hom (Hom hom prs)) in
          rewrite sym (prs (neg x) x) in
          rewrite rightInv x in
          Refl
