module Homomorphisms

import Algebra.Groups
import Foundations.Functions

%default total
%access public export

data Homomorphism : (Group a, Group b) =>
                    (hom : a -> b) ->
                    Type where
  IsHom : (Group a, Group b) =>
          (hom : a -> b) ->
          (preservation : (x : a) ->
                          (y : a) ->
                          hom (x <+> y) = hom x <+> hom y) ->
          Homomorphism hom

data Isomorphism : (Group a, Group b) =>
                   (iso : a -> b) ->
                   Type where
  IsIso : (Group a, Group b) =>
          (iso : a -> b) ->
          Homomorphism iso ->
          Bijective iso ->
          Isomorphism iso

data Kernel : (Group a, Group b) =>
              (hom : (a -> b) ** Homomorphism hom) ->
              (x : a) ->
              Type where
  InKernel : (Group a, Group b) =>
             (x : a) ->
             (hom : (a -> b)) ->
             (sigma_hom : (hom : (a -> b) ** Homomorphism hom)) ->
             hom x = Groups.zero ->
             Kernel sigma_hom x

zero_to_zero : (Group a, Group b) =>
               (hom : a -> b) ->
               Homomorphism hom ->
               hom Groups.zero = Groups.zero
zero_to_zero {a} {b} hom (IsHom _ prs) = ?hole where
  eq_2 : hom Groups.zero = hom (Groups.zero <+> Groups.zero)
  eq_2 = cong {f=hom} $ sym $ fst $ identity zero
  eq_3 : hom (Groups.zero <+> Groups.zero) = hom Groups.zero <+> hom Groups.zero
  eq_3 = prs _ _
