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

-- This proof is somewhat unsightly and goes over 80 chars per line =/
-- I may fix it up later
zero_to_zero : (Group a, Group b) =>
               (hom : a -> b) ->
               Homomorphism hom ->
               hom Groups.zero = Groups.zero
zero_to_zero {a} {b} hom (IsHom _ prs) = sym step_5 where
  step_1 : hom Groups.zero = hom (Groups.zero <+> Groups.zero)
  step_1 = cong {f=hom} $ sym $ fst $ identity _
  step_2 : hom (Groups.zero <+> Groups.zero) = hom Groups.zero <+> hom Groups.zero
  step_2 = prs _ _
  step_3 : hom Groups.zero = hom Groups.zero <+> hom Groups.zero
  step_3 = trans step_1 step_2
  step_4 : Groups.zero <+> hom Groups.zero = hom Groups.zero <+> hom Groups.zero
  step_4 = trans (snd (identity _)) step_3
  step_5 : Groups.zero = hom Groups.zero
  step_5 = cancel_right _ _ _ step_4

zero_in_kernel : (Group a, Group b) =>
                 (sigma_hom : (hom : (a -> b) ** Homomorphism hom)) ->
                 Kernel sigma_hom Groups.zero
zero_in_kernel sigma_hom =
  InKernel _ _ _ (zero_to_zero (fst sigma_hom) (snd sigma_hom))
