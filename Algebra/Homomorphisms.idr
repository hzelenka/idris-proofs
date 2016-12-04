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
              (a -> b) ->
              (x : a) ->
              Type where
  InKernel : (Group a, Group b) =>
             (x : a) ->
             (hom : (a -> b)) ->
             Homomorphism hom ->
             hom x = Groups.zero ->
             Kernel hom x

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
                 (hom : (a -> b)) ->
                 Homomorphism hom ->
                 Kernel hom Groups.zero
zero_in_kernel hom hom_prf = InKernel _ _ hom_prf (zero_to_zero hom hom_prf)

-- Homomorphisms preserve inverses
hom_negative : (Group a, Group b) =>
               (hom : (a -> b)) ->
               Homomorphism hom ->
               (x : a) ->
               hom (neg x) = neg (hom x)
hom_negative hom (IsHom _ prs) x = neg_unique _ _ (left, right) where
  left : hom x <+> hom (neg x) = Groups.zero
  left = rewrite (sym (zero_to_zero hom (IsHom hom prs))) in
         rewrite (sym (prs x (neg x))) in
         rewrite (fst (inverse x)) in
         Refl
  right : hom (neg x) <+> hom x = Groups.zero
  right = rewrite (sym (zero_to_zero hom (IsHom hom prs))) in
          rewrite (sym (prs (neg x) x)) in
          rewrite (snd (inverse x)) in
          Refl
