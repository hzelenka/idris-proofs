module Subgroups

import Algebra.Groups
import Algebra.Homomorphisms

%default total
%access public export

data Subgroup : Group a =>
                (restriction : a -> Type) ->
                Type where
  IsSubgroup : Group a =>
               (restriction : a -> Type) ->
               (nonempty : (x : a ** restriction x)) ->
               (op_closure : ((x : a) ->
                              restriction x ->
                              (y : a) ->
                              restriction y ->
                              restriction (x <+> y))) ->
               (neg_closure : ((x : a) ->
                               restriction x ->
                               restriction (neg x))) ->
                Subgroup restriction

data Normal : Group a =>
              Subgroup {a} restriction ->
              Type where
  IsNormal : Group a =>
             (subgp : Subgroup restriction) ->
             (conjugacy : (x : a) ->
                          (y : a ** restriction y) ->
                          restriction (x <+> y <+> (neg x))) ->
            Normal subgp

subgroup_contains_zero : Group a =>
                         Subgroup {a} r ->
                         r Groups.zero
subgroup_contains_zero (IsSubgroup r (nonempty ** restr) op_cl neg_cl) =
  rewrite sym $ fst $ inverse nonempty
  in op_cl nonempty restr (neg nonempty) (neg_cl nonempty restr)

kernel_subgroup : (Group a, Group b) =>
                  (sigma_hom : (hom : (a -> b) ** Homomorphism hom)) ->
                  Subgroup (Kernel sigma_hom)
kernel_subgroup {a} {b} sigma_hom = IsSubgroup {a} _ nonempty op_cls ?neg_cls where
  nonempty : (x : a ** Kernel sigma_hom x)
  nonempty = (zero ** zero_in_kernel _)
  op_cls : (Group a, Group b) =>
           (x : a) ->
           Kernel sigma_hom x ->
           (y : a) ->
           Kernel sigma_hom y ->
           Kernel sigma_hom (x <+> y)
  op_cls x x_zero y y_zero = ?op_hole --op_hole x_zero y_zero
  {-neg_cls = ?neg_hole -}
