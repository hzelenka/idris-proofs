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

kernel_op : (Group a, Group b) =>
            (hom : (a -> b)) ->
            Homomorphism hom ->
            (x : a) ->
            Kernel hom x ->
            (y : a) ->
            Kernel hom y ->
            Kernel hom (x <+> y)
kernel_op hom (IsHom _ prs) x (InKernel _ _ _ x_zero) y (InKernel _ _ _ y_zero) =
  step_5 where
    step_1 : hom x <+> hom y = Groups.zero <+> Groups.zero
    step_1 = operate_eq (hom x) zero (hom y) zero x_zero y_zero
    step_2 : hom (x <+> y) = hom x <+> hom y
    step_2 = prs x y
    step_3 : hom (x <+> y) = Groups.zero <+> Groups.zero
    step_3 = trans step_2 step_1
    step_4 : hom (x <+> y) = Groups.zero
    step_4 = trans step_3 (fst (identity zero))
    step_5 : Kernel hom (x <+> y)
    step_5 = InKernel (x <+> y) hom (IsHom _ prs) step_4

kernel_neg : (Group a, Group b) =>
             (hom : (a -> b)) ->
             Homomorphism hom ->
             (x : a) ->
             Kernel hom x ->
             Kernel hom (neg x)
kernel_neg hom (IsHom _ prs) x (InKernel _ _ _ x_zero) =
  InKernel _ _ (IsHom _ prs) (sym step_5) where
    step_1 : hom x <+> hom (neg x) = Groups.zero <+> hom (neg x)
    step_1 = cong {f=(<+> hom (neg x))} x_zero
    step_2 : hom (x <+> neg x) = Groups.zero <+> hom (neg x)
    step_2 = rewrite prs x (neg x) in step_1
    step_3 : hom (Groups.zero) = Groups.zero <+> hom (neg x)
    step_3 = rewrite (sym (fst (inverse x))) in step_2
    step_4 : Groups.zero = Groups.zero <+> hom (neg x)
    step_4 = trans (sym (zero_to_zero hom (IsHom hom prs))) step_3
    step_5 : Groups.zero = hom (neg x)
    step_5 = rewrite (sym (snd (identity (hom (neg x))))) in step_4

kernel_subgroup : (Group a, Group b) =>
                  (hom : (a -> b)) ->
                  Homomorphism hom ->
                  Subgroup (Kernel hom)
kernel_subgroup {a} {b} hom (IsHom hom prs) =
  IsSubgroup _ nonempty op_cls neg_cls where
    nonempty = (zero ** zero_in_kernel hom (IsHom hom prs))
    op_cls = kernel_op hom (IsHom hom prs)
    neg_cls = kernel_neg hom (IsHom hom prs)

kernel_conj : (Group a, Group b) =>
              (hom : (a -> b)) ->
              Homomorphism hom ->
              (x : a) ->
              (y : a) ->
              Kernel hom y ->
              Kernel hom (x <+> y <+> neg x)
kernel_conj hom (IsHom _ prs) x y (InKernel _ _ _ y_zero) =
  InKernel _ _ (IsHom _ prs) exact where
    exact = rewrite (prs (x <+> y) (neg x)) in
            rewrite (prs x y) in 
            rewrite y_zero in
            rewrite (fst (identity (hom x))) in
            rewrite (sym (prs x (neg x))) in
            rewrite (fst (inverse x)) in
            zero_to_zero hom (IsHom _ prs)

-- This needs to be refactored b/c Idris doesn't recognize that the y picked up
-- in ?normal_hole is the same one in prs
kernel_normal : (Group a, Group b) =>
                (hom : (a -> b)) ->
                Homomorphism hom ->
                (subgp : Subgroup (Kernel hom)) ->
                Normal subgp
kernel_normal hom (IsHom hom prs) subgp = IsNormal subgp ?normal_hole
