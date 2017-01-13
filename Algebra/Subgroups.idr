module Subgroups

import Algebra.Groups
import Algebra.Homomorphisms

%default total
%access public export

data Subgroup : Group a =>
                (restriction : a -> Type) ->
                Type where
  Subgp : Group a =>
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
  Norm : Group a =>
         (subgp : Subgroup restriction) ->
         (conjugacy : (x : a) ->
                      (y : a ** restriction y) ->
                      restriction (x <+> y <+> (neg x))) ->
         Normal subgp

||| Subgroups automatically contain the identity
subgroupContainsZero : Group a =>
                       Subgroup {a} subgp ->
                       subgp Groups.zero
subgroupContainsZero (Subgp subgp (nonempty ** restr) op_cl neg_cl) =
  rewrite sym $ fst $ inverse nonempty
  in op_cl nonempty restr (neg nonempty) $ neg_cl nonempty restr

||| An operation on two kernel elements results in another kernel element
kernelOp : (Group a, Group b) =>
           (hom : (a -> b)) ->
           Homomorphism hom ->
           (x : a) ->
           Kernel hom x ->
           (y : a) ->
           Kernel hom y ->
           Kernel hom (x <+> y)
kernelOp hom (Hom _ prs) x (Kern _ _ _ x_zero) y (Kern _ _ _ y_zero) =
  step_5 where
    step_1 : hom x <+> hom y = Groups.zero <+> Groups.zero
    step_1 = operateEq (hom x) zero (hom y) zero x_zero y_zero
    step_2 : hom (x <+> y) = hom x <+> hom y
    step_2 = prs x y
    step_3 : hom (x <+> y) = Groups.zero <+> Groups.zero
    step_3 = trans step_2 step_1
    step_4 : hom (x <+> y) = Groups.zero
    step_4 = trans step_3 $ fst $ identity zero
    step_5 : Kernel hom (x <+> y)
    step_5 = Kern (x <+> y) hom (Hom _ prs) step_4

kernelNeg : (Group a, Group b) =>
            (hom : (a -> b)) ->
            Homomorphism hom ->
            (x : a) ->
            Kernel hom x ->
            Kernel hom (neg x)
kernelNeg hom (Hom _ prs) x (Kern _ _ _ x_zero) =
  Kern _ _ (Hom _ prs) (sym step_5) where
    step_1 : hom x <+> hom (neg x) = Groups.zero <+> hom (neg x)
    step_1 = cong {f=(<+> hom (neg x))} x_zero
    step_2 : hom (x <+> neg x) = Groups.zero <+> hom (neg x)
    step_2 = rewrite prs x (neg x) in step_1
    step_3 : hom (Groups.zero) = Groups.zero <+> hom (neg x)
    step_3 = rewrite (sym (fst (inverse x))) in step_2
    step_4 : Groups.zero = Groups.zero <+> hom (neg x)
    step_4 = trans (sym (zeroToZero hom (Hom hom prs))) step_3
    step_5 : Groups.zero = hom (neg x)
    step_5 = rewrite (sym (snd (identity (hom (neg x))))) in step_4

kernelSubgroup : (Group a, Group b) =>
                 (hom : (a -> b)) ->
                 Homomorphism hom ->
                 Subgroup (Kernel hom)
kernelSubgroup {a} {b} hom (Hom hom prs) =
  Subgp _ nonempty op_cls neg_cls where
    nonempty = (zero ** zeroInKernel hom (Hom hom prs))
    op_cls = kernelOp hom (Hom hom prs)
    neg_cls = kernelNeg hom (Hom hom prs)

kernelConj : (Group a, Group b) =>
             (hom : (a -> b)) ->
             Homomorphism hom ->
             (x : a) ->
             (y : a) ->
             Kernel hom y ->
             Kernel hom (x <+> y <+> neg x)
kernelConj hom (Hom _ prs) x y (Kern _ _ _ y_zero) =
  Kern _ _ (Hom _ prs) exact where
    exact = rewrite (prs (x <+> y) (neg x)) in
            rewrite (prs x y) in 
            rewrite y_zero in
            rewrite (fst (identity (hom x))) in
            rewrite (sym (prs x (neg x))) in
            rewrite (fst (inverse x)) in
            zeroToZero hom (Hom _ prs)
