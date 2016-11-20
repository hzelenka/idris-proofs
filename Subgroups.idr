module Subgroups

import Groups

%default total
%access public export

data Subgroup : Group a =>
                (restriction : a -> Type) ->
                Type where
  IsSubgroup : Group a =>
               (restriction : a -> Type) ->
               (nonempty : (x : a ** restriction x)) ->
               (op_closure : ((x : a ** restriction x) ->
                              (y : a ** restriction x) ->
                               restriction (x <+> y))) ->
               (neg_closure : ((x : a ** restriction x) ->
                                restriction (neg x))) ->
                Subgroup restriction

subgroup_contains_e : Group a =>
                      Subgroup {a} r ->
                      r Groups.zero
subgroup_contains_e {a} (IsSubgroup r nonempty_prf op_prf neg_prf) = ?e_hole
