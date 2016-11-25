module Subgroups

import Groups
import Data.Vect

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

subgroup_contains_zero : Group a =>
                         Subgroup {a} r ->
                         r Groups.zero
subgroup_contains_zero (IsSubgroup r (nonempty ** restr) op_cl neg_cl) =
  rewrite sym $ fst $ inverse nonempty
  in op_cl nonempty restr (neg nonempty) (neg_cl nonempty restr)
