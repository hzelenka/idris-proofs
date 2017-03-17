module Subgroups

import Foundations.Functions
import Algebra.Groups
import Algebra.Homomorphisms

%default total
%access public export

data Subgroup : (Group a, Group b) =>
                (a : Type) ->
                (b : Type) ->
                Type where
  Subgp : (Group a, Group b) =>
          (incl : (a -> b) ** (Homomorphism incl, Injective incl)) ->
          Subgroup {a} {b} a b

