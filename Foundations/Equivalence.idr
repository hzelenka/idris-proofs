module Equivalence

import Foundations.Functions
import Foundations.Relations

%default total
%access public export

data EquivalenceRelation : Relation a ->
                           Type where
  IsEquiv : (r : Relation a) ->
            (reflexive : (x : a) ->
                         x `r` x) ->
            (symmetric : (x : a) ->
                         (y : a) ->
                         (x `r` y) ->
                         (y `r` x)) ->
            (transitive : (x : a) ->
                          (y : a) ->
                          (z : a) ->
                          x `r` y ->
                          y `r` z ->
                          x `r` z) ->
            EquivalenceRelation r