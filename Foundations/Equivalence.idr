module Equivalence

import Foundations.Relations

%default total
%access public export

data EquivalenceRelation : Relation a ->
                           Type where
  IsEquivalence : (r : Relation a) ->
                  (decidable : (x : a) ->
                               (y : a) ->
                               Dec (x `r` y)) ->
                  (reflexive : (x : a) ->
                               x `r` y) ->
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
