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

HasBij : Type -> Type -> Type
HasBij a b = (f : (a -> b) ** Bijective f)

bij_equiv : EquivalenceRelation HasBij
bij_equiv = IsEquiv _ rfl sym trs where
  rfl a = (id ** Bij _ (\_, _, eq => eq) (\z => (z ** Refl)))
  sym a b (f ** Bij _ inj srj) = ?sym_hole
  trs a b c (f ** Bij _ f_inj f_srj) (g ** Bij _ g_inj g_srj) =
    ((g . f) ** Bij _ trs_inj trs_srj) where
      trs_inj x y eq = f_inj x y $ g_inj (f x) (f y) eq
      trs_srj z = let (x ** x_prf) = g_srj z
                      (y ** y_prf) = f_srj x in
                  (y ** rewrite y_prf in x_prf)
