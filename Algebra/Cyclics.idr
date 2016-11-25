module Cyclics

import Data.Fin
import Foundations.Functions
import Algebra.Groups

%default total
%access public export

data CyclicGroup : Group a =>
                   (gen : a) ->
                   Type where
  IsCyclic : Group a =>
             (gen : a) ->
             ((el : a) ->
              (order : Nat ** (gen <^> order = el))) ->
             CyclicGroup gen

data Order : Group a =>
             (el : a) ->
             (order : Nat) ->
             Type where
  HasOrder : Group a =>
             (el : a) ->
             (order : Nat) ->
             el <^> order = Groups.zero ->
             ((order' : Nat) ->
              el <^> order' = Groups.zero ->
              LTE order order') ->
             Order el order

-- Group generated by the identity has order 1
trivial_group : Group a =>
                (gen : a) ->
                CyclicGroup {a} gen ->
                (gen = Groups.zero {a}) ->
                a ~= 1
trivial_group gen (IsCyclic {a} gen prf) eqg = Equi a 1 (f ** bij) where
  f : a -> Fin 1
  f _ = FZ
  inj : (x : a) -> (y : a) -> (FZ = FZ) -> x = y
  inj x y fz_refl with (prf x, prf y)
    | ((x_ord ** zero_x), (y_ord ** zero_y)) =
      rewrite sym zero_x in
      rewrite sym zero_y in
      rewrite eqg in
      trans (power_of_zero {a} x_ord) (sym (power_of_zero {a} y_ord))
  srj : (z : Fin 1) -> (x : a ** FZ = z)
  srj FZ = (gen ** Refl)
  srj (FS x) = absurd $ FinZAbsurd x
  bij : Bijective f
  bij = Bij f (Inj f inj) (Srj f srj)
