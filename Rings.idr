module Rings

import Groups

interface AbelianGroup a pl zero neg =>
          Ring (a : Type)
               (pl : a -> a -> a)
               (ml : a -> a -> a)
               (zero : a)
               (neg : a -> a) | a where
  ml_associativity : (x : a) ->
                     (y : a) ->
                     (z : a) ->
                     (x `ml` y) `ml` z = x `ml` (y `ml` z)
  distributivity : (x : a) ->
                   (y : a) ->
                   (z : a) ->
                   (x `ml` (y `pl` z) = (x `ml` y) `pl` (x `ml` z),
                    (y `pl` z) `ml` x = (y `ml` x) `pl` (z `ml` x))

times_zero_equals_zero : Ring a pl ml zero neg =>
                         (x : a) ->
                         (zero `ml` x = zero,
                          x `ml` zero = zero)
times_zero_equals_zero x = ?zero_hole

interface Ring a pl ml zero neg =>                       
          IntegralDomain (a : Type)
                         (pl : a -> a -> a)
                         (ml : a -> a -> a)
                         (zero : a)
                         (neg : a -> a) 
                         (one : a) | a where
  ml_commutativity : (x : a) ->
                     (y : a) ->
                     x `ml` y = y `ml` x
  ml_identity : (x : a) ->
                (x `ml` one = x,
                one `ml` x = x)
  no_divs_zero : (x : a) ->
                 (y : a) ->
                 x `ml` y = zero ->
                 Either (x = 0) (y = 0)

interface IntegralDomain a pl ml zero neg one =>
          Field (a : Type)
                (pl : a -> a -> a)
                (ml : a -> a -> a)
                (zero : a)
                (neg : a -> a) 
                (one : a) 
                (rcp : (x : a) -> a) | a where

