module Rings

import Algebra.Groups

%default total
%access public export
%hide Prelude.Applicative.(<*>)

interface AbelianGroup a => Ring a where
  (<*>) : a -> a -> a
  mult_associativity : (x : a) ->
                        (y : a) ->
                        (z : a) ->
                        (x <*> y) <*> z = x <*> (y <*> z)
  distributivity : (x : a) ->
                   (y : a) ->
                   (z : a) ->
                   (x <*> (y <+> z) = (x <*> y) <+> (x <*> z),
                    (y <+> z) <*> x = (y <*> x) <+> (z <*> x))

times_zero_equals_zero : Ring a =>
                         (x : a) ->
                         (Groups.zero <*> x = Groups.zero,
                          x <*> Groups.zero = Groups.zero)
times_zero_equals_zero x = (lmult, rmult) where
  lmult = ?lmulthole
  rmult = ?rmulthole

interface Ring a => IntegralDomain a where                    
  one : a
  ml_commutativity : (x : a) ->
                     (y : a) ->
                     x <*> y = y <*> x
  ml_identity : (x : a) ->
                (x <*> one = x,
                one <*> x = x)
  no_divs_zero : (x : a) ->
                 (y : a) ->
                 x <*> y = zero ->
                 Either (x = Groups.zero) (y = Groups.zero)
