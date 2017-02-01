module Polynomials

import Algebra.Groups
import Algebra.Rings
import Algebra.Fields

||| Collection of coefficients drawn from a field, the first being nonzero
||| Maybe Nat represents the degree of the polynomial, Nothing for the special
||| case of the empty polynomial
data Polynomial : Maybe Nat ->
                  (a : Type) ->
                  Type where
  ||| Polynomial with no coefficients and undefined degree
  Empty : Field a =>
          --(a : Type) ->
          Polynomial Nothing a
  ||| "Front" coefficient, forced to be nonzero
  Leading : Field a =>
            (x : a) ->
            {auto nonzero : Not (x = Groups.zero)} ->
            Polynomial (Just Z) a
  ||| Attach a potentially zero coefficient to a preexisting polynomial
  ||| Note that the constructor pattern matches on Just _ to preclude Empty
  Following : Field a =>
              (x : a) ->
              (p : Polynomial (Just m) a) ->
              Polynomial (Just (S m)) a

||| Converts Nothing to Just Z and Just x to itself
nothingZ : Maybe Nat -> Maybe Nat
nothingZ Nothing = Just Z
nothingZ (Just x) = Just x

addDegs : Maybe Nat -> Maybe Nat -> Maybe Nat
addDegs Nothing Nothing = Nothing
addDegs m n = (+) <$> nothingZ m <*> nothingZ n

||| Add two polynomials coefficient by coefficient
addPoly : Field a =>
          (f : Polynomial m a) ->
          (g : Polynomial n a) ->
          Polynomial (addDegs m n) a
addPoly Empty Empty = Empty
addPoly Empty g@(Leading {nonzero} x) = g
addPoly Empty g@(Following x p) = g
addPoly (Leading x) g = ?addpolyhole_2
addPoly (Following x p) g = ?addpolyhole_3
