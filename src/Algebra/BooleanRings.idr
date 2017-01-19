module BooleanRings

import Foundations.Utilities
import Algebra.Groups
import Algebra.Rings

%default total
%access public export

||| Ring in which every element multiplied by itself is itself
interface Ring a => BooleanRing a where
  boolean : (x : a) ->
            x = x <#> x

||| In a Boolean ring, every element added to itself is the identity
boolDouble : BooleanRing a =>
             (x : a) ->
             x <+> x = Groups.zero
boolDouble x =
  sym $
  cancelRight x zero (x <+> x) $
  rightId _ $=
  (cancelRight x x (x <+> x <+> x) $
  replace {P=\val=>x <+> x = val <+> val <+> val <+> val} (sym (boolean x)) $
  boolean (x <+> x) $=
  multSumSum x x x x)

||| In a Boolean ring, every element is self-inverse under addition
boolAddInv : BooleanRing a =>
             (x : a) ->
             x = neg x
boolAddInv x = negUniqAb x x $ Left $ boolDouble x

||| A Boolean ring is automatically commutative
boolComm : BooleanRing a =>
           (x, y : a) ->
           x <#> y = y <#> x
boolComm x y =
  sym $
  (negUniqAb (x <#> y) (y <#> x) $ Left $ sym $
  cancelLeft x zero (x <#> y <+> y <#> x) $
  leftId _ $=
  (cancelRight y x (x <+> x <#> y <+> y <#> x) $
  replace {P=\val => x <+> y = x <+> x <#> y <+> y <#> x <+> val}
          (sym (boolean y)) $
  replace {P=\val => x <+> y = val <+> x <#> y <+> y <#> x <+> y<#> y}
          (sym (boolean x)) $
  boolean (x <+> y) $=
  multSumSum x y x y) $=
  associativity x (x <#> y) (y <#> x)) $=
  sym (boolAddInv (x <#> y))

implementation BooleanRing a => CommutativeRing a where
  multComm = boolComm
