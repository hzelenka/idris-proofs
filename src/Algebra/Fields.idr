module Fields

import Algebra.Rings

%default total
%access public export

||| Ring with multiplicative unity, identity and invertibility (besides zero)
interface Ring a => Field a where
  one : a
  unity : (x : a) ->
          (x <#> one = x,
           one <#> x = x)
  multComm : (x, y : a) ->
             x <#> y = y <#> x
  multInv : (x : a) ->
            {auto nonzero : Not (x = zero)} ->
            (x' : a ** (x <#> x' = one,
                        x' <#> x = one))
