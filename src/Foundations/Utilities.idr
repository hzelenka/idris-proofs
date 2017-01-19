module Utilites

%default total
%access public export

infixl 2 $=
||| Infix version of transitivity to make equality proofs terser
||| Note that, due to precedence issues, $= often works poorly with $
($=) : a = b -> b = c -> a = c
eq1 $= eq2 = trans eq1 eq2