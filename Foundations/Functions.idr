module Functions

import Data.Fin

%default total
%access public export

infixl 1 <->
||| Coq-style if and only if
(<->) : Type -> Type -> Type
a <-> b = (a -> b, b -> a)

||| AKA one-to-one
data Injective : (domain -> codomain) -> Type where
  Inj : (f : domain -> codomain) ->
        (prf : (x : domain) ->
          (y : domain) ->
          (eq : f x = f y) ->
          (x = y)) ->
        Injective f

||| AKA onto
data Surjective : (domain -> codomain) -> Type where
  Srj : (f : domain -> codomain) ->
        (prf : (z : codomain) ->
          (x : domain ** f x = z)) ->
        Surjective f

||| AKA one-to-one and onto
data Bijective : (a -> b) -> Type where
  Bij : (f : domain -> codomain) ->
        (inj : (x : domain) ->
          (y : domain) ->
          (eq : f x = f y) ->
          (x = y)) ->
        (srj : (z : codomain) ->
          (x : domain ** f x = z)) ->
        Bijective f

||| Show a function is bijective given it is injective and surjective
from_inj_srj : (f : domain -> codomain) ->
               Injective f ->
               Surjective f ->
               Bijective f
from_inj_srj f (Inj f inj) (Srj f srj) = Bij f inj srj

||| There exists a function that forms the identity when composed on the left
data LeftInv : (domain -> codomain) ->
               (codomain -> domain) ->
               Type where
  LInv : (f : domain -> codomain) ->
         (g : codomain -> domain) ->
         ((x : domain) ->
          (g (f x) = x)) ->
         LeftInv f g

||| There exists a function that forms the identity when composed on the right
data RightInv : (domain -> codomain) ->
                (codomain -> domain) ->
                Type where
  RInv : (f : domain -> codomain) ->
         (g : codomain -> domain) ->
         ((y : codomain) ->
          (f (g y) = y)) ->
         RightInv f g

||| If f is left inverse to g, g is right inverse to f
linv_to_rinv : (f : domain -> codomain) ->
               (g : codomain -> domain) ->
               LeftInv f g ->
               RightInv g f
linv_to_rinv f g (LInv _ _ linv_prf) = RInv _ _ linv_prf

||| If f is right inverse to g, g is left inverse to f
rinv_to_linv : (f : domain -> codomain) ->
               (g : codomain -> domain) ->
               RightInv f g ->
               LeftInv g f
rinv_to_linv f g (RInv _ _ rinv_prf) = LInv _ _ rinv_prf

||| If a function has a left inverse, it is injective
||| NB: converse is unprovable constructively
left_inv_inj : (f : a -> b) ->
               (g : (b -> a) ** LeftInv f g) ->
               Injective f
left_inv_inj {a} {b} f (g ** LInv _ _ prf) = Inj _ inj where
    inj x y eq = rewrite sym (prf x) in
                 rewrite sym (prf y) in
                 cong {f=g} eq

||| A function is surjective iff it has a right inverse
right_inv_srj : (f : a -> b) ->
                Surjective f <-> (g : (b -> a) ** RightInv f g)
right_inv_srj {a} {b} f = (fwd, bwd) where
  fwd : Surjective f -> (g : (b -> a) ** RightInv f g)
  fwd (Srj _ prf) = ((\z => fst (prf z)) ** RInv _ _ rinv) where
    rinv y = snd (prf y)
  bwd : (g : (b -> a) ** RightInv f g) -> Surjective f
  bwd (g ** (RInv _ _ prf)) = Srj _ srj where
    srj z = (g z ** prf z)

||| Left and right inverses must be extensionally the same if they both exist
left_inv_right_inv : (f : a -> b) ->
                     (g : b -> a) ->
                     (h : b -> a) ->
                     LeftInv f g ->
                     RightInv f h ->
                     (y : b) ->
                     g y = h y
left_inv_right_inv f g h (LInv _ _ linv_prf) (RInv _ _ rinv_prf) y =
  trans step_1 step_2 where
    step_1 : g y = g (f (h y))
    step_1 = sym $ cong $ rinv_prf y
    step_2 : g (f (h y)) = h y
    step_2 = linv_prf $ h y

||| Given a function with a two-sided inverse, both are bijections
linv_rinv_bij : (f : domain -> codomain) ->
                (g : codomain -> domain) ->
                LeftInv f g ->
                RightInv f g ->
                (Bijective f, Bijective g)
linv_rinv_bij f g linv_prf rinv_prf = (left_prf, right_prf) where
  f_inj : Injective f
  f_inj = left_inv_inj f (g ** linv_prf)
  f_srj : Surjective f
  f_srj = snd (right_inv_srj f) (g ** rinv_prf)
  left_prf = from_inj_srj f f_inj f_srj
  g_inj : Injective g
  g_inj = left_inv_inj g (f ** rinv_to_linv f g rinv_prf)
  g_srj : Surjective g
  g_srj = snd (right_inv_srj g) (f ** linv_to_rinv f g linv_prf)
  right_prf = from_inj_srj g g_inj g_srj

||| A bijection may be inverted to form another bijection
bij_inv : (f : domain -> codomain) ->
          Bijective f ->
          (g : (codomain -> domain) ** Bijective g)
bij_inv f (Bij _ f_inj f_srj) = (g ** exact) where
  g : codomain -> domain
  g z = fst $ f_srj z
  g_rinv : (c : codomain) -> f (g c) = c
  g_rinv c with (f_srj c)
    | (d ** d_prf) = d_prf
  g_linv : (d : domain) -> g (f d) = d
  g_linv d with (f_srj (f d))
    | (d' ** d_prf') = f_inj _ _ d_prf'
  exact : Bijective g
  exact = snd $ linv_rinv_bij f g (LInv _ _ g_linv) (RInv _ _ g_rinv)

||| swap is a bijection from (a, b) to (b, a)
product_commutative : Bijective Prelude.Pairs.swap
product_commutative = Bij _ inj srj where
  inj (x1, x2) (y1, y2) eq = cong {f=swap} eq
  srj (x, y) = ((y, x) ** Refl)

||| mirror is a bijection from Either a b to Either b a
coproduct_commutative : Bijective Prelude.Either.mirror
coproduct_commutative = Bij _ inj srj where
  inj (Left l) (Left x) eq = cong $ rightInjective eq
  inj (Left l) (Right r) eq = absurd $ leftNotRight $ sym eq
  inj (Right r) (Left l) eq = absurd $ leftNotRight eq
  inj (Right r) (Right x) eq = cong $ leftInjective eq
  srj (Left l) = (Right l ** Refl)
  srj (Right r) = (Left r ** Refl)
