module Composition

import Foundations.Functions

%default total
%access public export

||| id is the right identity under function composition
composition_right_id : (f : a -> b) ->
                       f . Prelude.Basics.id = f
composition_right_id f = Refl

||| id is the left identity under function composition
composition_left_id : (f : a -> b) ->
                      Prelude.Basics.id . f = f
composition_left_id f = Refl

||| Function composition is associative
composition_associative : (f : c -> d) ->
                          (g : b -> c) ->
                          (h : a -> b) ->
                          (f . g) . h = f . (g . h)
composition_associative f g h = Refl

||| The composition of two injections is an injection
inj_comp_inj : (f : b -> c) ->
               Injective f ->
               (g : a -> b) ->
               Injective g ->
               Injective (f . g)
inj_comp_inj f (Inj f f_inj) g (Inj g g_inj) = Inj (f . g) fg_inj where
  fg_inj x y eq = g_inj x y $ f_inj (g x) (g y) eq

||| The composition of two surjections is a surjection
srj_comp_srj : (f : b -> c) ->
               Surjective f ->
               (g : a -> b) ->
               Surjective g ->
               Surjective (f . g)
srj_comp_srj f (Srj f f_srj) g (Srj g g_srj) = Srj (f . g) fg_srj where
  fg_srj z = let (c_val ** c_prf) = f_srj z
                 (b_val ** b_prf) = g_srj c_val
             in (b_val ** trans (cong b_prf) c_prf)

||| The composition of two bijections is a bijection
bij_comp_bij : (f : b -> c) ->
               Bijective f ->
               (g : a -> b) ->
               Bijective g ->
               Bijective (f . g)
bij_comp_bij f (Bij f f_inj f_srj) g (Bij g g_inj g_srj) =
  from_inj_srj (f . g) (inj_comp_inj f (Inj f f_inj) g (Inj g g_inj))
                       (srj_comp_srj f (Srj f f_srj) g (Srj g g_srj))

infixl 9 ~.
||| Compose two verified injections into another verified injection
(~.) : (f : (b -> c) ** Injective f) ->
       (g : (a -> b) ** Injective g) ->
       (h : (a -> c) ** Injective h)
(f ** f_inj) ~. (g ** g_inj) = ((f . g) ** inj_comp_inj f f_inj g g_inj)

infixl 9 .~
||| Compose two verified surjections into another verified surjection
(.~) : (f : (b -> c) ** Surjective f) ->
       (g : (a -> b) ** Surjective g) ->
       (h : (a -> c) ** Surjective h)
(f ** f_srj) .~ (g ** g_srj) = ((f . g) ** srj_comp_srj f f_srj g g_srj)

infixl 9 ~.~
||| Compose two verified bijections into another verified bijection
(~.~) : (f : (b -> c) ** Bijective f) ->
        (g : (a -> b) ** Bijective g) ->
        (h : (a -> c) ** Bijective h)
(f ** f_bij) ~.~ (g ** g_bij) = ((f . g) ** bij_comp_bij f f_bij g g_bij)
