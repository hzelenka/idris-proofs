module Functions

import Data.Fin

%access public export
%default total

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

||| There always exists a trivial bijection from a type to itself
bij_refl : (a : Type) ->
           (f : (a -> a) ** Bijective f)
bij_refl a = (id ** Bij _ (\_, _, eq => eq) (\z => (z ** Refl)))

||| The composition of two bijections is another bijection
bij_trans : (f : a -> b) ->
            Bijective f ->
            (g : b -> a) ->
            Bijective g ->
            Bijective (g . f)
bij_trans f (Bij _ f_inj f_srj) g (Bij _ g_inj g_srj) = Bij _ gf_inj gf_srj where
  gf_inj x y eq = f_inj x y $ g_inj (f x) (f y) eq
  gf_srj z = let (x ** x_prf) = g_srj z
                 (y ** y_prf) = f_srj x in
             (y ** rewrite y_prf in x_prf)

||| Simple utility for showing a function is bijective
from_inj_srj : (f : domain -> codomain) ->
               Injective f ->
               Surjective f ->
               Bijective f
from_inj_srj f (Inj f inj) (Srj f srj) = Bij f inj srj

infixl 2 ~=
||| Data type for having the same cardinality
data (~=) : Type -> Nat -> Type where
  ||| Cardinality of the empty set
  Absurd : (a : Type) ->
           Not a ->
           a ~= 0
  ||| Can be put into correspondence with some Fin (S n)
  Finite : (a : Type) ->
           (n : Nat) ->
           (bij : (f : (a -> Fin (S n)) ** Bijective f)) ->
           (~=) a (S n)

||| Has cardinality of the natural numbers
Aleph : Type -> Type
Aleph a = (f : (a -> Nat) ** Bijective f)

||| Maybe applied to a finite set has cardinality one greater
s_fin_maybe_fin : (n : Nat) ->
                  Maybe (Fin n) ~= S n
s_fin_maybe_fin Z = Finite _ _ (f ** Bij _ f_inj f_srj) where
  f : Maybe (Fin 0) -> Fin 1
  f Nothing = FZ
  f_inj Nothing Nothing _ = Refl
  f_srj FZ = (Nothing ** Refl)
s_fin_maybe_fin (S k) = Finite _ _ (f ** Bij _ f_inj f_srj) where
  f : Maybe (Fin n) -> Fin (S n)
  f Nothing = FZ
  f (Just n) = FS n
  f_inj Nothing Nothing eq = Refl
  f_inj Nothing (Just x) eq = absurd $ FZNotFS eq
  f_inj (Just x) Nothing eq = absurd $ FZNotFS $ sym eq
  f_inj (Just x) (Just y) eq = cong $ FSInjective _ _ eq
  f_srj FZ = (Nothing ** Refl)
  f_srj (FS x) = (Just x ** Refl)

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

||| If a function has a left inverse, it is injective
||| NB: The converse is unprovable constructively
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

interface Inhabited t where
  inhabited : t

Inhabited () where
  inhabited = ()

Inhabited Bool where
  inhabited = True

Inhabited Nat where
  inhabited = Z

replicate_length : Inhabited a =>
                   (z : Nat) ->
                   (elem : a) ->
                   (\x => length x = z) (replicate z elem)
replicate_length Z el = Refl
replicate_length (S k) el = let rec = replicate_length k el in
                            rewrite rec in Refl

length_srj : Inhabited ty => Surjective (Prelude.List.length {a=ty})
length_srj = Srj length choose_z
  where choose_z z = (replicate z inhabited ** (replicate_length {a=ty} z inhabited))

interface Inhabited t => OneInhabitant t where
  one_inhabitant : (x : t) ->
                   (y : t) ->
                   x = y

OneInhabitant () where
  one_inhabitant () () = Refl

{- The below is MORALLY WRONG / non-total
OneInhabitant Bool where
  one_inhabitant True True = Refl
  one_inhabitant False False = Refl -}

unique_length : OneInhabitant ty =>
                (x : List ty) ->
                (y : List ty) ->
                (eq : length x = length y) ->
                x = y
unique_length [] [] eq = Refl
unique_length (x :: xs) [] eq with (length xs)
  | len = absurd $ SIsNotZ eq
unique_length [] (y :: ys) eq with (length ys)
  | len = absurd $ SIsNotZ $ sym eq
unique_length (x :: xs) (y :: ys) eq = let rec_eq = (one_inhabitant x y) in
                                       let rec_len = cong {f=Prelude.Nat.pred} eq in
                                       rewrite rec_eq in cong (unique_length xs ys rec_len)

length_inj : OneInhabitant ty => Injective (Prelude.List.length {a=ty})
length_inj = Inj length unique_length

length_bij : OneInhabitant ty => Bijective (Prelude.List.length {a=ty})
length_bij = from_inj_srj length length_inj length_srj

