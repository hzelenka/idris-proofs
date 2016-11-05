module Functions

%access public export
%default total

data Injective : (domain -> codomain) -> Type where
  Inj : (f : domain -> codomain) ->
        (prf : (x : domain) ->
          (y : domain) ->
          (eq : f x = f y) ->
          (x = y)) ->
        Injective f

data Surjective : (domain -> codomain) -> Type where
  Srj : (f : domain -> codomain) ->
        (prf : (z : codomain) ->
          (x : domain ** f x = z)) ->
        Surjective f

data Bijective : (a -> b) -> Type where
  Bij : (f : domain -> codomain) ->
        Injective f ->
        Surjective f ->
        Bijective f

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
  where choose_z z = ( replicate z (inhabited {t=ty}) ** (replicate_length {a=ty} z inhabited))

interface Inhabited t => OneInhabitant t where
  one_inhabitant : (x : t) ->
                   (y : t) ->
                   x = y

OneInhabitant () where
  one_inhabitant () () = Refl

-- The below is MORALLY WRONG / non-total
{- OneInhabitant Bool where
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
length_inj = Inj length choose_x_y_st_eq
  where choose_x_y_st_eq = unique_length

length_bij : OneInhabitant ty => Bijective (Prelude.List.length {a=ty})
length_bij = Bij length length_inj length_srj
