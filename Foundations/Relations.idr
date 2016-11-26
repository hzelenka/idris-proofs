module Foundations

%default total
%access public export

Relation : (a : Type) -> Type
Relation a = a -> a -> Type

data LinearOrder : Relation a ->
                   Type where
  IsLinear : (r : Relation a) ->
             (irreflexivity : (x : a) ->
                              Not (x `r` x)) ->
             (asymmetry : (x : a) ->
                          (y : a) ->
                          Not (x `r` y, y `r` x)) ->
             (transitivity : (x : a) ->
                             (y : a) ->
                             (z : a) ->
                             x `r` y ->
                             y `r` z ->
                             x `r` z) ->
             (comparison : (x : a) ->
                           (z : a) ->
                           x `r` z ->
                           (y : a) ->
                           Either (x `r` y) (y `r` z)) ->
             (connectedness : (x : a) ->
                              (y : a) ->
                              Not (x `r` y) ->
                              Not (y `r` x) ->
                              x = y) ->
             LinearOrder r

data PartialOrder : Relation a ->
                    Type where
  IsPartial : (r : Relation a) ->
              (reflexivity : (x : a) ->
                             x `r` x) ->
              (transitivity : (x : a) ->
                              (y : a) ->
                              (z : a) ->
                              x `r` y ->
                              y `r` z ->
                              x `r` z) ->
              (antisymmetry : (x : a) ->
                              (y : a) ->
                              x `r` y ->
                              y `r` x ->
                              x = y) ->
              PartialOrder r

data TotalOrder : Relation a ->
                  Type where
  IsTotal : (r : Relation a) ->
            (already_partial : PartialOrder r) ->
            (totality : (x : a) ->
                        (y : a) ->
                        Either (x `r` y) (y `r` x)) ->
            TotalOrder r

not_linear_total : (r : Relation a) ->
                   LinearOrder r ->
                   TotalOrder (\x, y => Not (r x y))
not_linear_total {a} r (IsLinear r irf asm trs cmp con) =
  IsTotal q (IsPartial q rfl' trs' asm') ttl' where
    q : Relation a
    q = (\x, y => Not (r x y))
    rfl' : (x : a) -> x `q` x
    rfl' = irf
    trs' : (x : a) -> (y : a) -> (z : a) -> (x `q` y) -> (y `q` z) -> (x `q` z)
    trs' x y z x_q_y y_q_z x_r_z with (cmp x z x_r_z y)
      | Left x_r_y  = x_q_y x_r_y
      | Right y_r_z = y_q_z y_r_z
    asm' : (x : a) -> (y : a) -> x `q` y -> y `q` x -> x = y
    asm' = con
    ttl' : (x : a) -> (y : a) -> Either (x `q` y) (y `q` x)
    ttl' x y = ?ttl_hole
