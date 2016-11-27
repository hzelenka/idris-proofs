module Foundations

%default total
%access public export

Relation : (a : Type) -> Type
Relation a = a -> a -> Type

-- Both LinearOrder and PartialOrder (implicitly TotalOrder as well) have
-- double negative elimination, which is necessary later to prove that linear
-- and total orders are the negation of one another. This approach seems more
-- "honest" than using believe_me.

data LinearOrder : Relation a ->
                   Type where
  IsLinear : (r : Relation a) ->
             (double_neg : (x : a) ->
                           (y : a) ->
                           Not (Not (x `r` y)) ->
                           x `r` y) ->
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
              (double_neg : (x : a) ->
                           (y : a) ->
                           Not (Not (x `r` y)) ->
                           x `r` y) ->
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
not_linear_total r (IsLinear r dng irf asm trs cmp con) =
  IsTotal q (IsPartial q dng' rfl' trs' asm') ttl' where
    q : Relation a
    q = (\x, y => Not (r x y))
    rfl' = irf
    trs' x y z x_q_y y_q_z x_r_z with (cmp x z x_r_z y)
      | Left x_r_y  = x_q_y x_r_y
      | Right y_r_z = y_q_z y_r_z
    asm' = con
    ttl' x y = ?ttl_hole
    dng' x y contra x_r_y = ?dng_hole

not_total_linear : (r : Relation a) ->
                   TotalOrder r ->
                   LinearOrder (\x, y => Not (r x y))
not_total_linear r (IsTotal r (IsPartial r dng rfl trs ans) ttl) =
  IsLinear q dng' irf asm trs' cmp con where
    q : Relation a
    q = (\x, y => Not (r x y))
    irf x x_r_x = x_r_x $ rfl x
    asm x y (x_r_y_void, y_r_x_void) with (ttl x y)
      | Left x_r_y  = x_r_y_void x_r_y
      | Right y_r_x = y_r_x_void y_r_x
    trs' x y z x_r_y_void y_r_z_void x_r_z with (ttl x y)
      | Left x_r_y  = x_r_y_void x_r_y
      | Right y_r_x = y_r_z_void $ trs y x z y_r_x x_r_z
    cmp x z x_r_z_void y with (ttl x z)
      | Left x_r_z  = ?x_hole
      | Right z_r_x = ?z_hole
    con = ?con_hole
    dng' = ?dng_hole
