module Relations

%default total
%access public export

Relation : (a : Type) -> Type
Relation a = a -> a -> Type

-- Note that relations need to be decidable for some proofs later

data LinearOrder : Relation a ->
                   Type where
  IsLinear : (r : Relation a) ->
             (decidable : (x : a) ->
                          (y : a) ->
                          Dec (x `r` y)) ->
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
              (decidable : (x : a) ->
                           (y : a) ->
                           Dec (x `r` y)) ->
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
            (already_partial : PartialOrder r) -> -- NB: decidability in here
            (totality : (x : a) ->
                        (y : a) ->
                        Either (x `r` y) (y `r` x)) ->
            TotalOrder r

not_linear_total : (r : Relation a) ->
                   LinearOrder r ->
                   TotalOrder (\x, y => Not (r x y))
not_linear_total r (IsLinear r dec irf asm trs cmp con) =
  IsTotal q (IsPartial q dec' rfl' trs' asm') ttl' where
    q : Relation a
    q = (\x, y => Not (r x y))
    rfl' = irf
    trs' x y z x_q_y y_q_z x_r_z with (cmp x z x_r_z y)
      | Left x_r_y  = x_q_y x_r_y
      | Right y_r_z = y_q_z y_r_z
    asm' = con
    ttl' x y with (dec x y)
      | Yes prf with (dec y x)
        | Yes prf'   = absurd $ asm x y (prf, prf')
        | No contra' = Right contra'
      | No contra = Left contra
    dec' x y with (dec x y)
      | Yes prf   = No (\contra => contra prf) -- Introduce double negative
      | No contra = Yes contra

not_total_linear : (r : Relation a) ->
                   TotalOrder r ->
                   LinearOrder (\x, y => Not (r x y))
not_total_linear r (IsTotal r (IsPartial r dec rfl trs ans) ttl) =
  IsLinear q dec' irf' asm' trs' cmp' con' where
    q : Relation a
    q = (\x, y => Not (r x y))
    irf' x x_r_x = x_r_x $ rfl x
    asm' x y (x_r_y_void, y_r_x_void) with (ttl x y)
      | Left x_r_y  = x_r_y_void x_r_y
      | Right y_r_x = y_r_x_void y_r_x
    trs' x y z x_r_y_void y_r_z_void x_r_z with (ttl x y)
      | Left x_r_y  = x_r_y_void x_r_y
      | Right y_r_x = y_r_z_void $ trs y x z y_r_x x_r_z
    cmp' x z x_r_z_void y with (dec x y)
      | Yes prf with (dec y z)
        | Yes prf'   = absurd $ x_r_z_void $ trs x y z prf prf'
        | No contra' = Right contra'
      | No contra = Left contra
    con' x y r_x_y_dbl_neg r_y_x_dbl_neg with (dec x y)
      | Yes prf with (dec y x)
        | Yes prf'   = ans x y prf prf'
        | No contra' = absurd $ r_y_x_dbl_neg contra'
      | No contra = absurd $ r_x_y_dbl_neg contra
    dec' x y with (dec x y)
      | Yes prf   = No (\contra => contra prf) -- Introduce double negative
      | No contra = Yes contra
