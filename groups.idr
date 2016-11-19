module Groups

import Functions

%default total

interface Group (a : Type) (op : a -> a -> a) (e : a) (inv : a -> a) where
  associativity : (x : a) ->
                  (y : a) ->
                  (z : a) ->
                  (x `op` y) `op` z = x `op` (y `op` z)
  identity : (x : a) ->
             (x `op` e = x,
              e `op` x = x)
  inverse : (x : a) ->
             (x `op` (inv x) = e,
              (inv x) `op` x = e)

id_unique : Group a op e inv =>
            (e' : a) ->
            ((x : a) ->
             (x `op` e' = x,
              e' `op` x = x)) ->
            e = e'
id_unique {op} {e} {inv} e' prf = trans (sym eq_prf_1) eq_prf_2 where
  eq_prf_1 : e `op` e' = e
  eq_prf_1 = fst $ prf e
  eq_prf_2 : e `op` e' = e'
  eq_prf_2 = snd $ identity {inv} e'

cancel_left : Group a op e inv =>
              (x : a) ->
              (y : a) ->
              (z : a) ->
              x `op` y = x `op` z ->
              y = z             
cancel_left {op} {e} {inv} x y z xy_eq_xz = exact where
  exact = let left     = associativity {op} {e} {inv} (inv x) x y
              right    = associativity {op} {e} {inv} (inv x) x z
              elim_inv = sym $ snd $ inverse {op} {e} {inv} x
              elim_e_l = sym $ snd $ identity {op} {e} {inv} y
              elim_e_r = sym $ snd $ identity {op} {e} {inv} z in
              rewrite elim_e_l in
              rewrite elim_e_r in
              rewrite elim_inv in
              rewrite left in 
              rewrite right in 
              cong xy_eq_xz

{- cancel_right : Group a op e inv =>
               (x : a) ->
               (y : a) ->
               (z : a) ->
               y `op` x = z `op` x ->
               y = z             
cancel_right {op} {e} {inv} x y z yx_eq_zx = exact where
  exact = let left     = sym $ associativity {op} {e} {inv} y x (inv x)
              right    = sym $ associativity {op} {e} {inv} z x (inv x)
              elim_inv = sym $ fst $ inverse {op} {e} {inv} x
              elim_e_l = sym $ fst $ identity {op} {e} {inv} y
              elim_e_r = sym $ fst $ identity {op} {e} {inv} z in
              rewrite elim_e_l in
              rewrite elim_e_r in
              rewrite elim_inv in
              rewrite left in 
              rewrite right in 
                      cong {f=(\v => op v (inv x))} yx_eq_zx -}

inv_unique : Group a op e inv =>
             (x : a) ->
             (x' : a) ->
             (x `op` x' = e,
              x' `op` x = e) ->
             x' = inv x

inv_sym : Group a op e inv =>
          inv x = x' ->
          inv x' = x
