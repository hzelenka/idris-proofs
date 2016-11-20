module Groups

import Functions

%default total
%access public export

interface Group (a : Type) (op : a -> a -> a) (e : a) (inv : a -> a) | a where
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

lassoc : Group a op e inv =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         (x `op` y) `op` z = x `op` (y `op` z)
lassoc x y z = associativity x y z

rassoc : Group a op e inv =>
         (x : a) ->
         (y : a) ->
         (z : a) ->
         x `op` (y `op` z) = (x `op` y) `op` z
rassoc x y z = sym $ associativity x y z

cancel_left : Group a op e inv =>
              (x : a) ->
              (y : a) ->
              (z : a) ->
              x `op` y = x `op` z ->
              y = z             
cancel_left {op} {e} {inv} x y z xy_eq_xz =
  let left     = lassoc {op} {e} {inv} (inv x) x y
      right    = lassoc {op} {e} {inv} (inv x) x z
      elim_inv = sym $ snd $ inverse {op} {e} {inv} x
      elim_e_l = sym $ snd $ identity {op} {e} {inv} y
      elim_e_r = sym $ snd $ identity {op} {e} {inv} z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      cong xy_eq_xz

cancel_right : Group a op e inv =>
               (x : a) ->
               (y : a) ->
               (z : a) ->
               y `op` x = z `op` x ->
               y = z
cancel_right {op} {e} {inv} x y z yx_eq_zx =
  let left     = rassoc {op} {e} {inv} y x (inv x)
      right    = rassoc {op} {e} {inv} z x (inv x)
      elim_inv = sym $ fst $ inverse {op} {e} {inv} x
      elim_e_l = sym $ fst $ identity {op} {e} {inv} y
      elim_e_r = sym $ fst $ identity {op} {e} {inv} z in
      rewrite elim_e_l in
      rewrite elim_e_r in
      rewrite elim_inv in
      rewrite left in 
      rewrite right in
      apply_cong where
   apply_cong : (y `op` x) `op` (inv x) = (z `op` x) `op` (inv x)
   apply_cong = (cong {f=(\val => val `op` (inv x))} yx_eq_zx)

inv_unique : Group a op e inv =>
             (x : a) ->
             (x' : a) ->
             (x `op` x' = e,
              x' `op` x = e) ->
             x' = inv x
inv_unique {op} {e} {inv} x x' inv_prf =
  cancel_left x x' (inv x) $ trans left_eq right_eq where
    left_eq : x `op` x' = e
    left_eq = fst inv_prf
    right_eq : e = x `op` (inv x)
    right_eq = sym $ fst $ inverse x

double_inv : Group a op e inv =>
             (x : a) ->
             x = inv (inv x)
double_inv {inv} x = let elims = inverse x
                     in inv_unique (inv x) x (snd elims, fst elims)

inv_sym : Group a op e inv =>
          inv x = x' ->
          x = inv x'
inv_sym equality = rewrite double_inv x in cong equality

interface Group a op e inv =>
          AbelianGroup (a : Type) (op : a -> a -> a) (e : a) (inv : a -> a)
          where
  commutativity : (x : a) ->
                  (y : a) ->
                  x `op` y = y `op` x
