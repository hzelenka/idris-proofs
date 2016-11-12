module Groups

import Functions

||| Useful shorthand for later
data Id : a -> (a -> a -> a) -> Type where
  ||| Need to check inverse at the same time
  IdPrf : {a : Type} ->
          (op : a -> a -> a) ->
          (e : a ** (x : a) ->
                    ((x `op` e = x,
                      e `op` x = x),
                    (x `op` x' = e,
                     x' `op` x = e))) ->
          Id e op

||| Algebraic group with the properties:
||| (1) closure (2) identity (3) invertibility (4) associativity
data Group : (a -> a -> a) -> Type where
  ||| Closure is guaranteed by the type signature of op
  MkGrp : (op : a -> a -> a) ->
          Id e op ->
          (associativity : ((x1 : a) ->
                            (x2 : a) ->
                            (x3 : a) ->
                            (x1 `op` x2) `op` x3 = x1 `op` (x2 `op` x3))) ->
          Group op

-- Get the identity element out of a group
e : {op : a -> a -> a} -> Group op -> a
e (MkGrp _ (IdPrf _ (id_elem ** _)) _) = id_elem

id_unique : {op : a -> a -> a} ->
            (g : Group op) ->
            {e1 : a} ->
            {e2 : a} ->
            Id e1 op ->
            Id e2 op ->
            e1 = e2
id_unique gp (IdPrf _ (x ** eq_fn_1)) (IdPrf _ (y ** eq_fn_2)) =
  let eq_pf_1 = fst $ fst $ eq_fn_1 y
      eq_pf_2 = sym $ snd $ fst $ eq_fn_2 x
      eq_pf_3 = trans eq_pf_2 eq_pf_1
  in ?id_hole

||| Group that also has commutativity for all elements
data AbelianGroup : (a -> a -> a) -> Type where
  ||| Check it's a group, then that it has commutativity
  MkAbl : (op : a -> a -> a) ->
          Group op ->
          (commutativity : ((x : a) ->
                            (y : a) ->
                            x `op` y = y `op` x)) ->
          AbelianGroup op

data Subgroup : {a : Type} ->
                {op : a -> a -> a} ->
                (g : Group op) ->
                (constaint : a -> Bool) ->
                Type where
  MkSubgp : (g : Group op) ->
            (c : a -> Bool) ->
            (identity : c (e g) = True) ->
            (closure : (x : a ** c x = True) ->
                       (y : a ** c y = True) ->
                       (c (x `op` y) = True)) ->
            Subgroup g constraint
