module Groups

import Functions

||| Algebraic group with the properties:
||| (1) closure (2) identity (3) invertibility (4) associativity
data Group : (a -> a -> a) -> Type where
  ||| Single constructor. Identity and invertibility are checked simultaneously
  ||| b/c inverses need to return the identity. Closure is guaranteed by the
  ||| type signature of op.
  MkGrp : (op : a -> a -> a) ->
          (identity : (e : a ** ((x : a) ->
                       (x `op` e = x,
                       (x' : a) -> x `op` x' = e)))) ->
          (associativity : ((x1 : a) ->
                            (x2 : a) ->
                            (x3 : a) ->
                            (x1 `op` x2) `op` x3 = x1 `op` (x2 `op` x3))) ->
          Group op

-- Get the identity element out of a group
e : {op : a -> a -> a} -> Group op -> a
e (MkGrp _ (id_elem ** _) _) = id_elem

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
                (Group op) ->
                (constaint : a -> Bool) ->
                Type where
