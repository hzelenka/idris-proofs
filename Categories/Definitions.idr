module Definitions

%default total
%access public export

infixr 1 >>>
interface Category (obj : Type) (mph : Type) where
  dom : mph -> obj
  cod : mph -> obj
  (>>>) : mph -> mph -> Maybe mph
  conformable : (m1 : mph) ->
                (m2 : mph) ->
                cod m1 = dom m2 ->
                m1 >>> m2 = Just m3
  conformable_dom_cod : (m1 : mph) ->
                        (m2 : mph) ->
                        m1 >>> m2 = Just m3 ->
                        (dom m3 = dom m1, cod m3 = cod m2)
  unconformable : (m1 : mph) ->
                  (m2 : mph) ->
                  Not (cod m1 = dom m2) ->
                  m1 >>> m2 = Nothing
  comp_assoc : (m1 : mph) ->
               (m2 : mph) ->
               (m3 : mph) ->
               m1 >>> m2 = Just m12 ->
               m2 >>> m3 = Just m23 ->
               m12 >>> m3 = m1 >>> m23
  idn : obj -> mph
  idn_dom_cod : (o : obj) ->
                (dom (idn o) = o, cod (idn o) = o)
  idn_right : (m : mph) ->
              o = cod m ->
              m >>> idn o = Just m
  idn_left : (m : mph) ->
              o = dom m ->
              idn o >>> m = Just m

{-data InitialObject : Category o m =>
                     o ->
                     Type where
  IsInitial : (init : o) ->
              (other : o) ->
              (m1 : mph ** (dom m1 = init, cod m1 = other)) ->
              (m2 : mph ** (dom m1 = init, cod m1 = other)) ->
              m1 = m2 -}
