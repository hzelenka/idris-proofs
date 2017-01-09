module Groupoids

import Categories.Definitions

%default total
%access public export

||| A groupoid is a category in which every morphism is an isomorphism
||| Algebraically, a groupoid is a set endowed with a binary operator
interface Category obj => Groupoid obj where
  ||| Needs to be decidable whether two morphisms may be composed
  decComp : {o1, o2, o3, o4 : obj} ->
            (f : mor o1 o2) ->
            (g : mor o3 o4) ->
            Dec (o2 = o3)
  ||| Given an arbitrary morphism
  justIso : {o1, o2 : obj} ->
            (m : mor o1 o2) ->
            Isomorphism {obj} m

||| Rewrite a morphism type if possible
compHelper : Groupoid obj =>
             {o1, o2, o3, o4 : obj} ->
             (f : mor o1 o2) ->
             (g : mor o3 o4) ->
             Maybe (mor o2 o4)
compHelper {obj} f g with (decComp {obj} f g)
  | Yes prf = Just $ rewrite prf in g
  | No _ = Nothing

||| Attempt to compose two groupoid morphisms (Nothing means nonconformable)
groupoidComp : Groupoid obj =>
               {o1, o2, o3, o4 : obj} ->
               (f : mor o1 o2) ->
               (g : mor o3 o4) ->
               Maybe (mor o1 o4)
groupoidComp {obj} f g with (compHelper {obj} f g)
  | Just g' = Just $ catComp {obj} f g'
  | Nothing = Nothing

||| Provided composition is defined, it is associative
groupoidCompAssoc : Groupoid obj =>
                    {o1, o2, o3, o4, o5, o6 : obj} ->
                    (f : mor o1 o2) ->
                    (g : mor o3 o4) ->
                    (h : mor o5 o6) ->
                    map (groupoidComp {obj} f) (groupoidComp {obj} g h) =
                    map (\x => groupoidComp {obj} x h) (groupoidComp {obj} f g)
groupoidCompAssoc {obj} f g h with (decComp {obj} f g, decComp {obj} g h)
  | (No fg_contra, _)        = ?groupoidcompassochole_1
  | (_, No gh_contra)        = ?groupoidcompassochole_2
  | (Yes fg_prf, Yes gh_prf) = ?groupoidcompassochole_3

||| A group is a groupoid with just one object
||| Algebraically, a group is a set endowed with an associative binary operator
||| and inverse elements
interface Groupoid obj => Group obj where
  justObj : (o : obj ** (o' : obj) ->
                        o' = o)
