module Groupoids

import Categories.Definitions

%default total
%access public export

||| A groupoid is a category in which every morphism is an isomorphism
||| Algebraically, a groupoid is a set endowed with a binary operator
interface Category obj mor =>
          Groupoid (obj : Type) (mor : obj -> obj -> Type) where
  ||| Needs to be decidable whether two morphisms may be composed
  decComp : (f : mor o1 o2) ->
            (g : mor o3 o4) ->
            Dec (o2 = o3)
  ||| Given an arbitrary morphism
  justIso : (m : mor o1 o2) ->
            Isomorphism {mor} m

||| Rewrite a morphism type if possible
compHelper : Groupoid obj mor =>
             (f : mor o1 o2) ->
             (g : mor o3 o4) ->
             Maybe (mor o2 o4)
compHelper {mor} f g with (decComp {mor} f g)
  | Yes prf = Just $ rewrite prf in g
  | No _ = Nothing

||| Attempt to compose two groupoid morphisms (Nothing means nonconformable)
groupoidComp : Groupoid obj mor =>
               (f : mor o1 o2) ->
               (g : mor o3 o4) ->
               Maybe (mor o1 o4)
groupoidComp {mor} f g with (compHelper {mor} f g)
  | Just g' = Just $ catComp {mor} f g'
  | Nothing = Nothing

||| Provided composition is defined, it is associative
groupoidCompAssoc : Groupoid obj mor =>
                    (f : mor o1 o2) ->
                    (g : mor o3 o4) ->
                    (h : mor o5 o6) ->
                    map (groupoidComp {mor} f) (groupoidComp {mor} g h) =
                    map (\x => groupoidComp {mor} x h) (groupoidComp {mor} f g)
groupoidCompAssoc {mor} f g h with (decComp {mor} f g, decComp {mor} g h)
  | (No fg_contra, _)        = ?groupoidcompassochole_1
  | (_, No gh_contra)        = ?groupoidcompassochole_2
  | (Yes fg_prf, Yes gh_prf) = ?groupoidcompassochole_3

||| A group is a groupoid with just one object
||| Algebraically, a group is a set endowed with an associative binary operator
||| and inverse elements
interface Groupoid obj mor =>
          Group (obj : Type) (mor : obj -> obj -> Type) where
  justObj : (o : obj ** (o' : obj) ->
                        o' = o)
