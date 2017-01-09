module Sets

import Data.Vect
import Foundations.Functions

%default total
%access public export

data Set : Type -> Type where
  MkSet : (a : Type) ->
          (p : a -> Type) ->
          Set a

getProp : Set a -> a -> Type
getProp (MkSet a p) = p

compl : Set a -> Set a
compl (MkSet a p) = MkSet a $ \x => Not (p x)

infixl 2 #
||| Set element
data (#) : a ->
           Set a ->
           Type where
  IsElem : (x : a) ->
           (s : Set a) ->
           getProp s x ->
           x # s

infixl 1 :<:
||| Subset
data (:<:) : Set a ->
             Set a ->
             Type where
  IsSubset : (s1 : Set a) ->
             (s2 : Set a) ->
             ((x : a) ->
              x # s1 ->
              x # s2) ->
             s1 :<: s2

||| If s1 is a subset of s2 and s2 is a subset of s3, s1 is a subset of s3
subsetTransitive : (s1 : Set a) ->
                   (s2 : Set a) ->
                   (s3 : Set a) ->
                   s1 :<: s2 ->
                   s2 :<: s3 ->
                   s1 :<: s3
subsetTransitive s1 s2 s3 (IsSubset _ _ prf1) (IsSubset _ _ prf2) =
  IsSubset _ _ (\x, elem_prf => prf2 x (prf1 x elem_prf))

infixl 1 :=:
||| Set equality
data (:=:) : Set a ->
             Set a ->
             Type where
  SubsetEq : (s1 : Set a) ->
             (s2 : Set a) ->
             ((x : a) ->
              x # s1 <-> x # s2) ->
             s1 :=: s2

infixl 5 \/
||| Set union
(\/) : Set a -> Set a -> Set a
(MkSet a p) \/ (MkSet a q) = MkSet a (\x => Either (p x) (q x))

||| Set union is commutative up to set equivalence
unionCommutes : (s1 : Set a) ->
                (s2 : Set a) ->
                s1 \/ s2 :=: s2 \/ s1
unionCommutes (MkSet a p) (MkSet a q) =
  SubsetEq _ _ $ \x => (\(IsElem _ _ elem_prf) => IsElem _ _ $ mirror elem_prf,
                        \(IsElem _ _ elem_prf) => IsElem _ _ $ mirror elem_prf)

infixl 6 /\
||| Set intersection
(/\) : Set a -> Set a -> Set a
(MkSet a p) /\ (MkSet a q) = MkSet a (\x => (p x, q x))

||| Set intersection is commutative up to set equivalence
intersectionCommutes : (s1 : Set a) ->
                       (s2 : Set a) ->
                       s1 /\ s2 :=: s2 /\ s1
intersectionCommutes (MkSet a p) (MkSet a q) =
  SubsetEq _ _ $ \x => (\(IsElem _ _ elem_prf) => IsElem _ _ $ swap elem_prf,
                        \(IsElem _ _ elem_prf) => IsElem _ _ $ swap elem_prf)

infixl 4 ~\
||| Set difference
(~\) : Set a -> Set a -> Set a
(MkSet a p) ~\ (MkSet a q) = MkSet a (\x => (p x, Not (q x)))

||| Negation of p and negation of q implies negation of p or q
de_morgan_1 : (x : a) ->
              (s1 : Set a) ->
              (s2 : Set a) ->
              x # compl s1 /\ compl s2 ->
              x # compl (s1 \/ s2)
de_morgan_1 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ (\y => case y of Left p_prf => fst prf p_prf
                              Right q_prf => snd prf q_prf)

||| Negation of p or q implies negation of p and negation of q
de_morgan_2 : (x : a) ->
              (s1 : Set a) ->
              (s2 : Set a) ->
              x # compl (s1 \/ s2) ->
              x # compl s1 /\ compl s2
de_morgan_2 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ (\p_prf => prf (Left p_prf), \q_prf => prf (Right q_prf))

||| Negation of p or negation of q implies negation of p and q
de_morgan_3 : (x : a) ->
              (s1 : Set a) ->
              (s2 : Set a) ->
              x # compl s1 \/ compl s2 ->
              x # compl (s1 /\ s2)
de_morgan_3 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ (\(p_prf,q_prf) => case prf of Left p_contra => p_contra p_prf
                                            Right q_contra => q_contra q_prf)

-- De Morgan's 4th law (the converse of the above) is unprovable constructively

||| Set of all subsets
data Powerset : (s : Set a) ->
                Set (Set a) ->
                Type where
  IsPowerset : (s : Set a) ->
               (ps : Set (Set a)) ->
               ((s' : Set a) ->
                s' :<: s <-> s' # ps) ->
               Powerset s ps

||| The powerset is unique up to set equivalence
powersetUniq : (s : Set a) ->
               (ps : Set (Set a)) ->
               (ps' : Set (Set a)) ->
               Powerset s ps ->
               Powerset s ps' ->
               ps :=: ps'
powersetUniq (MkSet a s_prop) (MkSet _ ps_prop) (MkSet _ ps_prop')
             (IsPowerset _ _ ps_prf) (IsPowerset _ _ ps_prf') =
  SubsetEq _ _ (\x => (fwd, bwd)) where
    fwd : x # MkSet (Set a) ps_prop -> x # MkSet (Set a) ps_prop'
    fwd elem_prf with (ps_prf x, ps_prf' x)
      | ((_, ps_bwd), (ps_fwd', _)) = ps_fwd' $ ps_bwd elem_prf
    bwd : x # MkSet (Set a) ps_prop' -> x # MkSet (Set a) ps_prop
    bwd elem_prf with (ps_prf x, ps_prf' x)
      | ((ps_fwd, _), (_, ps_bwd')) = ps_fwd $ ps_bwd' elem_prf

||| Union of a collection of sets
unionOver : Vect n (Set a) ->
            Set a
unionOver [] = MkSet a (\_ => Void) -- Union over empty set is the empty set
unionOver (x :: xs) = x \/ unionOver xs

||| Intersection of a collection of sets
intersectionOver : Vect n (Set a) ->
                   Set a
intersectionOver [] = MkSet a (\_ => ()) -- Intr over empty set is the universe
intersectionOver (x :: xs) = x /\ intersectionOver xs
