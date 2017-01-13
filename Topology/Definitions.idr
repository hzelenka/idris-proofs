module Definitions

import Foundations.Functions
import Foundations.Sets

%default total
%access public export

||| Collection of subsets closed under unions and finite intersections
data Topology : Set a ->
                Set (Set a) ->
                Type where
  Top : (s : Set a) ->
        (t : Set (Set a)) ->
        Empty a # t ->
        s # t ->
        ((s1, s2 : Set a) ->
         (s1 # t) -> -- Unsure how to handle infinite unions
         (s2 # t) ->
         s1 \/ s2 # t) ->
        ((s1, s2 : Set a) ->
         (s1 # t) ->
         (s2 # t) ->
         s1 /\ s2 # t) ->
        Topology s t

||| Topology consisting of every subset
discreteTopology : (s : Set a) ->
                   (ps : Set (Set a)) ->
                   Powerset s ps ->
                   Topology s ps
discreteTopology (MkSet a s) (MkSet _ ps) (Pow _ _ prf) =
  Top _ _ empty full union intersection where
    empty : Empty a # MkSet _ ps
    empty = fst (prf _) $ emptySubset _
    full : MkSet a s # MkSet _ ps
    full = fst (prf _) $ subsetRefl _
    union : (s1, s2 : Set a) ->
            s1 # MkSet _ ps ->
            s2 # MkSet _ ps ->
            s1 \/ s2 # MkSet _ ps
    union s1 s2 (IsElem s1 _ prf1) (IsElem s2 _ prf2) =
      fst (prf _) $ unionPrsSubset s1 s2 _ exact1 exact2 where
        exact1 = snd (prf _) $ IsElem _ _ prf1
        exact2 = snd (prf _) $ IsElem _ _ prf2
    intersection : (s1, s2 : Set a) ->
                   s1 # (MkSet _ ps) ->
                   s2 # (MkSet _ ps) ->
                   s1 /\ s2 # (MkSet _ ps)
    intersection s1 s2 (IsElem s1 _ prf1) (IsElem s2 _ prf2) =
      fst (prf _) $ intersectionPrsSubset s1 s2 _ exact1 exact2 where
        exact1 = snd (prf _) $ IsElem _ _ prf1
        exact2 = snd (prf _) $ IsElem _ _ prf2

||| Topology consisting only of the two obligatory subsets
indiscreteTopology : (s : Set a) ->
                     (t : Set (Set a)) ->
                     Empty a # t ->
                     s # t ->
                     ((s' : Set a) ->
                      s' # t ->
                      Either (s' = Empty a) (s' = s)) ->
                     Topology s t
indiscreteTopology {a} s t empty full prf =
  Top _ _ empty full union intersection where
    union : (s1, s2 : Set a) -> s1 # t -> s2 # t -> s1 \/ s2 # t
    union s1 s2 elem1 elem2 with (prf s1 elem1, prf s2 elem2)
      | (Left l1, Left l2)   = rewrite l1 in ?unionhole_1
      | (Left l1, Right r1)  = rewrite l1 in rewrite r1 in ?unionhole_2
      | (Right r1, Left l1)  = rewrite r1 in rewrite l1 in ?unionhole_3
      | (Right r1, Right r2) = rewrite r1 in rewrite r2 in ?unionhole_4
    intersection : (s1, s2 : Set a) -> s1 # t -> s2 # t -> s1 /\ s2 # t
    intersection s1 s2 elem1 elem2 with (prf s1 elem1, prf s2 elem2)
      | (Left l1, Left l2)   = ?interhole_1
      | (Left l1, Right r1)  = ?interhole_2
      | (Right r1, Left l1)  = ?interhole_3
      | (Right r1, Right r2) = ?interhole_4
