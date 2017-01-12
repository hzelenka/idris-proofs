module Sets

import Data.Vect
import Foundations.Functions

%default total
%access public export

data Set : Type -> Type where
  MkSet : (a : Type) ->
          (p : a -> Type) ->
          Set a

Empty : (a : Type) -> Set a
Empty a = MkSet a $ \_ => Void

Universe : (a : Type) -> Set a
Universe a = MkSet a $ \_ => ()

getProp : Set a -> a -> Type
getProp (MkSet a p) = p

compl : Set a -> Set a
compl (MkSet a p) = MkSet a $ \x => Not $ p x

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
  IsSubset : (s1, s2 : Set a) ->
             ((x : a) ->
              x # s1 ->
              x # s2) ->
             s1 :<: s2

||| The empty set is a subset of all sets
emptySubset : (s : Set a) ->
              Empty a :<: s
emptySubset {a} s = IsSubset (Empty a) s $ \x, (IsElem x _ void) => absurd void

||| Being a subset is reflexive
subsetRefl : (s : Set a) ->
             s :<: s
subsetRefl s = IsSubset s s $ \_ => id

||| Being a subset is transitive
subsetTransitive : (s1, s2, s3 : Set a) ->
                   s1 :<: s2 ->
                   s2 :<: s3 ->
                   s1 :<: s3
subsetTransitive s1 s2 s3 (IsSubset s1 s2 prf1) (IsSubset s2 s3 prf2) =
  IsSubset s1 s3 $ \x, elem => prf2 x $ prf1 x elem

infixl 1 :=:
||| Set equivalence
data (:=:) : Set a ->
             Set a ->
             Type where
  Equiv : (s1, s2 : Set a) ->
          ((x : a) ->
           x # s1 <-> x # s2) ->
          s1 :=: s2

||| Set equivalence is reflexive
equivRefl : (s1 : Set a) ->
            s1 :=: s1
equivRefl s1 = Equiv s1 s1 $ \_ => (id, id)

||| Set equivalence is transitive
equivTrans : (s1, s2, s3 : Set a) ->
             s1 :=: s2 ->
             s2 :=: s3 ->
             s1 :=: s3
equivTrans s1 s2 s3 (Equiv s1 s2 iff_12) (Equiv s2 s3 iff_23) =
  Equiv s1 s3 $
    \x => (\elem => fst (iff_23 x) $ fst (iff_12 x) elem,
           \elem => snd (iff_12 x) $ snd (iff_23 x) elem)

||| Set equivalence is symmetric
equivSym : (s1, s2 : Set a) ->
           s1 :=: s2 ->
           s2 :=: s1
equivSym s1 s2 (Equiv s1 s2 iff) = Equiv s2 s1 $ \x => swap $ iff x

||| If two sets are propositionally equal, they must be equivalent as sets
||| The converse has extensionality issues: s1 and s2 might share the same
||| elements while their properties are defined differently
propEqIsSetEquiv : (s1, s2 : Set a) ->
                   s1 = s2 ->
                   s1 :=: s2
propEqIsSetEquiv s1 s2 eq = rewrite eq in equivRefl s2

infixl 5 \/
||| Set union
(\/) : Set a -> Set a -> Set a
(MkSet a p) \/ (MkSet a q) = MkSet a $ \x => Either (p x) (q x)

||| The empty set is an identity under set union
unionEmptyNeutral : (s : Set a) ->
                    (s \/ Empty a :=: s, Empty a \/ s :=: s)
unionEmptyNeutral (MkSet s prop) = (left, right) where
  left = Equiv _ _ $
    \x => (\(IsElem _ _ elem) => IsElem _ _ (case elem of Left l => l),
           \(IsElem _ _ elem) => IsElem _ _ $ Left elem)
  right = Equiv _ _ $
    \x => (\(IsElem _ _ elm_prf) => IsElem _ _ (case elm_prf of Right r => r),
           \(IsElem _ _ elem) => IsElem _ _ $ Right elem)

||| Set union is associative up to set equivalence
unionAssoc : (s1, s2, s3 : Set a) ->
             s1 \/ (s2 \/ s3) :=: (s1 \/ s2) \/ s3
unionAssoc (MkSet a s1) (MkSet a s2) (MkSet a s3) = Equiv _ _ exact where  
  helper1 : Either x (Either y z) -> Either (Either x y) z
  helper1 (Left l) = Left $ Left l
  helper1 (Right (Left rl)) = Left $ Right rl
  helper1 (Right (Right rr)) = Right rr
  helper2 : Either (Either x y) z -> Either x (Either y z)
  helper2 (Left (Left ll)) = Left ll
  helper2 (Left (Right lr)) = Right $ Left lr
  helper2 (Right r) = Right $ Right r
  exact x = (\(IsElem _ _ elem) => IsElem _ _ $ helper1 elem,
             \(IsElem _ _ elem) => IsElem _ _ $ helper2 elem)

||| Set union is commutative up to set equivalence
unionCommutes : (s1, s2 : Set a) ->
                s1 \/ s2 :=: s2 \/ s1
unionCommutes (MkSet a p) (MkSet a q) =
  Equiv _ _ $ \x => (\(IsElem _ _ elem) => IsElem _ _ $ mirror elem,
                     \(IsElem _ _ elem) => IsElem _ _ $ mirror elem)

||| The union of two subsets is another subset
unionPrsSubset : (s1, s2, s3 : Set a) ->
                 s1 :<: s3 ->
                 s2 :<: s3 ->
                 s1 \/ s2 :<: s3
unionPrsSubset (MkSet _ s1) (MkSet _ s2) (MkSet _ s3)
               (IsSubset _ _ prf1) (IsSubset _ _ prf2) =
  IsSubset _ _ $ \x, (IsElem x _ elem) =>
    case elem of Left l => prf1 x $ IsElem x _ l
                 Right r => prf2 x $ IsElem x _ r

infixl 6 /\
||| Set intersection
(/\) : Set a -> Set a -> Set a
(MkSet a p) /\ (MkSet a q) = MkSet a (\x => (p x, q x))

||| The universe is an identity under set intersection
intersectionEmptyNeutral : (s : Set a) ->
                           (s /\ Universe a :=: s, Universe a /\ s :=: s)
intersectionEmptyNeutral (MkSet s prop) = (left, right) where
  left = Equiv _ _ $
    \x => (\(IsElem _ _ elem) => IsElem _ _ $ fst elem,
           \(IsElem _ _ elem) => IsElem _ _ (elem, ()))
  right = Equiv _ _ $
    \x => (\(IsElem _ _ elem) => IsElem _ _ $ snd elem,
           \(IsElem _ _ elem) => IsElem _ _ ((), elem))

||| Set intersection is associative up to set equivalence
intersectionAssoc : (s1, s2, s3 : Set a) ->
                    s1 /\ (s2 /\ s3) :=: (s1 /\ s2) /\ s3
intersectionAssoc (MkSet a s1) (MkSet a s2) (MkSet a s3) =
  Equiv _ _ exact where
    exact x =
      (\(IsElem x _ (prf1, prf2, prf3)) => IsElem x _ ((prf1, prf2), prf3),
       \(IsElem x _ ((prf1, prf2), prf3)) => IsElem x _ (prf1, prf2, prf3))

||| Set intersection is commutative up to set equivalence
intersectionCommutes : (s1, s2 : Set a) ->
                       s1 /\ s2 :=: s2 /\ s1
intersectionCommutes (MkSet a p) (MkSet a q) =
  Equiv _ _ $ \x => (\(IsElem _ _ elem) => IsElem _ _ $ swap elem,
                     \(IsElem _ _ elem) => IsElem _ _ $ swap elem)

||| The intersection of two subsets is another subset
intersectionPrsSubset : (s1, s2, s3 : Set a) ->
                        s1 :<: s3 ->
                        s2 :<: s3 ->
                        s1 /\ s2 :<: s3
intersectionPrsSubset (MkSet _ s1) (MkSet _ s2) (MkSet _ s3)
                      (IsSubset _ _ prf1) (IsSubset _ _ prf2) =
  IsSubset _ _ $ \x, (IsElem x _ elem) => prf1 x $ IsElem x _ $ fst elem

infixl 4 ~\
||| Set difference
(~\) : Set a -> Set a -> Set a
(MkSet a p) ~\ (MkSet a q) = MkSet a $ \x => (p x, Not $ q x)

infixl 4 /~\
||| Symmetric difference
(/~\) : Set a -> Set a -> Set a
s1 /~\ s2 = (s1 ~\ s2) \/ (s2 ~\ s1)

||| Negation of p and negation of q implies negation of p or q
de_morgan_1 : (x : a) ->
              (s1, s2 : Set a) ->
              x # compl s1 /\ compl s2 ->
              x # compl (s1 \/ s2)
de_morgan_1 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ $ \y => case y of Left p_prf => fst prf p_prf
                               Right q_prf => snd prf q_prf

||| Negation of p or q implies negation of p and negation of q
de_morgan_2 : (x : a) ->
              (s1, s2 : Set a) ->
              x # compl (s1 \/ s2) ->
              x # compl s1 /\ compl s2
de_morgan_2 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ (\p_prf => prf (Left p_prf), \q_prf => prf (Right q_prf))

||| Negation of p or negation of q implies negation of p and q
de_morgan_3 : (x : a) ->
              (s1, s2 : Set a) ->
              x # compl s1 \/ compl s2 ->
              x # compl (s1 /\ s2)
de_morgan_3 x (MkSet a p) (MkSet a q) (IsElem x _ prf) =
  IsElem x _ $ \(p_prf,q_prf) => case prf of Left p_contra => p_contra p_prf
                                             Right q_contra => q_contra q_prf

-- De Morgan's 4th law (the converse of the above) is unprovable constructively

||| Set union is distributive over symmetric difference
unionDistrSymDiff : (s1, s2, s3 : Set a) ->
                    s1 /\ (s2 /~\ s3) :=: s1 /\ s2 /~\ s1 /\ s3
unionDistrSymDiff (MkSet a s1) (MkSet a s2) (MkSet a s3) = Equiv _ _ exact where
  exact x = (\(IsElem x _ elem) => IsElem x _
              (case elem of
                    (prf1, Left (prf2, contra3)) => Left ((prf1, prf2),
                      \(_, prf3) => contra3 prf3)
                    (prf1, Right (prf3, contra2)) => Right ((prf1, prf3),
                      \(_, prf2) => contra2 prf2)),
             \(IsElem x _ elem) => IsElem x _
              (case elem of
                    Left ((prf1, prf2), contra13) => (prf1, Left (prf2,
                      \prf3 => contra13 (prf1, prf3)))
                    Right ((prf1, prf3), contra12) => (prf1, Right (prf3,
                      \prf2 => contra12 (prf1, prf2)))))
-- Above proof is fairly ugly and hard to follow: it looks kind of Lispy, which
-- is not necessarily a bad thing but not what I want to go for in Idris! I
-- will fix it up later

||| Set of sets
Family : (a : Type) -> Type
Family a = Set $ Set a

||| Data constructor for families
MkFamily : (a : Type) -> (Set a -> Type) -> Family a
MkFamily a p = MkSet (Set a) p

||| Set of all subsets
data Powerset : Set a ->
                Family a ->
                Type where
  Pow : (s : Set a) ->
               (ps : Family a) ->
               ((s' : Set a) ->
                s' :<: s <-> s' # ps) ->
               Powerset s ps

||| The powerset is unique up to set equivalence
powersetUniq : (s : Set a) ->
               (ps, ps' : Family a) ->
               Powerset s ps ->
               Powerset s ps' ->
               ps :=: ps'
powersetUniq (MkSet a s_prop) (MkSet _ ps_prop) (MkSet _ ps_prop')
             (Pow _ _ ps_prf) (Pow _ _ ps_prf') =
  Equiv _ _ (\x => (fwd, bwd)) where
    fwd : x # MkFamily a ps_prop -> x # MkFamily a ps_prop'
    fwd elem with (ps_prf x, ps_prf' x)
      | ((_, ps_bwd), (ps_fwd', _)) = ps_fwd' $ ps_bwd elem
    bwd : x # MkFamily a ps_prop' -> x # MkFamily a ps_prop
    bwd elem with (ps_prf x, ps_prf' x)
      | ((ps_fwd, _), (_, ps_bwd')) = ps_fwd $ ps_bwd' elem

||| Union of a collection of sets
unionOver : Vect n (Set a) ->
            Set a
unionOver = foldr (\/) (Empty a)

||| Intersection of a collection of sets
intersectionOver : Vect n (Set a) ->
                   Set a
intersectionOver = foldr (/\) (Universe a)
