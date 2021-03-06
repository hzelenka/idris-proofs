module DecSets

%default total
%access public export

||| Set with a guarantee that the property is decidable
record DecSet a where
  constructor MkSet
  prop : (x : a) -> Type
  dec : (x : a) -> Dec (prop x)

||| Set of all values not satisfying the property of another set
compl : DecSet a -> DecSet a
compl s = MkSet (\x => Not (prop s x)) dec_prf where
  dec_prf x with (dec s x)
    | Yes prf   = No (\contra => contra prf)
    | No contra = Yes contra

infixl 2 #
||| DecSet element
data (#) : a ->
           DecSet a ->
           Type where
  IsElem : (x : a) ->
           (s : DecSet a) ->
           prop s x ->
           x # s

infixl 1 :<:
||| DecSet subset
data (:<:) : DecSet a ->
             DecSet a ->
             Type where
  IsSubset : (s1 : DecSet a) ->
             (s2 : DecSet a) ->
             ((x : a) ->
              x # s1 ->
              x # s2) ->
              s1 :<: s2

infixl 1 :=:
||| DecSet equality
data (:=:) : DecSet a ->
             DecSet a ->
             Type where
  SubsetEq : (s1 : DecSet a) ->
             (s2 : DecSet a) ->
             (fwd : ((x : a) ->
                     x # s1 ->
                     x # s2)) ->
             (bwd : ((x : a) ->
                     x # s2 ->
                     x # s1)) ->
             s1 :=: s2

infixl 5 \/
||| DecSet union
(\/) : DecSet a -> DecSet a -> DecSet a
p \/ q = MkSet (\x => Either (prop p x) (prop q x)) dec_prf where
  dec_prf el with (dec p el, dec q el)
    | (Yes p_prf, Yes q_prf)     = Yes $ Left p_prf
    | (Yes p_prf, No q_contra)   = Yes $ Left p_prf
    | (No p_contra, Yes q_prf)   = Yes $ Right q_prf
    | (No p_contra, No q_contra) = No (\e => case e of
                                        Left prf => p_contra prf
                                        Right prf => q_contra prf)

infixl 6 /\
||| DecSet intersection
(/\) : DecSet a -> DecSet a -> DecSet a
p /\ q = MkSet (\x => (prop p x, prop q x)) dec_prf where
  dec_prf el with (dec p el, dec q el)
    | (Yes p_prf, Yes q_prf)     = Yes (p_prf, q_prf)
    | (Yes p_prf, No q_contra)   = No (\(_,q) => q_contra q)
    | (No p_contra, Yes q_prf)   = No (\(p, _) => p_contra p)
    | (No p_contra, No q_contra) = No (\(p, _) => p_contra p)

infixl 4 ~\
||| DecSet difference
(~\) : DecSet a -> DecSet a -> DecSet a
p ~\ q = MkSet (\x => (prop p x, Not (prop q x))) dec_prf where
  dec_prf el with (dec p el, dec q el)
    | (Yes p_prf, Yes q_prf) = No (\(_,q_contra) => q_contra q_prf)
    | (Yes p_prf, No q_contra) = Yes (p_prf, q_contra)
    | (No p_contra, Yes q_prf) = No (\(p_prf,_) => p_contra p_prf)
    | (No p_contra, No q_contra) = No (\(p_prf,_) => p_contra p_prf)

-- TO DO: Symmetric difference

||| Negation of p and negation of p implies negation of p or q
de_morgan_1 : (x : a) ->
              (p : DecSet a) ->
              (q : DecSet a) ->
              x # compl p /\ compl q ->
              x # compl (p \/ q)
de_morgan_1 x (MkSet prop_p dec_p) (MkSet prop_q dec_q) (IsElem x _ prf)
  with (dec_p x, dec_q x)
    | (Yes p_prf, Yes q_prf)     = absurd $ fst prf p_prf
    | (Yes p_prf, No q_contra)   = absurd $ fst prf p_prf
    | (No p_contra, Yes q_prf)   = absurd $ snd prf q_prf
    | (No p_contra, No q_contra) = IsElem _ _ cases where
      cases : Either (prop_p x) (prop_q x) -> Void
      cases (Left p_prf) = p_contra p_prf
      cases (Right q_prf) = q_contra q_prf

||| Negation of p or q implies negation of p and negation of q
de_morgan_2 : (x : a) ->
              (p : DecSet a) ->
              (q : DecSet a) ->
              x # compl (p \/ q) ->
              x # compl p /\ compl q
de_morgan_2 x (MkSet prop_p dec_p) (MkSet prop_q dec_q) (IsElem x _ prf)
  with (dec_p x, dec_q x)
    | (Yes p_prf, Yes q_prf)     = absurd $ prf $ Left p_prf
    | (Yes p_prf, No q_contra)   = absurd $ prf $ Left p_prf
    | (No p_contra, Yes q_prf)   = absurd $ prf $ Right q_prf
    | (No p_contra, No q_contra) = IsElem _ _ (p_contra, q_contra)

||| Negation of p or negation of q implies negation of p and q
de_morgan_3 : (x : a) ->
              (p : DecSet a) ->
              (q : DecSet a) ->
              x # compl p \/ compl q ->
              x # compl (p /\ q)
de_morgan_3 x (MkSet prop_p dec_p) (MkSet prop_q dec_q) (IsElem x _ prf)
  with (dec_p x, dec_q x) proof p
    | (Yes p_prf, Yes q_prf)     = absurd $ cases prf where
       cases : Either (prop_p x -> Void) (prop_q x -> Void) -> Void
       cases (Left p_absurd) = p_absurd p_prf
       cases (Right q_absurd) = q_absurd q_prf
    | (Yes p_prf, No q_contra)   = IsElem _ _ (\(_,q_prf) => q_contra q_prf)
    | (No p_contra, Yes q_prf)   = IsElem _ _ (\(p_prf,_) => p_contra p_prf)
    | (No p_contra, No q_contra) = IsElem _ _ cases where
      cases : (prop_p x, prop_q x) -> Void
      cases (p_prf, q_prf) = case prf of Left p_absurd => p_absurd p_prf
                                         Right q_absurd => q_absurd q_prf

||| Negation of p and q implies negation of p or negation of q
de_morgan_4 : (x : a) ->
              (p : DecSet a) ->
              (q : DecSet a) ->
              x # compl (p /\ q) ->
              x # compl p \/ compl q
de_morgan_4 x (MkSet prop_p dec_p) (MkSet prop_q dec_q) (IsElem x _ prf)
  with (dec_p x, dec_q x)
    | (Yes p_prf, Yes q_prf)     = absurd $ prf (p_prf, q_prf)
    | (Yes p_prf, No q_contra)   = IsElem _ _ (Right q_contra)
    | (No p_contra, Yes q_prf)   = IsElem _ _ (Left p_contra)
    | (No p_contra, No q_contra) = IsElem _ _ (Left p_contra)
