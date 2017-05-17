module Valleys

%default total

data Decreasing : (Nat -> Nat) -> Type where
  Decr : (f : Nat -> Nat) ->
         ((m, n : Nat) ->
          LTE m n ->
          LTE (f n) (f m)) ->
         Decreasing f

||| Valley m f n means there exists a valley of length m in f ending at n
data Valley : Nat -> (Nat -> Nat) -> Nat -> Type where
  ||| There is trivially a valley of length 1 at any point
  ValZ : (f : Nat -> Nat) ->
         (n : Nat) ->
         Valley (S Z) f n
  ||| If a valley of length m ends at n, and f (S n) = f n, there is also a
  ||| valley of length (S m) ending at (S n)
  ValS : (v : Valley m f n) ->
         f (S n) = f n ->
         Valley (S m) f (S n)

lteNeqLT : (m, n : Nat) ->
           LTE m n ->
           (m = n -> Void) ->
           LT m n
lteNeqLT Z Z lte neq = absurd $ neq Refl
lteNeqLT Z (S k) lte neq = LTESucc LTEZero
lteNeqLT (S k) Z lte neq impossible
lteNeqLT (S k) (S j) lte neq =
  LTESucc $ lteNeqLT k j (fromLteSucc lte) (\eq => neq (cong eq))

bothLTEEq : (m, n : Nat) ->
            LTE m n ->
            LTE n m ->
            m = n
bothLTEEq Z Z _ _ = Refl
bothLTEEq Z (S k) lte1 lte2 impossible
bothLTEEq (S k) Z lte1 lte2 impossible
bothLTEEq (S k) (S j) lte1 lte2 =
  cong {f=S} $ bothLTEEq k j (fromLteSucc lte1) (fromLteSucc lte2)

eitherValleySmaller : (f : Nat -> Nat) ->
                      Decreasing f ->
                      (f_Z : Nat) ->
                      f Z = f_Z ->
                      (m : Nat) ->
                      Either (Valley (S m) f m) (LT (f m) f_Z)
eitherValleySmaller f (Decr f decr) f_Z f_Z_eq Z = Left $ ValZ f Z
eitherValleySmaller f (Decr f decr) f_Z f_Z_eq (S k)
  with (eitherValleySmaller f (Decr f decr) f_Z f_Z_eq k)
    | Right lt    = Right $ lteTransitive (LTESucc (decr k (S k)
                            (lteSuccRight lteRefl))) lt
    | Left valley with (decEq (f (S k)) (f k))
      | Yes eq = Left $ ValS valley eq
      | No neq = rewrite sym f_Z_eq in
                 Right $ lteNeqLT _ _ (decr Z (S k) LTEZero) $
                 \eq => neq $ bothLTEEq (f (S k)) (f k) (decr k (S k)
                              (lteSuccRight lteRefl)) $
                              rewrite eq in decr 0 k LTEZero

lteZeroIsZero : (m : Nat) ->
                LTE m Z ->
                m = Z
lteZeroIsZero Z _ = Refl

decrZConst : (f : Nat -> Nat) ->
             Decreasing f ->
             f Z = Z ->
             (m : Nat) ->
             f m = Z
decrZConst f (Decr f decr) eq k =
  lteZeroIsZero (f k) $ rewrite sym eq in decr 0 k LTEZero

baseCase : (f : Nat -> Nat) ->
           Decreasing f ->
           f Z = Z ->
           (m : Nat) ->
           Valley (S m) f m
baseCase f _ eq Z = ValZ f Z
baseCase f (Decr f decr) eq (S k) =
  let rec = baseCase f (Decr f decr) eq k
  in ValS rec $ trans (decrZConst f (Decr f decr) eq (S k)) $
                sym (decrZConst f (Decr f decr) eq k)

inductiveStep : (limit : Nat) ->
                ((f : Nat -> Nat) ->
                  Decreasing f ->
                  (k : Nat) ->
                  LTE k limit ->
                  f Z = k ->
                  (m : Nat) ->
                  (n : Nat ** Valley (S m) f n)) ->
                (g : Nat -> Nat) ->
                Decreasing g ->
                (m : Nat) ->
                g Z = S limit ->
                (n : Nat ** Valley (S m) g n)
inductiveStep limit inductive g decr m eq with (eitherValleySmaller g decr (g Z) Refl m)
  | Left val = (m ** val)
  | Right lt = let (rec ** rec_prf) = inductive (g . (m+)) ?decreasinghole (g m)
                                      (fromLteSucc (rewrite sym eq in lt))
                                      (cong {f=g} (plusZeroRightNeutral m)) m
               in (m + rec ** ?righthole1)

StrongInductionHolds : Nat -> Type
StrongInductionHolds n = (p : Nat -> Type) ->
                         (j : Nat) ->
                         LTE j n ->
                         p Z ->
                         ((limit : Nat) ->
                          ((m : Nat) ->
                          LTE m limit ->
                          p m) ->
                          p (S limit)) ->
                         p j

strongInductionHoldsBase : StrongInductionHolds Z
strongInductionHoldsBase p Z _ base _ = base

strongInductionInductive : (q : Nat) ->
                           StrongInductionHolds q ->
                           StrongInductionHolds (S q)
strongInductionInductive q ind_q p Z lte base inductive = base
strongInductionInductive q strong_ind_q p (S k) lte base ind_s_q =
  ind_s_q k $ \m, lte' => strong_ind_q p m (lteTransitive lte' (fromLteSucc lte)) base $ \limit, ind => ind_s_q limit ind

strongInductionAllN : (n : Nat) ->
                      StrongInductionHolds n
strongInductionAllN Z = strongInductionHoldsBase
strongInductionAllN (S k) = strongInductionInductive k $ strongInductionAllN k

strongInduction : (p : Nat -> Type) ->
                  (n : Nat) ->
                  p Z ->
                  ((limit : Nat) ->
                   ((m : Nat) ->
                    LTE m limit ->
                    p m) ->
                    p (S limit)) ->
                  p n
strongInduction p n base inductive =
  let strongInductionPrf = strongInductionAllN n
  in strongInductionPrf p n lteRefl base inductive

alwaysValley : (f : Nat -> Nat) ->
               Decreasing f ->
               (m, f_Z : Nat) ->
               f Z = f_Z ->
               (n : Nat ** Valley (S m) f n)

