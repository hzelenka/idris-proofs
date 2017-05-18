module Valleys

%default total

||| A weakly decreasing function on natural numbers
data Decreasing : (Nat -> Nat) -> Type where
  ||| Given Nats m and n with m <= n, f n <= f m
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

||| If m <= n but m /= n, then m < n
lteNeqLT : (m, n : Nat) ->
           LTE m n ->
           (m = n -> Void) ->
           LT m n
lteNeqLT Z Z lte neq = absurd $ neq Refl
lteNeqLT Z (S k) lte neq = LTESucc LTEZero
lteNeqLT (S k) Z lte neq impossible
lteNeqLT (S k) (S j) lte neq =
  LTESucc $ lteNeqLT k j (fromLteSucc lte) (\eq => neq (cong eq))

||| If m <= n and n <= m, then m = n
bothLTEEq : (m, n : Nat) ->
            LTE m n ->
            LTE n m ->
            m = n
bothLTEEq Z Z _ _ = Refl
bothLTEEq Z (S k) lte1 lte2 impossible
bothLTEEq (S k) Z lte1 lte2 impossible
bothLTEEq (S k) (S j) lte1 lte2 =
  cong {f=S} $ bothLTEEq k j (fromLteSucc lte1) (fromLteSucc lte2)

||| The <= is preserved by addition
addLeftLte : (x, y, z : Nat) ->
             LTE x y ->
             LTE (z + x) (z + y)
addLeftLte x y Z lte = lte
addLeftLte x y (S k) lte = LTESucc $ addLeftLte x y k lte

||| There either exists a valley of length m starting at Z and ending at m or
||| f m < f Z (strictly)
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

||| Only Z is <= Z
lteZeroIsZero : (m : Nat) ->
                LTE m Z ->
                m = Z
lteZeroIsZero Z _ = Refl

||| A decreasing function with f Z = Z is constant
decrZConst : (f : Nat -> Nat) ->
             Decreasing f ->
             f Z = Z ->
             (m : Nat) ->
             f m = Z
decrZConst f (Decr f decr) eq k =
  lteZeroIsZero (f k) $ rewrite sym eq in decr 0 k LTEZero

{-||| There (trivially) exists a valley of any length for a 
baseCase : (f : Nat -> Nat) ->
           Decreasing f ->
           f Z = Z ->
           (m : Nat) ->
           (n : Nat ** Valley (S m) f n)
baseCase f _ eq Z = (Z ** ValZ f Z)
baseCase f (Decr f decr) eq (S k) =
  let (rec ** rec_prf) = baseCase f (Decr f decr) eq k
  in (S rec ** ValS rec_prf $ trans (decrZConst f (Decr f decr) eq (S rec)) $
                              sym (decrZConst f (Decr f decr) eq rec))

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
inductiveStep limit inductive g (Decr _ decr) m eq
  with (eitherValleySmaller g (Decr _ decr) (g Z) Refl m)
    | Left val = (m ** val)
    | Right lt =
      let (rec ** rec_prf) = inductive (g . (m+))
                             (Decr _ (\x, y, lte => decr (m+x) (m+y)
                                                    (addLeftLte x y m lte)))
                             (g m) (fromLteSucc (rewrite sym eq in lt))
                             (cong {f=g} (plusZeroRightNeutral m)) m
                             in (m + rec ** ?righthole1) -}

||| Strong induction holds for a particular Nat n if:
|||   for all properties p of Nats
|||   for all j <= n
|||   p Z holds
|||   given some nat m such that p m' holds for all m' <= m, p (S m) also holds
||| it can be concluded that p j holds.
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

||| Strong induction holds for Z trivially
strongInductionHoldsBase : StrongInductionHolds Z
strongInductionHoldsBase p Z _ base _ = base

||| If strong induction holds for a Nat q, it also holds for S q
strongInductionInductive : (q : Nat) ->
                           StrongInductionHolds q ->
                           StrongInductionHolds (S q)
strongInductionInductive q ind_q p Z lte base inductive = base
strongInductionInductive q strong_ind_q p (S k) lte base ind_s_q =
  ind_s_q k $ \m, lte' => strong_ind_q p m (lteTransitive lte'
                          (fromLteSucc lte)) base $
                          \limit, ind => ind_s_q limit ind

||| Strong induction holds for all Nats
strongInductionAllN : (n : Nat) ->
                      StrongInductionHolds n
strongInductionAllN Z = strongInductionHoldsBase
strongInductionAllN (S k) = strongInductionInductive k $ strongInductionAllN k

||| Terser version of strong induction
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
  strongInductionAllN n p n lteRefl base inductive

alwaysValleyInductive : (limit : Nat) ->
                        (f : Nat -> Nat) ->
                        Decreasing f ->
                        (m, f_Z : Nat) ->
                        f_Z = f Z ->
                        LTE (f_Z) limit ->
                        (n : Nat ** Valley (S m) f n)
alwaysValleyInductive = ?valleyinductiveholee
