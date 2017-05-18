module Valleys

%default total

-- I originally tried to do this by regular induction but that didn't work, so
-- I prove strong induction below. It may be useful for another Idris project
-- so feel free to use it!

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
  LTESucc $ lteNeqLT k j (fromLteSucc lte) $ \eq => neq (cong eq)

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

||| m <= n is preserved by addition
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

||| The "valley property" holds for a Nat n if, for all decreasing f with
||| f Z <= n, we can always find valleys of arbitrary length
ValleyProperty : Nat -> Type
ValleyProperty n' = (f : Nat -> Nat) ->
                    Decreasing f ->
                    (f Z) = n' ->
                    (m : Nat) ->
                    (position : Nat ** Valley (S m) f position)

||| The valley property holds (trivially) for Z
valleyBase : ValleyProperty Z
valleyBase f decr eq Z = (Z ** ValZ f Z)
valleyBase f (Decr f decr) eq (S k) =
  let (rec ** rec_prf) = valleyBase f (Decr f decr) eq k
  in (S rec ** ValS rec_prf $ trans (decrZConst f (Decr f decr) eq (S rec)) $
  sym (decrZConst f (Decr f decr) eq rec))

||| If the left-composition of a function with addition by some Nat has a
||| valley, then so does the function itself
shiftValley : (m, n, shift : Nat) ->
              (f : Nat -> Nat) ->
              Valley (S m) (\x => f (shift + x)) n ->
              Valley (S m) f (shift+n)
shiftValley m n Z f valley = valley
shiftValley Z n (S k) f (ValZ _ n) = ValZ f _
shiftValley (S m) (S n) (S k) f (ValS val eq) =
  let rec = shiftValley m n (S k) f val
  in rewrite sym (plusSuccRightSucc k n)
  in ValS rec $ trans (cong {f=f . S} (plusSuccRightSucc k n)) eq

||| (Strong) inductive step for the valley property
valleyInductive : (m : Nat) ->
                  (limit : Nat) ->
                  ((m' : Nat) ->
                   LTE m' limit ->
                   ValleyProperty m') ->
                  ValleyProperty (S limit)
valleyInductive _ limit valley_m f (Decr f decr) eq m
  with (eitherValleySmaller f (Decr f decr) (S limit) eq m)
    | Left valley = (m ** valley)
    | Right lt = f_valley where
      g : Nat -> Nat
      g = \x => f (m + x)
      g_decr : (x, y : Nat) -> LTE x y -> LTE (g y) (g x)
      g_decr x y lte = decr (m+x) (m+y) (addLeftLte x y m lte)
      g_valley : (n : Nat ** Valley (S m) g n)
      g_valley = valley_m (f m) (fromLteSucc lt) g (Decr g g_decr)
                 (cong {f=f} (plusZeroRightNeutral m)) m
      f_valley : (pos : Nat ** Valley (S m) f pos)
      f_valley = let (g_pos ** g_prf) = g_valley
                 in (m+g_pos ** shiftValley m g_pos m f g_prf)

||| The valley property holds for all natural numbers
valleyAllN : (m : Nat) -> ValleyProperty m
valleyAllN m = strongInduction ValleyProperty m valleyBase (valleyInductive m)

||| Cleaner version of the above
alwaysValley : (f : Nat -> Nat) ->
               Decreasing f ->
               (m : Nat) ->
               (position : Nat ** Valley (S m) f position)
alwaysValley f decr m = valleyAllN (f Z) f decr Refl m
