module Church

%default total
%access public export

Church : Type -> Type
Church a = (a -> a) -> a -> a

CZ : Church a
CZ = (\f => (\x => x))

CS : Church a -> Church a
CS = (\m => (\f => (\x => f (m f x))))

nat_to_church : Nat -> Church Nat
nat_to_church Z = CZ
nat_to_church (S k) = CS $ nat_to_church k

church_to_nat : Church Nat -> Nat
church_to_nat m = m S Z

nat_church_nat : (m : Nat) ->
                 m = church_to_nat (nat_to_church m)
nat_church_nat Z = Refl
nat_church_nat (S k) = let rec = nat_church_nat k in cong rec

church_nat_church : (m : Church Nat) ->
                    (f : Nat -> Nat) ->
                    (x : Nat) ->
                    m f x = (nat_to_church (church_to_nat m)) f x
church_nat_church m f x = ?eq_hole

Pred : Church a -> Church a
Pred = (\m => (\f => (\x => m ?pred_hole ?pred_hole_2)))

infixl 8 \+\,\-\
infixl 9 \*\

(\+\) : Church a -> Church a -> Church a
(\+\) = (\m => (\n => (\f => (\x => m f (n f x)))))

church_plus_is_plus : (m : Nat) ->
                      (n : Nat) ->
                      m + n = (nat_to_church m \+\ nat_to_church n) S Z
church_plus_is_plus Z Z = Refl
church_plus_is_plus Z (S k) = let rec = church_plus_is_plus Z k in cong rec
church_plus_is_plus (S k) j = let rec = church_plus_is_plus k j in cong rec

(\*\) : Church a -> Church a -> Church a
(\*\) = (\m => (\n => (\f => (\x => m (n f) x))))

church_times_is_times : (m : Nat) ->
                        (n : Nat) ->
                        m * n = (nat_to_church m \*\ nat_to_church n) S Z
church_times_is_times Z _ = Refl
church_times_is_times (S k) Z = church_times_is_times k Z
church_times_is_times (S k) (S j) =
  let rec = church_times_is_times k (S j) in
  rewrite sym rec in
  ?church_times_hole_3
