module ClassicalAxioms

||| A fun problem I found in Software Foundations (which itself got it from
||| Coq'Art): prove that the following axioms of classical logic are equivalent
||| See bottom of http://www.seas.upenn.edu/~bcpierce/sf/current/Logic.html

PeirceLemma : Type
PeirceLemma = (a, b : Type) ->
              ((a -> b) -> a) -> a

DoubleNegativeElimination : Type
DoubleNegativeElimination = (a : Type) ->
                            ((a -> Void) -> Void) ->
                            a

DeMorganFourth : Type
DeMorganFourth = (a, b : Type) ->
                 (((a -> Void), (b -> Void)) -> Void) ->
                 Either a b

ImpliesToOr : Type
ImpliesToOr = (a, b : Type) ->
              (a -> b) ->
              Either (a -> Void) b

ExcludedMiddle : Type
ExcludedMiddle = (a : Type) ->
                 Either a (a -> Void)

peirceDoubleNeg : PeirceLemma -> DoubleNegativeElimination
peirceDoubleNeg peirce a not_not_a =
  peirce a Void $ \not_a => absurd $ not_not_a not_a

doubleNegDeMorgan : DoubleNegativeElimination -> DeMorganFourth
doubleNegDeMorgan double_neg a b hyp = double_neg (Either a b) exact where
  exact : (Either a b -> Void) -> Void
  exact not_or = absurd $ hyp (\a_prf => not_or $ Left a_prf,
                               \b_prf => not_or $ Right b_prf)

deMorganFourthImpliesToOr : DeMorganFourth -> ImpliesToOr
deMorganFourthImpliesToOr dm4 a b a_to_b = dm4 (a -> Void) b exact where
  contra : (b -> Void) -> (a -> Void)
  contra not_b a_prf = absurd $ not_b $ a_to_b a_prf
  exact : ((a -> Void) -> Void, b -> Void) -> Void
  exact (not_not_a, not_b) = absurd $ not_not_a $ contra not_b

impliesToOrExcludedMiddle : ImpliesToOr -> ExcludedMiddle
impliesToOrExcludedMiddle impl a = mirror $ impl a a id

excludedMiddlePeirce : ExcludedMiddle -> PeirceLemma
excludedMiddlePeirce excl a b a_b_a =
  case excl a of Left a_prf => a_prf
                 Right not_a => a_b_a $ \a_prf => absurd $ not_a a_prf
