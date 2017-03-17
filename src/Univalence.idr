module Univalence

%default total
%access public export

infixl 1 ~~
data (~~) : (t : Type) ->
            (s : Type) ->
            Type where
  Equiv : (f : (t -> s) **
           g : (s -> t) **
           (x : t) ->
           g (f x) ~=~ x) ->
          t ~~ s

equalToEquiv : (a ~=~ b) -> (a ~~ b)
equalToEquiv {a} {b} eq = Equiv equiv where
  equiv = rewrite eq in (id ** id ** \x => Refl)

equivToEqual : (a ~~ b) -> (a ~=~ b)
equivToEqual = believe_me

univalence : (a ~=~ b) ~~ (a ~~ b)
univalence {a} {b} = Equiv {t=a~=~b} {s=a~~b} (equalToEquiv ** equivToEqual ** ?univhole)
