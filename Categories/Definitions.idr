module Definitions

%default total
%access public export

||| Using obj as the determining parameter feels _wrong_ somehow, but it makes
||| some code terser
interface Category (obj : Type) (mor : obj -> obj -> Type) | obj where
  catId : (o : obj) ->
          mor o o
  catComp : (f : mor o1 o2) ->
            (g : mor o2 o3) ->
            mor o1 o3
  catCompAssoc : (f : mor o1 o2) ->
                 (g : mor o2 o3) ->
                 (h : mor o3 o4) ->
                  f `catComp` (g `catComp` h) =
                 (f `catComp` g) `catComp` h
  catIdIsId : (f : mor o1 o2) ->
              (f `catComp` (catId o2) = f,
               (catId o1) `catComp` f = f)

||| Left-cancellable morphism
data Monomorphism : Category obj mor =>
                    mor o1 o2 ->
                    Type where
  Monic : Category obj mor =>
          (f : mor o1 o2) ->
          ((o3 : obj) ->
           (g : mor o2 o3) ->
           (h : mor o2 o3) ->
           catComp {mor} f g = catComp {mor} f h ->
           g = h) ->
          Monomorphism {mor} f

||| Section f g means g is right inverse to f
data Section : Category obj mor =>
               mor o1 o2 ->
               mor o2 o1 ->
               Type where
  Sect : Category obj mor =>
         (f : mor o1 o2) ->
         (g : mor o2 o1) ->
         catComp {mor} f g = catId o1 ->
         Section {mor} f g

||| All morphisms that aare sections of other morphisms are monic
||| Note that the converse does not hold in some categories
sectIsMonic : Category obj mor =>
                (f : mor o1 o2) ->
                (g : mor o2 o1) ->
                Section {mor} f g ->
                Monomorphism {mor} g
sectIsMonic {mor} f g (Sect f g sec_prf) = Monic g monic where
  monic o' h i eq =
    let step1 = cong {f=catComp {mor} f} eq
        step2 = trans (sym (catCompAssoc {mor} f g h)) step1
        step3 = trans step2 $ catCompAssoc {mor} f g i
        step4 = replace {P=\val=>catComp {mor} val h = catComp {mor} val i}
                                                        sec_prf step3
        step5 = trans (sym (snd (catIdIsId {mor} h))) step4
        step6 = trans step5 $ snd $ catIdIsId {mor} i
    in step6

||| Right-cancellable morphism
data Epimorphism : Category obj mor =>
                   mor o2 o3 ->
                   Type where
  Epi : Category obj mor =>
        (f : mor o2 o3) ->
        ((o1 : obj) ->
         (g : mor o1 o2) ->
         (h : mor o1 o2) ->
         catComp {mor} g f = catComp {mor} h f ->
         g = h) ->
        Epimorphism {mor} f

||| Retraction f g means g is left inverse to f
data Retraction : Category obj mor =>
                  mor o2 o1 ->
                  mor o1 o2 ->
                  Type where
  Retr : Category obj mor =>
         (f : mor o1 o2) ->
         (g : mor o2 o1) ->
         catComp {mor} g f = catId o2 ->
         Retraction {mor} f g

||| All morphisms that are retractions of other morphisms are epi
||| Note that the converse does not hold in some categories
retrIsEpi : Category obj mor =>
              (f : mor o1 o2) ->
              (g : mor o2 o1) ->
              Retraction {mor} f g ->
              Epimorphism {mor} g
retrIsEpi {mor} f g (Retr f g retr_prf) = Epi g epi where
  epi o' h i eq =
    let step1 = cong {f=\val => catComp {mor} val f} eq
        step2 = trans (catCompAssoc {mor} h g f) step1
        step3 = trans step2 $ sym $ catCompAssoc {mor} i g f
        step4 = replace {P=\val=>catComp {mor} h val = catComp {mor} i val}
                                                        retr_prf step3
        step5 = trans (sym (fst (catIdIsId {mor} h))) step4
        step6 = trans step5 $ fst $ catIdIsId {mor} i
    in step6

||| Morphism admitting a two-sided inverse
data Isomorphism : Category obj mor =>
                   (f : mor o1 o2) ->
                   Type where
  Iso : Category obj mor =>
        (f : mor o1 o2) ->
        (g : mor o2 o1) ->
        Section {mor} f g ->
        Retraction {mor} f g ->
        Isomorphism {mor} f

||| Get the inverse out of an isomorphism
invIso : Category obj mor =>
         (f : mor o1 o2) ->
         Isomorphism {mor} f ->
         (g : mor o2 o1 ** (Section {mor} f g, Retraction {mor} f g))
invIso f (Iso f g sect retr) = (g ** (sect, retr))

||| The inverse of an isomorphism is unique
invIsoUniq : Category obj mor =>
             (f : mor o1 o2) ->
             (iso : Isomorphism {mor} f) ->
             (g : mor o2 o1) ->
             Section {mor} f g ->
             Retraction {mor} g f ->
             g = fst $ invIso f iso
invIsoUniq {mor} f (Iso f g sect (Retr f g retr)) g' (Sect f g' sect') retr' =
  let step1 = sym $ fst $ catIdIsId {mor} g
      step2 = trans step1 $ cong {f=catComp {mor} g} $ sym sect'
      step3 = trans step2 $ catCompAssoc {mor} g f g'
      step4 = trans step3 $ cong {f=\val=>catComp {mor} val g'} $ retr
      step5 = trans step4 $ snd $ catIdIsId {mor} g'
  in sym step5
