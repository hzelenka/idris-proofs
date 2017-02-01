module Definitions

%default total
%access public export

||| obj is the only parameter b/c multi-parameter interfaces are frustrating
interface Category obj where
  ||| Possibly uninhabited type for each pair of objects
  mor : obj ->
        obj ->
        Type
  ||| Provide an identity morphism for every object
  catId : (o : obj) ->
          mor o o
  ||| Compose two conformable morphisms into a new morphism
  catComp : (f : mor o1 o2) ->
            (g : mor o2 o3) ->
            mor o1 o3
  ||| Composition of morphisms is associative
  catCompAssoc : (f : mor o1 o2) ->
                 (g : mor o2 o3) ->
                 (h : mor o3 o4) ->
                  f `catComp` (g `catComp` h) =
                 (f `catComp` g) `catComp` h
  ||| The identity morphism is in fact an identity
  catIdIsId : (f : mor o1 o2) ->
              (f `catComp` (catId o2) = f,
               (catId o1) `catComp` f = f)

||| There is only one identity arrow for each object
idUniq : Category obj =>
         (o : obj) ->
         (id' : mor o o) ->
         Either ((f : mor o o') ->
                 catComp {obj} id' f = f)
                ((f : mor o' o) ->
                 catComp {obj} f id' = f) ->
         id' = catId o
idUniq {obj = obj} o id' (Left prf) = ?iduniqhole_1
idUniq {obj = obj} o id' (Right prf) = ?iduniqhole_2

||| Left-cancellable morphism
data Monomorphism : Category obj =>
                    {o1, o2 : obj} ->
                    mor o1 o2 ->
                    Type where
  ||| Show that f . g = f . h implies g = h
  Monic : Category obj =>
          (f : mor o1 o2) ->
          ((o3 : obj) ->
           (g : mor o2 o3) ->
           (h : mor o2 o3) ->
           catComp {obj} f g = catComp {obj} f h ->
           g = h) ->
          Monomorphism {obj} f

||| Section f g means g is right inverse to f
data Section : Category obj =>
               {o1, o2 : obj} ->
               mor o1 o2 ->
               mor o2 o1 ->
               Type where
  ||| Show that f . g = id
  Sect : Category obj =>
         (f : mor o1 o2) ->
         (g : mor o2 o1) ->
         catComp {obj} f g = catId {obj} o1 ->
         Section {obj} f g

||| All morphisms that are sections of other morphisms are monic
||| Note that the converse does not hold in some categories
sectIsMonic : Category obj =>
              {o1, o2 : obj} ->
              (f : mor o1 o2) ->
              (g : mor o2 o1) ->
              Section {obj} f g ->
              Monomorphism {obj} g
sectIsMonic {obj} f g (Sect f g sec_prf) = Monic g monic where
  monic o' h i eq =
    let step1 = trans (sym (catCompAssoc {obj} f g h)) $ cong eq
        step2 = trans step1 $ catCompAssoc {obj} f g i
        step3 = replace {P=\val=>catComp {obj} val h = catComp {obj} val i}
                                                        sec_prf step2
        step4 = trans (sym (snd (catIdIsId {obj} h))) step3
        step5 = trans step4 $ snd $ catIdIsId {obj} i
    in step5

||| Right-cancellable morphism
data Epimorphism : Category obj =>
                   {o2, o3 : obj} ->
                   mor o2 o3 ->
                   Type where
  ||| Show that g . f = h . f implies g = h
  Epi : Category obj =>
        (f : mor o2 o3) ->
        ((o1 : obj) ->
         (g : mor o1 o2) ->
         (h : mor o1 o2) ->
         catComp {obj} g f = catComp {obj} h f ->
         g = h) ->
        Epimorphism {obj} f

||| Retraction f g means g is left inverse to f
data Retraction : Category obj =>
                  {o1, o2 : obj} ->
                  mor o2 o1 ->
                  mor o1 o2 ->
                  Type where
  ||| Show that g . f = id
  Retr : Category obj =>
         (f : mor o1 o2) ->
         (g : mor o2 o1) ->
         catComp {obj} g f = catId {obj} o2 ->
         Retraction {obj} f g

||| All morphisms that are retractions of other morphisms are epi
||| Note that the converse does not hold in some categories
retrIsEpi : Category obj =>
            {o1, o2 : obj} ->
            (f : mor o1 o2) ->
            (g : mor o2 o1) ->
            Retraction {obj} f g ->
            Epimorphism {obj} g
retrIsEpi {obj} f g (Retr f g retr_prf) = Epi g epi where
  epi o' h i eq =
    let step1 = cong {f=\val => catComp {obj} val f} eq
        step2 = trans (catCompAssoc {obj} h g f) step1
        step3 = trans step2 $ sym $ catCompAssoc {obj} i g f
        step4 = replace {P=\val=>catComp {obj} h val = catComp {obj} i val}
                                                        retr_prf step3
        step5 = trans (sym (fst (catIdIsId {obj} h))) step4
        step6 = trans step5 $ fst $ catIdIsId {obj} i
    in step6

||| Morphism admitting a two-sided inverse
data Isomorphism : Category obj =>
                   {o1, o2 : obj} ->
                   (f : mor o1 o2) ->
                   Type where
  ||| Show there exists some g such that f . g = g . f = id
  Iso : Category obj =>
        {o1, o2 : obj} ->
        (f : mor o1 o2) ->
        (g : mor o2 o1) ->
        Section {obj} f g ->
        Retraction {obj} f g ->
        Isomorphism {obj} f

||| Get the inverse out of an isomorphism
invIso : Category obj =>
         {o1, o2 : obj} ->
         (f : mor o1 o2) ->
         Isomorphism {obj} f ->
         (g : mor o2 o1 ** (Section {obj} f g, Retraction {obj} f g))
invIso f (Iso f g sect retr) = (g ** (sect, retr))

||| The inverse of an isomorphism is unique
invIsoUniq : Category obj =>
             {o1, o2 : obj} ->
             (f : mor o1 o2) ->
             (iso : Isomorphism {obj} f) ->
             (g : mor o2 o1) ->
             Section {obj} f g ->
             Retraction {obj} g f ->
             g = fst $ invIso f iso
invIsoUniq {obj} f (Iso f g sect (Retr f g retr)) g' (Sect f g' sect') retr' =
  let step1 = sym $ fst $ catIdIsId {obj} g
      step2 = trans step1 $ cong {f=catComp {obj} g} $ sym sect'
      step3 = trans step2 $ catCompAssoc {obj} g f g'
      step4 = trans step3 $ cong {f=\val=>catComp {obj} val g'} $ retr
      step5 = trans step4 $ snd $ catIdIsId {obj} g'
  in sym step5
