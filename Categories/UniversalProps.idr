module UniversalProps

import Categories.Definitions

%default total
%access public export

||| Object with exactly one morphism to each other object
data InitialObject : Category obj mor =>
                     obj ->
                     Type where
  IsInitial : Category obj mor =>
              (o : obj) ->
              ((o' : obj) ->
               (f : mor o o' ** ((g : (mor o o')) ->
                                  f = g))) ->
              InitialObject {mor} o

||| All initial objects in a category are isomorphic
initialObjIso : Category obj mor =>
                (o1 : obj) ->
                InitialObject {mor} o1 ->
                (o2 : obj) ->
                InitialObject {mor} o2 ->
                (f : mor o1 o2 ** Isomorphism {mor} f)
initialObjIso {mor} o1 (IsInitial o1 o1_prf) o2 (IsInitial o2 o2_prf) =
  (f ** Iso {mor} f g (Sect {mor} f g sect) (Retr {mor} f g retr)) where
    f : mor o1 o2
    f = fst $ o1_prf o2
    id1Uniq : (f' : mor o1 o1) -> f' = catId o1
    id1Uniq f' with (o1_prf o1)
      | (uniq_f ** prf) = trans (sym (prf f')) $ prf $ catId o1
    g : mor o2 o1
    g = fst $ o2_prf o1
    id2Uniq : (g' : mor o2 o2) -> g' = catId o2
    id2Uniq g' with (o2_prf o2)
      | (uniq_g ** prf) = trans (sym (prf g')) $ prf $ catId o2
    sect = id1Uniq $ catComp {mor} f g
    retr = id2Uniq $ catComp {mor} g f

||| Object with exactly one morphism to each other object
data TerminalObject : Category obj mor =>
                      obj ->
                      Type where
  IsTerminal : Category obj mor =>
               (o : obj) ->
               ((o' : obj) ->
                (f : mor o' o ** ((g : (mor o' o)) ->
                                  f = g))) ->
               TerminalObject o

||| All terminal objects in a category are isomorphic
terminalObjIso : Category obj mor =>
                 (o1 : obj) ->
                 TerminalObject o1 ->
                 (o2 : obj) ->
                 TerminalObject o2 ->
                 (f : mor o1 o2 ** Isomorphism {mor} f)
terminalObjIso {mor} o1 (IsTerminal o1 o1_prf) o2 (IsTerminal o2 o2_prf) =
  (f ** Iso {mor} f g (Sect {mor} f g sect) (Retr {mor} f g retr)) where
    f : mor o1 o2
    f = fst $ o2_prf o1
    id1Uniq : (f' : mor o1 o1) -> f' = catId o1
    id1Uniq f' with (o1_prf o1)
      | (uniq_f ** prf) = trans (sym (prf f')) $ prf $ catId o1
    g : mor o2 o1
    g = fst $ o1_prf o2
    id2Uniq : (g' : mor o2 o2) -> g' = catId o2
    id2Uniq g' with (o2_prf o2)
      | (uniq_g ** prf) = trans (sym (prf g')) $ prf $ catId o2
    sect = id1Uniq $ catComp {mor} f g
    retr = id2Uniq $ catComp {mor} g f

||| Candidate for the (co)product
data ProductDiagram : Category obj mor =>
                      obj ->
                      obj ->
                      Type where
  MkProduct : Category obj mor =>
              (z : obj) ->
              (a : obj) ->
              (b : obj) ->
              Not (a = b) ->
              mor z a ->
              mor z b ->
              ProductDiagram a b {mor}

-- Ideally I would have declared ProductDiagram as a record
-- I couldn't get it to type check so I have to define all of these =/

get_z : Category obj mor => ProductDiagram {mor} a b -> obj
get_z (MkProduct z _ _ _ _ _) = z

get_a : Category obj mor => ProductDiagram {mor} a b -> obj
get_a (MkProduct _ a _ _ _ _) = a

get_b : Category obj mor => ProductDiagram {mor} a b -> obj
get_b (MkProduct _ _ b _ _ _) = b

get_f : Category obj mor => (p : ProductDiagram {mor} a b) -> mor (get_z p) a
get_f (MkProduct _ _ _ _ f _) = f

get_g : Category obj mor => (p : ProductDiagram {mor} a b) -> mor (get_z p) b
get_g (MkProduct _ _ _ _ _ g) = g

data ProductDiagramMor : Category obj mor =>
                         ProductDiagram {mor} a b ->
                         ProductDiagram {mor} a b ->
                         Type where
  DiagCommutes : Category obj mor =>
                 (a : obj) ->
                 (b : obj) ->
                 (p1 : ProductDiagram {mor} a b) ->
                 (p2 : ProductDiagram {mor} a b) ->
                 (sigma : mor (get_z p2) (get_z p1)) ->
                 get_f p2 = catComp {mor} sigma $ get_f p1 ->
                 get_g p2 = catComp {mor} sigma $ get_g p1 ->
                 ProductDiagramMor p1 p2

||| Identity morphism for product diagrams: has one diagram twice
diagId : Category obj mor =>
         (p : ProductDiagram {mor} a b) ->
         ProductDiagramMor {mor} p p
diagId p@(MkProduct z a b ineq f g) =
  DiagCommutes a b p p (catId z) (sym (snd (catIdIsId {mor} f))) $ sym $ snd $
               catIdIsId {mor} g

||| Compose two product diagrams by composing their sigma functions
diagComp : Category obj mor =>
           ProductDiagramMor {mor} p1 p2 ->
           ProductDiagramMor {mor} p2 p3 ->
           ProductDiagramMor {mor} p1 p3
diagComp {mor} pf@(DiagCommutes a b p1 p2 sigma1 f1 g1)
               pg@(DiagCommutes a b p2 p3 sigma2 f2 g2) =
  DiagCommutes {mor} a b p1 p3 sigma f_prf g_prf where
    sigma : mor (get_z p3) (get_z p1)
    sigma = catComp {mor} sigma2 sigma1
    f_prf : get_f p3 = catComp {mor} sigma $ get_f p1
    f_prf = trans (trans f2 (cong f1)) $
            catCompAssoc {mor} sigma2 sigma1 $ get_f p1
    g_prf : get_g p3 = catComp {mor} sigma $ get_g p1
    g_prf = trans (trans g2 (cong g1)) $
            catCompAssoc {mor} sigma2 sigma1 $ get_g p1

||| Composition of product diagrams is associative
diagCompAssoc : Category obj mor =>
                (pf : ProductDiagramMor {mor} p1 p2) ->
                (pg : ProductDiagramMor {mor} p2 p3) ->
                (ph : ProductDiagramMor {mor} p3 p4) ->
                diagComp {mor} pf (diagComp {mor} pg ph) =
                diagComp {mor} (diagComp {mor} pf pg) ph

||| The identity diagram is in fact an identity composed on either side
diagIdIsId : Category obj mor =>
             (p : ProductDiagramMor {mor} p1 p2) ->
             (diagComp {mor} p (diagId p2) = p,
              diagComp {mor} (diagId p1) p = p)

{-using (obj : Type, a : obj, b : obj,  mor : obj -> obj -> Type, Category obj mor)
implementation Category obj mor =>
                 Category (ProductDiagram {mor} {obj} a b)
                          (ProductDiagramMor {a} {b} {mor} {obj}) where
    catId {obj} {mor} p = ?catidhole
    catComp = ?catcomphole
    catCompAssoc = ?assochole
    catIdIsId = ?catidisidhole -}
