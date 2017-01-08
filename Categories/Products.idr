module Products

import Categories.Definitions
import Categories.UniversalProps

%default total
%access public export

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
              ProductDiagram a b

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
  DiagCommutes a b p p
               (catId z)
               (sym (snd (catIdIsId {mor} f))) $
               sym $ snd $ catIdIsId {mor} g

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
diagCompAssoc pf@(DiagCommutes a b p1 p2 sigma1 f1 g1)
              pg@(DiagCommutes a b p2 p3 sigma2 f2 g2)
              ph@(DiagCommutes a b p3 p4 sigma3 f3 g3) =
                ?diagcompassochole

||| The identity diagram is in fact an identity composed on either side
diagIdIsId : Category obj mor =>
             (p : ProductDiagramMor {mor} p1 p2) ->
             (diagComp {mor} p (diagId p2) = p,
             diagComp {mor} (diagId p1) p = p)
