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

||| An initial object has only one morphism to itself
initialObjIdUniq : Category obj mor =>
                   (o : obj) ->
                   InitialObject o ->
                   (f : mor o o) ->
                   f = catId o
initialObjIdUniq o (IsInitial o o_prf) f =
  let (uniq_f ** prf) = o_prf o
  in trans (sym (prf f)) $ prf $ catId o

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
    g : mor o2 o1
    g = fst $ o2_prf o1
    sect = initialObjIdUniq o1 (IsInitial o1 o1_prf) $ catComp {mor} f g
    retr = initialObjIdUniq o2 (IsInitial o2 o2_prf) $ catComp {mor} g f

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

||| A terminal object has only one morphism to itself
terminalObjIdUniq : Category obj mor =>
                   (o : obj) ->
                   TerminalObject o ->
                   (f : mor o o) ->
                   f = catId o
terminalObjIdUniq o (IsTerminal o o_prf) f =
  let (uniq_f ** prf) = o_prf o
  in trans (sym (prf f)) $ prf $ catId o

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
    g : mor o2 o1
    g = fst $ o1_prf o2
    sect = terminalObjIdUniq o1 (IsTerminal o1 o1_prf) $ catComp {mor} f g
    retr = terminalObjIdUniq o2 (IsTerminal o2 o2_prf) $ catComp {mor} g f
