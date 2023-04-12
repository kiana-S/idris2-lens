module Control.Lens.Getter

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Lens

%default total


public export
record IsGetter p where
  constructor MkIsGetter
  runIsGetter : (Strong p, Cochoice p, Bicontravariant p)

export %hint
getterToLens : IsGetter p => IsLens p
getterToLens @{MkIsGetter _} = MkIsLens %search


public export
0 Getter : (s,a : Type) -> Type
Getter = Simple (Optic IsGetter)


public export
to : (s -> a) -> Getter s a
to f @{MkIsGetter _} = lmap f . rphantom


public export
views : Getter s a -> (a -> r) -> (s -> r)
views l = runForget . l . MkForget

public export
view : Getter s a -> (s -> a)
view l = views l id

infixl 8 ^.

public export
(^.) : s -> Getter s a -> a
(^.) x l = view l x
