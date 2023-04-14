module Control.Lens.Getter

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Lens

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsGetter p where
  constructor MkIsGetter
  runIsGetter : (Strong p, Cochoice p, Bicontravariant p)

export %hint
getterToLens : IsGetter p => IsLens p
getterToLens @{MkIsGetter _} = MkIsLens %search


||| A getter is an optic that only supports getting, not setting.
|||
||| `Getter s a` is equivalent to a simple function `s -> a`.
public export
0 Getter : (s,a : Type) -> Type
Getter = Simple (Optic IsGetter)


------------------------------------------------------------------------------
-- Utilities for getters
------------------------------------------------------------------------------


||| Construct a getter from a function.
public export
to : (s -> a) -> Getter s a
to f @{MkIsGetter _} = lmap f . rphantom

||| Construct a getter that always returns a constant value.
public export
like : a -> Getter s a
like = to . const


||| Access the value of an optic and apply a function to it, returning the result.
public export
views : Getter s a -> (a -> r) -> (s -> r)
views l = runForget . l . MkForget

||| Access the focus value of an optic, particularly a `Getter`.
public export
view : Getter s a -> s -> a
view l = views l id


infixl 8 ^.

||| Access the focus value of an optic, particularly a `Getter`.
|||
||| This is the operator form of `view`.
public export
(^.) : s -> Getter s a -> a
(^.) x l = view l x
