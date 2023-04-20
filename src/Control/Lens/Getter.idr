module Control.Lens.Getter

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.Lens

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsGetter p where
  constructor MkIsGetter
  runIsGetter : (Strong p, Bicontravariant p)

export %hint
getterToLens : IsGetter p => IsLens p
getterToLens @{MkIsGetter _} = MkIsLens %search

export %hint
indexedGetter : IsGetter p => IsGetter (Indexed i p)
indexedGetter @{MkIsGetter _} = MkIsGetter %search


||| A getter is an optic that only supports getting, not setting.
|||
||| `Getter s a` is equivalent to a simple function `s -> a`.
public export
0 Getter : (s,a : Type) -> Type
Getter = Simple (Optic IsGetter)

||| An indexed getter returns an index while getting.
public export
0 IndexedGetter : (i,s,a : Type) -> Type
IndexedGetter = Simple . IndexedOptic IsGetter


------------------------------------------------------------------------------
-- Utilities for getters
------------------------------------------------------------------------------


||| Construct a getter from a function.
public export
to : (s -> a) -> Getter s a
to f @{MkIsGetter _} = lmap f . rphantom

||| Construct an indexed getter from a function.
public export
ito : (s -> (i, a)) -> IndexedGetter i s a
ito f @{MkIsGetter _} @{ind} = lmap f . rphantom . indexed @{ind}

||| Construct a getter that always returns a constant value.
public export
like : a -> Getter s a
like = to . const


||| Access the value of an optic and apply a function to it, returning the result.
public export
views : Getter s a -> (a -> r) -> s -> r
views l = runForget . l . MkForget

||| Access the focus value of an optic, particularly a `Getter`.
public export
view : Getter s a -> s -> a
view l = views l id

public export
iviews : IndexedGetter i s a -> (i -> a -> r) -> s -> r
iviews l = runForget . l @{%search} @{Idxed} . MkForget . uncurry

public export
iview : IndexedGetter i s a -> s -> (i, a)
iview l = runForget $ l @{%search} @{Idxed} $ MkForget id


infixl 8 ^.
infixl 8 ^@.

||| Access the focus value of an optic, particularly a `Getter`.
|||
||| This is the operator form of `view`.
public export
(^.) : s -> Getter s a -> a
(^.) x l = view l x

public export
(^@.) : s -> IndexedGetter i s a -> (i, a)
(^@.) x l = iview l x
