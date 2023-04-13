module Control.Lens.Setter

import Data.Contravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Control.Lens.Optic
import Control.Lens.Traversal

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsSetter p where
  constructor MkIsSetter
  runIsSetter : Mapping p


export %hint
setterToTraversal : IsSetter p => IsTraversal p
setterToTraversal @{MkIsSetter _} = MkIsTraversal %search


||| A setter is an optic that only supports setting, not getting.
|||
||| More specifically, a setter can modify zero or more focus elements. This
||| means that all traversals are setters.
|||
||| Setters can be thought of as a generalization of the `Functor` interface,
||| allowing one to map over the contents of a structure.
public export
0 Setter : (s,t,a,b : Type) -> Type
Setter = Optic IsSetter

||| `Setter'` is the `Simple` version of `Setter`.
public export
0 Setter' : (s,a : Type) -> Type
Setter' = Simple Setter


------------------------------------------------------------------------------
-- Utilities for setters
------------------------------------------------------------------------------


||| Construct a setter from a modifying function.
public export
sets : ((a -> b) -> s -> t) -> Setter s t a b
sets f @{MkIsSetter _} = roam f

||| Derive a setter from a `Functor` implementation.
public export
mapped : Functor f => Setter (f a) (f b) a b
mapped @{_} @{MkIsSetter _} = map'

||| Derive a setter from a `Contravariant` implementation.
public export
contramapped : Contravariant f => Setter (f a) (f b) b a
contramapped = sets contramap


||| Modify the focus or focuses of an optic.
public export
over : Setter s t a b -> (a -> b) -> s -> t
over l = l @{MkIsSetter Function}

||| Set the focus or focuses of an optic to a constant value.
public export
set : Setter s t a b -> b -> s -> t
set l = over l . const
