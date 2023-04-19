module Control.Lens.Setter

import Data.Contravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Control.Monad.State
import Control.Lens.Optic
import Control.Lens.Indexed
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

public export
0 IndexedSetter : (i,s,t,a,b : Type) -> Type
IndexedSetter = IndexedOptic IsSetter

public export
0 IndexedSetter' : (i,s,a : Type) -> Type
IndexedSetter' = Simple . IndexedSetter


------------------------------------------------------------------------------
-- Utilities for setters
------------------------------------------------------------------------------


||| Construct a setter from a modifying function.
public export
sets : ((a -> b) -> s -> t) -> Setter s t a b
sets f @{MkIsSetter _} = roam f

public export
isets : ((i -> a -> b) -> s -> t) -> IndexedSetter i s t a b
isets f @{MkIsSetter _} @{ind} = roam (f . curry) . indexed @{ind}

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

infixr 4 %~

||| Modify the focus or focuses of an optic.
|||
||| This is the operator form of `over`.
public export
(%~) : Setter s t a b -> (a -> b) -> s -> t
(%~) = over


public export
iover : IndexedSetter i s t a b -> (i -> a -> b) -> s -> t
iover l = l @{MkIsSetter Function} @{Idxed} . uncurry

infixr 4 %@~

public export
(%@~) : IndexedSetter i s t a b -> (i -> a -> b) -> s -> t
(%@~) = iover


||| Set the focus or focuses of an optic to a constant value.
public export
set : Setter s t a b -> b -> s -> t
set l = over l . const

infixr 4 .~

||| Set the focus or focuses of an optic to a constant value.
|||
||| This is the operator form of `set`.
public export
(.~) : Setter s t a b -> b -> s -> t
(.~) = set


public export
iset : IndexedSetter i s t a b -> (i -> b) -> s -> t
iset l = iover l . (const .)

infix 4 .@~

public export
(.@~) : IndexedSetter i s t a b -> (i -> b) -> s -> t
(.@~) = iset


------------------------------------------------------------------------------
-- More operators
------------------------------------------------------------------------------

infixr 4 ?~; infixr 4 <.~; infixr 4 <?~; infixr 4 +~; infixr 4 *~; infixr 4 -~
infixr 4 /~; infixr 4 ||~; infixr 4 &&~; infixr 4 <+>~

infix 4 %=; infix 4 %@=; infix 4 .=; infix 4 .@=; infix 4 ?=; infix 4 <.=
infix 4 <?=; infix 4 +=; infix 4 *=; infix 4 -=; infix 4 /=; infix 4 ||=
infix 4 &&=; infixr 4 <+>=

infixr 4 <~


||| Set the focus of an optic to `Just` a value.
public export
(?~) : Setter s t a (Maybe b) -> b -> s -> t
(?~) l = set l . Just

||| Set a value with pass-through.
public export
(<.~) : Setter s t a b -> b -> s -> (b, t)
(<.~) l x = (x,) . set l x

||| Set `Just` a value with pass-through.
public export
(<?~) : Setter s t a (Maybe b) -> b -> s -> (b, t)
(<?~) l x = (x,) . (?~) l x


||| Add a constant value to the focus of an optic.
public export
(+~) : Num a => Setter s t a a -> a -> s -> t
(+~) l = over l . (+)

||| Multiply the focus of an optic by a constant value.
public export
(*~) : Num a => Setter s t a a -> a -> s -> t
(*~) l = over l . (*)

||| Subtract a constant value from the focus of an optic.
public export
(-~) : Neg a => Setter s t a a -> a -> s -> t
(-~) l = over l . flip (-)

||| Divide the focus of an optic by a constant value.
public export
(/~) : Fractional a => Setter s t a a -> a -> s -> t
(/~) l = over l . flip (/)

||| Logically OR the focus of an optic with a constant value.
|||
||| Like `(||)`, this operator takes a lazy second argument.
public export
(||~) : Setter s t Bool Bool -> Lazy Bool -> s -> t
(||~) l = over l . flip (||)

||| Logically AND the focus of an optic with a constant value.
|||
||| Like `(&&)`, this operator takes a lazy second argument.
public export
(&&~) : Setter s t Bool Bool -> Lazy Bool -> s -> t
(&&~) l = over l . flip (&&)

||| Modify the focus of an optic using the semigroup/monoid operator.
|||
||| The constant value is applied to the focus from the right:
||| ```idris
||| l <+>~ x = over l (<+> x)
||| ```
public export
(<+>~) : Semigroup a => Setter s t a a -> a -> s -> t
(<+>~) l = over l . flip (<+>)


||| Modify the focus of an optic within a state monad.
public export
(%=) : MonadState s m => Setter s s a b -> (a -> b) -> m ()
(%=) = modify .: over

public export
(%@=) : MonadState s m => IndexedSetter i s s a b -> (i -> a -> b) -> m ()
(%@=) = modify .: iover

||| Set the focus of an optic within a state monad.
public export
(.=) : MonadState s m => Setter s s a b -> b -> m ()
(.=) = modify .: set

public export
(.@=) : MonadState s m => IndexedSetter i s s a b -> (i -> b) -> m ()
(.@=) = modify .: iset

||| Set the focus of an optic within a state monad to `Just` a value.
public export
(?=) : MonadState s m => Setter s s a (Maybe b) -> b -> m ()
(?=) = modify .: (?~)

||| Set within a state monad with pass-through.
public export
(<.=) : MonadState s m => Setter s s a b -> b -> m b
(<.=) l x = (l .= x) >> pure x

||| Set to `Just` a value within a state monad with pass-through.
public export
(<?=) : MonadState s m => Setter s s a (Maybe b) -> b -> m b
(<?=) l x = (l ?= x) >> pure x

||| Add a constant value to the focus of an optic within a state monad.
public export
(+=) : Num a => MonadState s m => Setter' s a -> a -> m ()
(+=) = modify .: (+~)

||| Multiply the focus of an optic into state by a constant value.
public export
(*=) : Num a => MonadState s m => Setter' s a -> a -> m ()
(*=) = modify .: (*~)

||| Subtract a constant value from the focus of an optic within a state monad.
public export
(-=) : Neg a => MonadState s m => Setter' s a -> a -> m ()
(-=) = modify .: (-~)

||| Divide the focus of an optic into state by a constant value.
public export
(//=) : Fractional a => MonadState s m => Setter' s a -> a -> m ()
(//=) = modify .: (/~)

||| Logically OR the focus of an optic into state with a constant value.
|||
||| Like `(||)`, this operator takes a lazy second argument.
public export
(||=) : MonadState s m => Setter' s Bool -> Lazy Bool -> m ()
(||=) = modify .: (||~)

||| Logically AND the focus of an optic into state with a constant value.
|||
||| Like `(&&)`, this operator takes a lazy second argument.
public export
(&&=) : MonadState s m => Setter' s Bool -> Lazy Bool -> m ()
(&&=) = modify .: (&&~)

||| Modify the focus of an optic into state using the semigroup/monoid operator.
|||
||| The constant value is applied to the focus from the right.
public export
(<+>=) : Semigroup a => MonadState s m => Setter' s a -> a -> m ()
(<+>=) = modify .: (<+>~)


||| Run a monadic action and set the focus of an optic in state to the result.
|||
||| This can be thought of as a variation on the do-notation pseudo-operator (<-),
||| storing the result of a computation within state instead of in a local
||| variable.
public export
(<~) : MonadState s m => Setter s s a b -> m b -> m ()
(<~) l m = m >>= (l .=)
