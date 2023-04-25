module Control.Lens.Each

import Control.Monad.Identity
import Control.Applicative.Const
import Control.Lens.Optic
import Control.Lens.Iso
import Control.Lens.Lens
import Control.Lens.Optional
import Control.Lens.Traversal

%default total


||| An interface for accessing every element of a container.
|||
||| This can be thought of as a generalized version of `traversed` for
||| containers that do not have a `Traversable` implementation.
public export
interface Each s t a b | s where

  ||| Access every element of a container at the same time.
  |||
  ||| This can be thought of as a generalized version of `traversed` for
  ||| containers that do not have a `Traversable` implementation.
  each : Traversal s t a b


public export
Each (Identity a) (Identity b) a b where
  each = Id_

public export
Each (Const a b) (Const c d) a c where
  each = Const_
