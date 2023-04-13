module Control.Lens.Traversal

import Control.Monad.State
import Data.Zippable
import Data.Profunctor
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Lens.Optic
import Control.Lens.Optional

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsTraversal p where
  constructor MkIsTraversal
  runIsTraversal : Traversing p

export %hint
traversalToOptional : IsTraversal p => IsOptional p
traversalToOptional @{MkIsTraversal _} = MkIsOptional %search


||| A traversal is a lens that may have more than one focus.
public export
0 Traversal : (s,t,a,b : Type) -> Type
Traversal = Optic IsTraversal

||| `Traversal'` is the `Simple` version of `Traversal`.
public export
0 Traversal' : (s,a : Type) -> Type
Traversal' = Simple Traversal


------------------------------------------------------------------------------
-- Utilities for traversals
------------------------------------------------------------------------------


||| Derive a traversal from a `Traversable` implementation.
public export
traversed : Traversable t => Traversal (t a) (t b) a b
traversed @{_} @{MkIsTraversal _} = traverse'

||| Reverse the order of a traversal's focuses.
public export
backwards : Traversal s t a b -> Traversal s t a b
backwards l @{MkIsTraversal _} = wander func
  where
    func : Applicative f => (a -> f b) -> s -> f t
    func fn = forwards . applyStar {f = Backwards f} (l $ MkStar (MkBackwards . fn))


||| Map each focus of a traversal to a computation, evaluate those computations
||| and combine the results.
public export
traverseOf : Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
traverseOf l = applyStar . l . MkStar {f}

||| A version of `traverseOf` but with the arguments flipped.
public export
forOf : Applicative f => Traversal s t a b -> s -> (a -> f b) -> f t
forOf l = flip $ traverseOf l

||| Evaluate each computation within the traversal and collect the results.
public export
sequenceOf : Applicative f => Traversal s t (f a) a -> s -> f t
sequenceOf l = traverseOf l id

||| Fold across the focuses of a traversal from the leftmost focus, providing a
||| replacement value for each focus, and return the final accumulator along
||| with the new structure.
public export
mapAccumLOf : Traversal s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t)
mapAccumLOf l f z =
  let g = state . flip f
  in runState z . traverseOf l g

||| Fold across the focuses of a traversal from the rightmost focus, providing a
||| replacement value for each focus, and return the final accumulator along
||| with the new structure.
public export
mapAccumROf : Traversal s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t)
mapAccumROf l f z =
  let g = MkBackwards {f=State acc} . state . flip f
  in runState z . forwards . traverseOf l g

||| Fold across the focuses of a traversal from the left, returning each
||| intermediate value of the fold.
public export
scanl1Of : Traversal s t a a -> (a -> a -> a) -> s -> t
scanl1Of l f =
  let step : Maybe a -> a -> (Maybe a, a)
      step Nothing  x = (Just x, x)
      step (Just s) x = let r = f s x in (Just r, r)
  in snd . mapAccumLOf l step Nothing

||| Fold across the focuses of a traversal from the right, returning each
||| intermediate value of the fold.
public export
scanr1Of : Traversal s t a a -> (a -> a -> a) -> s -> t
scanr1Of l f =
  let step : Maybe a -> a -> (Maybe a, a)
      step Nothing  x = (Just x, x)
      step (Just s) x = let r = f s x in (Just r, r)
  in snd . mapAccumROf l step Nothing
