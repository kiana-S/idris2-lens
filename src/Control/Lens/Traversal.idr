module Control.Lens.Traversal

import Control.Monad.State
import Data.Zippable
import Data.Profunctor
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Applicative.Indexing
import Control.Lens.Optic
import Control.Lens.Optional
import Control.Lens.Lens
import Control.Lens.Prism

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

||| Contstruct a traversal over a `Bitraversable` container with matching types.
public export
both : Bitraversable t => Traversal (t a a) (t b b) a b
both @{_} @{MkIsTraversal _} = wander (\f => bitraverse f f)


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
||| replacement value for each, and return the final accumulator along with the
||| new structure.
public export
mapAccumLOf : Traversal s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t)
mapAccumLOf l f z =
  let g = state . flip f
  in runState z . traverseOf l g

||| Fold across the focuses of a traversal from the rightmost focus, providing a
||| replacement value for each, and return the final accumulator along with the
||| new structure.
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


||| Try to map over a traversal, failing if the traversal has no focuses.
public export
failover : Alternative f => Traversal s t a b -> (a -> b) -> s -> f t
failover l f x =
  let _ = Bool.Monoid.Any
      (b, y) = traverseOf l ((True,) . f) x
  in  guard b $> y

||| Convert a traversal into a lens over a list of values.
|||
||| Note that this is only a true lens if the invariant of the list's length is
||| maintained. You should avoid mapping `over` this lens with a function that
||| changes the list's length.
public export
partsOf : Traversal s t a a -> Lens s t (List a) (List a)
partsOf l = lens (runForget $ l $ MkForget pure)
                  (flip evalState . traverseOf l update)
  where
    update : a -> State (List a) a
    update x = get >>= \case
      x' :: xs' => put xs' >> pure x'
      []        => pure x


||| Construct an optional that focuses on the first value of a traversal.
|||
||| For the fold version of this, see `pre`.
public export
singular : Traversal' s a -> Optional' s a
singular l = optional' (runForget $ l (MkForget Just)) set
  where
    set : s -> a -> s
    set str x = evalState True $ traverseOf l
      (\y => if !get then put False $> x else pure y) str

||| Filter the focuses of a traversal by a predicate on their ordinal positions.
public export
elementsOf : Traversal s t a a -> (Nat -> Bool) -> Traversal s t a a
elementsOf l p @{MkIsTraversal _} = wander func
  where
    func : Applicative f => (a -> f a) -> s -> f t
    func fn = indexing {f} (traverseOf l) $
      \i,x => if p i then fn x else pure {f} x

||| Traverse over the elements of a `Traversable` container that satisfy a
||| predicate.
public export
elements : Traversable t => (Nat -> Bool) -> Traversal' (t a) a
elements = elementsOf traversed

||| Construct an optional that focuses on the nth element of a traversal.
public export
elementOf : Traversal' s a -> Nat -> Optional' s a
elementOf l n = singular $ elementsOf l (n ==)

||| Construct an optional that focuses on the nth element of a `Traversable`
||| container.
public export
element : Traversable t => Nat -> Optional' (t a) a
element = elementOf traversed


||| Limit a traversal to its first n focuses.
public export
taking : Nat -> Traversal s t a a -> Traversal s t a a
taking n l = elementsOf l (< n)

||| Remove the first n focuses from a traversal.
public export
dropping : Nat -> Traversal s t a a -> Traversal s t a a
dropping i l = elementsOf l (>= i)
