module Control.Lens.Traversal

import Control.Monad.State
import Data.List
import Data.Profunctor
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Applicative.Indexing
import Control.Lens.Optic
import Control.Lens.Indexed
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

export %hint
indexedTraversal : IsTraversal p => IsTraversal (Indexed i p)
indexedTraversal @{MkIsTraversal _} = MkIsTraversal %search


||| A traversal is a lens that may have more than one focus.
public export
0 Traversal : (s,t,a,b : Type) -> Type
Traversal = Optic IsTraversal

||| `Traversal'` is the `Simple` version of `Traversal`.
public export
0 Traversal' : (s,a : Type) -> Type
Traversal' = Simple Traversal

public export
0 IndexedTraversal : (i,s,t,a,b : Type) -> Type
IndexedTraversal = IndexedOptic IsTraversal

public export
0 IndexedTraversal' : (i,s,a : Type) -> Type
IndexedTraversal' = Simple . IndexedTraversal


------------------------------------------------------------------------------
-- Utilities for traversals
------------------------------------------------------------------------------


public export
iordinal : Num i => Traversal s t a b -> IndexedTraversal i s t a b
iordinal @{_} l @{MkIsTraversal _} @{ind} = wander (func . curry) . indexed @{ind}
  where
    func : forall f. Applicative f => (i -> a -> f b) -> s -> f t
    func = indexing $ applyStar . l . MkStar {f = Indexing i f}


||| Derive a traversal from a `Traversable` implementation.
public export
traversed : Traversable t => Traversal (t a) (t b) a b
traversed @{_} @{MkIsTraversal _} = traverse'

public export
itraversed : Num i => Traversable t => IndexedTraversal i (t a) (t b) a b
itraversed = iordinal traversed

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

public export
itraverseOf : Applicative f => IndexedTraversal i s t a b -> (i -> a -> f b) -> s -> f t
itraverseOf l = traverseOf (l @{%search} @{Idxed}) . uncurry

||| A version of `traverseOf` but with the arguments flipped.
public export
forOf : Applicative f => Traversal s t a b -> s -> (a -> f b) -> f t
forOf = flip . traverseOf

public export
iforOf : Applicative f => IndexedTraversal i s t a b -> s -> (i -> a -> f b) -> f t
iforOf = flip . itraverseOf

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

public export
ifailover : Alternative f => IndexedTraversal i s t a b -> (i -> a -> b) -> s -> f t
ifailover l = failover (l @{%search} @{Idxed}) . uncurry


partsOf_update : a -> State (List a) a
partsOf_update x = get >>= \case
  x' :: xs' => put xs' >> pure x'
  []        => pure x

||| Convert a traversal into a lens over a list of values.
|||
||| Note that this is only a true lens if the invariant of the list's length is
||| maintained. You should avoid mapping `over` this lens with a function that
||| changes the list's length.
public export
partsOf : Traversal s t a a -> Lens s t (List a) (List a)
partsOf l = lens (runForget $ l $ MkForget pure)
                  (flip evalState . traverseOf l partsOf_update)

public export
ipartsOf : IndexedTraversal i s t a a -> IndexedLens (List i) s t (List a) (List a)
ipartsOf l = ilens (unzip . (runForget $ l @{%search} @{Idxed} $ MkForget pure))
                   (flip evalState . itraverseOf l (const partsOf_update))


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
