module Control.Lens.Traversal

import Control.Monad.State
import Data.Zippable
import Data.Profunctor
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Lens.Optic
import Control.Lens.Optional

%default total


public export
record IsTraversal p where
  constructor MkIsTraversal
  runIsTraversal : Traversing p

export %hint
traversalToOptional : IsTraversal p => IsOptional p
traversalToOptional @{MkIsTraversal _} = MkIsOptional %search


public export
0 Traversal : (s,t,a,b : Type) -> Type
Traversal = Optic IsTraversal

public export
0 Traversal' : (s,a : Type) -> Type
Traversal' = Simple Traversal


public export
traversed : Traversable t => Traversal (t a) (t b) a b
traversed @{_} @{MkIsTraversal _} = traverse'

public export
backwards : Traversal s t a b -> Traversal s t a b
backwards l @{MkIsTraversal _} = wander func
  where
    func : Applicative f => (a -> f b) -> s -> f t
    func fn = forwards . applyStar {f = Backwards f} (l $ MkStar (MkBackwards . fn))


public export
traverseOf : Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
traverseOf l = applyStar . l . MkStar {f}

public export
forOf : Applicative f => Traversal s t a b -> s -> (a -> f b) -> f t
forOf l = flip $ traverseOf l

public export
sequenceOf : Applicative f => Traversal s t (f a) a -> s -> f t
sequenceOf l = traverseOf l id

public export
mapAccumLOf : Traversal s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t)
mapAccumLOf l f z =
  let g = state . flip f
  in runState z . traverseOf l g

public export
mapAccumROf : Traversal s t a b -> (acc -> a -> (acc, b)) -> acc -> s -> (acc, t)
mapAccumROf l f z =
  let g = MkBackwards {f=State acc} . state . flip f
  in runState z . forwards . traverseOf l g

public export
scanl1Of : Traversal s t a a -> (a -> a -> a) -> s -> t
scanl1Of l f =
  let step : Maybe a -> a -> (Maybe a, a)
      step Nothing  x = (Just x, x)
      step (Just s) x = let r = f s x in (Just r, r)
  in snd . mapAccumLOf l step Nothing

public export
scanr1Of : Traversal s t a a -> (a -> a -> a) -> s -> t
scanr1Of l f =
  let step : Maybe a -> a -> (Maybe a, a)
      step Nothing  x = (Just x, x)
      step (Just s) x = let r = f s x in (Just r, r)
  in snd . mapAccumROf l step Nothing
