module Control.Applicative.Indexing

import Data.Contravariant

%default total


public export
record Indexing {0 k : Type} i f (a : k) where
  constructor MkIndexing
  runIndexing : i -> (i, f a)


public export
Functor f => Functor (Indexing i f) where
  map f (MkIndexing g) = MkIndexing (mapSnd (map f) . g)

public export
Applicative f => Applicative (Indexing i f) where
  pure x = MkIndexing $ \i => (i, pure x)
  MkIndexing mf <*> MkIndexing ma = MkIndexing $ \i =>
    let (j, ff) = mf i
        (k, fa) = ma j
    in (k, ff <*> fa)

public export
Contravariant f => Contravariant (Indexing i f) where
  contramap f (MkIndexing g) = MkIndexing (mapSnd (contramap f) . g)


public export
indexing : Num i => ((a -> Indexing i f b) -> s -> Indexing i f t) -> (i -> a -> f b) -> s -> f t
indexing l fn s = snd $ runIndexing {f} (l (\x => MkIndexing $ \i => (1 + i, fn i x)) s) 0
