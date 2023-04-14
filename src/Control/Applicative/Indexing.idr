module Control.Applicative.Indexing

import Data.Contravariant

%default total


public export
record Indexing {0 k : Type} f (a : k) where
  constructor MkIndexing
  runIndexing : Nat -> (Nat, f a)


public export
Functor f => Functor (Indexing f) where
  map f (MkIndexing g) = MkIndexing (mapSnd (map f) . g)

public export
Applicative f => Applicative (Indexing f) where
  pure x = MkIndexing $ \i => (i, pure x)
  MkIndexing mf <*> MkIndexing ma = MkIndexing $ \i =>
    let (j, ff) = mf i
        (k, fa) = ma j
    in (k, ff <*> fa)

public export
Contravariant f => Contravariant (Indexing f) where
  contramap f (MkIndexing g) = MkIndexing (mapSnd (contramap f) . g)


public export
indexing : ((a -> Indexing f b) -> s -> Indexing f t) -> (Nat -> a -> f b) -> s -> f t
indexing l fn s = snd $ runIndexing {f} (l (\x => MkIndexing $ \i => (S i, fn i x)) s) 0
