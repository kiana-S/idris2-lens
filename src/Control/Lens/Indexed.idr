module Control.Lens.Indexed

import Data.Tensor
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Bicontravariant
import Control.Lens.Optic
import Control.Lens.Iso

%default total


public export
interface Indexable i (0 p, p' : Type -> Type -> Type) | p, p' where
  indexed : p' a b -> p (i, a) b


-- Non-indexed use (default)
public export
IsIso p => Indexable i p p where
  indexed @{MkIsIso _} = lmap snd

-- Indexed use
public export
[Idxed] Indexable i p (p . (i,)) where
  indexed = id


public export
0 IndexedOptic' : (Type -> Type -> Type) -> (i,s,t,a,b : Type) -> Type
IndexedOptic' p i s t a b = forall p'. Indexable i p p' => p' a b -> p s t

public export
0 IndexedOptic : ((Type -> Type -> Type) -> Type) -> (i,s,t,a,b : Type) -> Type
IndexedOptic constr i s t a b =
  forall p,p'. constr p => Indexable i p p' => p' a b -> p s t



public export
record Indexed i (p : Type -> Type -> Type) a b where
  constructor MkIndexed
  runIndexed : p (i, a) b

public export
Bifunctor p => Bifunctor (Indexed i p) where
  bimap f g (MkIndexed k) = MkIndexed $ bimap (mapSnd f) g k
  mapFst f (MkIndexed k) = MkIndexed $ mapFst (mapSnd f) k
  mapSnd f (MkIndexed k) = MkIndexed $ mapSnd f k

public export
Bicontravariant p => Bicontravariant (Indexed i p) where
  contrabimap f g (MkIndexed k) = MkIndexed $ contrabimap (mapSnd f) g k

public export
Profunctor p => Profunctor (Indexed i p) where
  dimap f g (MkIndexed k) = MkIndexed $ dimap (mapSnd f) g k
  lmap f (MkIndexed k) = MkIndexed $ lmap (mapSnd f) k
  rmap f (MkIndexed k) = MkIndexed $ rmap f k

public export
Bifunctor ten => GenStrong ten p => GenStrong ten (Indexed i p) where
  strongl (MkIndexed k) = MkIndexed $ lmap (\(i,x) => mapFst (i,) x) (strongl {ten,p} k)
  strongr (MkIndexed k) = MkIndexed $ lmap (\(i,x) => mapSnd (i,) x) (strongr {ten,p} k)

public export
Traversing p => Traversing (Indexed i p) where
  wander tr (MkIndexed k) = MkIndexed $ wander (\f,(i,x) => tr (f . (i,)) x) k

public export
Closed p => Closed (Indexed i p) where
  closed (MkIndexed k) = MkIndexed $ lmap (\(i,f),x => (i, f x)) (closed k)

public export
Mapping p => Mapping (Indexed i p) where
  roam mp (MkIndexed k) = MkIndexed $ roam (\f,(i,x) => mp (f . (i,)) x) k

export %hint
indexedIso : IsIso p => IsIso (Indexed i p)
indexedIso @{MkIsIso _} = MkIsIso %search



||| Compose two indexed optics, using a function to combine the indices of each
||| optic.
public export
icompose : IsIso p => (i -> j -> k) ->
            IndexedOptic' p i s t a b -> IndexedOptic' (Indexed i p) j a b a' b' ->
            IndexedOptic' p k s t a' b'
icompose @{MkIsIso _} f l l' @{ind} =
  l @{Idxed} . runIndexed . l' @{Idxed} . MkIndexed {p}
  . lmap (mapFst (uncurry f) . assocl) . indexed @{ind}

export infixr 9 <.>, .>, <.

||| Compose two indexed optics, returning an optic indexed by a pair of indices.
|||
||| Mnemonically, the angle brackets point to the fact that we want to preserve
||| both indices.
public export
(<.>) : IsIso p => IndexedOptic' p i s t a b -> IndexedOptic' (Indexed i p) j a b a' b' ->
                    IndexedOptic' p (i, j) s t a' b'
(<.>) = icompose (,)

||| Compose a non-indexed optic with an indexed optic.
|||
||| Mnemonically, the angle bracket points to the index that we want to preserve.
public export
(.>) : Optic' p s t a b -> IndexedOptic' p i a b a' b' -> IndexedOptic' p i s t a' b'
(.>) l l' = l . l'

||| Compose an indexed optic with a non-indexed optic.
|||
||| Mnemonically, the angle bracket points to the index that we want to preserve.
public export
(<.) : IndexedOptic' p i s t a b -> Optic' (Indexed i p) a b a' b' -> IndexedOptic' p i s t a' b'
(<.) l l' @{ind} = l @{Idxed} . runIndexed . l' . MkIndexed {p} . indexed @{ind}


||| Augment an optic with an index that is constant for all inputs.
public export
constIndex : IsIso p => i -> Optic' p s t a b -> IndexedOptic' p i s t a b
constIndex i l @{MkIsIso _} @{ind} = l . lmap (i,) . indexed @{ind}

||| Modify the indices of an indexed optic.
public export
reindexed : IsIso p => (i -> j) -> IndexedOptic' p i s t a b -> IndexedOptic' p j s t a b
reindexed @{MkIsIso _} f l @{ind} = l @{Idxed} . lmap (mapFst f) . indexed @{ind}
