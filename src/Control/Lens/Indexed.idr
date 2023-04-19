module Control.Lens.Indexed

import Data.Profunctor
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
