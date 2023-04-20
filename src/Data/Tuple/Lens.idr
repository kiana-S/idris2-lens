module Data.Tuple.Lens

import Data.Vect
import Data.Profunctor
import public Control.Lens

%default total


||| A lens to the first element of a pair.
public export
fst_ : Lens (a, c) (b, c) a b
fst_ @{MkIsLens _} = first

||| A lens to the second element of a pair.
public export
snd_ : Lens (c, a) (c, b) a b
snd_ @{MkIsLens _} = second


||| An indexed lens to the first element of a pair, indexed by the other element.
public export
ifst_ : IndexedLens i (a, i) (b, i) a b
ifst_ = ilens swap (flip $ mapFst . const)

||| An indexed lens to the second element of a pair, indexed by the other element.
public export
isnd_ : IndexedLens i (i, a) (i, b) a b
isnd_ = ilens id (flip $ mapSnd . const)
