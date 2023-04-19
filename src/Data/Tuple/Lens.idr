module Data.Tuple.Lens

import Data.Vect
import Data.Profunctor
import public Control.Lens

%default total


public export
fst_ : Lens (a, c) (b, c) a b
fst_ @{MkIsLens _} = first

public export
snd_ : Lens (c, a) (c, b) a b
snd_ @{MkIsLens _} = second


public export
ifst_ : IndexedLens i (a, i) (b, i) a b
ifst_ = ilens swap (flip $ mapFst . const)

public export
isnd_ : IndexedLens i (i, a) (i, b) a b
isnd_ = ilens id (flip $ mapSnd . const)
