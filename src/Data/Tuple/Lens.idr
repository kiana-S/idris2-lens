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
