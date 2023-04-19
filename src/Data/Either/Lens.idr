module Data.Either.Lens

import Data.Profunctor
import public Control.Lens

%default total


public export
Left_ : Prism (Either a c) (Either b c) a b
Left_ @{MkIsPrism _} = left

public export
Right_ : Prism (Either c a) (Either c b) a b
Right_ @{MkIsPrism _} = right


public export
chosen : IndexedLens (Either () ()) (Either a a) (Either b b) a b
chosen = ilens
  (\case
    Left x => (Left (), x)
    Right x => (Right (), x))
  (\case
    Left _ => Left
    Right _ => Right)
