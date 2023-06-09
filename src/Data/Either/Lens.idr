module Data.Either.Lens

import Data.Profunctor
import public Control.Lens

%default total


||| A prism to the left of an `Either`.
public export
Left_ : Prism (Either a c) (Either b c) a b
Left_ @{MkIsPrism _} = left

||| A prism to the right of an `Either`.
public export
Right_ : Prism (Either c a) (Either c b) a b
Right_ @{MkIsPrism _} = right


public export
chosen : IndexedLens (Either () ()) (Either a a) (Either b b) a b
chosen = ilens
  (either (Left (),) (Right (),))
  (\case
    Left _ => Left
    Right _ => Right)
