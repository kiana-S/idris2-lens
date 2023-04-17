module Data.Maybe.Lens

import Data.Maybe
import Data.Profunctor
import public Control.Lens

%default total


public export
Nothing_ : Prism' (Maybe a) ()
Nothing_ = prism' (const Nothing) (guard . isNothing)

public export
Just_ : Prism (Maybe a) (Maybe b) a b
Just_ = prism Just $ \case
  Nothing => Left Nothing
  Just x => Right x

infixl 9 .?

public export
(.?) : IsPrism p => Optic' p s t (Maybe a) (Maybe b) -> Optic' p a b a' b' -> Optic' p s t a' b'
l .? l' = l . Just_ . l'
