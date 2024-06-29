module Data.Maybe.Lens

import Data.Maybe
import Data.Profunctor
import public Control.Lens

%default total


||| A prism of the `Nothing` case of a `Maybe`.
public export
Nothing_ : Prism (Maybe a) (Maybe b) () ()
Nothing_ = prism (const Nothing) (maybe (Right ()) (const $ Left Nothing))

||| A prism of the `Just` case of a `Maybe`.
public export
Just_ : Prism (Maybe a) (Maybe b) a b
Just_ = prism Just $ \case
  Nothing => Left Nothing
  Just x => Right x

export infixl 9 .?

||| The composition `l .? l'` is equivalent to `l . Just_ . l'`.
||| Useful for optics whose focus type is a `Maybe`, such as `at`.
public export
(.?) : IsPrism p => Optic' p s t (Maybe a) (Maybe b) -> Optic' p a b a' b' -> Optic' p s t a' b'
l .? l' = l . Just_ . l'


public export
Each (Maybe a) (Maybe b) a b where
  -- each = Just_
  each = traversed
