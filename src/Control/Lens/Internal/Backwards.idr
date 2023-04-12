module Control.Lens.Internal.Backwards

%default total


public export
record Backwards {0 k : Type} (f : k -> Type) a where
  constructor MkBackwards
  forwards : f a


public export
Functor f => Functor (Backwards f) where
  map f (MkBackwards x) = MkBackwards (map f x)

public export
Applicative f => Applicative (Backwards f) where
  pure = MkBackwards . pure
  MkBackwards f <*> MkBackwards x = MkBackwards (flip apply <$> x <*> f)
