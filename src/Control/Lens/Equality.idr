module Control.Lens.Equality

import Control.Lens.Optic

%default total


public export
record IsEquality {0 k,k' : _} (p : k -> k' -> Type) where
  constructor MkIsEquality

public export
0 Equality : k -> k' -> k -> k' -> Type
Equality s t a b = forall p. IsEquality p => p a b -> p s t

public export
0 Equality' : k -> k -> Type
Equality' = Simple Equality


public export
runEq : Equality s t a b -> (s = a, t = b)
runEq l = (l {p = \x,_ => x = a} Refl,
           l {p = \_,y => y = b} Refl)

public export
runEq' : Equality s t a b -> s = a
runEq' l = l {p = \x,_ => x = a} Refl


public export
substEq : forall p. Equality s t a b -> p a b a b -> p s t a b
substEq {p} l = l {p = \x,y => p x y a b}

public export
congEq : forall f,g. Equality s t a b -> Equality (f s) (g t) (f a) (g b)
congEq l {p} = l {p = \x,y => p (f x) (g y)}

public export
symEq : Equality s t a b -> Equality b a t s
symEq l = case runEq l of (Refl, Refl) => id


public export
refl : Equality a b a b
refl = id

public export
simple : Equality' a a
simple = id
