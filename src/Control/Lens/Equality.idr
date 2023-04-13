module Control.Lens.Equality

import Control.Lens.Optic

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


-- This type is trivial and thus really isn't necessary;
-- it's only defined and used in order to assist Idris with optic coersion.
public export
record IsEquality {0 k,k' : _} (p : k -> k' -> Type) where
  constructor MkIsEquality


||| An `Equality s t a b` is a witness that `(s = a, t = b)` that can be used
||| as an optic.
|||
||| The canonical `Equality` is `id : Equality a b a b`.
|||
||| An `Equality` can be coerced to any other optic.
public export
0 Equality : k -> k' -> k -> k' -> Type
Equality s t a b = forall p. IsEquality p => p a b -> p s t

||| An `Equality' s a` is a witness that `s = a` that can be used as an optic.
||| This is the `Simple` version of `Equality`.
public export
0 Equality' : (s,a : k) -> Type
Equality' = Simple Equality


------------------------------------------------------------------------------
-- Utilities for Equality
------------------------------------------------------------------------------


||| Extract the two `Equal` values from an `Equality`.
public export
runEq : Equality s t a b -> (s = a, t = b)
runEq l = (l {p = \x,_ => x = a} Refl,
           l {p = \_,y => y = b} Refl)

||| Extract an `Equal` value from an `Equality`.
public export
runEq' : Equality s t a b -> s = a
runEq' l = l {p = \x,_ => x = a} Refl


||| `Equality` is a congruence.
public export
congEq : forall f,g. Equality s t a b -> Equality (f s) (g t) (f a) (g b)
congEq l {p} = l {p = \x,y => p (f x) (g y)}

||| Symmetry of an `Equality` optic.
public export
symEq : Equality s t a b -> Equality b a t s
symEq l = case runEq l of (Refl, Refl) => id

public export
substEq : forall p. Equality s t a b -> p a b a b -> p s t a b
substEq {p} l = l {p = \x,y => p x y a b}


||| A trivial `Simple Equality`.
||| Composing this optic with any other can force it to be a `Simple` optic.
public export
simple : Equality' a a
simple = id
