module Control.Lens.Iso

import Data.Maybe
import Data.Contravariant
import Data.Tensor
import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Equality

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsIso p where
  constructor MkIsIso
  runIsIso : Profunctor p


||| An `Iso` is an isomorphism family between types. It allows a value to be
||| converted or updated across this isomorphism.
public export
0 Iso : (s,t,a,b : Type) -> Type
Iso = Optic IsIso

||| An `Iso'` is an isomorphism family between types. It allows a value to be
||| converted or updated across this isomorphism.
||| This is the `Simple` version of `Iso`.
public export
0 Iso' : (s,a : Type) -> Type
Iso' = Simple Iso


------------------------------------------------------------------------------
-- Utilities for isomorphisms
------------------------------------------------------------------------------


-- Eliminators

||| Extract the conversion functions from an `Iso`.
public export
getIso : Iso s t a b -> (s -> a, b -> t)
getIso l = l @{MkIsIso coexp} (id, id)
  where
    [coexp] Profunctor (\x,y => (x -> a, b -> y)) where
      dimap f g (f', g') = (f' . f, g . g')

||| Extract the conversion functions from an `Iso`.
public export
withIso : Iso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso l f = uncurry f (getIso l)



-- Constructors

||| Construct an `Iso` from two inverse functions.
public export
iso : (s -> a) -> (b -> t) -> Iso s t a b
iso f g @{MkIsIso _} = dimap f g

||| Construct a simple `Iso` from an equivalence.
public export
fromEqv : s <=> a -> Iso' s a
fromEqv (MkEquivalence l r) = iso l r

||| Invert an isomorphism.
public export
from : Iso s t a b -> Iso b a t s
from l @{MkIsIso _} = withIso l (flip dimap)


-- `au`

||| Based on Epigram's `ala`.
public export
au : Functor f => Iso s t a b -> ((b -> t) -> f s) -> f a
au l f = withIso l $ \g,h => g <$> f h

||| Based on Epigram's `ala'`.
public export
auf : (Functor f, Functor g) => Iso s t a b -> (f t -> g s) -> f b -> g a
auf l f x = withIso l $ \g,h => g <$> f (h <$> x)

||| An alias for `au . from`.
public export
xplat : Functor f => Iso s t a b -> ((s -> a) -> f b) -> f t
xplat l f = withIso l $ \g,h => h <$> f g

||| an alias for `auf . from`.
public export
xplatf : (Functor f, Functor g) => Iso s t a b -> (f a -> g b) -> f s -> g t
xplatf l f x = withIso l $ \g,h => h <$> f (g <$> x)


||| Update a value under an `Iso`, as opposed to `over` it.
||| In other words, this is a convenient alias for `over . from`.
public export
under : Iso s t a b -> (t -> s) -> (b -> a)
under l = let (f,g) = getIso l in (f .) . (. g)


-- Examples of isomorphisms

||| An "isomorphism" between a function and its result type, assuming that
||| the parameter type is inhabited.
public export
constant : a -> Iso (a -> b) (a' -> b') b b'
constant x = iso ($ x) const

||| Construct an isomorphism given an involution.
public export
involuted : (a -> a) -> Iso' a a
involuted f = iso f f

||| Flipping a function's arguments forms an isomorphism.
public export
flipped : Iso (a -> b -> c) (a' -> b' -> c') (b -> a -> c) (b' -> a' -> c')
flipped = iso flip flip

||| Swapping a symmetric tensor product's parameters is an isomorphism.
public export
swapped : Symmetric f => Iso (f a b) (f a' b') (f b a) (f b' a')
swapped = iso swap' swap'

||| Casting between types forms an isomorphism.
||| WARNING: This is only a true isomorphism if casts in both directions are
||| lossless and mutually inverse.
public export
casted : (Cast s a, Cast b t) => Iso s t a b
casted = iso cast cast

||| The isomorphism `non x` converts between `Maybe a` and `a` sans the
||| element `x`.
|||
||| This is useful for working with optics whose focus type is `Maybe a`,
||| such as `at`.
public export
non : Eq a => a -> Iso' (Maybe a) a
non x = iso (fromMaybe x) (\y => guard (x /= y) $> y)


-- Mapping

||| Lift an isomorphism through a `Functor`.
public export
mapping : (Functor f, Functor g) => Iso s t a b -> Iso (f s) (g t) (f a) (g b)
mapping l = withIso l $ \f,g => iso (map f) (map g)

||| Lift an isomorphism through a `Contravariant` functor.
public export
contramapping : (Contravariant f, Contravariant g) => Iso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping l = withIso l $ \f,g => iso (contramap f) (contramap g)

||| Lift isomorphisms through a `Bifunctor`.
public export
bimapping : (Bifunctor f, Bifunctor g) => Iso s t a b -> Iso s' t' a' b' ->
              Iso (f s s') (g t t') (f a a') (g b b')
bimapping l r = withIso l $ \f,g => withIso r $ \f',g' =>
  iso (bimap f f') (bimap g g')

||| Lift an isomorphism through the first parameter of a `Bifunctor`.
public export
mappingFst : (Bifunctor f, Bifunctor g) => Iso s t a b ->
              Iso (f s x) (g t y) (f a x) (g b y)
mappingFst l = withIso l $ \f,g => iso (mapFst f) (mapFst g)

||| Lift an isomorphism through the second parameter of a `Bifunctor`.
public export
mappingSnd : (Bifunctor f, Bifunctor g) => Iso s t a b ->
              Iso (f x s) (g y t) (f x a) (g y b)
mappingSnd l = withIso l $ \f,g => iso (mapSnd f) (mapSnd g)

||| Lift isomorphisms through a `Profunctor`.
public export
dimapping : (Profunctor f, Profunctor g) => Iso s t a b -> Iso s' t' a' b' ->
              Iso (f a s') (g b t') (f s a') (g t b')
dimapping l r = withIso l $ \f,g => withIso r $ \f',g' =>
  iso (dimap f f') (dimap g g')

||| Lift an isomorphism through the first parameter of a `Profunctor`.
public export
lmapping : (Profunctor f, Profunctor g) => Iso s t a b ->
              Iso (f a x) (g b y) (f s x) (g t y)
lmapping l = withIso l $ \f,g => iso (lmap f) (lmap g)

||| Lift an isomorphism through the second parameter of a `Profunctor`.
public export
rmapping : (Profunctor f, Profunctor g) => Iso s t a b ->
              Iso (f x s) (g y t) (f x a) (g y b)
rmapping l = withIso l $ \f,g => iso (rmap f) (rmap g)

