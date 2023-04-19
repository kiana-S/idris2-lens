module Control.Lens.Prism

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.Iso

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsPrism p where
  constructor MkIsPrism
  runIsPrism : Choice p

export %hint
prismToIso : IsPrism p => IsIso p
prismToIso @{MkIsPrism _} = MkIsIso %search


||| A prism is a first-class reference to one of the cases of a sum type.
||| Prisms allow one to determine whether a value matches the focused case
||| and extract the corresponding data if it does.
|||
||| More precisely, a `Prism` is an `Optional` that can be flipped to obtain
||| a `Getter` in the opposite direction.
public export
0 Prism : (s,t,a,b : Type) -> Type
Prism = Optic IsPrism

||| `Prism'` is the `Simple` version of `Prism`.
public export
0 Prism' : (s,a : Type) -> Type
Prism' = Simple Prism

public export
0 IndexedPrism : (i,s,t,a,b : Type) -> Type
IndexedPrism = IndexedOptic IsPrism

public export
0 IndexedPrism' : (i,s,a : Type) -> Type
IndexedPrism' = Simple . IndexedPrism


------------------------------------------------------------------------------
-- Utilities for prisms
------------------------------------------------------------------------------


||| Construct a prism from injection and projection functions.
public export
prism : (b -> t) -> (s -> Either t a) -> Prism s t a b
prism inj prj @{MkIsPrism _} = dimap prj (either id inj) . right

||| Construct a simple prism from injection and projection functions.
public export
prism' : (b -> s) -> (s -> Maybe a) -> Prism s s a b
prism' inj prj = prism inj (\x => maybe (Left x) Right (prj x))

public export
iprism : (b -> t) -> (s -> Either t (i, a)) -> IndexedPrism i s t a b
iprism inj prj @{_} @{ind} = prism inj prj . indexed @{ind}

public export
iprism' : (b -> s) -> (s -> Maybe (i, a)) -> IndexedPrism i s s a b
iprism' inj prj = iprism inj (\x => maybe (Left x) Right (prj x))


||| Extract injection and projection functions from a prism.
public export
getPrism : Prism s t a b -> (b -> t, s -> Either t a)
getPrism l = l @{MkIsPrism choice} (id, Right)
  where
    Profunctor (\x,y => (b -> y, x -> Either y a)) where
      dimap f g (inj, prj) = (g . inj, either (Left . g) Right . prj . f)

    [choice] GenStrong Either (\x,y => (b -> y, x -> Either y a)) where
      strongl (inj, prj) = (Left . inj, either (either (Left . Left) Right . prj) (Left . Right))
      strongr (inj, prj) = (Right . inj, either (Left . Left) (either (Left . Right) Right . prj))

||| Extract injection and projection functions from a prism.
public export
withPrism : Prism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism l f = uncurry f (getPrism l)


||| Construct a prism that uses a predicate to determine if a value matches.
public export
nearly : a -> (a -> Bool) -> Prism' a ()
nearly x p = prism' (const x) (guard . p)

||| Construct a prism that matches only one value.
public export
only : Eq a => a -> Prism' a ()
only x = nearly x (x ==)


||| Create a prism that operates on `Either` values from two other prisms.
|||
||| This can be seen as dual to `alongside`.
public export
without : Prism s t a b -> Prism s' t' a' b' -> Prism (Either s s') (Either t t') (Either a a') (Either b b')
without l l' =
  let (inj1, prj1) = getPrism l
      (inj2, prj2) = getPrism l'
  in prism (bimap inj1 inj2) (either (bimap Left Left . prj1) (bimap Right Right . prj2))

||| Lift a prism through a `Traversable` container.
|||
||| The constructed prism will only match if all of the inner elements of the
||| `Traversable` container match.
public export
below : Traversable f => Prism' s a -> Prism' (f s) (f a)
below l = withPrism l $ \inj,prj =>
  prism (map inj) $ \s => mapFst (const s) (traverse prj s)

||| Lift a prism through part of a product type.
public export
aside : Prism s t a b -> Prism (e, s) (e, t) (e, a) (e, b)
aside l = withPrism l $ \inj,prj => prism (map inj) $ \(e,s) => bimap (e,) (e,) (prj s)
