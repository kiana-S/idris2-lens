module Control.Lens.Prism

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Iso

%default total


public export
record IsPrism p where
  constructor MkIsPrism
  runIsPrism : Choice p

export %hint
prismToIso : IsPrism p => IsIso p
prismToIso @{MkIsPrism _} = MkIsIso %search


public export
0 Prism : (s,t,a,b : Type) -> Type
Prism = Optic IsPrism

public export
0 Prism' : (s,a : Type) -> Type
Prism' s a = Prism s s a a


public export
prism : (b -> t) -> (s -> Either t a) -> Prism s t a b
prism inj prj @{MkIsPrism _} = dimap prj (either id inj) . right

public export
prism' : (b -> s) -> (s -> Maybe a) -> Prism s s a b
prism' inj prj = prism inj (\x => maybe (Left x) Right (prj x))


public export
getPrism : Prism s t a b -> (b -> t, s -> Either t a)
getPrism l = l @{MkIsPrism choice} (id, Right)
  where
    Profunctor (\x,y => (b -> y, x -> Either y a)) where
      dimap f g (inj, prj) = (g . inj, either (Left . g) Right . prj . f)

    [choice] GenStrong Either (\x,y => (b -> y, x -> Either y a)) where
      strongl (inj, prj) = (Left . inj, either (either (Left . Left) Right . prj) (Left . Right))
      strongr (inj, prj) = (Right . inj, either (Left . Left) (either (Left . Right) Right . prj))

public export
withPrism : Prism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism l f = uncurry f (getPrism l)


public export
nearly : a -> (a -> Bool) -> Prism' a ()
nearly x p = prism' (const x) (guard . p)

public export
only : Eq a => a -> Prism' a ()
only x = nearly x (x ==)
