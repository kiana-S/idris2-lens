module Control.Lens.Lens

import Data.Profunctor
import Data.Profunctor.Yoneda
import Control.Lens.Optic
import Control.Lens.Equality
import Control.Lens.Iso

%default total


public export
record IsLens p where
  constructor MkIsLens
  runIsLens : Strong p

export %hint
lensToIso : IsLens p => IsIso p
lensToIso @{MkIsLens _} = MkIsIso %search


public export
0 Lens : (s,t,a,b : Type) -> Type
Lens = Optic IsLens

public export
0 Lens' : (s,a : Type) -> Type
Lens' = Simple Lens


public export
lens : (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get set @{MkIsLens _} = dimap (\x => (x, get x)) (uncurry set) . second

public export
getLens : Lens s t a b -> (s -> a, s -> b -> t)
getLens l = l @{MkIsLens strong} (id, const id)
  where
    Profunctor (\x,y => (x -> a, x -> b -> y)) where
      dimap f g (get, set) = (get . f, (g .) . set . f)

    [strong] GenStrong Pair (\x,y => (x -> a, x -> b -> y)) where
      strongl (get, set) = (get . fst, \(a,c),b => (set a b, c))
      strongr (get, set) = (get . snd, \(c,a),b => (c, set a b))

public export
withLens : Lens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = uncurry f (getLens l)


public export
devoid : Lens Void Void a b
devoid @{MkIsLens _} = dimap absurd snd . first

public export
united : Lens' a ()
united @{MkIsLens _} = dimap ((),) snd . first



public export
fusing : IsIso p => Optic' (Yoneda p) s t a b -> Optic' p s t a b
fusing @{MkIsIso _} l = proextract . l . propure
