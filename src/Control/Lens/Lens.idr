module Control.Lens.Lens

import Data.Profunctor
import Data.Profunctor.Yoneda
import Control.Lens.Optic
import Control.Lens.Equality
import Control.Lens.Iso

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsLens p where
  constructor MkIsLens
  runIsLens : Strong p

export %hint
lensToIso : IsLens p => IsIso p
lensToIso @{MkIsLens _} = MkIsIso %search


||| A *lens* is a functional reference to a value within a larger data structure.
||| Lenses allow one to access or modify the value that they reference, called
||| the "focus" or "focus element".
|||
||| For example, the lens `fst_` from `Data.Tuple.Lens` focuses on the first
||| element of a pair. It has the type:
|||
||| ```idris
||| fst_ : Lens (a, c) (b, c) a b
||| ```
|||
||| The types `s, t` correspond to the type of the outside data structure, and
||| `a, b` correspond to the type of the focus element. Two of each type is
||| provided to allow for operations that change the type of the focus.
public export
0 Lens : (s,t,a,b : Type) -> Type
Lens = Optic IsLens

||| `Lens'` is the `Simple` version of `Lens`.
public export
0 Lens' : (s,a : Type) -> Type
Lens' = Simple Lens


------------------------------------------------------------------------------
-- Utilities for lenses
------------------------------------------------------------------------------


||| Construct a lens given getter and setter functions.
|||
||| @ get The getter function
||| @ set The setter function, where the first argument is the data structure
||| to modify and the second argument is the new focus value
public export
lens : (get : s -> a) -> (set : s -> b -> t) -> Lens s t a b
lens get set @{MkIsLens _} = dimap (\x => (x, get x)) (uncurry set) . second

||| Extract getter and setter functions from a lens.
public export
getLens : Lens s t a b -> (s -> a, s -> b -> t)
getLens l = l @{MkIsLens strong} (id, const id)
  where
    Profunctor (\x,y => (x -> a, x -> b -> y)) where
      dimap f g (get, set) = (get . f, (g .) . set . f)

    [strong] GenStrong Pair (\x,y => (x -> a, x -> b -> y)) where
      strongl (get, set) = (get . fst, \(a,c),b => (set a b, c))
      strongr (get, set) = (get . snd, \(c,a),b => (c, set a b))

||| Extract getter and setter functions from a lens.
public export
withLens : Lens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = uncurry f (getLens l)


||| `Void` vacuously "contains" a value of any other type.
public export
devoid : Lens Void Void a b
devoid @{MkIsLens _} = dimap absurd snd . first

||| All values contain a unit.
public export
united : Lens' a ()
united @{MkIsLens _} = dimap ((),) snd . first

||| Create a lens that operates on pairs from two other lenses.
public export
alongside : Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
alongside l l' =
  let (get1, set1) = getLens l
      (get2, set2) = getLens l'
  in lens (bimap get1 get2) (uncurry bimap . bimap set1 set2)



||| Optimize a composition of optics by fusing their uses of `dimap` into one.
|||
||| This function exploits the Yoneda lemma. `fusing (a . b)` is essentially
||| equivalent to `a . b`, but the former will only call `dimap` once.
public export
fusing : IsIso p => Optic' (Yoneda p) s t a b -> Optic' p s t a b
fusing @{MkIsIso _} l = proextract . l . propure
