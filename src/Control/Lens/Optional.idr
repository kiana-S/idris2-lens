module Control.Lens.Optional

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Lens
import Control.Lens.Prism

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsOptional p where
  constructor MkIsOptional
  runIsOptional : (Strong p, Choice p)

export %hint
optionalToLens : IsOptional p => IsLens p
optionalToLens @{MkIsOptional _} = MkIsLens %search

export %hint
optionalToPrism : IsOptional p => IsPrism p
optionalToPrism @{MkIsOptional _} = MkIsPrism %search


||| An `Optional` is a lens that may or may not contain the focus value.
||| As such, accesses will return a `Maybe` value.
public export
0 Optional : (s,t,a,b : Type) -> Type
Optional = Optic IsOptional

||| `Optional'` is the `Simple` version of `Optional`.
public export
0 Optional' : (s,a : Type) -> Type
Optional' = Simple Optional


------------------------------------------------------------------------------
-- Utilities for Optionals
------------------------------------------------------------------------------


||| Construct an optional from a projection and a setter function.
public export
optional : (s -> Either t a) -> (s -> b -> t) -> Optional s t a b
optional prj set @{MkIsOptional _} = dimap @{fromStrong}
  (\s => (prj s, set s))
  (\(e, f) => either id f e)
  . first . right
  where
    -- arbitrary choice of where to pull profunctor instance from
    fromStrong : Strong p => Profunctor p
    fromStrong = %search

||| Construct a simple optional from a projection and a setter function.
public export
optional' : (s -> Maybe a) -> (s -> b -> s) -> Optional s s a b
optional' prj = optional (\x => maybe (Left x) Right (prj x))

||| The trivial optic that has no focuses.
public export
ignored : Optional s s a b
ignored = optional' (const Nothing) const


||| Extract projection and setter functions from an optional.
public export
getOptional : Optional s t a b -> (s -> Either t a, s -> b -> t)
getOptional l = l @{MkIsOptional (strong,choice)} (Right, const id)
  where
    Profunctor (\x,y => (x -> Either y a, x -> b -> y)) where
      dimap f g (prj, set) = (either (Left . g) Right . prj . f, (g .) . set . f)

    [strong] GenStrong Pair (\x,y => (x -> Either y a, x -> b -> y)) where
      strongl (prj, set) = (\(a,c) => mapFst (,c) (prj a), \(a,c),b => (set a b, c))
      strongr (prj, set) = (\(c,a) => mapFst (c,) (prj a), \(c,a),b => (c, set a b))

    [choice] GenStrong Either (\x,y => (x -> Either y a, x -> b -> y)) where
      strongl (prj, set) = (either (either (Left . Left) Right . prj) (Left . Right),
                            \e,b => mapFst (`set` b) e)
      strongr (prj, set) = (either (Left . Left) (either (Left . Right) Right . prj),
                            \e,b => mapSnd (`set` b) e)

||| Extract projection and setter functions from an optional.
public export
withOptional : Optional s t a b -> ((s -> Either t a) -> (s -> b -> t) -> r) -> r
withOptional l f = uncurry f (getOptional l)

||| Retrieve the focus value of an optional, or allow its type to change if there
||| is no focus.
public export
matching : Prism s t a b -> s -> Either t a
matching = snd . getPrism
