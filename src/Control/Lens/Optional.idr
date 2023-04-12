module Control.Lens.Optional

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Lens
import Control.Lens.Prism

%default total

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


public export
0 Optional : (s,t,a,b : Type) -> Type
Optional = Optic IsOptional

public export
0 Optional' : (s,a : Type) -> Type
Optional' = Simple Optional


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

public export
optional' : (s -> Maybe a) -> (s -> b -> s) -> Optional s s a b
optional' prj = optional (\x => maybe (Left x) Right (prj x))


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

public export
withOptional : Optional s t a b -> ((s -> Either t a) -> (s -> b -> t) -> r) -> r
withOptional l f = uncurry f (getOptional l)


public export
ignored : Optional s s a b
ignored @{MkIsOptional _} = dimap @{fromStrong}
  (\x => (Left x, const x))
  (\(e, f) => either id (the (b -> s) f) e)
  . first . right
  where
    -- arbitrary choice of where to pull profunctor instance from
    fromStrong : Strong p => Profunctor p
    fromStrong = %search
