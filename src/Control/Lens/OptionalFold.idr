module Control.Lens.OptionalFold

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Optional
import Control.Lens.Getter

%default total


public export
record IsOptFold p where
  constructor MkIsOptFold
  runIsOptFold : (Strong p, Choice p, Cochoice p, Bicontravariant p)

export %hint
optFoldToOptional : IsOptFold p => IsOptional p
optFoldToOptional @{MkIsOptFold _} = MkIsOptional %search

export %hint
optFoldToGetter : IsOptFold p => IsGetter p
optFoldToGetter @{MkIsOptFold _} = MkIsGetter %search


public export
0 OptionalFold : (s,a : Type) -> Type
OptionalFold = Simple (Optic IsOptFold)


public export
folding : (s -> Maybe a) -> OptionalFold s a
folding f @{MkIsOptFold _} =
  contrabimap (\x => maybe (Left x) Right (f x)) Left . right

public export
filtered : (a -> Bool) -> OptionalFold a a
filtered p = folding (\x => if p x then Just x else Nothing)
