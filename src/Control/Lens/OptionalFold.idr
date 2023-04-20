module Control.Lens.OptionalFold

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.Optional
import Control.Lens.Getter

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsOptFold p where
  constructor MkIsOptFold
  runIsOptFold : (Strong p, Choice p, Bicontravariant p)

export %hint
optFoldToOptional : IsOptFold p => IsOptional p
optFoldToOptional @{MkIsOptFold _} = MkIsOptional %search

export %hint
optFoldToGetter : IsOptFold p => IsGetter p
optFoldToGetter @{MkIsOptFold _} = MkIsGetter %search

export %hint
indexedOptFold : IsOptFold p => IsOptFold (Indexed i p)
indexedOptFold @{MkIsOptFold _} = MkIsOptFold %search


||| An `OptionalFold` is a getter that may not return a focus value.
||| `OptionalFold s a` is equivalent to `s -> Maybe a`.
public export
0 OptionalFold : (s,a : Type) -> Type
OptionalFold = Simple (Optic IsOptFold)

public export
0 IndexedOptionalFold : (i,s,a : Type) -> Type
IndexedOptionalFold = Simple . IndexedOptic IsOptFold


------------------------------------------------------------------------------
-- Utilities for OptionalFolds
------------------------------------------------------------------------------


||| Construct an `OptionalFold` from a function.
public export
folding : (s -> Maybe a) -> OptionalFold s a
folding f @{MkIsOptFold _} =
  contrabimap (\x => maybe (Left x) Right (f x)) Left . right

public export
ifolding : (s -> Maybe (i, a)) -> IndexedOptionalFold i s a
ifolding f @{MkIsOptFold _} @{ind} =
  contrabimap (\x => maybe (Left x) Right (f x)) Left . right . indexed @{ind}


||| Construct an `OptionalFold` that can be used to filter the focuses
||| of another optic.
|||
||| To be more specific, this optic passes the value through unchanged if it
||| satisfies the predicate and returns no values if it does not.
public export
filtered : (a -> Bool) -> OptionalFold a a
filtered p = folding (\x => if p x then Just x else Nothing)
