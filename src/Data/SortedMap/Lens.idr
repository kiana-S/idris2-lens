module Data.SortedMap.Lens

import Decidable.Equality
import Data.SortedMap.Dependent
import Data.SortedMap
import public Control.Lens

%default total


public export
Ixed k v (SortedMap k v) where
  ix k = optional' (lookup k) (flip $ insert k)

public export
At k v (SortedMap k v) where
  at k = lens (lookup k) (flip $ \case
    Nothing => delete k
    Just v => insert k v)


public export
ixDep : DecEq k => {0 p : k -> Type} -> (x : k) ->
          Optional' (SortedDMap k p) (p x)
ixDep {p} x = optional' (lookupPrecise x) (\m,v => insert x v m)

public export
atDep : DecEq k => {0 p : k -> Type} -> (x : k) ->
          Lens' (SortedDMap k p) (Maybe $ p x)
atDep {p} x = lens (lookupPrecise x) (\m => \case
  Nothing => delete x m
  Just v => insert x v m)


public export
Each (SortedMap k v) (SortedMap k w) v w where
  each = traversed

public export
IEach k (SortedMap k v) (SortedMap k w) v w where
  ieach = itraversal func
    where
      func : Applicative f => (k -> v -> f w) -> SortedMap k v -> f (SortedMap k w)
      func f = map (cast {from = SortedDMap k (const w)})
                . Dependent.traverse (f %search)
                . cast {to = SortedDMap k (const v)}
