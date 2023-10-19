module Data.SortedSet.Lens

import Data.SortedSet
import public Control.Lens

%default total


public export
each : Fold (SortedSet k) k
each = folding SortedSet.toList


public export
Ixed k () (SortedSet k) where
  ix k = optional' (ignore . guard . contains k) const

public export
At k () (SortedSet k) where
  at k = lens (ignore . guard . contains k) (flip $ \case
    Nothing => delete k
    Just _ => insert k)
