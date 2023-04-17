module Data.Vect.Lens

import Data.Vect
import Control.Lens

%default total


public export
reversed : Iso (Vect n a) (Vect n b) (Vect n a) (Vect n b)
reversed = iso reverse reverse


public export
Ixed Nat a (Vect n a) where
  ix n = optional' (ixMaybe n) (set n)
    where
      ixMaybe : forall n. Nat -> Vect n a -> Maybe a
      ixMaybe _ [] = Nothing
      ixMaybe Z (x :: _) = Just x
      ixMaybe (S n) (_ :: xs) = ixMaybe n xs

      set : forall n. Nat -> Vect n a -> a -> Vect n a
      set _ [] _ = []
      set Z (_ :: xs) y = y :: xs
      set (S n) (x :: xs) y = x :: set n xs y


public export
Ixed' Nat (Fin n) a (Vect n a) where
  ix' n = lens (index n) (flip $ replaceAt n)
