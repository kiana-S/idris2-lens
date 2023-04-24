module Data.Vect.Lens

import Data.Vect
import public Control.Lens
import Data.Tuple.Lens

%default total


||| An isomorphism between a `Vect` and its reverse.
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


public export
cons_ : Iso (Vect (S n) a) (Vect (S n) b) (a, Vect n a) (b, Vect n b)
cons_ = iso (\(x :: xs) => (x,xs)) (uncurry (::))

public export
head_ : Lens' (Vect (S n) a) a
head_ = cons_ . fst_

public export
tail_ : Lens' (Vect (S n) a) (Vect n a)
tail_ = cons_ . snd_

public export
snoc_ : Iso (Vect (S n) a) (Vect (S n) b) (Vect n a, a) (Vect n b, b)
snoc_ = iso unsnoc (uncurry snoc)

public export
init_ : Lens' (Vect (S n) a) (Vect n a)
init_ = snoc_ . fst_

public export
last_ : Lens' (Vect (S n) a) a
last_ = snoc_ . snd_
