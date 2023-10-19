module Data.Vect.Lens

import Data.Vect
import public Control.Lens
import Data.Tuple.Lens
import Data.Profunctor.Traversing

%default total


||| An isomorphism between a `Vect` and its reverse.
public export
reversed : Iso (Vect n a) (Vect n b) (Vect n a) (Vect n b)
reversed = iso reverse reverse


public export
Ixed Nat a (Vect n a) where
  ix = element

public export
Ixed' Nat (Fin n) a (Vect n a) where
  ix' n = lens (index n) (flip $ replaceAt n)

public export
Each (Vect n a) (Vect n b) a b where
  each = traversed

public export
IEach (Fin n) (Vect n a) (Vect n b) a b where
  ieach = itraversal func
    where
      func : forall n. Applicative f => (Fin n -> a -> f b) -> Vect n a -> f (Vect n b)
      func f [] = pure []
      func f (x :: xs) = [| f FZ x :: func (f . FS) xs |]


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
