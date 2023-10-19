module Data.List1.Lens

import Data.List1
import Data.Profunctor
import public Control.Lens
import Data.Tuple.Lens

%default total

||| An isomorphism between a list and its reverse.
public export
reversed : Iso (List1 a) (List1 b) (List1 a) (List1 b)
reversed = iso reverse reverse


public export
cons_ : Iso (List1 a) (List1 b) (a, List a) (b, List b)
cons_ = iso (\(x:::xs) => (x,xs)) (uncurry (:::))

public export
head_ : Lens' (List1 a) a
head_ = cons_ . fst_

public export
tail_ : Lens' (List1 a) (List a)
tail_ = cons_ . snd_

public export
snoc_ : Iso (List1 a) (List1 b) (List a, a) (List b, b)
snoc_ = iso unsnoc (uncurry lappend . mapSnd singleton)

public export
init_ : Lens' (List1 a) (List a)
init_ = snoc_ . fst_

public export
last_ : Lens' (List1 a) a
last_ = snoc_ . snd_


public export
Ixed Nat a (List1 a) where
  ix = element

public export
Each (List1 a) (List1 b) a b where
  each = traversed

public export
Num i => IEach i (List1 a) (List1 b) a b where
  ieach = itraversed
