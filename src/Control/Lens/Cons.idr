module Control.Lens.Cons

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Iso
import Control.Lens.Prism
import Control.Lens.Optional

%default total


public export
interface Cons s t a b | s where
  cons_ : Prism s t (a, s) (b, t)

public export
head_ : Cons s s a a => Optional' s a
head_ @{_} @{MkIsOptional _} = cons_ . first

public export
tail_ : Cons s s a a => Optional' s s
tail_ @{_} @{MkIsOptional _} = cons_ . second


public export
interface Snoc s t a b | s where
  snoc_ : Prism s t (s, a) (t, b)

public export
init_ : Snoc s s a a => Optional' s s
init_ @{_} @{MkIsOptional _} = snoc_ . first

public export
last_ : Snoc s s a a => Optional' s a
last_ @{_} @{MkIsOptional _} = snoc_ . second

