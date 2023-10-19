module Control.Lens.Cons

import Data.Profunctor
import Control.Lens.Optic
import Control.Lens.Iso
import Control.Lens.Prism
import Control.Lens.Review
import Control.Lens.Optional

%default total


||| An interface that provides a way to detach and inspect elements from the
||| left side of a sequence.
public export
interface Cons s t a b | s where
  ||| An isomorphism that can inspect the left side of a sequence.
  consIso : Iso s t (Maybe (a, s)) (Maybe (b, t))

  ||| A prism that can attach or detach a value from the left side of a
  ||| sequence.
  cons_ : Prism s t (a, s) (b, t)
  cons_ = consIso . prism Just (\case
    Nothing => Left Nothing
    Just x => Right x)

||| Access the head (left-most element) of a sequence, if it is non-empty.
public export
head_ : Cons s s a a => Optional' s a
head_ @{_} @{MkIsOptional _} = cons_ . first

||| Access the tail (all but the left-most element) of a sequence, if it is
||| non-empty.
public export
tail_ : Cons s s a a => Optional' s s
tail_ @{_} @{MkIsOptional _} = cons_ . second

||| Use a `Cons` implementation to construct an empty sequence.
public export
nil : Cons s s a a => s
nil = review consIso Nothing


||| An interface that provides a way to detach and inspect elements from the
||| right side of a sequence.
public export
interface Snoc s t a b | s where
  ||| An isomorphism that can inspect the right side of a sequence.
  snocIso : Iso s t (Maybe (s, a)) (Maybe (t, b))

  ||| This is a prism that can attach or detach a value from the right side of a
  ||| sequence.
  snoc_ : Prism s t (s, a) (t, b)
  snoc_ = snocIso . prism Just (\case
    Nothing => Left Nothing
    Just x => Right x)

||| Access all but the right-most element of a sequence, if it is non-empty.
public export
init_ : Snoc s s a a => Optional' s s
init_ @{_} @{MkIsOptional _} = snoc_ . first

||| Access the last (right-most) element of a sequence, if it is non-empty.
public export
last_ : Snoc s s a a => Optional' s a
last_ @{_} @{MkIsOptional _} = snoc_ . second

||| Use a `Snoc` implementation to construct an empty sequence.
public export
nil' : Snoc s s a a => s
nil' = review snocIso Nothing
