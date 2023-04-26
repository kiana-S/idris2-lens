module Data.Stream.Lens

import Data.Stream
import public Control.Lens
import Data.Tuple.Lens

%default total


replaceList : List a -> Stream a -> Stream a
replaceList [] ys = ys
replaceList (x :: xs) (_ :: ys) = x :: replaceList xs ys

replaceAt : Nat -> a -> Stream a -> Stream a
replaceAt Z x (_ :: ys) = x :: ys
replaceAt (S n) x (y :: ys) = y :: replaceAt n x ys


public export
cons_ : Iso (Stream a) (Stream b) (a, Stream a) (b, Stream b)
cons_ = iso (\(x::xs) => (x,xs)) (\(x,xs) => x::xs)

public export
head_ : Lens' (Stream a) a
head_ = cons_ . fst_

public export
tail_ : Lens' (Stream a) (Stream a)
tail_ = cons_ . snd_


public export
taken' : Nat -> Lens' (Stream a) (List a)
taken' n = lens (take n) (flip replaceList)

public export
taken : Nat -> Traversal' (Stream a) a
taken n = taken' n . traversed


public export
Ixed Nat a (Stream a) where
  ix n = lens (index n) (flip $ replaceAt n)

public export
Ixed' Nat Nat a (Stream a) where
  ix' n = lens (index n) (flip $ replaceAt n)
