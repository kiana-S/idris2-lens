module Data.List.Lens

import Data.List
import Data.Profunctor
import public Control.Lens

%default total


stripPrefix : Eq a => List a -> List a -> Maybe (List a)
stripPrefix [] ys = Just ys
stripPrefix (_ :: _) [] = Nothing
stripPrefix (x :: xs) (y :: ys) = guard (x == y) *> stripPrefix xs ys

stripSuffix : Eq a => List a -> List a -> Maybe (List a)
stripSuffix qs xs0 = go xs0 zs
  where
    drp : List a -> List a -> List a
    drp (_::ps) (_::xs) = drp ps xs
    drp [] xs = xs
    drp _  [] = []

    zs : List a
    zs = drp qs xs0

    go : List a -> List a -> Maybe (List a)
    go (_::xs) (_::ys) = go xs ys
    go xs [] = zipWith const xs0 zs <$ guard (xs == qs)
    go [] _  = Nothing


||| A prism that strips a prefix from a list of values.
public export
prefixed : Eq a => List a -> Prism' (List a) (List a)
prefixed xs = prism' (xs ++) (stripPrefix xs)

||| A prism that strips a suffix from a list of values.
public export
suffixed : Eq a => List a -> Prism' (List a) (List a)
suffixed xs = prism' (++ xs) (stripSuffix xs)


||| An isomorphism between a list and its reverse.
public export
reversed : Iso (List a) (List b) (List a) (List b)
reversed = iso reverse reverse


public export
Ixed Nat a (List a) where
  ix n = optional' (getAt n) (\xs,x => case inBounds n xs of
    Yes _ => replaceAt n x xs
    No _ => xs)


public export
Cons (List a) (List b) a b where
  cons_ = prism (uncurry (::)) (\case
    [] => Left []
    x :: xs => Right (x, xs))

public export
Snoc (List a) (List b) a b where
  snoc_ = prism (uncurry snoc) (\case
    [] => Left []
    x :: xs => Right $ unsnoc x xs)
    where
      unsnoc : a -> List a -> (List a, a)
      unsnoc x [] = ([], x)
      unsnoc x (y :: xs) = mapFst (x ::) $ unsnoc y xs
