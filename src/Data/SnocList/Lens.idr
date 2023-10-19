module Data.SnocList.Lens

import Data.Zippable
import Data.SnocList
import Data.Profunctor
import public Control.Lens

%default total


stripPrefix : Eq a => SnocList a -> SnocList a -> Maybe (SnocList a)
stripPrefix qs xs0 = go xs0 zs
  where
    drp : SnocList a -> SnocList a -> SnocList a
    drp (ps :< _) (xs :< _) = drp ps xs
    drp [<] xs = xs
    drp _  [<] = [<]

    zs : SnocList a
    zs = drp qs xs0

    go : SnocList a -> SnocList a -> Maybe (SnocList a)
    go (xs :< _) (ys :< _) = go xs ys
    go xs [<] = zipWith const xs0 zs <$ guard (xs == qs)
    go [<] _  = Nothing

stripSuffix : Eq a => SnocList a -> SnocList a -> Maybe (SnocList a)
stripSuffix [<] ys = Just ys
stripSuffix (_ :< _) [<] = Nothing
stripSuffix (xs :< x) (ys :< y) = guard (x == y) *> stripSuffix xs ys


||| A prism that strips a prefix from a snoclist of values.
public export
prefixed : Eq a => SnocList a -> Prism' (SnocList a) (SnocList a)
prefixed xs = prism' (xs ++) (stripPrefix xs)

||| A prism that strips a suffix from a snoclist of values.
public export
suffixed : Eq a => SnocList a -> Prism' (SnocList a) (SnocList a)
suffixed xs = prism' (++ xs) (stripSuffix xs)

||| An isomorphism between a snoclist and its reverse.
public export
reversed : Iso (SnocList a) (SnocList b) (SnocList a) (SnocList b)
reversed = iso reverse reverse


public export
Ixed Nat a (SnocList a) where
  ix = element

public export
Snoc (SnocList a) (SnocList b) a b where
  snocIso = iso (\case
      [<] => Nothing
      xs :< x => Just (xs,x))
    (maybe [<] $ uncurry (:<))

  snoc_ = prism (uncurry (:<)) (\case
    [<] => Left [<]
    xs :< x => Right (xs,x))

uncons : SnocList a -> a -> (a, SnocList a)
uncons [<] x = (x, [<])
uncons (ys :< y) x = mapSnd (:< x) $ uncons ys y

public export
Cons (SnocList a) (SnocList b) a b where
  consIso = iso (\case
      [<] => Nothing
      xs :< x => Just $ uncons xs x)
    (maybe [<] $ uncurry cons)

  cons_ = prism (uncurry cons) (\case
    [<] => Left [<]
    xs :< x => Right $ uncons xs x)

public export
Each (SnocList a) (SnocList b) a b where
  each = traversed

public export
Num i => IEach i (SnocList a) (SnocList b) a b where
  ieach = itraversed
