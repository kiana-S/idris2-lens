||| A system for type-safe, traversal-based zippers into arbitrary datatypes.
module Control.Zipper

import Data.Maybe
import Data.List
import Control.Lens

%default total


------------------------------------------------------------------------------
-- Pointer
------------------------------------------------------------------------------


Pointer : (i, a : Type) -> Type
Pointer i a = (SnocList (i, a), List (i, a))

fromPointer : i -> a -> Pointer i a -> List (i, a)
fromPointer k x (l, r) = l <>> (k,x) :: r


------------------------------------------------------------------------------
-- Zipper
------------------------------------------------------------------------------


infix 9 @>
public export
data ZipLayer : Type where
  (@>) : (i, a : Type) -> ZipLayer

public export
getTy : ZipLayer -> Type
getTy (_ @> a) = a


data Coil : List ZipLayer -> Type -> Type -> Type where
  Nil  : Coil [] i a
  Cons : Pointer j s -> j -> (List (i, a) -> s) ->
          Coil hs j s -> Coil (j @> s :: hs) i a


export
data Zipper : List ZipLayer -> Type -> Type -> Type where
  MkZipper : Coil hs i a -> Pointer i a -> i -> a -> Zipper hs i a


export
zipper : a -> Zipper [] () a
zipper x = MkZipper Nil ([<], []) () x

export
focus : IndexedLens' i (Zipper hs i a) a
focus = ilens (\(MkZipper _ _ i x) => (i, x))
              (\(MkZipper coil p i _),x => MkZipper coil p i x)


------------------------------------------------------------------------------
-- Zipper movement
------------------------------------------------------------------------------


export
upward : Zipper (j @> s :: hs) i a -> Zipper hs j s
upward (MkZipper (Cons p j k coil) q i x) =
  MkZipper coil p j $ k $ fromPointer i x q

export
tug : (a -> Maybe a) -> a -> a
tug f x = fromMaybe x (f x)

export
rightward : Alternative f => Zipper hs i a -> f (Zipper hs i a)
rightward (MkZipper _ (_, []) _ _) = empty
rightward (MkZipper coil (l, (j,y) :: r) i x) =
  pure $ MkZipper coil (l :< (i,x), r) j y

export
leftward : Alternative f => Zipper hs i a -> f (Zipper hs i a)
leftward (MkZipper _ ([<], _) _ _) = empty
leftward (MkZipper coil (l :< (j,y), r) i x) =
  pure $ MkZipper coil (l, (i,x) :: r) j y

export
leftmost : Zipper hs i a -> Zipper hs i a
leftmost (MkZipper coil p i x) =
  case fromPointer i x p of
    (j,y) :: xs => MkZipper coil ([<], xs) j y
    -- Too lazy to prove this impossible for now
    [] => assert_total $ idris_crash "Unreachable"

export
rightmost : Zipper hs i a -> Zipper hs i a
rightmost (MkZipper coil (l,r) i x) =
  case l :< (i,x) <>< r of
    xs :< (j,y) => MkZipper coil (xs, []) j y
    -- Too lazy to prove this impossible for now
    [<] => assert_total $ idris_crash "Unreachable"


export
idownward : IndexedLens' i s a -> Zipper hs j s -> Zipper (j @> s :: hs) i a
idownward l (MkZipper coil p j y) =
  let (i,x) = iview l y
  in MkZipper (Cons p j (go . map snd) coil) ([<],[]) i x
  where
    go : List a -> s
    go ls = set (partsOf l) ls y

export
downward : Lens' s a -> Zipper hs j s -> Zipper (j @> s :: hs) () a
downward l (MkZipper coil p i x) =
  MkZipper (Cons p i (go . map snd) coil) ([<], []) () (x ^. l)
  where
    go : List a -> s
    go ls = set (partsOf l) ls x

export
iwithin : Alternative f => IndexedTraversal' i s a -> Zipper hs j s -> f (Zipper (j @> s :: hs) i a)
iwithin l (MkZipper coil p j y) =
  case itoListOf l y of
    (i,x) :: xs => pure $ MkZipper (Cons p j (go . map snd) coil) ([<], xs) i x
    [] => empty
  where
    go : List a -> s
    go ls = set (partsOf l) ls y

export
within : Alternative f => Traversal' s a -> Zipper hs j s -> f (Zipper (j @> s :: hs) Nat a)
within = iwithin . iordinal


recoil : Coil hs i a -> List (i, a) -> getTy $ last (i @> a :: hs)
recoil Nil xs = assert_total $ case xs of (_,x) :: _ => x
recoil (Cons p i f coil) xs = recoil coil $ fromPointer i (f xs) p

export
rezip : Zipper hs i a -> getTy $ last (i @> a :: hs)
rezip (MkZipper coil p i x) = recoil coil $ fromPointer i x p
