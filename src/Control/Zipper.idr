||| A system for type-safe, traversal-based zippers into arbitrary datatypes.
module Control.Zipper

import Data.Maybe
import Data.List
import Control.Lens

%default total


------------------------------------------------------------------------------
-- Pointer
------------------------------------------------------------------------------


||| The pointer stores the values on the current layer other than the focused one,
||| indirectly pointing to the focused value.
Pointer : (i, a : Type) -> Type
Pointer i a = (SnocList (i, a), List (i, a))

fromPointer : i -> a -> Pointer i a -> List (i, a)
fromPointer k x (l, r) = l <>> (k,x) :: r


------------------------------------------------------------------------------
-- Zipper
------------------------------------------------------------------------------


infix 9 @>

||| A simple type that represents a layer of the zipper as it moves downwards.
|||
||| It also carries an index for that particular layer, if an indexed lens was
||| used to create it.
public export
data ZipLayer : Type where
  (@>) : (i, a : Type) -> ZipLayer

||| Get the type from a layer of a zipper.
public export
getTy : ZipLayer -> Type
getTy (_ @> a) = a


||| The coil keeps track of the data not being focused on by the zipper, and
||| allows the final value to be repackaged at the end.
data Coil : List ZipLayer -> Type -> Type -> Type where
  Nil  : Coil [] i a
  Cons : Pointer j s -> j -> (List (i, a) -> s) ->
          Coil hs j s -> Coil (j @> s :: hs) i a


||| A zipper is a temporary data structure that can be "opened" on a particular
||| value, and allows one to move through its structure and operate on any
||| part of it.
||| A zipper can be opened from *any* value using `zipper`.
|||
||| Rather than being defined for a particular data structure, this zipper type
||| uses lenses to traverse through its value. The zipper can be moved down
||| through a traversal or lens, up out of one, or left and right between the
||| focuses of a traversal.
|||
||| You can use `rezip` to repackage the zipper back into a regular value.
export
data Zipper : List ZipLayer -> Type -> Type -> Type where
  MkZipper : Coil hs i a -> Pointer i a -> i -> a -> Zipper hs i a


||| Open a zipper from a value.
export
zipper : a -> Zipper [] () a
zipper x = MkZipper Nil ([<], []) () x

||| A lens that points to the current focus of the zipper.
export
focus : IndexedLens' i (Zipper hs i a) a
focus = ilens (\(MkZipper _ _ i x) => (i, x))
              (\(MkZipper coil p i _),x => MkZipper coil p i x)


------------------------------------------------------------------------------
-- Zipper movement
------------------------------------------------------------------------------


||| Move up a layer of the zipper.
export
upward : Zipper (j @> s :: hs) i a -> Zipper hs j s
upward (MkZipper (Cons p j k coil) q i x) =
  MkZipper coil p j $ k $ fromPointer i x q

||| Perform an action on a zipper, but leave the zipper's state unchanged if the
||| action fails.
|||
||| This is intended to be used as `tug rightward`, `tug leftward`, etc.
export
tug : (a -> Maybe a) -> a -> a
tug f x = fromMaybe x (f x)

||| Move right one value in the current layer. This will fail if already at the
||| rightmost value.
export
rightward : Alternative f => Zipper hs i a -> f (Zipper hs i a)
rightward (MkZipper _ (_, []) _ _) = empty
rightward (MkZipper coil (l, (j,y) :: r) i x) =
  pure $ MkZipper coil (l :< (i,x), r) j y

||| Move left one value in the current layer. This will fail if already at the
||| leftmost value.
export
leftward : Alternative f => Zipper hs i a -> f (Zipper hs i a)
leftward (MkZipper _ ([<], _) _ _) = empty
leftward (MkZipper coil (l :< (j,y), r) i x) =
  pure $ MkZipper coil (l, (i,x) :: r) j y

||| Move to the rightmost value in the current layer.
export
rightmost : Zipper hs i a -> Zipper hs i a
rightmost (MkZipper coil (l,r) i x) =
  case l :< (i,x) <>< r of
    xs :< (j,y) => MkZipper coil (xs, []) j y
    -- Too lazy to prove this impossible for now
    [<] => assert_total $ idris_crash "Unreachable"

||| Move to the leftmost value in the current layer.
export
leftmost : Zipper hs i a -> Zipper hs i a
leftmost (MkZipper coil p i x) =
  case fromPointer i x p of
    (j,y) :: xs => MkZipper coil ([<], xs) j y
    -- Too lazy to prove this impossible for now
    [] => assert_total $ idris_crash "Unreachable"


||| Move downward through an indexed lens.
|||
||| This cannot fail, since a lens always contains a value.
export
idownward : IndexedLens' i s a -> Zipper hs j s -> Zipper (j @> s :: hs) i a
idownward l (MkZipper coil p j y) =
  let (i,x) = iview l y
  in MkZipper (Cons p j (go . map snd) coil) ([<],[]) i x
  where
    go : List a -> s
    go ls = set (partsOf l) ls y

||| Move downward through a lens.
|||
||| This cannot fail, since a lens always contains a value.
export
downward : Lens' s a -> Zipper hs j s -> Zipper (j @> s :: hs) () a
downward l (MkZipper coil p i x) =
  MkZipper (Cons p i (go . map snd) coil) ([<], []) () (x ^. l)
  where
    go : List a -> s
    go ls = set (partsOf l) ls x

||| Move downward through an indexed traversal. This will fail if the traversal
||| has no focuses.
|||
||| If the traversal has multiple values, the zipper will focus on the leftmost one.
export
iwithin : Alternative f => IndexedTraversal' i s a -> Zipper hs j s -> f (Zipper (j @> s :: hs) i a)
iwithin l (MkZipper coil p j y) =
  case itoListOf l y of
    (i,x) :: xs => pure $ MkZipper (Cons p j (go . map snd) coil) ([<], xs) i x
    [] => empty
  where
    go : List a -> s
    go ls = set (partsOf l) ls y

||| Move downward through a traversal. This will fail if the traversal has no
||| focuses.
|||
||| If the traversal has multiple values, the zipper will focus on the leftmost one.
export
within : Alternative f => Traversal' s a -> Zipper hs j s -> f (Zipper (j @> s :: hs) Nat a)
within = iwithin . iordinal


recoil : Coil hs i a -> List (i, a) -> getTy $ last (i @> a :: hs)
recoil Nil xs = assert_total $ case xs of (_,x) :: _ => x
recoil (Cons p i f coil) xs = recoil coil $ fromPointer i (f xs) p

||| Close a zipper, repackaging it back into a value of its original type.
export
rezip : Zipper hs i a -> getTy $ last (i @> a :: hs)
rezip (MkZipper coil p i x) = recoil coil $ fromPointer i x p
