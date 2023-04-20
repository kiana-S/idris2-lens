module Control.Lens.Fold

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.OptionalFold
import Control.Lens.Traversal

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


-- IsFold

public export
record IsFold p where
  constructor MkIsFold
  runIsFold : (Traversing p, Bicontravariant p)

export %hint
foldToOptFold : IsFold p => IsOptFold p
foldToOptFold @{MkIsFold _} = MkIsOptFold %search

export %hint
foldToTraversal : IsFold p => IsTraversal p
foldToTraversal @{MkIsFold _} = MkIsTraversal %search


-- Fold

||| A fold is a getter that accesses multiple focus elements.
||| `Fold s a` is equivalent to `s -> List a`.
public export
0 Fold : (s,a : Type) -> Type
Fold = Simple (Optic IsFold)

||| An indexed fold returns indices while getting.
public export
0 IndexedFold : (i,s,a : Type) -> Type
IndexedFold = Simple . IndexedOptic IsFold


------------------------------------------------------------------------------
-- Utilities for folds
------------------------------------------------------------------------------


||| Derive a fold from a `Foldable` implementation.
public export
folded : Foldable f => Fold (f a) a
folded @{_} @{MkIsFold _} = rphantom . wander traverse_

||| Construct a fold from an unfolding function.
|||
||| This function is not total, as it may result in an infinite amount
||| of focuses.
public export covering
unfolded : (s -> Maybe (a, s)) -> Fold s a
unfolded coalg @{MkIsFold _} = rphantom . wander loop
  where
    loop : Applicative f => (a -> f a) -> s -> f ()
    loop f = maybe (pure ()) (uncurry $ \x,y => f x *> loop f y) . coalg

||| Construct a fold from a function into a foldable container.
public export
folding : Foldable f => (s -> f a) -> Fold s a
folding @{_} f @{MkIsFold _} = rphantom . contramapFst f . wander traverse_

||| Construct an indexed fold from a function into a foldable container.
public export
ifolding : Foldable f => (s -> f (i, a)) -> IndexedFold i s a
ifolding @{_} f @{MkIsFold _} @{ind} =
  rphantom . contramapFst f . wander traverse_  . indexed @{ind}


||| Reverse the order of a fold's focuses.
public export
backwards : Fold s a -> Fold s a
backwards l @{MkIsFold _} = rphantom . wander func
  where
    traversing : Applicative f => Traversing (Forget (f ()))
    traversing =
      let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
      in %search

    func : Applicative f => (a -> f a) -> s -> f ()
    func fn = let _ = traversing in
      forwards . runForget (l $ MkForget (MkBackwards {f} . ignore . fn))

||| Construct a fold that replicates the input n times.
public export
replicated : Nat -> Fold a a
replicated n @{MkIsFold _} = rphantom . wander (\f,x => rep n (f x))
  where
    rep : Applicative f => Nat -> f a -> f ()
    rep Z _ = pure ()
    rep (S Z) x = ignore x
    rep (S n@(S _)) x = x *> rep n x


||| Map each focus of an optic to a monoid value and combine them.
public export
foldMapOf : Monoid m => Fold s a -> (a -> m) -> s -> m
foldMapOf l = runForget . l . MkForget

||| Map each focus of an optic to a monoid value with access to the index and
||| combine them.
public export
ifoldMapOf : Monoid m => IndexedFold i s a -> (i -> a -> m) -> s -> m
ifoldMapOf l = runForget . l @{%search} @{Idxed} . MkForget . uncurry

||| Combine the focuses of an optic using the provided function, starting from
||| the right.
public export
foldrOf : Fold s a -> (a -> acc -> acc) -> acc -> s -> acc
foldrOf l = flip . foldMapOf @{MkMonoid @{MkSemigroup (.)} id} l

||| Combine the focuses of an optic using the provided function with access to
||| the index, starting from the right.
public export
ifoldrOf : IndexedFold i s a -> (i -> a -> acc -> acc) -> acc -> s -> acc
ifoldrOf l = flip . ifoldMapOf @{MkMonoid @{MkSemigroup (.)} id} l

||| Combine the focuses of an optic using the provided function, starting from
||| the left.
public export
foldlOf : Fold s a -> (acc -> a -> acc) -> acc -> s -> acc
foldlOf l = flip . foldMapOf @{MkMonoid @{MkSemigroup $ flip (.)} id} l . flip

||| Combine the focuses of an optic using the provided function with access to
||| the index, starting from the left.
public export
ifoldlOf : IndexedFold i s a -> (i -> acc -> a -> acc) -> acc -> s -> acc
ifoldlOf l = flip . ifoldMapOf @{MkMonoid @{MkSemigroup $ flip (.)} id} l . (flip .)

||| Combine each focus value of an optic using a monoid structure.
public export
concatOf : Monoid m => Fold s m -> s -> m
concatOf l = foldMapOf l id

||| Fold over the focuses of an optic using Alternative.
public export
choiceOf : Alternative f => Fold s (Lazy (f a)) -> s -> f a
choiceOf = force .: concatOf @{MonoidAlternative}

||| Evaluate each computation of an optic and discard the results.
public export
sequenceOf_ : Applicative f => Fold s (f a) -> s -> f ()
sequenceOf_ l =
  let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
  in foldMapOf l ignore

||| Map each focus of an optic to a computation, evaluate those
||| computations and discard the results.
public export
traverseOf_ : Applicative f => Fold s a -> (a -> f b) -> s -> f ()
traverseOf_ l f =
  let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
  in foldMapOf l (ignore . f)

||| Map each focus of an optic to a computation with access to the index,
||| evaluate those computations and discard the results.
public export
itraverseOf_ : Applicative f => IndexedFold i s a -> (i -> a -> f b) -> s -> f ()
itraverseOf_ l f =
  let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
  in ifoldMapOf l (ignore .: f)

||| A version of `traverseOf_` with the arguments flipped.
public export
forOf_ : Applicative f => Fold s a -> s -> (a -> f b) -> f ()
forOf_ = flip . traverseOf_

||| A version of `itraverseOf_` with the arguments flipped.
public export
iforOf_ : Applicative f => IndexedFold i s a -> s -> (i -> a -> f b) -> f ()
iforOf_ = flip . itraverseOf_

||| The conjunction of an optic containing lazy boolean values.
public export
andOf : Fold s (Lazy Bool) -> s -> Bool
andOf = force .: concatOf @{All}

||| The disjunction of an optic containing lazy boolean values.
public export
orOf : Fold s (Lazy Bool) -> s -> Bool
orOf = force .: concatOf @{Any}

||| Return `True` if all focuses of the optic satisfy the predicate.
public export
allOf : Fold s a -> (a -> Bool) -> s -> Bool
allOf = foldMapOf @{All}

||| Return `True` if all focuses of the indexed optic satisfy the predicate.
public export
iallOf : IndexedFold i s a -> (i -> a -> Bool) -> s -> Bool
iallOf = ifoldMapOf @{All}

||| Return `True` if any focuses of the optic satisfy the predicate.
public export
anyOf : Fold s a -> (a -> Bool) -> s -> Bool
anyOf = foldMapOf @{Any}

||| Return `True` if any focuses of the indexed optic satisfy the predicate.
public export
ianyOf : IndexedFold i s a -> (i -> a -> Bool) -> s -> Bool
ianyOf = ifoldMapOf @{Any}


||| Return `True` if the element occurs in the focuses of the optic.
public export
elemOf : Eq a => Fold s a -> a -> s -> Bool
elemOf l = allOf l . (==)

||| Calculate the number of focuses of the optic.
public export
lengthOf : Fold s a -> s -> Nat
lengthOf l = foldMapOf @{Additive} l (const 1)

||| Access the first focus value of an optic, returning `Nothing` if there are
||| no focuses.
|||
||| This is identical to `preview`.
public export
firstOf : Fold s a -> s -> Maybe a
firstOf l = foldMapOf l Just

||| Access the first focus value and index of an indexed optic, returning Nothing
||| if there are no focuses.
|||
||| This is identical to `ipreview`.
public export
ifirstOf : IndexedFold i s a -> s -> Maybe (i, a)
ifirstOf l = runForget $ l @{%search} @{Idxed} $ MkForget Just

||| Access the last focus value of an optic, returning `Nothing` if there are
||| no focuses.
public export
lastOf : Fold s a -> s -> Maybe a
lastOf l = foldMapOf @{MkMonoid @{MkSemigroup $ flip (<+>)} neutral} l Just

||| Access the last focus value and index of an indexed optic, returning Nothing
||| if there are no focuses.
public export
ilastOf : IndexedFold i s a -> s -> Maybe (i, a)
ilastOf l =
  let _ = MkMonoid @{MkSemigroup $ flip (<+>)} neutral
  in runForget $ l @{%search} @{Idxed} $ MkForget Just



------------------------------------------------------------------------------
-- Accessing folds
------------------------------------------------------------------------------


||| Return `True` if the optic focuses on any values.
public export
has : Fold s a -> s -> Bool
has l = anyOf l (const True)

||| Return `True` if the optic does not focus on any values.
public export
hasn't : Fold s a -> s -> Bool
hasn't l = allOf l (const False)


||| Access the first focus value of an optic and apply a function to it,
||| returning `Nothing` if there are no focuses.
public export
previews : Fold s a -> (a -> r) -> s -> Maybe r
previews l f = foldMapOf l (Just . f)

||| Access the first focus value of an optic, returning `Nothing` if there are
||| no focuses.
|||
||| This is an alias for `firstOf`.
public export
preview : Fold s a -> s -> Maybe a
preview = firstOf

infixl 8 ^?

||| Access the first focus value of an optic, returning `Nothing` if there are
||| no focuses.
|||
||| This is the operator form of `preview`.
public export
(^?) : s -> Fold s a -> Maybe a
(^?) x l = preview l x


||| Access the first focus value and index of an indexed optic, returning Nothing
||| if there are no focuses.
|||
||| This is an alias for `ifirstOf`.
public export
ipreview : IndexedFold i s a -> s -> Maybe (i, a)
ipreview = ifirstOf

infixl 8 ^@?

||| Access the first focus value and index of an indexed optic, returning Nothing
||| if there are no focuses.
|||
||| This is the operator form of `ipreview`.
public export
(^@?) : s -> IndexedFold i s a -> Maybe (i, a)
(^@?) x l = ipreview l x


||| Convert a `Fold` into an `OptionalFold` that accesses the first focus element.
|||
||| For the traversal version of this, see `singular`.
public export
pre : Fold s a -> OptionalFold s a
pre = folding . preview

||| Convert an `IndexedFold` into an `IndexedOptionalFold` that accesses the
||| first focus element.
|||
||| For the traversal version of this, see `isingular`.
public export
ipre : IndexedFold i s a -> IndexedOptionalFold i s a
ipre = ifolding . ipreview


||| Return a list of all focuses of a fold.
public export
toListOf : Fold s a -> s -> List a
toListOf l = foldrOf l (::) []

infixl 8 ^..

||| Return a list of all focuses of a fold.
|||
||| This is the operator form of `toListOf`.
public export
(^..) : s -> Fold s a -> List a
(^..) s l = toListOf l s


||| Return a list of all focuses and indices of an indexed fold.
public export
itoListOf : IndexedFold i s a -> s -> List (i, a)
itoListOf l = ifoldrOf l ((::) .: (,)) []

infixl 8 ^@..

||| Return a list of all focuses and indices of an indexed fold.
|||
||| This is the operator form of `itoListOf`.
public export
(^@..) : s -> IndexedFold i s a -> List (i, a)
(^@..) x l = itoListOf l x
