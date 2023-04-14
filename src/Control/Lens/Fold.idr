module Control.Lens.Fold

import Data.Bicontravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Control.Applicative.Backwards
import Control.Lens.Optic
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
  runIsFold : (Traversing p, Cochoice p, Bicontravariant p)

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
Fold s a = Optic IsFold s s a a


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

||| Combine the focuses of an optic using the provided function, starting from
||| the right.
public export
foldrOf : Fold s a -> (a -> acc -> acc) -> acc -> s -> acc
foldrOf l = flip . foldMapOf @{MkMonoid @{MkSemigroup (.)} id} l

||| Combine the focuses of an optic using the provided function, starting from
||| the left.
public export
foldlOf : Fold s a -> (acc -> a -> acc) -> acc -> s -> acc
foldlOf l = flip . foldMapOf @{MkMonoid @{MkSemigroup $ flip (.)} id} l . flip

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

||| A version of `traverseOf_` with the arguments flipped.
public export
forOf_ : Applicative f => Fold s a -> s -> (a -> f b) -> f ()
forOf_ = flip . traverseOf_

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

||| Return `True` if any focuses of the optic satisfy the predicate.
public export
anyOf : Fold s a -> (a -> Bool) -> s -> Bool
anyOf = foldMapOf @{Any}


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

||| Access the last focus value of an optic, returning `Nothing` if there are
||| no focuses.
public export
lastOf : Fold s a -> s -> Maybe a
lastOf l = foldMapOf @{MkMonoid @{MkSemigroup $ flip (<+>)} neutral} l Just



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
(^?) s l = preview l s


||| Convert a `Fold` into an `OptionalFold` that accesses the first focus element.
|||
||| For the traversal version of this, see `singular`.
public export
pre : Fold s a -> OptionalFold s a
pre = folding . preview


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