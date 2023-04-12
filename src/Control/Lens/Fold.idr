module Control.Lens.Fold

import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Control.Lens.Internal.Bicontravariant
import Control.Lens.Internal.Backwards
import Control.Lens.Optic
import Control.Lens.OptionalFold
import Control.Lens.Traversal

%default total


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


public export
0 Fold : (s,a : Type) -> Type
Fold s a = Optic IsFold s s a a


public export
folded : Foldable f => Fold (f a) a
folded @{_} @{MkIsFold _} = rphantom . wander traverse_

public export covering
unfolded : (s -> Maybe (a, s)) -> Fold s a
unfolded coalg @{MkIsFold _} = rphantom . wander loop
  where
    loop : Applicative f => (a -> f a) -> s -> f ()
    loop f = maybe (pure ()) (uncurry $ \x,y => f x *> loop f y) . coalg

public export
folding : Foldable f => (s -> f a) -> Fold s a
folding @{_} f @{MkIsFold _} = rphantom . contramapFst f . wander traverse_

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


public export
foldMapOf : Monoid m => Fold s a -> (a -> m) -> s -> m
foldMapOf l = runForget . l . MkForget

public export
foldMapByOf : Fold s a -> (m -> m -> m) -> m -> (a -> m) -> (s -> m)
foldMapByOf l fork nil =
  let _ = MkMonoid @{MkSemigroup fork} nil
  in foldMapOf l

public export
foldrOf : Fold s a -> (a -> acc -> acc) -> acc -> s -> acc
foldrOf l = flip . foldMapByOf l (.) id

public export
foldlOf : Fold s a -> (acc -> a -> acc) -> acc -> s -> acc
foldlOf l = flip . foldMapByOf l (flip (.)) id . flip

public export
concatOf : Monoid m => Fold s m -> s -> m
concatOf l = foldMapOf l id

public export
sequenceOf_ : Applicative f => Fold s (f a) -> s -> f ()
sequenceOf_ l =
  let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
  in foldMapOf l ignore

public export
traverseOf_ : Applicative f => Fold s a -> (a -> f b) -> s -> f ()
traverseOf_ l f =
  let _ = MkMonoid @{MkSemigroup (*>)} (pure ())
  in foldMapOf l (ignore . f)

public export
forOf_ : Applicative f => Fold s a -> s -> (a -> f b) -> f ()
forOf_ = flip . traverseOf_

public export
andOf : Fold s (Lazy Bool) -> s -> Bool
andOf = force .: concatOf @{All}

public export
orOf : Fold s (Lazy Bool) -> s -> Bool
orOf = force .: concatOf @{Any}

public export
allOf : Fold s a -> (a -> Bool) -> s -> Bool
allOf = foldMapOf @{All}

public export
anyOf : Fold s a -> (a -> Bool) -> s -> Bool
anyOf = foldMapOf @{Any}


public export
has : Fold s a -> s -> Bool
has l = anyOf l (const True)

public export
hasn't : Fold s a -> s -> Bool
hasn't l = allOf l (const False)

public export
previews : Fold s a -> (a -> r) -> s -> Maybe r
previews l f = foldMapOf @{MonoidAlternative} l (Just . f)

public export
preview : Fold s a -> s -> Maybe a
preview l = foldMapOf @{MonoidAlternative} l Just

infixl 8 ^?

public export
(^?) : s -> Fold s a -> Maybe a
(^?) s l = preview l s

public export
toListOf : Fold s a -> s -> List a
toListOf l = foldrOf l (::) []

infixl 8 ^..

public export
(^..) : s -> Fold s a -> List a
(^..) s l = toListOf l s
