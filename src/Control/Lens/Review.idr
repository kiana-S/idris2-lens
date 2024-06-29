module Control.Lens.Review

import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Prism
import Control.Lens.Getter

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsReview p where
  constructor MkIsReview
  runIsReview : (Bifunctor p, Costrong p, Choice p)

export %hint
reviewToPrism : IsReview p => IsPrism p
reviewToPrism @{MkIsReview _} = MkIsPrism %search


||| A review is an optic whose only capability is being flipped into a `Getter`
||| in the other direction.
|||
||| Any `Prism` or `Iso` can be used as a review.
public export
0 Review : (s,a : Type) -> Type
Review = Simple (Optic IsReview)


------------------------------------------------------------------------------
-- Utilities for Reviews
------------------------------------------------------------------------------


lphantom : (Bifunctor p, Profunctor p) => p b c -> p a c
lphantom = mapFst absurd . lmap {a=Void} absurd

||| Construct a review from an injection function.
||| Analogous to `to` for getters.
public export
unto : (a -> s) -> Review s a
unto f @{MkIsReview _} = lphantom . rmap f

||| Flip a `Getter` to form a `Review`.
public export
un : Getter s a -> Review a s
un = unto . view


||| Turn an optic around to inject a focus value into the larger data structure
||| after applying a function to it.
||| This function takes a `Review`, which can also be a `Prism` or `Iso`.
public export
reviews : Review s a -> (e -> a) -> (e -> s)
reviews l = runCoforget . l . MkCoforget

||| Turn an optic around to inject a focus value into the larger data structure.
||| This function takes a `Review`, which can also be a `Prism` or `Iso`.
public export
review : Review s a -> a -> s
review l = reviews l id

export infixr 8 ^$

||| Turn an optic around to inject a focus value into the larger data structure.
||| This function takes a `Review`, which can also be a `Prism` or `Iso`.
|||
||| This is the operator form of `review`.
public export
(^$) : Review s a -> a -> s
(^$) = review

||| Flip a `Prism`, `Iso` or `Review` to form a `Getter` in the other direction.
public export
re : Review s a -> Getter a s
re = to . review
