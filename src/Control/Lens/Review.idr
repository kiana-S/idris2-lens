module Control.Lens.Review

import Data.Profunctor
import Data.Profunctor.Costrong
import Control.Lens.Optic
import Control.Lens.Prism
import Control.Lens.Getter

%default total


public export
record IsReview p where
  constructor MkIsReview
  runIsReview : (Bifunctor p, Costrong p, Choice p)

export %hint
reviewToPrism : IsReview p => IsPrism p
reviewToPrism @{MkIsReview _} = MkIsPrism %search


public export
0 Review : (s,a : Type) -> Type
Review s a = Optic IsReview s s a a


lphantom : (Bifunctor p, Profunctor p) => p b c -> p a c
lphantom = mapFst absurd . lmap {a=Void} absurd

public export
unto : (a -> s) -> Review s a
unto f @{MkIsReview _} = lphantom . rmap f

public export
un : Getter s a -> Review a s
un = unto . view


public export
reviews : Review s a -> (e -> a) -> (e -> s)
reviews l = runCoforget . l . MkCoforget

public export
review : Review s a -> a -> s
review l = reviews l id

infixr 8 >.

public export
(>.) : a -> Review s a -> s
(>.) x l = review l x

public export
re : Review s a -> Getter a s
re = to . review
