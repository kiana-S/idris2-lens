module Control.Lens.Setter

import Data.Contravariant
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Control.Lens.Optic
import Control.Lens.Traversal

%default total


public export
record IsSetter p where
  constructor MkIsSetter
  runIsSetter : Mapping p


export %hint
setterToTraversal : IsSetter p => IsTraversal p
setterToTraversal @{MkIsSetter _} = MkIsTraversal %search


public export
0 Setter : (s,t,a,b : Type) -> Type
Setter = Optic IsSetter

public export
0 Setter' : (s,a : Type) -> Type
Setter' = Simple Setter


public export
sets : ((a -> b) -> s -> t) -> Setter s t a b
sets f @{MkIsSetter _} = roam f

public export
mapped : Functor f => Setter (f a) (f b) a b
mapped @{_} @{MkIsSetter _} = map'

public export
contramapped : Contravariant f => Setter (f a) (f b) b a
contramapped = sets contramap


public export
over : Setter s t a b -> (a -> b) -> s -> t
over l = l @{MkIsSetter Function}

public export
set : Setter s t a b -> b -> s -> t
set l = over l . const
