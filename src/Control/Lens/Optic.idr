module Control.Lens.Optic

import Data.Tensor
import Data.Profunctor

%default total


public export
Simple : (k -> k -> k' -> k' -> r) -> k -> k' -> r
Simple f s a = f s s a a


public export
Optic' : (p : Type -> Type -> Type) -> (s,t,a,b : Type) -> Type
Optic' p s t a b = p a b -> p s t

public export
0 Optic : ((Type -> Type -> Type) -> Type) -> (s,t,a,b : Type) -> Type
Optic constr s t a b = forall p. constr p => Optic' p s t a b

