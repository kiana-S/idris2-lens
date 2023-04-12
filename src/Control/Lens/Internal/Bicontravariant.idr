module Control.Lens.Internal.Bicontravariant

import Data.Morphisms
import Data.Contravariant
import Data.Profunctor

%default total


public export
interface Bicontravariant f where
  contrabimap : (a -> b) -> (c -> d) -> f b d -> f a c
  contrabimap f g = contramapFst f . contramapSnd g

  contramapFst : (a -> b) -> f b c -> f a c
  contramapFst f = contrabimap f id

  contramapSnd : (b -> c) -> f a c -> f a b
  contramapSnd = contrabimap id


public export
Contravariant f => Bicontravariant (Star f) where
  contrabimap f g = MkStar . dimap @{Function} f (contramap g) . applyStar

public export
Contravariant f => Bicontravariant (Kleislimorphism f) where
  contrabimap f g = Kleisli . dimap @{Function} f (contramap g) . applyKleisli

public export
Bicontravariant (Forget {k=Type} r) where
  contrabimap f _ = MkForget . lmap @{Function} f . runForget


public export
rphantom : (Profunctor p, Bicontravariant p) => p a b -> p a c
rphantom = contramapSnd (const ()) . rmap (const ())

public export
biphantom : (Bifunctor p, Bicontravariant p) => p a b -> p c d
biphantom = contrabimap (const ()) (const ()) . bimap (const ()) (const ())
