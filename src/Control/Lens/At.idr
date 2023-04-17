module Control.Lens.At

import Control.Lens.Optic
import Control.Lens.Lens
import Control.Lens.Optional
import Control.Lens.Traversal
import Control.Lens.Setter

%default total


public export
interface Ixed i v a | a where
  ix : i -> Optional' a v

public export
[Function] Eq e => Ixed e a (e -> a) where
  ix k = optional' (Just . ($ k)) (\f,x,k' => if k == k' then x else f k')


public export
interface Ixed i v a => Ixed' i i' v a | a where
  ix' : i' -> Lens' a v

public export
[Function'] Eq e => Ixed' e e a (e -> a) using Function where
  ix' k = lens ($ k) (\f,x,k' => if k == k' then x else f k')


public export
interface Ixed i v a => At i v a | a where
  at : i -> Lens' a (Maybe v)

public export
sans : At i v a => i -> a -> a
sans k = at k .~ Nothing
