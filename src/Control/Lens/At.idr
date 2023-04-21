module Control.Lens.At

import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.Iso
import Control.Lens.Lens
import Control.Lens.Optional
import Control.Lens.Traversal
import Control.Lens.Setter

%default total


||| An interface that provides an `Optional` to access a given index in a
||| container, such as an ordinal position in a `List` or `Vect` or a key in a
||| map.
public export
interface Ixed i v a | a where
  ||| An optional that possibly accesses a value at a given index of a container.
  ix : i -> Optional' a v

||| An indexed version of `ix`.
public export
iix : Ixed i v a => i -> IndexedOptional' i a v
iix i = constIndex i (ix i)


public export
[Function] Eq e => Ixed e a (e -> a) where
  ix k = optional' (Just . ($ k)) (\f,x,k' => if k == k' then x else f k')


||| An interface that provides a lens to access a given index in a collection.
||| This is different from `Ixed` in that the lens cannot fail to get a value.
|||
||| Implementations of this interface may use different index types for `ix` and
||| `ix'`; for example, `Vect n a` uses `Nat` for `ix` and `Fin n` for `ix'`.
public export
interface Ixed i v a => Ixed' i i' v a | a where
  ||| An lens that infallibly accesses a value at a given index of a container.
  ix' : i' -> Lens' a v

||| An indexed version of `ix'`.
public export
iix' : Ixed' i i' v a => i' -> IndexedLens' i' a v
iix' i = constIndex i (ix' i)


public export
[Function'] Eq e => Ixed' e e a (e -> a) using Function where
  ix' k = lens ($ k) (\f,x,k' => if k == k' then x else f k')


||| This interface provides a lens to read, write, add or delete the value
||| associated to a key in a map or map-like container.
|||
||| This lens should satisfy:
||| * `ix i == at i . Just_`
|||
||| If you do not need to add or delete keys, `ix` is more convenient.
public export
interface Ixed i v a => At i v a | a where
  ||| A lens that can be used to read, write, add or delete a value associated
  ||| with a key in a map-like container.
  |||
  ||| If you do not need to add or delete keys, `ix` is more convenient.
  at : i -> Lens' a (Maybe v)


||| An indexed version of `at`.
public export
iat : At i v a => i -> IndexedLens' i a (Maybe v)
iat i = constIndex i (at i)


||| Delete the value at a particular key in a container using `At`.
public export
sans : At i v a => i -> a -> a
sans k = at k .~ Nothing

||| Add a value at a particular key in a container using `At`.
public export
add : At i v a => i -> v -> a -> a
add k = (at k ?~)
