module Control.Lens.Lens

import Data.Profunctor
import Data.Profunctor.Yoneda
import Control.Monad.State
import Control.Lens.Optic
import Control.Lens.Indexed
import Control.Lens.Equality
import Control.Lens.Iso

%default total


------------------------------------------------------------------------------
-- Type definitions
------------------------------------------------------------------------------


public export
record IsLens p where
  constructor MkIsLens
  runIsLens : Strong p

export %hint
lensToIso : IsLens p => IsIso p
lensToIso @{MkIsLens _} = MkIsIso %search

export %hint
indexedLens : IsLens p => IsLens (Indexed i p)
indexedLens @{MkIsLens _} = MkIsLens %search


||| A *lens* is a functional reference to a value within a larger data structure.
||| Lenses allow one to access or modify the value that they reference, called
||| the "focus" or "focus element".
|||
||| For example, the lens `fst_` from `Data.Tuple.Lens` focuses on the first
||| element of a pair. It has the type:
|||
||| ```idris
||| fst_ : Lens (a, c) (b, c) a b
||| ```
|||
||| The types `s, t` correspond to the type of the outside data structure, and
||| `a, b` correspond to the type of the focus element. Two of each type is
||| provided to allow for operations that change the type of the focus.
public export
0 Lens : (s,t,a,b : Type) -> Type
Lens = Optic IsLens

||| `Lens'` is the `Simple` version of `Lens`.
public export
0 Lens' : (s,a : Type) -> Type
Lens' = Simple Lens

||| An indexed lens allows access to the index of a focus while setting it.
|||
||| Any indexed lens can be coerced into a regular lens and used in normal lens
||| functions, but there are also special functions that take indexed lenses
||| (i.e. `iover` instead of `over`).
public export
0 IndexedLens : (i,s,t,a,b : Type) -> Type
IndexedLens = IndexedOptic IsLens

||| `IndexedLens'` is the `Simple` version of `IndexedLens`.
public export
0 IndexedLens' : (i,s,a : Type) -> Type
IndexedLens' = Simple . IndexedLens


------------------------------------------------------------------------------
-- Utilities for lenses
------------------------------------------------------------------------------


||| Construct a lens given getter and setter functions.
|||
||| @ get The getter function
||| @ set The setter function, where the first argument is the data structure
||| to modify and the second argument is the new focus value
public export
lens : (get : s -> a) -> (set : s -> b -> t) -> Lens s t a b
lens get set @{MkIsLens _} = dimap (\x => (x, get x)) (uncurry set) . second

||| Construct an indexed lens given getter and setter functions.
public export
ilens : (get : s -> (i, a)) -> (set : s -> b -> t) -> IndexedLens i s t a b
ilens get set @{_} @{ind} = lens get set . indexed @{ind}


||| Extract getter and setter functions from a lens.
public export
getLens : Lens s t a b -> (s -> a, s -> b -> t)
getLens l = l @{MkIsLens strong} (id, const id)
  where
    Profunctor (\x,y => (x -> a, x -> b -> y)) where
      dimap f g (get, set) = (get . f, (g .) . set . f)

    [strong] GenStrong Pair (\x,y => (x -> a, x -> b -> y)) where
      strongl (get, set) = (get . fst, \(a,c),b => (set a b, c))
      strongr (get, set) = (get . snd, \(c,a),b => (c, set a b))

||| Extract getter and setter functions from a lens.
public export
withLens : Lens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = uncurry f (getLens l)


||| `Void` vacuously "contains" a value of any other type.
public export
devoid : IndexedLens i Void t a b
devoid = ilens absurd absurd

||| All values contain a unit.
public export
united : Lens' a ()
united @{MkIsLens _} = dimap ((),) snd . first

||| Create a lens that operates on pairs from two other lenses.
public export
alongside : Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
alongside l l' =
  let (get1, set1) = getLens l
      (get2, set2) = getLens l'
  in lens (bimap get1 get2) (uncurry bimap . bimap set1 set2)



||| Optimize a composition of optics by fusing their uses of `dimap` into one.
|||
||| This function exploits the Yoneda lemma. `fusing (a . b)` is essentially
||| equivalent to `a . b`, but the former will only call `dimap` once.
public export
fusing : IsIso p => Optic' (Yoneda p) s t a b -> Optic' p s t a b
fusing @{MkIsIso _} l = proextract . l . propure


------------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------------

infixr 4 %%~; infix 4 %%=; infix 4 %%@~; infix 4 %%@=

infixr 4 <%~; infixr 4 <%@~; infixr 4 <+~; infixr 4 <*~; infixr 4 <-~
infixr 4 </~; infixr 4 <||~; infixr 4 <&&~; infixr 4 <<+>~

infixr 4 <<%~; infixr 4 <<%@~; infixr 4 <<.~; infixr 4 <<?~; infixr 4 <<+~
infixr 4 <<*~; infixr 4 <<-~; infixr 4 <</~; infixr 4 <<||~; infixr 4 <<&&~
infixr 4 <<<+>~

infix 4 <%=; infix 4 <%@=; infix 4 <+=; infix 4 <*=; infix 4 <-=; infix 4 </=
infix 4 <||=; infix 4 <&&=; infix 4 <<+>=

infix 4 <<%=; infix 4 <<%@=; infix 4 <<.=; infix 4 <<?=; infix 4 <<+=; infix 4 <<*=
infix 4 <<-=; infix 4 <</=; infix 4 <<||=; infix 4 <<&&=; infix 4 <<<+>=

infixr 1 <<<~


public export
(%%~) : Functor f => Lens s t a b -> (a -> f b) -> s -> f t
(%%~) l = applyStar . l . MkStar {f}

public export
(%%=) : MonadState s m => Lens s s a b -> (a -> (r, b)) -> m r
(%%=) = (state . (swap .)) .: (%%~)

public export
(%%@~) : Functor f => IndexedLens i s t a b -> (i -> a -> f b) -> s -> f t
(%%@~) l = applyStar . l {p=Star f} @{%search} @{Idxed}
            . MkStar . uncurry

public export
(%%@=) : MonadState s m => IndexedLens i s s a b -> (i -> a -> (r, b)) -> m r
(%%@=) = (state . (swap .)) .: (%%@~)


||| Modify a value with pass-through.
public export
(<%~) : Lens s t a b -> (a -> b) -> s -> (b, t)
(<%~) l f = l %%~ (\x => (x,x)) . f

||| Modify a value with pass-through, having access to the index.
public export
(<%@~) : IndexedLens i s t a b -> (i -> a -> b) -> s -> (b, t)
(<%@~) l f = l %%@~ (\x => (x,x)) .: f

||| Add a value to the lens with pass-through.
public export
(<+~) : Num a => Lens s t a a -> a -> s -> (a, t)
(<+~) l = (<%~) l . (+)

||| Multiply the lens by a value with pass-through.
public export
(<*~) : Num a => Lens s t a a -> a -> s -> (a, t)
(<*~) l = (<%~) l . (*)

||| Subtract a value from the lens with pass-through.
public export
(<-~) : Neg a => Lens s t a a -> a -> s -> (a, t)
(<-~) l = (<%~) l . flip (-)

||| Divide the lens by a value with pass-through.
public export
(</~) : Fractional a => Lens s t a a -> a -> s -> (a, t)
(</~) l = (<%~) l . flip (/)

||| Logically OR the lens with a constant value with pass-through.
|||
||| Like (||) and (||~), this operator takes a lazy second argument.
public export
(<||~) : Lens s t Bool Bool -> Lazy Bool -> s -> (Bool, t)
(<||~) l = (<%~) l . flip (||)

||| Logically AND the lens with a constant value with pass-through.
|||
||| Like (&&) and (&&~), this operator takes a lazy second argument.
public export
(<&&~) : Lens s t Bool Bool -> Lazy Bool -> s -> (Bool, t)
(<&&~) l = (<%~) l . flip (&&)

||| Modify an lens's focus with the semigroup/monoid operator with pass-through.
|||
||| The constant value is applied to the focus from the right:
||| ```
||| l <<+>~ x = l <%~ (<+> x)
||| ```
public export
(<<+>~) : Semigroup a => Lens s t a a -> a -> s -> (a, t)
(<<+>~) l = (<%~) l . flip (<+>)


||| Modify the value of a lens and return the old value.
public export
(<<%~) : Lens s t a b -> (a -> b) -> s -> (a, t)
(<<%~) l f = l %%~ (\x => (x, f x))

||| Modify the value of an indexed lens and return the old value.
(<<%@~) : IndexedLens i s t a b -> (i -> a -> b) -> s -> (a, t)
(<<%@~) l f = l %%@~ (\i,x => (x, f i x))

||| Set the value of a lens and return the old value.
public export
(<<.~) : Lens s t a b -> b -> s -> (a, t)
(<<.~) l x = l %%~ (,x)

||| Set a lens to `Just` a value and return the old value.
public export
(<<?~) : Lens s t a (Maybe b) -> b -> s -> (a, t)
(<<?~) l = (<<.~) l . Just

||| Add a constant value to a lens's focus and return the old value.
public export
(<<+~) : Num a => Lens s t a a -> a -> s -> (a, t)
(<<+~) l = (<<%~) l . (+)

||| Multiply a lens's focus by a constant value and return the old value.
public export
(<<*~) : Num a => Lens s t a a -> a -> s -> (a, t)
(<<*~) l = (<<%~) l . (*)

||| Subtract a constant value from a lens's focus and return the old value.
public export
(<<-~) : Neg a => Lens s t a a -> a -> s -> (a, t)
(<<-~) l = (<%~) l . flip (-)

||| Divide a lens's focus by a constant value and return the old value.
public export
(<</~) : Fractional a => Lens s t a a -> a -> s -> (a, t)
(<</~) l = (<<%~) l . flip (/)

||| Logically OR a lens's focus by a constant value and return the old value.
|||
||| Like (||) and (||~), this operator takes a lazy second argument.
public export
(<<||~) : Lens s t Bool Bool -> Lazy Bool -> s -> (Bool, t)
(<<||~) l = (<<%~) l . flip (||)

||| Logically AND a lens's focus by a constant value and return the old value.
|||
||| Like (&&) and (&&~), this operator takes a lazy second argument.
public export
(<<&&~) : Lens s t Bool Bool -> Lazy Bool -> s -> (Bool, t)
(<<&&~) l = (<<%~) l . flip (&&)

||| Modify a lens's focus using the semigroup/monoid operator and return the
||| old value.
|||
||| The constant value is applied to the focus from the right:
||| ```
||| l <<<+>~ x = l <<%~ (<+> x)
||| ```
public export
(<<<+>~) : Semigroup a => Lens s t a a -> a -> s -> (a, t)
(<<<+>~) l = (<<%~) l . flip (<+>)


||| Modify within a state monad with pass-through.
public export
(<%=) : MonadState s m => Lens s s a b -> (a -> b) -> m b
(<%=) = (state . (swap .)) .: (<%~)

||| Modify within a state monad with pass-through, having access to the index.
public export
(<%@=) : MonadState s m => IndexedLens i s s a b -> (i -> a -> b) -> m b
(<%@=) = (state . (swap .)) .: (<%@~)

||| Add a value to the lens into state with pass-through.
public export
(<+=) : Num a => MonadState s m => Lens' s a -> a -> m a
(<+=) = (state . (swap .)) .: (<+~)

||| Multiply a lens's focus into state by a constant value with pass-through.
public export
(<*=) : Num a => MonadState s m => Lens' s a -> a -> m a
(<*=) = (state . (swap .)) .: (<*~)

||| Subtract a value from the lens into state with pass-through.
public export
(<-=) : Neg a => MonadState s m => Lens' s a -> a -> m a
(<-=) = (state . (swap .)) .: (<-~)

||| Divide a lens's focus into state by a constant value with pass-through.
public export
(</=) : Fractional a => MonadState s m => Lens' s a -> a -> m a
(</=) = (state . (swap .)) .: (</~)

||| Logically OR a lens's focus into state with a constant value with pass-through.
public export
(<||=) : MonadState s m => Lens s s Bool Bool -> Lazy Bool -> m Bool
(<||=) = (state . (swap .)) .: (<||~)

||| Logically AND a lens's focus into state with a constant value with pass-through.
public export
(<&&=) : MonadState s m => Lens s s Bool Bool -> Lazy Bool -> m Bool
(<&&=) = (state . (swap .)) .: (<&&~)

||| Modify a lens's focus into state using a semigroup operation with pass-through.
public export
(<<+>=) : MonadState s m => Semigroup a => Lens' s a -> a -> m a
(<<+>=) = (state . (swap .)) .: (<<+>~)


||| Modify the value of a lens into state and return the old value.
public export
(<<%=) : MonadState s m => Lens s s a b -> (a -> b) -> m a
(<<%=) = (state . (swap .)) .: (<<%~)

||| Modify the value of an indexed lens into state and return the old value.
public export
(<<%@=) : MonadState s m => IndexedLens i s s a b -> (i -> a -> b) -> m a
(<<%@=) = (state . (swap .)) .: (<<%@~)

||| Set the value of a lens into state and return the old value.
public export
(<<.=) : MonadState s m => Lens s s a b -> b -> m a
(<<.=) = (state . (swap .)) .: (<<.~)

||| Set a lens into state to `Just` a value and return the old value.
public export
(<<?=) : MonadState s m => Lens s s a (Maybe b) -> b -> m a
(<<?=) = (state . (swap .)) .: (<<?~)

||| Add a value to the lens into state and return the old value.
public export
(<<+=) : Num a => MonadState s m => Lens' s a -> a -> m a
(<<+=) = (state . (swap .)) .: (<<+~)

||| Multiply a lens's focus into state by a constant value and return the old
||| value.
public export
(<<*=) : Num a => MonadState s m => Lens' s a -> a -> m a
(<<*=) = (state . (swap .)) .: (<<*~)

||| Subtract a value from the lens into state and return the old value.
public export
(<<-=) : Neg a => MonadState s m => Lens' s a -> a -> m a
(<<-=) = (state . (swap .)) .: (<<-~)

||| Divide a lens's focus into state by a constant value and return the old
||| value.
public export
(<</=) : Fractional a => MonadState s m => Lens' s a -> a -> m a
(<</=) = (state . (swap .)) .: (<</~)

||| Logically OR a lens's focus into state with a constant value and return the
||| old value.
public export
(<<||=) : MonadState s m => Lens s s Bool Bool -> Lazy Bool -> m Bool
(<<||=) = (state . (swap .)) .: (<<||~)

||| Logically AND a lens's focus into state with a constant value and return the
||| old value.
public export
(<<&&=) : MonadState s m => Lens s s Bool Bool -> Lazy Bool -> m Bool
(<<&&=) = (state . (swap .)) .: (<<&&~)

||| Modify a lens's focus into state using a semigroup operation and return the
||| old value.
public export
(<<<+>=) : MonadState s m => Semigroup a => Lens' s a -> a -> m a
(<<<+>=) = (state . (swap .)) .: (<<<+>~)


||| Run a monadic action and set the focus of an optic in state to the result.
||| This is different from `(<~)` and `(<<~)` in that it also passes though
||| the old value of the optic.
public export
(<<<~) : MonadState s m => Lens s s a b -> m b -> m a
(<<<~) l m = l <<.= !m
