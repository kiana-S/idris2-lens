# Profunctor Optics in Idris2

This package provides utilities for working with lenses, prisms, traversals,
and other optics in Idris. This library uses *profunctor optics*.

## Comparison to Monocle

[Monocle](https://github.com/stefan-hoeck/idris2-monocle) is another Idris 2 library
for lenses. That library represents lenses using a datatype, which is often less
efficient at run-time, but results in better error messages and is generally
simpler to understand.

## Comparisons to Non-Idris Libraries

This library is inspired by the Haskell libraries [lens](https://hackage.haskell.org/package/lens-5.2.2),
[optics](https://hackage.haskell.org/package/optics) and [fresnel](https://hackage.haskell.org/package/fresnel),
along with the Purescript library [purescript-profunctor-lenses](https://pursuit.purescript.org/packages/purescript-profunctor-lenses/8.0.0).
Different design decisions are taken from each library.

Like `lens`, this library comes "batteries-included" with many useful lenses for
common types. It also includes the many lens operators. Like `optics`, `fresnel`
and `purescript-profunctor-lenses`, but unlike `lens`, this library uses
profunctor optics as opposed to van Laarhoven optics.

Like `lens` and `fresnel`, this library defines optics through type synonyms and
uses the `(.)` operator to compose them. Like `fresnel`, and unlike `lens`,
this library goes to some effort to ensure that type signatures and error
messages are understandable to some degree.

This library's optics hierarchy is most similar to that of `fresnel`, though it
also includes the `Equality` optic from `lens`. Unlike `fresnel`, this library also
supports indexed optics.

## Installation

This package depends on the `profunctors` package. It can be installed from `pack`
or from its GitHub repository [here](https://github.com/kiana-S/idris2-profunctors).

To install using `idris2` directly:

``` sh
git clone https://github.com/kiana-S/idris2-lens
cd idris2-lens
idris2 --install lens.ipkg
```

Or you can install using [pack](https://github.com/stefan-hoeck/idris2-pack):

``` sh
pack install lens
```

## Thanks

Special thanks to [Stefan Höck](https://github.com/stefan-hoeck) for assistance
with writing elaboration scripts.
