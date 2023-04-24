module Data.String.Lens

import Data.String
import Data.Profunctor
import public Control.Lens
import Data.List.Lens

%default total


||| An isomorphism between a string and a list of characters.
|||
||| ```idris
||| unpacked = from packed
||| ```
public export
unpacked : Iso' String (List Char)
unpacked = iso unpack pack

||| An isomorphism between a list of characters and a string.
|||
||| ```idris
||| packed = from unpacked
||| ```
public export
packed : Iso' (List Char) String
packed = iso pack unpack


public export
Ixed Nat Char String where
  ix k = unpacked . ix k

public export
Cons String String Char Char where
  cons_ = prism' (uncurry strCons) strUncons

public export
Snoc String String Char Char where
  snoc_ = unpacked . snoc_ . mappingFst packed
