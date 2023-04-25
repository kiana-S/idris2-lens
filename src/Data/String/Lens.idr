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

||| An isomorphism between a string and its reverse.
public export
reversed : Iso' String String
reversed = involuted reverse


public export
Ixed Nat Char String where
  ix k = unpacked . ix k

public export
Cons String String Char Char where
  consIso = iso strUncons (maybe "" $ uncurry strCons)
  cons_ = prism' (uncurry strCons) strUncons

snoc : String -> Char -> String
snoc s c = s ++ singleton c

unsnoc : String -> Maybe (String, Char)
unsnoc s =
  case length s of
    Z => Nothing
    (S n) => Just (substr Z n s,
                    assert_total $ strIndex s (cast n))

public export
Snoc String String Char Char where
  snocIso = iso unsnoc (maybe "" $ uncurry snoc)
  snoc_ = prism' (uncurry snoc) unsnoc

public export
Each String String Char Char where
  each = unpacked . traversed
