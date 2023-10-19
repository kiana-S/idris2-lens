module Derive.Lens.Options

import Data.String

%default total

public export
record LensOptions where
  constructor MkLensOptions
  fieldName :       String -> String
  constructorName : String -> String
  dataTypeName    : String -> String

export
toLowerHead : String -> String
toLowerHead s = case strUncons s of
  Nothing      => s
  Just (x, xs) => singleton (toLower x) ++ xs

export
defaultOptions : LensOptions
defaultOptions = MkLensOptions (++ "_") (++ "_") (\x => toLowerHead x ++ "Iso")
