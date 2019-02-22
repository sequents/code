module Str

import Data.Primitives.Views

%default total
%access public export

parseBinStr : String -> Maybe Integer
parseBinStr s = go (unpack s) 0
  where
  go : List Char -> Integer -> Maybe Integer
  go []        i = Just i
  go ('0'::xs) i = go xs (2*i)
  go ('1'::xs) i = go xs (2*i+1)
  go (_::_)    _ = Nothing

toBinStr : Integer -> String
toBinStr i = go i ""
  where
  go : Integer -> String -> String
  go i s with (divides i 2)
    go (2*j+r) s | DivBy prf = if (j==0) then show r++s else assert_total $ go j (show r++s)
  