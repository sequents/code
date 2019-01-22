module Iter

import TParsec

%default total
%access public export

data Error : Type where
  ParseError : Position -> Error
  TypeError : Error
  
Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecM Error Void) chars
 
Subset (Position, List Void) Error where
  into = ParseError . fst
