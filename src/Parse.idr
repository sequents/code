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

andbox : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
andbox p q =
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q
