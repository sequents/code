module Parse

import Data.NEList
import TParsec

%default total
%access public export

data Error : Type where
  ParseError : Position -> Error
  IncompleteParse : Error
  TypeError : String -> Error

parseErr : Position -> String
parseErr (MkPosition l r) = "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"

Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecM Error Void) chars

Subset (Position, List Void) Error where
  into = ParseError . fst

andbox : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
andbox p q =
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q

roptandbox : All (Parser' s :-> Box (Parser' t) :-> Box (Parser' t))
roptandbox p q =
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.roptand p q) p q

lowerAlphas : {p : Parameters mn} ->
         (Alternative mn, Monad mn, Subset Char (Tok p), Subset (Tok p) Char, Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Parser mn p String)
lowerAlphas = map (pack . map into . NEList.toList) (nelist lowerAlpha)
