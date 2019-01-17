module Main

import TParsec
import Lambda.Untyped.TermDB
import Lambda.Untyped.Parser

partial
main : IO ()
main = 
  repl ">" $ \s => 
    case parseDB s of 
      Right s => show s ++ "\n"
      Left (ParseError (MkPosition l r)) => "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"