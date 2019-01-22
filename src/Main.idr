module Main

import TParsec
import Lambda.Untyped.TermDB
import Lambda.Untyped.Parser
import Lambda.Untyped.Scoped.Term
import Lambda.Untyped.Scoped.Parser
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.TyCheck

%default partial

untyped : IO ()
untyped = 
  repl ">" $ \s => 
    case parseDB s of 
      Right t => show t ++ "\n"
      Left (ParseError (MkPosition l r)) => "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"
      Left TypeError => "type error (can't happen for ULC)\n"

scoped : IO ()
scoped = 
  repl ">" $ \s => 
    case parseTerm s of 
      Right (n**t) => show t ++ ": " ++ show n ++ "\n"
      Left (ParseError (MkPosition l r)) => "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"
      Left TypeError => "type error (can't happen for scoped ULC)\n"

typed : IO ()
typed = 
  repl ">" $ \s => 
    case parseCheckTerm s of 
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError (MkPosition l r)) => "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"
      Left TypeError => "type error\n"

main : IO ()      
main = 
  do args <- getArgs 
     case args of 
       [_, "u"] => untyped
       [_, "s"] => scoped
       [_, "t"] => typed
       _        => putStrLn "Wrong args, run with 'u' (untyped), 's' (scoped) or 't' (typed)"