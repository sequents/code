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

total
parseErr : Position -> String
parseErr (MkPosition l r) = "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"

untyped : IO ()
untyped = 
  repl "u>" $ \s => 
    case parseDB s of 
      Right t => show t ++ "\n"
      Left (ParseError p) => parseErr p
      Left TypeError => "type error (can't happen for ULC)\n"

scoped : IO ()
scoped = 
  repl "s>" $ \s => 
    case parseTerm s of 
      Right (n**t) => show t ++ ": " ++ show n ++ "\n"
      Left (ParseError p) => parseErr p
      Left TypeError => "type error (can't happen for scoped ULC)\n"

typed : IO ()
typed = 
  repl "t>" $ \s => 
    case parseCheckTerm s of 
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left TypeError => "type error\n"

main : IO ()      
main = 
  do args <- getArgs 
     case args of 
       [_, "u"] => untyped
       [_, "s"] => scoped
       [_, "t"] => typed
       _        => putStrLn "Wrong args, run with 'u' (untyped), 's' (scoped) or 't' (typed)"