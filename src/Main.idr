module Main

import Data.Fuel
import TParsec.Position
import Iter
import Binary
import Lambda.Untyped.TermDB
import Lambda.Untyped.Parser
import Lambda.Untyped.Scoped.Term
import Lambda.Untyped.Scoped.Parser
import Lambda.STLC.Ty as STLC
import Lambda.STLC.Term
import Lambda.STLC.TyCheck
import PCF.Term
import PCF.Parser
import PCF.TyCheck
import PCF.Bytecode
import PCF.InstructN
import PCF.InstructV
import LambdaMu.Ty as STLMC
import LambdaMu.Term
import LambdaMu.TyCheck

%default covering

total
parseErr : Position -> String
parseErr (MkPosition l r) = "parse error at line " ++ show l ++ " row " ++ show r ++ "\n"

untyped : IO ()
untyped =
  repl "u> " $ \s =>
    case parseDB s of
      Right t => show t ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse"
      Left TypeError => "type error (can't happen for ULC)\n"

scoped : IO ()
scoped =
  repl "s> " $ \s =>
    case parseTerm s of
      Right (n**t) => show t ++ ": " ++ show n ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse"
      Left TypeError => "type error (can't happen for scoped ULC)\n"

typed : IO ()
typed =
  repl "t> " $ \s =>
    case STLC.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse"
      Left TypeError => "type error\n"

mu : IO ()
mu =
  repl "m> " $ \s =>
    case LambdaMu.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse"
      Left TypeError => "type error\n"

compilePCF : String -> String -> IO ()
compilePCF fnin fnout =
  do Right prog <- readFile fnin | Left err => printLn err
     case PCF.TyCheck.parseCheckTerm prog of
       Right (ty**t) => ioe_run (do buf <- initBinary
                                    b1 <- toBuf buf (the (List STLC.Ty) [])
                                    b2 <- toBuf b1 ty
                                    toBuf b2 (compile t))
                          putStrLn
                          (\bin => do res <- writeToFile fnout bin
                                      case res of
                                        Left fe => printLn fe
                                        Right () => pure ())
       Left (ParseError p) => printLn $ parseErr p
       Left IncompleteParse => putStrLn "parse error: incomplete parse\n"
       Left TypeError => putStrLn "type check error\n"

stepLim : Nat
stepLim = 1000

cbnPCF : String -> IO ()
cbnPCF fnin =
  do Right buf <- readFromFile fnin | Left err => printLn err
     ioe_run {a=(s**c**Control s c)}
        (do (g, b1) <- fromBuf buf {a = List STLC.Ty}
            (a, b2) <- fromBuf b1  {a = STLC.Ty}
            (ctr, _) <- fromBuf b2 {a = Control g a}
            pure (g**a**ctr))
        putStrLn
        (\(s**c**ctr) =>
           putStrLn $ case s of
            [] => case iterFuel (limit stepLim) InstructN.step (init ctr) of
                    (Just n, st) => "Reached in " ++ show n ++ " steps: " ++ show st
                    (Nothing, st) => "Timed out after " ++ show stepLim ++ " steps, last state: " ++ show st
            _ => "Computing open terms is not supported")

cbvPCF : String -> IO ()
cbvPCF fnin =
  do Right buf <- readFromFile fnin | Left err => printLn err
     ioe_run {a=(s**c**Control s c)}
        (do (g, b1) <- fromBuf buf {a = List STLC.Ty}
            (a, b2) <- fromBuf b1  {a = STLC.Ty}
            (ctr, _) <- fromBuf b2 {a = Control g a}
            pure (g**a**ctr))
        putStrLn
        (\(s**c**ctr) =>
           putStrLn $ case s of
            [] => case iterFuel (limit stepLim) InstructV.step (init ctr) of
                    (Just n, st) => "Reached in " ++ show n ++ " steps: " ++ show st
                    (Nothing, st) => "Timed out after " ++ show stepLim ++ " steps, last state: " ++ show st
            _ => "Computing open terms is not supported")

main : IO ()
main =
  do args <- getArgs
     case args of
       [_, "pu"] => untyped
       [_, "ps"] => scoped
       [_, "pt"] => typed
       [_, "pm"] => mu
       [_, "cp", fni, fno] => compilePCF fni fno
       [_, "rn", fni] => cbnPCF fni
       [_, "rv", fni] => cbvPCF fni
       _        => do putStrLn "Wrong args, run with:"
                      putStrLn " 'pu' (parse untyped lambda, interactive)"
                      putStrLn " 'ps' (parse scoped lambda, interactive)"
                      putStrLn " 'pt' (parse typed lambda, interactive)"
                      putStrLn " 'pm' (parse typed lambda-mu, interactive)"
                      putStrLn " 'cp <infile> <outfile>' (compile typed PCF term)"
                      putStrLn " 'rn <infile>' (run compiled PCF term in call-by-name VM)"
                      putStrLn " 'rv <infile>' (run compiled PCF term in call-by-value VM)"