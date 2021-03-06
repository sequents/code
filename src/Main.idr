module Main

import Data.Fuel
import TParsec
import Parse
import Iter
import Binary

import Lambda.Untyped.TermDB
import Lambda.Untyped.Parser

import Lambda.Scoped.Term
import Lambda.Scoped.Parser

import Lambda.STLC.Ty as STLC
import Lambda.STLC.Term
import Lambda.STLC.TyCheck

import Lambda.PCF.Term
import Lambda.PCF.TyCheck
import Lambda.PCF.BigstepV
import Lambda.PCF.Bytecode
import Lambda.PCF.InstructN
import Lambda.PCF.InstructV

import LambdaMu.Ty as STLMC
import LambdaMu.Term
import LambdaMu.TyCheck

import LambdaMu.PCF.Term
import LambdaMu.PCF.TyCheck
import LambdaMu.PCF.Bytecode
import LambdaMu.PCF.InstructN
--import LambdaMu.PCF.InstructV

import LJ.T.PCF.Term
import LJ.T.PCF.TyCheck

%default covering

untyped : IO ()
untyped =
  repl "u> " $ \s =>
    case parseDB s of
      Right t => show t ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error (can't happen for ULC): " ++ e ++ "\n"

scoped : IO ()
scoped =
  repl "s> " $ \s =>
    case parseTerm s of
      Right (n**t) => show t ++ ": " ++ show n ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error (can't happen for scoped ULC): " ++ e ++ "\n"

typed : IO ()
typed =
  repl "t> " $ \s =>
    case STLC.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error: " ++ e ++ "\n"

pcf : IO ()
pcf =
  repl "p> " $ \s =>
    case Lambda.PCF.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error: " ++ e ++ "\n"

bigpcf : IO ()
bigpcf =
  repl "bp> " $ \s =>
    case Lambda.PCF.TyCheck.parseCheckTerm s of
      Right (ty**t) => show (eval0 t) ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error: " ++ e ++ "\n"

mu : IO ()
mu =
  repl "m> " $ \s =>
    case LambdaMu.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error: " ++ e ++ "\n"

ljt : IO ()
ljt =
  repl "j> " $ \s =>
    case LJ.T.PCF.TyCheck.parseCheckTerm s of
      Right (ty**t) => show t ++ ": " ++ show ty ++ "\n"
      Left (ParseError p) => parseErr p
      Left IncompleteParse => "parse error: incomplete parse\n"
      Left (TypeError e) => "type error: " ++ e ++ "\n"

compilePCF : String -> String -> IO ()
compilePCF fnin fnout =
  do Right prog <- readFile fnin | Left err => printLn err
     case Lambda.PCF.TyCheck.parseCheckTerm prog of
       Right (ty**t) => ioe_run (do buf <- initBinary
                                    b1 <- toBuf buf (the (List STLC.Ty) [])
                                    b2 <- toBuf b1 ty
                                    toBuf b2 (PCF.Bytecode.compile t))
                          putStrLn
                          (\bin => do res <- writeToFile fnout bin
                                      case res of
                                        Left fe => printLn fe
                                        Right () => pure ())
       Left (ParseError p) => putStrLn $ parseErr p
       Left IncompleteParse => putStrLn "parse error: incomplete parse\n"
       Left (TypeError e) => putStrLn $ "type error: " ++ e ++ "\n"

compileMuPCF : String -> String -> IO ()
compileMuPCF fnin fnout =
  do Right prog <- readFile fnin | Left err => printLn err
     case LambdaMu.PCF.TyCheck.parseCheckTerm prog of
       Right (ty**t) => ioe_run (do buf <- initBinary
                                    b1 <- toBuf buf (the (List STLMC.Ty) [])
                                    b2 <- toBuf b1 ty
                                    b3 <- toBuf b2 (the (List STLMC.Ty) [])
                                    toBuf b3 (LambdaMu.PCF.Bytecode.compile t))
                          putStrLn
                          (\bin => do res <- writeToFile fnout bin
                                      case res of
                                        Left fe => printLn fe
                                        Right () => pure ())
       Left (ParseError p) => putStrLn $ parseErr p
       Left IncompleteParse => putStrLn "parse error: incomplete parse\n"
       Left (TypeError e) => putStrLn $ "type check: " ++ e ++ "\n"

stepLim : Nat
stepLim = 1000

cbnPCF : String -> IO ()
cbnPCF fnin =
  do Right buf <- readFromFile fnin | Left err => printLn err
     ioe_run {a=(s**c**PCF.Bytecode.Control s c)}
        (do (g, b1) <- fromBuf buf {a = List STLC.Ty}
            (a, b2) <- fromBuf b1  {a = STLC.Ty}
            (ctr, _) <- fromBuf b2 {a = PCF.Bytecode.Control g a}
            pure (g**a**ctr))
        putStrLn
        (\(s**c**ctr) =>
           putStrLn $ case s of
            [] => case iterFuel (limit stepLim) Lambda.PCF.InstructN.step (init ctr) of
                    (Just n, st) => "Reached in " ++ show n ++ " steps: " ++ show st
                    (Nothing, st) => "Timed out after " ++ show stepLim ++ " steps, last state: " ++ show st
            _ => "Computing open terms is not supported")

cbvPCF : String -> IO ()
cbvPCF fnin =
  do Right buf <- readFromFile fnin | Left err => printLn err
     ioe_run {a=(s**c**Lambda.PCF.Bytecode.Control s c)}
        (do (g, b1)  <- fromBuf buf {a = List STLC.Ty}
            (a, b2)  <- fromBuf b1  {a = STLC.Ty}
            (ctr, _) <- fromBuf b2 {a = PCF.Bytecode.Control g a}
            pure (g**a**ctr))
        putStrLn
        (\(s**c**ctr) =>
           putStrLn $ case s of
            [] => case iterFuel (limit stepLim) Lambda.PCF.InstructV.step (init ctr) of
                    (Just n, st) => "Reached in " ++ show n ++ " steps: " ++ show st
                    (Nothing, st) => "Timed out after " ++ show stepLim ++ " steps, last state: " ++ show st
            _ => "Computing open terms is not supported")

cbnMuPCF : String -> IO ()
cbnMuPCF fnin =
  do Right buf <- readFromFile fnin | Left err => printLn err
     ioe_run {a=(s**c**t**LambdaMu.PCF.Bytecode.Control s c t)}
        (do (g, b1)  <- fromBuf buf {a = List STLMC.Ty}
            (a, b2)  <- fromBuf b1  {a = STLMC.Ty}
            (d, b3)  <- fromBuf b2  {a = List STLMC.Ty}
            (ctr, _) <- fromBuf b3  {a = LambdaMu.PCF.Bytecode.Control g a d}
            pure (g**a**d**ctr))
        putStrLn
        (\(s**c**t**ctr) =>
           putStrLn $ case (decEq s [], decEq t []) of
            (Yes Refl, Yes Refl) =>
              case iterFuel (limit stepLim) LambdaMu.PCF.InstructN.step (init ctr) of
                (Just n, st) => "Reached in " ++ show n ++ " steps: " ++ show st
                (Nothing, st) => "Timed out after " ++ show stepLim ++ " steps, last state: " ++ show st
            (_, _) => "Computing open terms is not supported")

main : IO ()
main =
  do args <- getArgs
     case args of
       [_, "pu"] => untyped
       [_, "ps"] => scoped
       [_, "pt"] => typed
       [_, "pp"] => pcf
       [_, "bp"] => bigpcf
       [_, "pm"] => mu
       [_, "pj"] => ljt
       [_, "cp", fni, fno] => compilePCF fni fno
       [_, "cpm", fni, fno] => compileMuPCF fni fno
       [_, "rn", fni] => cbnPCF fni
       [_, "rv", fni] => cbvPCF fni
       [_, "rnm", fni] => cbnMuPCF fni
       _        => do putStrLn "Wrong args, run with:"
                      putStrLn " 'pu' (parse untyped lambda, interactive)"
                      putStrLn " 'ps' (parse scoped lambda, interactive)"
                      putStrLn " 'pt' (parse typed lambda, interactive)"
                      putStrLn " 'pm' (parse typed lambda-mu, interactive)"
                      putStrLn " 'pj' (parse typed LJT PCF, interactive)"
                      putStrLn " 'cp <infile> <outfile>' (compile typed PCF term)"
                      putStrLn " 'cpm <infile> <outfile>' (compile typed MuPCF term)"
                      putStrLn " 'rn <infile>' (run compiled PCF term in call-by-name VM)"
                      putStrLn " 'rv <infile>' (run compiled PCF term in call-by-value VM)"
                      putStrLn " 'rnm <infile>' (run compiled MuPCF term in call-by-name VM)"
