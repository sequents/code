module LambdaMu.Top.Parser

import Data.NEList
import TParsec
import TParsec.Running
import Parse
import LambdaMu.Ty

%access public export
%default total

-- bidirectional-style raw terms

mutual
  data Val : Type where
    Lam : String -> Val -> Val 
    Mu : String -> Val -> Val
    Emb : Neu -> Val
    Named : String -> Val -> Val
    Top : Val -> Val

  data Neu : Type where
    Var : String -> Neu 
    App : Neu -> Val -> Neu 
    Cut : Val -> Ty -> Neu 

type : All (Parser' Ty)
type =
  fix _ $ \rec =>
  let
    base = alts [ cmap A $ char '*'
                , cmap Bot $ string "_|_"
                , parens rec 
                ]
    arr = cmap Imp (withSpaces (string "->"))
   in
  chainr1 base arr

name : All (Parser' String)
name = alphas

-- neutrals

var : All (Parser' Neu)
var = map Var name

app : All (Box (Parser' Val) :-> Parser' Val)
app rec = alt (map Emb var) (parens rec)

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,t) => Cut v t) $ 
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (rand (withSpaces (char ':'))
                              type))

neu : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recv recn = 
  hchainl 
    (alts [ var
          , cut recv
          , parens recn
          ]) 
    (cmap App spaces) 
    (app recv)

-- values

lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\(s,v) => Lam s v) $ 
          rand (char '\\') 
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))
                
mu : All (Box (Parser' Val) :-> Parser' Val)
mu rec = map (\(s,v) => Mu s v) $ 
          rand (string "M") 
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

named : All (Box (Parser' Val) :-> Parser' Val)
named rec = map (\(s,v) => Named s v) $ 
            and (between (char '[') (char ']') $ withSpaces name)
                (roptandbox spaces (Nat.map {a=Parser' _} commit rec))

top : All (Box (Parser' Val) :-> Parser' Val)
top rec = map Top $ 
          rand (string "[]")
               (roptandbox spaces (Nat.map {a=Parser' _} commit rec))

emb : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
emb recv recn = map Emb (neu recv recn)
        
val : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val recv recn = alts [ lam recv
                     , mu recv
                     , named recv
                     , top recv
                     , emb recv recn
                     , parens recv
                     ]

record STLMtpC (n : Nat) where
  constructor MkSTLMtpC
  lmtpval : Parser' Val n
  lmtpneu : Parser' Neu n

stlmtpc : All STLMtpC
stlmtpc = fix _ $ \rec =>
  let 
    ihv = Nat.map {a=STLMtpC} lmtpval rec 
    ihn = Nat.map {a=STLMtpC} lmtpneu rec 
   in
  MkSTLMtpC (val ihv ihn) (neu ihv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (lmtpval stlmtpc) 

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (lmtpneu stlmtpc) 
