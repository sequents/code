module PCF.Parser

import Data.NEList
import TParsec
import TParsec.Running
import Parse
import Lambda.STLC.Ty
import PCF.Term

%access public export
%default total

-- bidirectional-style raw terms

mutual
  data Val : Type where
    Lam : String -> Val -> Val 
    Zero : Val 
    Succ : Val -> Val 
    If0 : Neu -> Val -> String -> Val -> Val 
    Fix : String -> Val -> Val 
    Emb : Neu -> Val 

  data Neu : Type where
    Var : String -> Neu 
    App : Neu -> Val -> Neu 
    Cut : Val -> Ty -> Neu 

type : All (Parser' Ty)
type =
  fix _ $ \rec =>
  let
    base = alt (cmap A (char '*')) (parens rec)
    arr = cmap Imp (withSpaces (string "->"))
   in
  chainr1 base arr

name : All (Parser' String)
name = alphas

var : All (Parser' Neu)
var = map Var name

app : All (Parser' (Neu -> Val -> Neu))
app = cmap App space

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,t) => Cut v t) $ 
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (rand (withSpaces (char ':'))
                              type))

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (var `alt` (cut rec)) app rec 

zero : All (Parser' Val)
zero = cmap Zero $ char '0'

succ : All (Box (Parser' Val) :-> Parser' Val)
succ rec = map (\t => Succ t) $ 
           rand (char '+') 
                (Nat.map {a=Parser' _} commit rec)

lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\(s,v) => Lam s v) $ 
          rand (char '^') 
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))
                
fix : All (Box (Parser' Val) :-> Parser' Val)
fix rec = map (\(s,v) => Fix s v) $ 
          rand (char '@') 
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

if0 : All (Box (Parser' Neu) :-> Box (Parser' Val) :-> Parser' Val)                          
if0 recn recv = map (\(p,t,s,f) => If0 p t s f) $
                between (char '<') (char '>')
                  (andbox recn
                          (rand (char '?')
                                (andbox recv 
                                        (rand (char ':')
                                              (and name 
                                                   (rand (char '.') recv))))))

emb : All (Box (Parser' Val) :-> Parser' Val)
emb rec = map Emb (neu rec)
        
val : All (Box (Parser' Neu) :-> Box (Parser' Val) :-> Parser' Val)
val recn recv = alts [ lam recv
                     , zero
                     , succ recv
                     , if0 recn recv
                     , fix recv
                     , emb recv
                     ]

record PCF (n : Nat) where
  constructor MkPCF
  pval : Parser' Val n
  pneu : Parser' Neu n

pcf : All PCF
pcf = fix _ $ \rec =>
  let 
    ihv = Nat.map {a=PCF} pval rec 
    ihn = Nat.map {a=PCF} pneu rec 
   in
  MkPCF (val ihn ihv) (neu ihv)

parseVal : String -> Either Error Val
parseVal s = result Left Left Right $ parseResult s (pval pcf) 

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left Right $ parseResult s (pneu pcf) 
