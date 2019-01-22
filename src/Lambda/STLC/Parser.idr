module Lambda.STLC.Parser

import Data.NEList
import TParsec
import TParsec.Running
import Parse
import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

-- bidirectional-style raw terms

mutual
  data Val : Type where
    Lam : String -> Val -> Val 
    Emb : Neu -> Val 

  data Neu : Type where
    Var : String -> Neu 
    Cut : Val -> Ty -> Neu 
    App : Neu -> Val -> Neu 

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

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,t) => Cut v t) $ 
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (rand (withSpaces (char ':'))
                              type))
  where
    andbox : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
    andbox p q =
      Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q

app : All (Parser' (Neu -> Val -> Neu))
app = cmap App space

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (var `alt` (cut rec)) app rec 
      
lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\(s,v) => Lam s v) $ 
          rand (char '^') 
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

emb : All (Box (Parser' Val) :-> Parser' Val)
emb rec = map Emb (neu rec)
        
val : All (Box (Parser' Val) :-> Parser' Val)
val rec = (lam rec) `alt` (emb rec)

record STLC (n : Nat) where
  constructor MkSTLC
  val : Parser' Val n
  neu : Parser' Neu n

stlc : All STLC
stlc = fix _ $ \rec =>
  let ihv = Nat.map {a=STLC} val rec in
  MkSTLC (val ihv) (neu ihv)

parseVal : String -> Either Error Val
parseVal s = result Left Left Right $ parseResult s (STLC.val stlc) 

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left Right $ parseResult s (STLC.neu stlc) 
