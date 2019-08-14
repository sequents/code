module Lambda.Untyped.Parser

import Data.NEList
import TParsec
import TParsec.Running
import public Parse
import Lambda.Untyped.TermConvert

%access public export
%default total

-- bidirectional-style terms with positional info

mutual
  data Val : Type where
    Lam : Position -> String -> Val -> Val
    Emb : Position -> Neu -> Val

  data Neu : Type where
    Var : String -> Neu
    Cut : Position -> Val -> Neu
    App : Position -> Neu -> Val -> Neu

name : All (Parser' String)
name = alphas

-- neutrals

var : All (Parser' Neu)
var = map Var name

app : All (Box (Parser' Val) :-> Parser' Val)
app rec = alt (map (uncurry Emb) $ mand getPosition var) (parens rec)

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,p) => Cut p v) $ 
          andm (parens $ Nat.map {a=Parser' _} commit rec) getPosition

neu : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recv recn = 
  hchainl 
    (alts [ var
          , cut recv
          , parens recn
          ]) 
    (map Parser.App $ randm space getPosition) 
    (app recv)

-- values 
      
lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\((p,s),v) => Lam p s v) $ 
          rand (char '\\') 
               (and (mand getPosition 
                          (withSpaces name)) 
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

emb : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
emb recv recn = map (uncurry Emb) $ mand getPosition (neu recv recn)
        
val : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val recv recn = 
  alts [ lam recv 
       , emb recv recn
       , parens recv
       ]

-- tying the knot

record ULC (n : Nat) where
  constructor MkULC
  val : Parser' Val n
  neu : Parser' Neu n

ulc : All ULC
ulc = fix _ $ \rec =>
  let 
    ihv = Nat.map {a=ULC} val rec 
    ihn = Nat.map {a=ULC} neu rec 
   in
  MkULC (val ihv ihn) (neu ihv ihn)

-- converting to terms  

mutual
  v2t : Val -> TermNam.Term  
  v2t (Lam _ x t) = Lam (x, 0) (v2t t)
  v2t (Emb _ n)   = n2t n

  n2t : Neu -> TermNam.Term
  n2t (Var x)       = Var (x, 0)
  n2t (Cut _ v)     = v2t v
  n2t (App _ t1 t2) = App (n2t t1) (v2t t2)

parseNam : String -> Either Error TermNam.Term
parseNam s = result Left Left (maybe (Left EmptyParse) (Right . v2t)) $ parseResult s (val ulc) 

parseDB : String -> Either Error TermDB.Term
parseDB s = toDB nameNum <$> parseNam s
  