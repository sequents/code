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

var : All (Parser' Neu)
var = map Var name

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,p) => Cut p v) $ 
          andm (parens $ Nat.map {a=Parser' _} commit rec) getPosition

app : All (Parser' (Neu -> Val -> Neu))
app = map App $ randm space getPosition

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (var `alt` (cut rec)) app rec 
      
lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\((p,s),v) => Lam p s v) $ 
          rand (char '^') 
               (and (mand getPosition 
                          (withSpaces name)) 
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

emb : All (Box (Parser' Val) :-> Parser' Val)
emb rec = map (uncurry Emb) $ mand getPosition (neu rec)
        
val : All (Box (Parser' Val) :-> Parser' Val)
val rec = (lam rec) `alt` (emb rec) 

-- tying the knot

record ULC (n : Nat) where
  constructor MkULC
  val : Parser' Val n
  neu : Parser' Neu n

ulc : All ULC
ulc = fix _ $ \rec =>
  let ihv = Nat.map {a=ULC} val rec in
  MkULC (val ihv) (neu ihv)

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
parseNam s = result Left Left (Right . v2t) $ parseResult s (val ulc) 

parseDB : String -> Either Error TermDB.Term
parseDB s = toDB nameNum <$> parseNam s
  