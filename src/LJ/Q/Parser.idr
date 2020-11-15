module LJ.Q.Parser

import Data.NEList
import TParsec
import TParsec.Running
import Parse
import Lambda.STLC.Ty

%default covering

-- raw terms

mutual
  public export
  data Val = Lam String Neu
           | Emb NeuV

  public export
  data NeuV = Var String
            | Cut Val Ty

  public export
  data Neu = V NeuV
           | GApp String String Val Neu
           | Let String NeuV Neu

-- type parsing

ty : All (Parser' Ty)
ty =
  fix _ $ \rec =>
  let
    base = (cmap A $ char '*') `alt` (parens rec)
    arr = cmap Imp (withSpaces $ string "->")
   in
  chainr1 base arr

-- term parsing

name : All (Parser' String)
name = lowerAlphas

cut : All (Box (Parser' Val) :-> Parser' NeuV)
cut recv = map (uncurry Cut) $
           parens $
           andbox (Nat.map {a=Parser' _} commit recv) $
           rand (withSpaces $ char ':')
                ty

neuV : All (Box (Parser' Val) :-> Parser' NeuV)
neuV recv = (map Var name) `alt` (cut recv)

gapp : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
gapp recv recn = map (\(x,f,v,n) => GApp x f v n) $
                 rand (string "LETF") $
                 and (withSpaces name) $
                 rand (char '=') $
                 and (withSpaces name) $
                 andbox (Nat.map {a=Parser' _} commit recv) $
                 rand (withSpaces $ string "IN") $
                      (Nat.map {a=Parser' _} commit recn)

lett : All (Box (Parser' NeuV) :-> Box (Parser' Neu) :-> Parser' Neu)
lett recnv recn = map (\(x,nv,n) => Let x nv n) $
                  rand (string "LET") $
                  and (withSpaces name) $
                  rand (andopt (char '=') spaces) $
                  andbox (Nat.map {a=Parser' _} commit recnv) $
                  rand (withSpaces $ string "IN") $
                       (Nat.map {a=Parser' _} commit recn)

neu : All (Box (Parser' Val) :-> Box (Parser' NeuV) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recv recnv recn = alts [ map V $ neuV recv
                           , gapp recv recn
                           , lett recnv recn
                           ]

lam : All (Box (Parser' Neu) :-> Parser' Val)
lam recn = map (uncurry Lam) $
           rand (char '\\') $
           and (withSpaces name) $
           rand (andopt (char '.') spaces)
                (Nat.map {a=Parser' _} commit recn)

val : All (Box (Parser' Neu) :-> Box (Parser' Val) :-> Parser' Val)
val recn recv = (lam recn) `alt` (map Emb $ neuV recv)

record LJQ (n : Nat) where
  constructor MkLJQ
  pval : Parser' Val  n
  pnev : Parser' NeuV n
  pneu : Parser' Neu  n

ljq : All LJQ
ljq = fix _ $ \rec =>
  let
    ihv  = Nat.map {a=LJQ} pval rec
    ihnv = Nat.map {a=LJQ} pnev rec
    ihn  = Nat.map {a=LJQ} pneu rec
   in
  MkLJQ (val ihn ihv) (neuV ihv) (neu ihv ihnv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pval ljq)

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pneu ljq)

-- "LET f = (\\x.x : (*->*)->(*->*)) IN LETF t = f \\x.x IN t"
-- "LET f = (\\x.x : ((*->*)->(*->*))->((*->*)->(*->*))) IN LETF g = f \\x.x IN LETF t = g \\x.x IN t"
-- "LET f = (\\x.x : (*->*)->(*->*)) IN LETF g = f \\x.x IN LET h = (\\x.x : (*->*)->(*->*)) IN LETF t = h g IN t"
-- "LET f = (\\x.x : (*->*)->(*->*)) IN LETF g = f \\x.x IN LETF t = f g IN t"