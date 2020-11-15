module LJ.T.Parser

import Data.NEList
import TParsec
import TParsec.Running
import Parse
import Lambda.STLC.Ty

%access public export
%default total

-- bidirectional-style raw terms

mutual
  data Val : Type where
    Lam : String -> Val -> Val
    Emb : Neu -> Val

  data Spn : Type where
    Nil  : Spn
    Cons : Val -> Spn -> Spn

  data Neu : Type where
    Var : String -> Spn -> Neu
    Cut : Neu -> Spn -> Neu
    Ann : Val -> Ty -> Neu

ty : All (Parser' Ty)
ty =
  fix _ $ \rec =>
  let
    base = alt (cmap A (char '*')) (parens rec)
    arr = cmap Imp (withSpaces (string "->"))
   in
  chainr1 base arr

name : All (Parser' String)
name = lowerAlphas

var : All (Box (Parser' Spn) :-> Parser' Neu)
var recs = map (uncurry Var) $
           between (char '<') (char '>') $
           andbox name (rand spaces recs)

ann : All (Box (Parser' Val) :-> Parser' Neu)
ann recv = map (uncurry Ann) $
           parens $
           andbox (Nat.map {a=Parser' _} commit recv) $
           rand (withSpaces $ char ':')
                ty

lam : All (Box (Parser' Val) :-> Parser' Val)
lam recv = map (uncurry Lam) $
           rand (char '\\') $
           and (withSpaces name) $
           rand (andopt (char '.') spaces)
                (Nat.map {a=Parser' _} commit recv)

spn : All (Box (Parser' Val) :-> Parser' Spn)
spn recv = alt (cmap Nil $ string "[]") $
           between (char '[') (char ']') $
           Combinators.map (flip apply Nil) $
           chainl1
             (map Cons $ rand (char '`') recv)
             (cmap (.) $ withSpaces $ char ',')

neu : All (Box (Parser' Spn) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recs recv recn =
  hchainl
    (alts [ var recs
          , ann recv
          , parens recn
          ])
    (cmap Cut spaces)
    (spn recv)

val : All (Box (Parser' Spn) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val recs recv recn = alts [ lam recv
                          , map Emb $ neu recs recv recn
                          , parens recv
                          ]

record LJT (n : Nat) where
  constructor MkLJT
  pval : Parser' Val n
  pspn : Parser' Spn n
  pneu : Parser' Neu n

ljt : All LJT
ljt = fix _ $ \rec =>
  let
    ihv = Nat.map {a=LJT} pval rec
    ihs = Nat.map {a=LJT} pspn rec
    ihn = Nat.map {a=LJT} pneu rec
   in
  MkLJT (val ihs ihv ihn) (spn ihv) (neu ihs ihv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pval ljt)

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pneu ljt)
