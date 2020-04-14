module LJPCF.T.Parser

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
    Lam  : String -> Val -> Val
    Zero : Val
    Succ : Val -> Val
    Fix  : String -> Val -> Val
    Emb  : Neu -> Val

  data Arg : Type where
    Nil  : Arg
    Cons : Val -> Arg -> Arg
    Tst  : Val -> String -> Val -> Arg -> Arg
    Inc  : Arg -> Arg

  data Neu : Type where
    Var : String -> Arg -> Neu
    Cut : Neu -> Arg -> Neu
    Ann : Val -> Ty -> Neu

type : All (Parser' Ty)
type =
  fix _ $ \rec =>
  let
    base = alt (cmap A (char '*')) (parens rec)
    arr = cmap Imp (withSpaces (string "->"))
   in
  chainr1 base arr

name : All (Parser' String)
name = lowerAlphas

var : All (Box (Parser' Arg) :-> Parser' Neu)
var reca = map (\(n,k) => Var n k) $
           between (char '<') (char '>') $
           andbox name (rand spaces reca)

zero : All (Parser' Val)
zero = cmap Zero $ char 'Z'

cut : All (Box (Parser' Arg) :-> Box (Parser' Val) :-> Parser' Val)
cut reca recv = alts [ map Emb (var reca)
                     , zero
                     , parens recv
                     ]

ann : All (Box (Parser' Val) :-> Parser' Neu)
ann rec = map (\(v,t) => Ann v t) $
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (rand (withSpaces (char ':'))
                              type))

succ : All (Box (Parser' Val) :-> Parser' Val)
succ rec = map Succ $
           rand (andopt (char 'S') spaces)
                (Nat.map {a=Parser' _} commit rec)

lam : All (Box (Parser' Val) :-> Parser' Val)
lam recv = map (\(s,v) => Lam s v) $
           rand (char '\\')
                (and (withSpaces name)
                     (rand (andopt (char '.') spaces)
                           (Nat.map {a=Parser' _} commit recv)))

fix : All (Box (Parser' Val) :-> Parser' Val)
fix recv = map (\(s,v) => Fix s v) $
          rand (string "FIX")
               (and (withSpaces name)
                    (rand (andopt (char '.') spaces)
                          (Nat.map {a=Parser' _} commit recv)))

tst : All (Box (Parser' Val) :-> Parser' (Arg -> Arg))
tst recv = map (\(t,s,f) => Tst t s f) $
           rand (andopt (string "TST") spaces)
                (andbox recv
                        (rand (optand spaces (string "ELSE\\"))
                              (and (withSpaces name)
                                   (rand (andopt (char '.') spaces) (Nat.map {a=Parser' _} commit recv)))))

arg : All (Box (Parser' Val) :-> Parser' Arg)
arg recv = alt (cmap Nil $ string "[]") $
           between (char '[') (char ']') $
           Combinators.map (flip apply Nil) $
           chainl1
             (alts [ cmap Inc $ char '$'
                   , tst recv
                   , map Cons $ rand (char '`') recv
                   ])
             (cmap (.) $ withSpaces $ char ',')

neu : All (Box (Parser' Arg) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu reca recv recn =
  hchainl
    (alts [ var reca
          , ann recv
          , parens recn
          ])
    (cmap Cut spaces)
    (arg recv)

emb : All (Box (Parser' Arg) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
emb reca recv recn = map Emb (neu reca recv recn)

val : All (Box (Parser' Arg) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val reca recv recn = alts [ lam recv
                          , zero
                          , succ recv
                          , fix recv
                          , emb reca recv recn
                          , parens recv
                          ]

record PCF (n : Nat) where
  constructor MkPCF
  pval : Parser' Val n
  parg : Parser' Arg n
  pneu : Parser' Neu n

pcf : All PCF
pcf = fix _ $ \rec =>
  let
    ihv = Nat.map {a=PCF} pval rec
    iha = Nat.map {a=PCF} parg rec
    ihn = Nat.map {a=PCF} pneu rec
   in
  MkPCF (val iha ihv ihn) (arg ihv) (neu iha ihv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pval pcf)

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pneu pcf)
