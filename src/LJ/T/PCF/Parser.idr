module LJ.T.PCF.Parser

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

  data Spn : Type where
    Nil  : Spn
    Cons : Val -> Spn -> Spn
    Tst  : Neu -> String -> Val -> Spn -> Spn
    Inc  : Spn -> Spn

  data Neu : Type where
    Var : String -> Spn -> Neu
    Cut : Neu -> Spn -> Neu
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

var : All (Box (Parser' Spn) :-> Parser' Neu)
var recs = map (\(n,k) => Var n k) $
           between (char '<') (char '>') $
           andbox name (rand spaces recs)

zero : All (Parser' Val)
zero = cmap Zero $ char 'Z'

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

tst : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' (Spn -> Spn))
tst recv recn = map (\(t,s,f) => Tst t s f) $
                rand (andopt (string "TST") spaces)
                     (andbox recn
                             (rand (optand spaces (string "ELSE\\"))
                                   (and (withSpaces name)
                                        (rand (andopt (char '.') spaces) (Nat.map {a=Parser' _} commit recv)))))

spn : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Spn)
spn recv recn = alt (cmap Nil $ string "[]") $
                between (char '[') (char ']') $
                Combinators.map (flip apply Nil) $
                chainl1
                  (alts [ cmap Inc $ char '$'
                        , tst recv recn
                        , map Cons $ rand (char '`') recv
                        ])
                  (cmap (.) $ withSpaces $ char ',')

neu : All (Box (Parser' Spn) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recs recv recn =
  hchainl
    (alts [ var recs
          , ann recv
          , parens recn
          ])
    (cmap Cut spaces)
    (spn recv recn)

emb : All (Box (Parser' Spn) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
emb recs recv recn = map Emb (neu recs recv recn)

val : All (Box (Parser' Spn) :-> Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val recs recv recn = alts [ lam recv
                          , zero
                          , succ recv
                          , fix recv
                          , emb recs recv recn
                          , parens recv
                          ]

record PCF (n : Nat) where
  constructor MkPCF
  pval : Parser' Val n
  pspn : Parser' Spn n
  pneu : Parser' Neu n

pcf : All PCF
pcf = fix _ $ \rec =>
  let
    ihv = Nat.map {a=PCF} pval rec
    ihs = Nat.map {a=PCF} pspn rec
    ihn = Nat.map {a=PCF} pneu rec
   in
  MkPCF (val ihs ihv ihn) (spn ihv ihn) (neu ihs ihv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pval pcf)

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pneu pcf)
