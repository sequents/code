module Lambda.Scoped.Parser

import Data.Fin
import Data.NEList
import TParsec
import TParsec.Running
import Parse
import OrdNat
import Lambda.Scoped.Term

%access public export
%default total

-- bidirectional-style indexed terms with positional info

mutual
  data Val : Nat -> Type where
    Lam : Position -> Val (S n) -> Val n
    Emb : Position -> Neu n -> Val n

  data Neu : Nat -> Type where
    Var : Fin n -> Neu n
    Cut : Position -> Val n -> Neu n
    App : Position -> Neu n -> Val n -> Neu n

mutual
  weakenVal : (k : Nat) -> Val n -> Val (n+k)
  weakenVal k (Lam p v) = Lam p $ weakenVal k v
  weakenVal k (Emb p n) = Emb p $ weakenNeu k n

  weakenNeu : (k : Nat) -> Neu n -> Neu (n+k)
  weakenNeu k (Var f)     = Var $ weakenN k f
  weakenNeu k (Cut p v)   = Cut p $ weakenVal k v
  weakenNeu k (App p n v) = App p (weakenNeu k n) (weakenVal k v)

weakApp : Position -> (n : Nat) -> Neu n -> (m : Nat) -> Val m -> (p ** Neu p)
weakApp pos n ne m va with (ordNat n m)
  weakApp pos  m    ne  m    va | EQN   = (m   ** App pos              ne               va )
  weakApp pos  n    ne (n+k) va | LTN k = (n+k ** App pos (weakenNeu k ne)              va )
  weakApp pos (m+k) ne  m    va | GTN k = (m+k ** App pos              ne  (weakenVal k va))

-- neutrals

var : All (Parser' (n ** Neu n))
var = map (\n => (S n ** Parser.Var $ last {n})) $ decimalNat

app : All (Box (Parser' (n ** Val n)) :-> Parser' (n ** Val n))
app rec = alt (map (\(p,(n**v)) => (n ** Emb p v)) $ mand getPosition var) (parens rec)

cut : All (Box (Parser' (n ** Val n)) :-> Parser' (n ** Neu n))
cut rec = map (\((n**v),p) => (n ** Cut p v)) $
          andm (parens $ Nat.map {a=Parser' _} commit rec) getPosition

neu : All (Box (Parser' (n ** Val n)) :-> Box (Parser' (n ** Neu n)) :-> Parser' (n ** Neu n))
neu recv recn =
  hchainl
    (alts [ var
          , cut recv
          , parens recn
          ])
    (Combinators.map (\pos, (n**x), (m**y) => weakApp pos n x m y) $
                     randm space getPosition)
    (app recv)

-- values

lam : All (Box (Parser' (n ** Val n)) :-> Parser' (n ** Val n))
lam rec = map (\(p,(n**v)) => case n of
                    Z => (Z ** Lam p (weakenVal 1 v))
                    S n => (n ** Lam p v)) $
          mand getPosition
              (rand (char '\\')
                    (Nat.map {a=Parser' _} commit rec))

emb : All (Box (Parser' (n ** Val n)) :-> Box (Parser' (n ** Neu n)) :-> Parser' (n ** Val n))
emb recv recn = map (\(p,(n**v)) => (n ** Emb p v)) $ mand getPosition (neu recv recn)

val : All (Box (Parser' (n ** Val n)) :-> Box (Parser' (n ** Neu n)) :-> Parser' (n ** Val n))
val recv recn =
  alts [ lam recv
       , emb recv recn
       , parens recv
       ]

-- tying the knot

record ULC (m : Nat) where
  constructor MkULC
  val : Parser' (n ** Val n) m
  neu : Parser' (n ** Neu n) m

ulc : All ULC
ulc = fix _ $ \rec =>
  let
    ihv = Nat.map {a=ULC} val rec
    ihn = Nat.map {a=ULC} neu rec
   in
  MkULC (val ihv ihn) (neu ihv ihn)

-- converting to terms

mutual
  v2t : Val n -> Term n
  v2t (Lam _ t) = Lam (v2t t)
  v2t (Emb _ n) = n2t n

  n2t : Neu n -> Term n
  n2t (Var f)       = Var f
  n2t (Cut _ v)     = v2t v
  n2t (App _ t1 t2) = App (n2t t1) (v2t t2)

parseTerm : String -> Either Error (n ** Term n)
parseTerm s = result Left Left (maybe (Left IncompleteParse) (\(n**v) => Right (n ** v2t v))) $ parseResult s (val ulc)
