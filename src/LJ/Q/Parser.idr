module LJ.Q.Parser

--import Data.String.Parser
--import Data.String.Parser.Expression
import TParsec
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
    base = alt (cmap A (char '*')) (parens rec)
    arr = cmap Imp (withSpaces (string "->"))
   in
  chainr1 base arr

-- term parsing

name : All (Parser' String)
name = lowerAlphas

var : All (Parser' NeuV)
var = map Var name

cut : All (Parser' NeuV)
cut = (uncurry Cut) <$>
      (parens [| (lexeme val, token ":" *> ty) |])

neuV : All (Parser' NeuV)
neuV = alts [var, cut]

gapp : All (Parser' Neu)
gapp = (\(x,f,v,n) => GApp x f v n) <$>
       [| (,,,) (token "LETF" *> lexeme name <* token "=")
                (lexeme name)
                (lexeme val <* token "IN")
                (lexeme neu) |]

lett : All (Parser' Neu)
lett = (\(x,nv,n) => Let x nv n) <$>
       [| (,,) (token "LET" *> lexeme name <* token "=")
               (lexeme neuV <* token "IN")
               (lexeme neu) |]

neu : All (Parser' Neu)
neu = alts [ V <$> neuV
           , gapp
           , lett ]

lam : All (Parser' Val)
lam = (uncurry Lam) <$>
      [| (token "\\" *> lexeme name, token "." *> neu) |]

emb : All (Parser' Val)
emb = Emb <$> neuV

val : All (Parser' Val)
val = alts [ lam, emb ]

record LJQ (n : Nat) where
  constructor MkLJQ
  pval : Parser' Val n
  pnev : Parser' NeuV n
  pneu : Parser' Neu n

ljq : All LJQ
ljq = fix _ $ \rec =>
  let
    ihv  = Nat.map {a=LJQ} pval rec
    ihnv = Nat.map {a=LJQ} pnev rec
    ihn  = Nat.map {a=LJQ} pneu rec
   in
  MkLJQ (val ihs ihv ihn) (nev ihv) (neu ihs ihv ihn)

parseVal : String -> Either Error Val
parseVal s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pval ljq)

parseNeu : String -> Either Error Neu
parseNeu s = result Left Left (maybe (Left IncompleteParse) Right) $ parseResult s (pneu ljq)

-- "LET f = (\\x.x : (1->1)->(1->1)) IN LETF t = f \\x.x IN t"
-- "LET f = (\\x.x : ((1->1)->(1->1))->((1->1)->(1->1))) IN LETF g = f \\x.x IN LETF t = g \\x.x IN t"
-- "LET f = (\\x.x : (1->1)->(1->1)) IN LETF g = f \\x.x IN LET h = (\\x.x : (1->1)->(1->1)) IN LETF t = h g IN t"