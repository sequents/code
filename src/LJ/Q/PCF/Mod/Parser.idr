module LJ.Q.PCF.Mod.Parser

{-
import Data.NEList
import TParsec
import TParsec.Running
import Parse
-}
import LJ.Q.PCF.Mod.Ty

%default total

-- raw terms

mutual
  public export
  data Val = Lam String Neu
           | Fix String Neu
           | Emb NeuV

  public export
  data NeuV = Var String
            | Zero
            | Succ NeuV
            | Cut Val Ty

  public export
  data Neu = V NeuV
           | GApp String String Val Neu
           | GIf0 String String Neu String Neu Neu
           | Bnd  String String Neu
           | Let String NeuV Neu

-- Let "x" (Cut (Lam "x" (V (Var "x"))) (Imp A A)) (GApp "t" "f" (Lam "x" (V (Var "x"))) (V (Var "t")))

-- Let "f" (Cut (Lam "x" $ V $ Zero) (Imp A A)) $ Let "ww" (Cut (Fix "xx" $ Bnd "x" "xx" $ V $ Succ $ Var "x") (C A)) $ Bnd "w" "ww" $ GApp "t" "f" (Emb $ Var "w") $ V $ Var "t"
