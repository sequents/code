module LJ.LJ

import Data.List
import Subset

import Lambda.STLC.Ty
--import Lambda.STLC.Term

%default total
%access public export

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a ~> b)
--  ImpL : Term g a -> Term (b::g) c -> Term ((a~>b)::g) c
  ImpL : Term g a -> Term (b::g) c -> Elem (a~>b) g -> Term g c
  Cut  : Term g a -> Term (a::g) b -> Term g b

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)      = Var $ r el
rename r (Lam t)       = Lam $ rename (ext r) t
rename r (ImpL t u el) = ImpL (rename r t) (rename (ext r) u) (r el)
rename r (Cut t u)     = Cut (rename r t) (rename (ext r) u)

-- step : Term g a -> Maybe (Term g a)
-- step (Cut (Lam t) (ImpL u v el)) = Just $ ?wat
-- step (Cut (ImpL u v el) (Lam t)) = Just $ ?wat2
-- step  _                         = Nothing

-- Lam $ App (Var $ There $ There Here) (Var $ There Here)

ambig1 : Term [a, a~>b] (c~>b)
ambig1 = Lam $ rename help $ ImpL (Var $ There $ There Here) (Var Here) Here
  where
  help : Subset [c, a, b] [a, b, c]
  help  Here                = There $ There Here
  help (There  Here)        = Here
  help (There (There Here)) = There Here

ambig2 : Term [a, a~>b] (c~>b)
ambig2 = rename permute $ ImpL (Var $ There Here) (Lam $ Var $ There Here) Here

data TermS : List Ty -> Ty -> Type where
  VarS  : Elem a g -> TermS g a
  LamS  : TermS (a::g) b -> TermS g (a ~> b)
  ImpLS : TermS g a -> TermS (b::g) c -> TermS ((a~>b)::g) c
  CutS  : TermS g a -> TermS (a::g) b -> TermS g b
  Weak  : TermS g b -> TermS (a::g) b
  Ctr   : TermS (a::a::g) b -> TermS (a::g) b
  Perm  : (g : List Ty) -> TermS (g ++ a::b::d) c -> TermS (g ++ b::a::d) c

ambig1S : TermS [a, a~>b] (c~>b)
ambig1S {c} = LamS $ Perm [c] $ Perm [] $ ImpLS (VarS $ There Here) (VarS Here)

ambig2S : TermS [a, a~>b] (c~>b)
ambig2S = Perm [] $ ImpLS (VarS Here) (LamS $ VarS $ There Here)
