module Lambda.STLC.TyCheckE

import Data.List
import Parse
import Ctx
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Parser
import Lambda.STLC.TyCheck

%access public export
%default total

-- bidirectional typechecker redux

mutual
  data NotVal : Ctx Ty -> Val -> Ty -> Type where
    NotLamA :                          NotVal g (Lam s v) A
    NotLam  : NotVal ((s,a)::g) v b -> NotVal g (Lam s v) (a~>b)
    NotEmb  : NotNeu g m               -> NotVal g (Emb m) a
    NotEmbQ : Neu g m a -> Not (a = b) -> NotVal g (Emb m) b

  data NotNeu : Ctx Ty -> Neu -> Type where
    NotVar   : Not (a ** InCtx g s a) -> NotNeu g (Var s)
    NotAppF  : NotNeu g l                     -> NotNeu g (App l m)
    NotAppFA : Neu g l A                      -> NotNeu g (App l m)
    NotAppA  : Neu g l (a~>b) -> NotVal g m a -> NotNeu g (App l m)
    NotCut   : NotVal g m a -> NotNeu g (Cut m a)

notCut : Not (a=b) -> Not (Neu g (Cut m a) b)
notCut neq (Cut n) = neq Refl

mutual
  valNot : NotVal g m a -> Val g m a -> Void
  valNot      NotLamA         v           = uninhabited v
  valNot     (NotLam nv)     (Lam v)      = valNot nv v
  valNot {a} (NotEmb nn)     (Emb n Refl) = neuNot nn (a**n)
  valNot     (NotEmbQ n neq)  v           = notSwitch n neq v

  neuNot : NotNeu g m -> (a ** Neu g m a) -> Void
  neuNot (NotVar nc)       (t**Var c)       = nc (t**c)
  neuNot (NotAppF nn)      (t**App {a} n _) = neuNot nn ((a~>t)**n)
  neuNot (NotAppFA na)     (_**App n _)     = uninhabited $ neuUniq na n
  neuNot (NotAppA n0 nv)   (t**App n v)     = notArg n0 (valNot nv) (t**App n v)
  neuNot (NotCut {a=b} nv) (t**n)           = case decEq b t of
    Yes Refl => let Cut v = n in valNot nv v
    No ctra => notCut ctra n

mutual
  synth2 : (g : Ctx Ty) -> (m : Neu) -> Either (NotNeu g m) (a ** Neu g m a)
  synth2 g (Var s)   = case lookup g s of
    Yes (a**el) => Right (a ** Var el)
    No ctra => Left $ NotVar ctra
  synth2 g (App t u) = case synth2 g t of
    Right (A**n) => Left $ NotAppFA n
    Right ((Imp a b)**n) => case inherit2 g u a of
      Right m => Right (b ** App n m)
      Left ctra => Left $ NotAppA n ctra
    Left ctra => Left $ NotAppF ctra
  synth2 g (Cut v t) = case inherit2 g v t of
    Right val => Right (t ** Cut val)
    Left ctra => Left $ NotCut ctra

  inherit2 : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Either (NotVal g m a) (Val g m a)
  inherit2 g (Lam s v)  A        = Left NotLamA
  inherit2 g (Lam s v) (Imp a b) = case inherit2 ((s,a)::g) v b of
    Right w => Right $ Lam w
    Left ctra => Left $ NotLam ctra
  inherit2 g (Emb n)    a        = case synth2 g n of
    Right (b ** m) => case decEq a b of
      Yes prf => Right $ Emb m (sym prf)
      No ctra => Left $ NotEmbQ m (ctra . sym)
    Left ctra => Left $ NotEmb ctra

-- taking a shortcut here by using raw terms for printing

mutual
  Show (NotVal g m a) where
    show     (NotLamA {s} {v})         = "Tried to assign type A to a function " ++ show (Lam s v)
    show     (NotLam nv)               = show nv
    show     (NotEmb nn)               = show nn
    show {a} (NotEmbQ {a=b} {m} n neq) = show m ++ " was supposed to have type " ++ show a ++ " but its type was " ++ show b

  Show (NotNeu g m) where
    show (NotVar {s} {g} nc) = "Variable " ++ s ++ " not found in context " ++ show (fst <$> g)
    show (NotAppF nn)        = show nn
    show (NotAppFA {l} n)    = show l ++ " was supposed to be a function but its type was A"
    show (NotAppA n nv)      = show nv
    show (NotCut nv)         = show nv

parseCheckTerm2 : String -> Either Error (a ** Term [] a)
parseCheckTerm2 s = do b <- parseNeu s
                       case synth2 [] b of
                         Right (a ** n) => Right (a ** neu2Term n)
                         Left s => Left $ TypeError $ show s