module LJ.Q.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.Q.Term

%default total
%access public export

-- reduction

--mutual
--  subst1T : TermJ (a::g) b -> TermJ g a -> TermJ g b
--  subst1T (Var  Here      k) u = Cut u (subst1S k u)
--  subst1T (Var (There el) k) u = Var el (subst1S k u)
--  subst1T (Lam t)            u = Lam $ assert_total $ subst1T (shiftTerm t) (shiftTerm u) -- (renameT permute0 t) (renameT weaken u)
--  subst1T (Cut t k)          u = Cut (subst1T t u) (subst1S k u)
--

subst1V : ValQ (a::g) b -> ValQ g a -> ValQ g b
subst1V  t               (Var el) = renameVal (contract el) t
subst1V (Var Here)        u       = u
subst1V (Var (There el))  u       = Var el
subst1V (Lam t)           u       = Lam $ Let (shiftVal u) (shiftTerm t)

subst1T : TermQ (a::g) b -> TermQ g a -> TermQ g b
subst1T t (V v)         = Let v t
subst1T t (GApp u v el) = GApp u (subst1T (renameTerm (permute0 . weaken) t) v) el
subst1T t (Let v u)     = Let v (subst1T (renameTerm (permute0 . weaken) t) u)

stepT : TermQ g a -> Maybe (TermQ g a)
stepT (Let (Var el)  u                   ) = Just $ renameTerm (contract el) u
stepT (Let (Lam t)  (V v)                ) = Just $ V $ subst1V v (Lam t)
stepT (Let (Lam t)  (GApp v u Here)      ) = Just $ subst1T (Let (shiftVal (Lam t)) (shiftTerm u))
                                                            (Let (subst1V v (Lam t)) t)
stepT (Let (Lam t)  (GApp v u (There el))) = Just $ GApp (subst1V v (Lam t)) (Let (shiftVal (Lam t)) (shiftTerm u)) el
stepT (Let  v       (Let q t)            ) = Just $ Let ?wat ?wat2
stepT  _                                   = Nothing

stepIter : Term [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepT . encode

{-
mutual
  stepA : TermQ g a -> Maybe (TermQ g a)

  stepA (Let   (Var el)  t                   ) = Just $ renameTerm (contract el) t
  stepA (Let a@(Lam _ ) (Val p              )) = Just $ Val $ SubV a p
  stepA (Let a@(Lam u ) (GApp p t  Here     )) = Just $ Sub (Let (SubV a p) u) (Let (shiftVal a) (shiftTerm t))
  stepA (Let a@(Lam _ ) (GApp p t (There el))) = Just $ GApp (SubV a p) (Let (shiftVal a) (shiftTerm t)) el
  stepA (Let    k        m                   ) = [| Let (stepRS k) (pure m) |] <|> [| Let (pure k) (stepA m) |]

  stepA (Sub (Val p      ) t) = Just $ Let p t
  stepA (Sub (GApp p v el) t) = Just $ GApp p (Sub v (shiftTerm t)) el
  stepA (Sub  u            k) = [| Sub (stepA u) (pure k) |] <|> [| Sub (pure u) (stepA k) |]

  stepA  _                    = Nothing

  --stepA (Val p)                                = Val <$> stepRS p

  stepRS : ValQ g a -> Maybe (ValQ g a)
  stepRS (SubV   (Var el)  p              ) = Just $ renameValQ (contract el) p
  stepRS (SubV a@(Lam _)  (Var  Here     )) = Just a
  stepRS (SubV   (Lam _)  (Var (There el))) = Just $ Var el
  stepRS (SubV a@(Lam _)  (Lam t         )) = Just $ Lam $ Let (shiftValQ a) (shiftTermQ t)
  stepRS (SubV    k        m              ) = [| SubV (stepRS k) (pure m) |] <|> [| SubV (pure k) (stepRS m) |]
  stepRS  _                                 = Nothing

-- strong reduction

isCoval : TermQ g a -> Bool
isCoval (Val (Var Here)) = True
isCoval (GApp p m Here)  = isJust (renameMValQ contractM p) && isJust (renameMTermQ contractM (renameTermQ permute m))
isCoval  _               = False

mutual
  stepStrA : TermQ g a -> Maybe (TermQ g a)

  stepStrA (Let p (Val q)              ) = Just $ Val $ SubV p q
  stepStrA (Let p (GApp q m  Here)     ) = Just $ Sub (Val p) (GApp (SubV (shiftValQ p) (shiftValQ q))
                                                              (Let (shiftValQ p) (shiftTermQ m)) Here)
  stepStrA (Let p (GApp q m (There el))) = Just $ GApp (SubV p q) (Let (shiftValQ p) (shiftTermQ m)) el
  stepStrA (Let p (Sub n m)            ) = Just $ Sub (Let p n) (Let (shiftValQ p) (shiftTermQ m))
--stepStrA (Let p  m                   ) = [| Let (stepStrRS p) (pure m) |] <|> [| Let (pure p) (stepStrA m) |]

  stepStrA (Sub (Val (Lam n))                 (GApp p m Here)) =
    do p' <- renameMValQ contractM p
       m' <- renameMTermQ contractM (renameTermQ permute m)
       pure $ Sub (Sub (Val p') n) m'
  stepStrA (Sub (Val (Var el))                 m             ) = Just $ renameTermQ (contract el) m
  stepStrA (Sub (GApp p n el)                  m             ) = Just $ GApp p (Sub n (shiftTermQ m)) el
  stepStrA (Sub (Sub (Val p) (GApp q n Here))  m             ) =
    do q' <- renameMValQ contractM q
       n' <- renameMTermQ contractM (renameTermQ permute n)
       pure $ Sub (Val p) (GApp (shiftValQ q') (Sub (shiftTermQ n') (shiftTermQ m)) Here)
  stepStrA (Sub (Sub  n m)                     k             ) = Just $ Sub n (Sub m (shiftTermQ k))
  stepStrA (Sub (Val (Lam n))                  m             ) = if isCoval m
                                                                   then Nothing
                                                                   else Just $ Let (Lam n) m
  stepStrA (Sub  u                             k             ) = [| Sub (stepStrA u) (pure k) |] <|> [| Sub (pure u) (stepStrA k) |]

  stepStrA  _                                                  = Nothing

  stepStrRS : ValQ g a -> Maybe (ValQ g a)
  stepStrRS (SubV p (Var  Here)     ) = Just p
  stepStrRS (SubV p (Var (There el))) = Just $ Var el
  stepStrRS (SubV p (Lam m)         ) = Just $ Lam $ Let (shiftValQ p) (shiftTermQ m)
  stepStrRS (SubV p  q              ) = [| SubV (stepStrRS p) (pure q) |] <|> [| SubV (pure p) (stepStrRS q) |]
  stepStrRS  _                        = Nothing

-- reduction + conversion



stepSIter : Term [] a -> (Nat, TermQ [] a)
stepSIter = iterCount stepStrA . encode
  -}