module LJ.Q.ES.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.Q.ES.Term

%default total
%access public export

-- reduction

mutual
  stepT : TermQ g a -> Maybe (TermQ g a)

  stepT (Let   (Var el)  t                   ) = Just $ renameTerm (contract el) t
  stepT (Let a@(Lam _ ) (V p                )) = Just $ V $ SubV a p
  stepT (Let a@(Lam u ) (GApp p t  Here     )) = Just $ Sub (Let (SubV a p) u) (Let (shiftVal a) (shiftTerm t))
  stepT (Let a@(Lam _ ) (GApp p t (There el))) = Just $ GApp (SubV a p) (Let (shiftVal a) (shiftTerm t)) el
  stepT (Let    k        m                   ) = [| Let (pure k) (stepT m) |] <|> [| Let (stepV k) (pure m) |]

  stepT (Sub (V p)         t) = Just $ Let p t
  stepT (Sub (GApp p v el) t) = Just $ GApp p (Sub v (shiftTerm t)) el
  stepT (Sub  u            k) = [| Sub (pure u) (stepT k) |] <|> [| Sub (stepT u) (pure k) |]

  --stepT (Sub  u            k) = [| Sub (stepT u) (pure k) |] <|> [| Sub (pure u) (stepT k) |]


  --stepT (V p)                                = V <$> stepV p

  stepT  _                    = Nothing

  stepV : ValQ g a -> Maybe (ValQ g a)
  stepV (SubV   (Var el)  p              ) = Just $ renameVal (contract el) p
  stepV (SubV a@(Lam _)  (Var  Here     )) = Just a
  stepV (SubV   (Lam _)  (Var (There el))) = Just $ Var el
  stepV (SubV a@(Lam _)  (Lam t         )) = Just $ Lam $ Let (shiftVal a) (shiftTerm t)
  stepV (SubV    k        m              ) = [| SubV (pure k) (stepV m) |] <|> [| SubV (stepV k) (pure m) |]

  --stepV (SubV    k        m              ) = [| SubV (stepV k) (pure m) |] <|> [| SubV (pure k) (stepV m) |]
  stepV  _                                 = Nothing

-- strong reduction

isCoval : TermQ g a -> Bool
isCoval (V (Var Here))  = True
isCoval (GApp p m Here) = isJust (renameMVal contractM p) && isJust (renameMTerm contractM (renameTerm permute0 m))
isCoval  _              = False

mutual
  stepStrT : TermQ g a -> Maybe (TermQ g a)

  stepStrT (Let p (V q)                ) = Just $ V $ SubV p q
  stepStrT (Let p (GApp q m  Here)     ) = Just $ Sub (V p) (GApp (SubV (shiftVal p) (shiftVal q))
                                                              (Let (shiftVal p) (shiftTerm m)) Here)
  stepStrT (Let p (GApp q m (There el))) = Just $ GApp (SubV p q) (Let (shiftVal p) (shiftTerm m)) el
  stepStrT (Let p (Sub n m)            ) = Just $ Sub (Let p n) (Let (shiftVal p) (shiftTerm m))
--stepStrT (Let p  m                   ) = [| Let (stepStrV p) (pure m) |] <|> [| Let (pure p) (stepStrT m) |]

  stepStrT (Sub (V (Lam n))                 (GApp p m Here)) =
    do p' <- renameMVal contractM p
       m' <- renameMTerm contractM (renameTerm permute0 m)
       pure $ Sub (Sub (V p') n) m'
  stepStrT (Sub (V (Var el))                 m             ) = Just $ renameTerm (contract el) m
  stepStrT (Sub (GApp p n el)                m             ) = Just $ GApp p (Sub n (shiftTerm m)) el
  stepStrT (Sub (Sub (V p) (GApp q n Here))  m             ) =
    do q' <- renameMVal contractM q
       n' <- renameMTerm contractM (renameTerm permute0 n)
       pure $ Sub (V p) (GApp (shiftVal q') (Sub (shiftTerm n') (shiftTerm m)) Here)
  stepStrT (Sub (Sub  n m)                   k             ) = Just $ Sub n (Sub m (shiftTerm k))
  stepStrT (Sub (V (Lam n))                  m             ) = if isCoval m
                                                                   then Nothing
                                                                   else Just $ Let (Lam n) m
  stepStrT (Sub  u                           k             ) = [| Sub (stepStrT u) (pure k) |] <|> [| Sub (pure u) (stepStrT k) |]

  stepStrT  _                                                = Nothing

  stepStrV : ValQ g a -> Maybe (ValQ g a)
  stepStrV (SubV p (Var  Here)     ) = Just p
  stepStrV (SubV p (Var (There el))) = Just $ Var el
  stepStrV (SubV p (Lam m)         ) = Just $ Lam $ Let (shiftVal p) (shiftTerm m)
  stepStrV (SubV p  q              ) = [| SubV (stepStrV p) (pure q) |] <|> [| SubV (pure p) (stepStrV q) |]
  stepStrV  _                        = Nothing

-- reduction + conversion

stepIter : Term [] a -> (Nat, TermQ [] a)
stepIter = iterCount stepT . encode

stepSIter : Term [] a -> (Nat, TermQ [] a)
stepSIter = iterCount stepStrT . encode
