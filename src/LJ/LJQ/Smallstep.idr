module LJ.LJQ.Smallstep

import Data.List
import Subset
import Iter

import Lambda.STLC.Ty
import Lambda.STLC.Term
import LJ.LJQ.Term

%default total
%access public export

-- reduction

mutual
  stepA : Async g a -> Maybe (Async g a)

  stepA (Let   (Var el)  t                   ) = Just $ renameAsync (contract el) t
  stepA (Let a@(Lam _ ) (Val p              )) = Just $ Val $ SubV a p
  stepA (Let a@(Lam u ) (GApp p t  Here     )) = Just $ Sub (Let (SubV a p) u) (Let (shiftRSync a) (shiftAsync t))
  stepA (Let a@(Lam _ ) (GApp p t (There el))) = Just $ GApp (SubV a p) (Let (shiftRSync a) (shiftAsync t)) el
  stepA (Let    k        m                   ) = [| Let (stepRS k) (pure m) |] <|> [| Let (pure k) (stepA m) |]

  stepA (Sub (Val p      ) t) = Just $ Let p t
  stepA (Sub (GApp p v el) t) = Just $ GApp p (Sub v (shiftAsync t)) el
  stepA (Sub  u            k) = [| Sub (stepA u) (pure k) |] <|> [| Sub (pure u) (stepA k) |]

  stepA  _                    = Nothing

  --stepA (Val p)                                = Val <$> stepRS p

  stepRS : RSync g a -> Maybe (RSync g a)
  stepRS (SubV   (Var el)  p              ) = Just $ renameRSync (contract el) p
  stepRS (SubV a@(Lam _)  (Var  Here     )) = Just a
  stepRS (SubV   (Lam _)  (Var (There el))) = Just $ Var el
  stepRS (SubV a@(Lam _)  (Lam t         )) = Just $ Lam $ Let (shiftRSync a) (shiftAsync t)
  stepRS (SubV    k        m              ) = [| SubV (stepRS k) (pure m) |] <|> [| SubV (pure k) (stepRS m) |]
  stepRS  _                                 = Nothing

-- strong reduction

isCoval : Async g a -> Bool
isCoval (Val (Var Here)) = True
isCoval (GApp p m Here)  = isJust (renameMRSync contractM p) && isJust (renameMAsync contractM (renameAsync permute m))
isCoval  _               = False

mutual
  stepStrA : Async g a -> Maybe (Async g a)

  stepStrA (Let p (Val q)              ) = Just $ Val $ SubV p q
  stepStrA (Let p (GApp q m  Here)     ) = Just $ Sub (Val p) (GApp (SubV (shiftRSync p) (shiftRSync q))
                                                              (Let (shiftRSync p) (shiftAsync m)) Here)
  stepStrA (Let p (GApp q m (There el))) = Just $ GApp (SubV p q) (Let (shiftRSync p) (shiftAsync m)) el
  stepStrA (Let p (Sub n m)            ) = Just $ Sub (Let p n) (Let (shiftRSync p) (shiftAsync m))
--stepStrA (Let p  m                   ) = [| Let (stepStrRS p) (pure m) |] <|> [| Let (pure p) (stepStrA m) |]

  stepStrA (Sub (Val (Lam n))                 (GApp p m Here)) =
    do p' <- renameMRSync contractM p
       m' <- renameMAsync contractM (renameAsync permute m)
       pure $ Sub (Sub (Val p') n) m'
  stepStrA (Sub (Val (Var el))                 m             ) = Just $ renameAsync (contract el) m
  stepStrA (Sub (GApp p n el)                  m             ) = Just $ GApp p (Sub n (shiftAsync m)) el
  stepStrA (Sub (Sub (Val p) (GApp q n Here))  m             ) =
    do q' <- renameMRSync contractM q
       n' <- renameMAsync contractM (renameAsync permute n)
       pure $ Sub (Val p) (GApp (shiftRSync q') (Sub (shiftAsync n') (shiftAsync m)) Here)
  stepStrA (Sub (Sub  n m)                     k             ) = Just $ Sub n (Sub m (shiftAsync k))
  stepStrA (Sub (Val (Lam n))                  m             ) = if isCoval m
                                                                   then Nothing
                                                                   else Just $ Let (Lam n) m
  stepStrA (Sub  u                             k             ) = [| Sub (stepStrA u) (pure k) |] <|> [| Sub (pure u) (stepStrA k) |]

  stepStrA  _                                                  = Nothing

  stepStrRS : RSync g a -> Maybe (RSync g a)
  stepStrRS (SubV p (Var  Here)     ) = Just p
  stepStrRS (SubV p (Var (There el))) = Just $ Var el
  stepStrRS (SubV p (Lam m)         ) = Just $ Lam $ Let (shiftRSync p) (shiftAsync m)
  stepStrRS (SubV p  q              ) = [| SubV (stepStrRS p) (pure q) |] <|> [| SubV (pure p) (stepStrRS q) |]
  stepStrRS  _                        = Nothing

-- reduction + conversion

stepIter : Term [] a -> (Nat, Async [] a)
stepIter = iterCount stepA . encode

stepSIter : Term [] a -> (Nat, Async [] a)
stepSIter = iterCount stepStrA . encode
