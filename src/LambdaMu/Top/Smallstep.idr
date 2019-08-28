module LambdaMu.Top.Smallstep

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.Top.Term

%access public export
%default total

mutual
  rename : Subset g d -> Term g a s -> Term d a s
  rename r (Var el)  = Var $ r el
  rename r (Lam t)   = Lam $ rename (ext r) t
  rename r (App t u) = App (rename r t) (rename r u)
  rename r (Mu t)    = Mu $ renameCmd r t

  renameCmd : Subset g d -> Cmd g s -> Cmd d s
  renameCmd r (Named el t) = Named el $ rename r t
  renameCmd r (Top t)      = Top $ rename r t

mutual
  renameN : Subset d s -> Term g a d -> Term g a s
  renameN r (Var el)     = Var el
  renameN r (Lam t)      = Lam $ renameN r t
  renameN r (App t u)    = App (renameN r t) (renameN r u)
  renameN r (Mu t)       = Mu $ renameCmdN (ext r) t
  
  renameCmdN : Subset d s -> Cmd g d -> Cmd g s
  renameCmdN r (Named el t) = Named (r el) (renameN r t)
  renameCmdN r (Top t)      = Top $ renameN r t

mutual
  renameMN : SubsetM d s -> Term g a d -> Maybe (Term g a s)
  renameMN r (Var el)     = Just $ Var el
  renameMN r (Lam t)      = Lam <$> renameMN r t
  renameMN r (App t u)    = [| App (renameMN r t) (renameMN r u) |]
  renameMN r (Mu t)       = Mu <$> renameCmdMN (extM r) t
  
  renameCmdMN : SubsetM d s -> Cmd g d -> Maybe (Cmd g s)
  renameCmdMN r (Named el t) = [| Named (r el) (renameMN r t) |]
  renameCmdMN r (Top t)      = Top <$> renameMN r t

Subst : List Ty -> List Ty -> List Ty -> Type
Subst g d s = {x : Ty} -> Elem x g -> Term d x s

exts : Subst g d s -> Subst (b::g) (b::d) s
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

exts' : Subst g d s -> Subst g d (a::s)
exts' s = renameN There . s

mutual
  subst : Subst g d s -> Term g a s -> Term d a s
  subst s (Var el)     = s el
  subst s (Lam t)      = Lam $ subst (exts s) t
  subst s (App t u)    = App (subst s t) (subst s u)
  subst s (Mu t)       = Mu $ substCmd (exts' s) t
  
  substCmd : Subst g d s -> Cmd g s -> Cmd d s
  substCmd s (Named el t) = Named el $ subst s t
  substCmd s (Top t)      = Top $ subst s t
  
subst1 : Term (b::g) a s -> Term g b s -> Term g a s
subst1 {g} {b} {s} t sub = subst {g=b::g} go t
  where
  go : Subst (b::g) g s
  go  Here      = sub
  go (There el) = Var el

-- commuting conversion / structural reduction
mutual
  appN : Term g c ((a~>b)::d) -> Term g a d -> Term g c (b::d)
  appN (Var e)    v = Var e
  appN (Lam t)    v = Lam $ appN t (rename There v)
  appN (App t u)  v = App (appN t v) (appN u v)
  appN (Mu t)     v = Mu $ renameCmdN permute $ assert_total $ appCmdN (renameCmdN permute t) (renameN There v)
  
  appCmdN : Cmd g ((a~>b)::d) -> Term g a d -> Cmd g (b::d)
  appCmdN (Named  Here     t) v = Named Here $ App (appN t v) (renameN There v)
  appCmdN (Named (There e) t) v = Named (There e) $ appN t v
  appCmdN (Top t)             v = Top $ appN t v

mutual
  appNR : Term g c (a::d) -> Term g (a~>b) d -> Term g c (b::d)
  appNR (Var e)    v = Var e
  appNR (Lam t)    v = Lam $ appNR t (rename There v)
  appNR (App t u)  v = App (appNR t v) (appNR u v)
  appNR (Mu t)     v = Mu $ renameCmdN permute $ assert_total $ appCmdNR (renameCmdN permute t) (renameN There v)

  appCmdNR : Cmd g (a::d) -> Term g (a~>b) d -> Cmd g (b::d)
  appCmdNR (Named  Here     t) v = Named Here $ App (renameN There v) (appNR t v)
  appCmdNR (Named (There e) t) v = Named (There e) $ appNR t v
  appCmdNR (Top t)             v = Top $ appNR t v

mutual
  substTop : Term g a (Bot::d) -> Term g a d
  substTop (Var el)  = Var el
  substTop (Lam t)   = Lam $ substTop t
  substTop (App t u) = App (substTop t) (substTop u)
  substTop (Mu t)    = Mu $ assert_total $ substTopCmd $ renameCmdN permute t

  substTopCmd : Cmd g (Bot::d) -> Cmd g d
  substTopCmd (Named Here t) = Top $ substTop t
  substTopCmd (Named (There el) t) = Named el $ substTop t
  substTopCmd (Top t) = Top $ substTop t

isVal : Term g a d -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a d -> Maybe (Term g a d)
step (App (Lam u) v)       = Just $ subst1 u v
step (App (Mu u)  v)       = Just $ Mu $ appCmdN u v
step (App  t      u)       = 
  if isVal t 
    then Nothing
    else [| App (step t) (pure u) |]
step (Mu (Named a (Mu u))) = Just $ Mu $ renameCmdN (contract a) u
step (Mu (Top (Mu u)))     = Just $ Mu $ substTopCmd u
step (Mu (Named Here t))   = 
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> step t 
step  _                    = Nothing

isMu : Term g a d -> Bool
isMu (Mu _) = True
isMu  _     = False

stepV : Term g a d -> Maybe (Term g a d)
stepV (App u  (Mu v))       = Just $ Mu $ appCmdNR v u
stepV (App t1  t2   )       = 
  if isVal t1 || isMu t1
    then 
      if isVal t2
      then
        case t1 of
          Lam u => Just $ subst1 u t2
          Mu u => Just $ Mu $ appCmdN u t2
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else [| App (stepV t1) (pure t2) |]
stepV (Mu (Named a (Mu u))) = Just $ Mu $ renameCmdN (contract a) u
stepV (Mu (Top (Mu u)))     = Just $ Mu $ substTopCmd u
stepV (Mu (Named Here t))   = 
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV t 
stepV  _                    = Nothing

-- ala Ong-Stewart'97
stepV2 : Term g a d -> Maybe (Term g a d)
stepV2 (App u  (Mu v))       = 
  if isVal u 
    then Just $ Mu $ appCmdNR v u
    else [| App (stepV2 u) (pure (Mu v)) |]
stepV2 (App (Mu u)  v)       = Just $ Mu $ appCmdN u v  
stepV2 (App t1  t2   )       = 
  if isVal t1
    then 
      if isVal t2
      then
        case t1 of
          Lam u => Just $ subst1 u t2
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else [| App (stepV t1) (pure t2) |]
stepV2 (Mu (Named a (Mu u))) = Just $ Mu $ renameCmdN (contract a) u
stepV2 (Mu (Top (Mu u)))     = Just $ Mu $ substTopCmd u
stepV2 (Mu (Named Here t))   = 
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV2 t 
stepV2  _                    = Nothing

iterStep : Term g a d -> Term g a d
iterStep = iter step

iterStepV : Term g a d -> Term g a d
iterStepV = iter stepV
