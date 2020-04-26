module LambdaMu.PCF.Top.Smallstep

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.PCF.Top.Term

%access public export
%default total

mutual
  rename : Subset g d -> Term g a s -> Term d a s
  rename r (Var el)    = Var $ r el
  rename r (Lam t)     = Lam $ rename (ext r) t
  rename r (App t u)   = App (rename r t) (rename r u)
  rename r (Mu t)      = Mu $ renameCmd r t
  rename r  Zero       = Zero
  rename r (Succ n)    = Succ $ rename r n
  rename r (If0 p t f) = If0 (rename r p) (rename r t) (rename (ext r) f)
  rename r (Fix f)     = Fix $ rename (ext r) f

  renameCmd : Subset g d -> Cmd g s -> Cmd d s
  renameCmd r (Named el t) = Named el $ rename r t
  renameCmd r (Top t)      = Top $ rename r t

mutual
  renameN : Subset d s -> Term g a d -> Term g a s
  renameN r (Var el)    = Var el
  renameN r (Lam t)     = Lam $ renameN r t
  renameN r (App t u)   = App (renameN r t) (renameN r u)
  renameN r (Mu t)      = Mu $ renameCmdN (ext r) t
  renameN r  Zero       = Zero
  renameN r (Succ n)    = Succ $ renameN r n
  renameN r (If0 p t f) = If0 (renameN r p) (renameN r t) (renameN r f)
  renameN r (Fix f)     = Fix $ renameN r f

  renameCmdN : Subset d s -> Cmd g d -> Cmd g s
  renameCmdN r (Named el t) = Named (r el) (renameN r t)
  renameCmdN r (Top t)      = Top $ renameN r t

mutual
  renameMN : SubsetM d s -> Term g a d -> Maybe (Term g a s)
  renameMN r (Var el)    = Just $ Var el
  renameMN r (Lam t)     = Lam <$> renameMN r t
  renameMN r (App t u)   = [| App (renameMN r t) (renameMN r u) |]
  renameMN r (Mu t)      = Mu <$> renameCmdMN (extM r) t
  renameMN r  Zero       = Just Zero
  renameMN r (Succ n)    = Succ <$> renameMN r n
  renameMN r (If0 p t f) = [| If0 (renameMN r p) (renameMN r t) (renameMN r f) |]
  renameMN r (Fix f)     = Fix <$> renameMN r f

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
  subst s (Var el)    = s el
  subst s (Lam t)     = Lam $ subst (exts s) t
  subst s (App t u)   = App (subst s t) (subst s u)
  subst s (Mu t)      = Mu $ substCmd (exts' s) t
  subst s  Zero       = Zero
  subst s (Succ n)    = Succ $ subst s n
  subst s (If0 p t f) = If0 (subst s p) (subst s t) (subst (exts s) f)
  subst s (Fix f)     = Fix $ subst (exts s) f

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
  appN (Var e)     v = Var e
  appN (Lam t)     v = Lam $ appN t (rename There v)
  appN (App t u)   v = App (appN t v) (appN u v)
  appN (Mu t)      v = Mu $ renameCmdN permute $ assert_total $ appCmdN (renameCmdN permute t) (renameN There v)
  appN  Zero       v = Zero
  appN (Succ n)    v = Succ $ appN n v
  appN (If0 p t f) v = If0 (appN p v) (appN t v) (appN f (rename There v))
  appN (Fix f)     v = Fix $ appN f (rename There v)

  appCmdN : Cmd g ((a~>b)::d) -> Term g a d -> Cmd g (b::d)
  appCmdN (Named  Here     t) v = Named Here $ App (appN t v) (renameN There v)
  appCmdN (Named (There e) t) v = Named (There e) $ appN t v
  appCmdN (Top t)             v = Top $ appN t v

mutual
  appNR : Term g c (a::d) -> Term g (a~>b) d -> Term g c (b::d)
  appNR (Var e)     v = Var e
  appNR (Lam t)     v = Lam $ appNR t (rename There v)
  appNR (App t u)   v = App (appNR t v) (appNR u v)
  appNR (Mu t)      v = Mu $ renameCmdN permute $ assert_total $ appCmdNR (renameCmdN permute t) (renameN There v)
  appNR  Zero       v = Zero
  appNR (Succ n)    v = Succ $ appNR n v
  appNR (If0 p t f) v = If0 (appNR p v) (appNR t v) (appNR f (rename There v))
  appNR (Fix f)     v = Fix $ appNR f (rename There v)

  appCmdNR : Cmd g (a::d) -> Term g (a~>b) d -> Cmd g (b::d)
  appCmdNR (Named  Here     t) v = Named Here $ App (renameN There v) (appNR t v)
  appCmdNR (Named (There e) t) v = Named (There e) $ appNR t v
  appCmdNR (Top t)             v = Top $ appNR t v

mutual
  substTop : Term g a (Bot::d) -> Term g a d
  substTop (Var el)    = Var el
  substTop (Lam t)     = Lam $ substTop t
  substTop (App t u)   = App (substTop t) (substTop u)
  substTop (Mu t)      = Mu $ assert_total $ substTopCmd $ renameCmdN permute t
  substTop  Zero       = Zero
  substTop (Succ n)    = Succ $ substTop n
  substTop (If0 p t f) = If0 (substTop p) (substTop t) (substTop f)
  substTop (Fix f)     = Fix $ substTop f

  substTopCmd : Cmd g (Bot::d) -> Cmd g d
  substTopCmd (Named Here t) = Top $ substTop t
  substTopCmd (Named (There el) t) = Named el $ substTop t
  substTopCmd (Top t) = Top $ substTop t

isVal : Term g a d -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a d -> Maybe (Term g a d)
step (App (Lam t) u)       = Just $ subst1 t u
step (App (Mu c)  u)       = Just $ Mu $ appCmdN c u
step (App  t      u)       =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Mu (Named e (Mu c))) = Just $ Mu $ renameCmdN (contract e) c
step (Mu (Top (Mu c)))     = Just $ Mu $ substTopCmd c
step (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> step t
step (Succ m)              = Succ <$> step m
step (If0 Zero t f)        = Just t
step (If0 (Succ n) t f)    = Just $ subst1 f n
step (If0 p t f)           = (\q => If0 q t f) <$> step p
step (Fix f)               = Just $ subst1 f (Fix f)
step  _                    = Nothing

isMu : Term g a d -> Bool
isMu (Mu _) = True
isMu  _     = False

stepV : Term g a d -> Maybe (Term g a d)
stepV (App u  (Mu c))       = Just $ Mu $ appCmdNR c u
stepV (App t   u    )       =
  if isVal t || isMu t
    then
      if isVal u
      then
        case t of
          Lam v => Just $ subst1 v u
          Mu c => Just $ Mu $ appCmdN c u
          _ => Nothing
      else App t <$> (stepV u)
    else [| App (stepV t) (pure u) |]
stepV (Mu (Named e (Mu c))) = Just $ Mu $ renameCmdN (contract e) c
stepV (Mu (Top (Mu c)))     = Just $ Mu $ substTopCmd c
stepV (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV t
stepV (Succ m)              = Succ <$> stepV m
stepV (If0 Zero t f)        = Just t
stepV (If0 (Succ n) t f)    = Just $ subst1 f n
stepV (If0 p t f)           = (\q => If0 q t f) <$> stepV p
stepV (Fix f)               = Just $ subst1 f (Fix f)
stepV  _                    = Nothing

-- ala Ong-Stewart'97
stepV2 : Term g a d -> Maybe (Term g a d)
stepV2 (App  t     (Mu c))   =
  if isVal t
    then Just $ Mu $ appCmdNR c t
    else [| App (stepV2 t) (pure (Mu c)) |]
stepV2 (App (Mu c)  u    )   = Just $ Mu $ appCmdN c u
stepV2 (App  t      u   )   =
  if isVal t
    then
      if isVal u
      then
        case t of
          Lam v => Just $ subst1 v u
          _ => Nothing
      else App t <$> (stepV u)
    else [| App (stepV t) (pure u) |]
stepV2 (Mu (Named e (Mu c))) = Just $ Mu $ renameCmdN (contract e) c
stepV2 (Mu (Top (Mu c)))     = Just $ Mu $ substTopCmd c
stepV2 (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV2 t
stepV2 (Succ m)              = Succ <$> stepV2 m
stepV2 (If0 Zero t f)        = Just t
stepV2 (If0 (Succ n) t f)    = Just $ subst1 f n
stepV2 (If0 p t f)           = (\q => If0 q t f) <$> stepV2 p
stepV2 (Fix f)               = Just $ subst1 f (Fix f)
stepV2  _                    = Nothing
