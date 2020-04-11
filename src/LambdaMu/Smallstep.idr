module LambdaMu.Smallstep

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import LambdaMu.Term

%access public export
%default total

rename : Subset g d -> Term g a s -> Term d a s
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Mu t)       = Mu $ rename r t
rename r (Named el t) = Named el (rename r t)

renameN : Subset d s -> Term g a d -> Term g a s
renameN r (Var el)     = Var el
renameN r (Lam t)      = Lam $ renameN r t
renameN r (App t u)    = App (renameN r t) (renameN r u)
renameN r (Mu t)       = Mu $ renameN (ext r) t
renameN r (Named el t) = Named (r el) (renameN r t)

renameMN : SubsetM d s -> Term g a d -> Maybe (Term g a s)
renameMN r (Var el)     = Just $ Var el
renameMN r (Lam t)      = Lam <$> renameMN r t
renameMN r (App t u)    = [| App (renameMN r t) (renameMN r u) |]
renameMN r (Mu t)       = Mu <$> renameMN (extM r) t
renameMN r (Named el t) = [| Named (r el) (renameMN r t) |]

Subst : List Ty -> List Ty -> List Ty -> Type
Subst g d s = {x : Ty} -> Elem x g -> Term d x s

exts : Subst g d s -> Subst (b::g) (b::d) s
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

exts' : Subst g d s -> Subst g d (a::s)
exts' s = renameN There . s

subst : Subst g d s -> Term g a s -> Term d a s
subst s (Var el)     = s el
subst s (Lam t)      = Lam $ subst (exts s) t
subst s (App t u)    = App (subst s t) (subst s u)
subst s (Mu t)       = Mu $ subst (exts' s) t
subst s (Named el t) = Named el (subst s t)

subst1 : Term (b::g) a s -> Term g b s -> Term g a s
subst1 {g} {b} {s} t sub = subst {g=b::g} go t
  where
  go : Subst (b::g) g s
  go  Here      = sub
  go (There el) = Var el

-- commuting conversion / structural reduction
appN : Term g c ((a~>b)::d) -> Term g a d -> Term g c (b::d)
appN (Var e)             v = Var e
appN (Lam t)             v = Lam $ appN t (rename There v)
appN (App t u)           v = App (appN t v) (appN u v)
appN (Mu t)              v = Mu $ renameN permute0 $ assert_total $ appN (renameN permute0 t) (renameN weaken v)
appN (Named  Here     t) v = Named Here (App (appN t v) (renameN There v))
appN (Named (There e) t) v = Named (There e) (appN t v)

appNR : Term g c (a::d) -> Term g (a~>b) d -> Term g c (b::d)
appNR (Var e)             v = Var e
appNR (Lam t)             v = Lam $ appNR t (rename There v)
appNR (App t u)           v = App (appNR t v) (appNR u v)
appNR (Mu t)              v = Mu $ renameN permute0 $ assert_total $ appNR (renameN permute0 t) (renameN weaken v)
appNR (Named  Here     t) v = Named Here $ App (renameN weaken v) (appNR t v)
appNR (Named (There e) t) v = Named (There e) $ appNR t v

isVal : Term g a d -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Term g a d -> Maybe (Term g a d)
step (App (Lam t) u)       = Just $ subst1 t u
step (App (Mu t)  u)       = Just $ Mu $ appN t u
step (App  t      u)       =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Mu (Named e (Mu t))) = Just $ Mu $ renameN (contract e) t
step (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> step t
step  _                    = Nothing

isMu : Term g a d -> Bool
isMu (Mu _) = True
isMu  _     = False

stepV : Term g a d -> Maybe (Term g a d)
stepV (App u  (Mu v))       = Just $ Mu $ appNR v u
stepV (App t   u    )       =
  if isVal t || isMu t
    then
      if isVal u
      then
        case t of
          Lam v => Just $ subst1 v u
          Mu v => Just $ Mu $ appN v u
          _ => Nothing
      else App t <$> (stepV u)
    else [| App (stepV t) (pure u) |]
stepV (Mu (Named e (Mu t))) = Just $ Mu $ renameN (contract e) t
stepV (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV t
stepV  _                    = Nothing

-- ala Ong-Stewart'97
stepV2 : Term g a d -> Maybe (Term g a d)
stepV2 (App u      (Mu v))   =
  if isVal u
    then Just $ Mu $ appNR v u
    else [| App (stepV2 u) (pure (Mu v)) |]
stepV2 (App (Mu u)  v    )   = Just $ Mu $ appN u v
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
stepV2 (Mu (Named e (Mu t))) = Just $ Mu $ renameN (contract e) t
stepV2 (Mu (Named Here t))   =
  case renameMN contractM t of
    Just t => Just t
    Nothing => (Mu . Named Here) <$> stepV2 t
stepV2  _                    = Nothing
