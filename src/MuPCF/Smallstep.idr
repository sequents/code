module MuPCF.Smallstep

import Data.List
import Iter
import Subset
import LambdaMu.Ty
import MuPCF.Term

%access public export
%default total

rename : Subset g d -> Term g a s -> Term d a s
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t1 t2)  = App (rename r t1) (rename r t2)
rename r (Mu t)       = Mu $ rename r t
rename r (Named el t) = Named el (rename r t)
rename r  Zero        = Zero
rename r (Succ n)     = Succ $ rename r n
rename r (If0 p t f)  = If0 (rename r p) (rename r t) (rename (ext r) f)
rename r (Fix f)      = Fix $ rename (ext r) f

renameN : Subset d s -> Term g a d -> Term g a s
renameN r (Var el)     = Var el
renameN r (Lam t)      = Lam $ renameN r t
renameN r (App t u)    = App (renameN r t) (renameN r u)
renameN r (Mu t)       = Mu $ renameN (ext r) t
renameN r (Named el t) = Named (r el) (renameN r t)
renameN r  Zero        = Zero
renameN r (Succ n)     = Succ $ renameN r n
renameN r (If0 p t f)  = If0 (renameN r p) (renameN r t) (renameN r f)
renameN r (Fix f)      = Fix $ renameN r f

renameMN : SubsetM d s -> Term g a d -> Maybe (Term g a s)
renameMN r (Var el)     = Just $ Var el
renameMN r (Lam t)      = Lam <$> renameMN r t
renameMN r (App t u)    = [| App (renameMN r t) (renameMN r u) |]
renameMN r (Mu t)       = Mu <$> renameMN (extM r) t
renameMN r (Named el t) = [| Named (r el) (renameMN r t) |]
renameMN r  Zero        = Just Zero
renameMN r (Succ n)     = Succ <$> renameMN r n
renameMN r (If0 p t f)  = [| If0 (renameMN r p) (renameMN r t) (renameMN r f) |]
renameMN r (Fix f)      = Fix <$> renameMN r f

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
subst s (App t1 t2)  = App (subst s t1) (subst s t2)
subst s (Mu t)       = Mu $ subst (exts' s) t
subst s (Named el t) = Named el (subst s t)
subst s  Zero        = Zero
subst s (Succ n)     = Succ $ subst s n
subst s (If0 p t f)  = If0 (subst s p) (subst s t) (subst (exts s) f)
subst s (Fix f)      = Fix $ subst (exts s) f

subst1 : Term (b::g) a s -> Term g b s -> Term g a s
subst1 {g} {b} {s} t sub = subst {g=b::g} go t
  where
  go : Subst (b::g) g s
  go  Here      = sub
  go (There el) = Var el

appN : Term g c ((a~>b)::d) -> Term g a d -> Term g c (b::d)
appN (Var e)             v = Var e
appN (Lam t)             v = Lam $ appN t (rename There v)
appN (App t u)           v = App (appN t v) (appN u v)
appN (Mu t)              v = Mu $ renameN permute $ assert_total $ appN (renameN permute t) (renameN There v)
appN (Named  Here     t) v = Named Here (App (appN t v) (renameN There v))
appN (Named (There e) t) v = Named (There e) (appN t v)
appN  Zero               v = Zero
appN (Succ n)            v = Succ $ appN n v
appN (If0 p t f)         v = If0 (appN p v) (appN t v) (appN f (rename There v))
appN (Fix f)             v = Fix $ appN f (rename There v)

appNR : Term g c (a::d) -> Term g (a~>b) d -> Term g c (b::d)
appNR (Var e)             v = Var e
appNR (Lam t)             v = Lam $ appNR t (rename There v)
appNR (App t u)           v = App (appNR t v) (appNR u v)
appNR (Mu t)              v = Mu $ renameN permute $ assert_total $ appNR (renameN permute t) (renameN There v)
appNR (Named  Here     t) v = Named Here $ App (renameN There v) (appNR t v)
appNR (Named (There e) t) v = Named (There e) $ appNR t v
appNR  Zero               v = Zero
appNR (Succ n)            v = Succ $ appNR n v
appNR (If0 p t f)         v = If0 (appNR p v) (appNR t v) (appNR f (rename There v))
appNR (Fix f)             v = Fix $ appNR f (rename There v)


isVal : Term g a d -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
isVal  Zero    = True
isVal (Succ n) = isVal n
isVal  _       = False  

step : Term g a d -> Maybe (Term g a d)
step (App (Lam u) v)       = Just $ subst1 u v
step (App (Mu u)  v)       = Just $ Mu $ appN u v
step (App  t      u)       = 
  if isVal t 
    then Nothing
    else [| App (step t) (pure u) |]
step (Mu (Named a (Mu u))) = Just $ Mu $ renameN (contract a) u
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
stepV (App u  (Mu v))       = Just $ Mu $ appNR v u
stepV (App t1  t2   )       = 
  if isVal t1 || isMu t1
    then 
      if isVal t2
      then
        case t1 of
          Lam u => Just $ subst1 u t2
          Mu u => Just $ Mu $ appN u t2
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else [| App (stepV t1) (pure t2) |]
stepV (Mu (Named a (Mu u))) = Just $ Mu $ renameN (contract a) u
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

stepV2 : Term g a d -> Maybe (Term g a d)
stepV2 (App u  (Mu v))       = 
  if isVal u 
    then Just $ Mu $ appNR v u
    else [| App (stepV2 u) (pure (Mu v)) |]
stepV2 (App (Mu u) v)        = Just $ Mu $ appN u v
stepV2 (App t1     t2)       = 
  if isVal t1
    then 
      if isVal t2
      then
        case t1 of
          Lam u => Just $ subst1 u t2
          _ => Nothing
      else App t1 <$> (stepV t2)           
    else [| App (stepV t1) (pure t2) |]
stepV2 (Mu (Named a (Mu u))) = Just $ Mu $ renameN (contract a) u
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
