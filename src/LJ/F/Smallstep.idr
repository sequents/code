module LJ.F.Smallstep

import Data.List
import Subset
import Iter

import LJ.F.Ty
import LJ.F.Term

%default total
%access public export

-- focused left cut
concat : Stack g a b -> Stack g b c -> Stack g a c
concat (Nil _)     s2 = s2
concat (Cons t s1) s2 = Cons t (concat s1 s2)
concat (C t)       s2 = C $ Cut t (renameStack weaken s2)

-- positive focused right cut
subst1R : Val g a -> Val (a::g) b -> Val g b
subst1R   (Var el)  q               = renameVal (contract el) q
subst1R p@(V _)    (Var  Here     ) = p
subst1R   (V _)    (Var (There el)) = Var el
subst1R p@(V _)    (V t)            = V $ Let p t

-- negative focused right cut
subst1RL : Val g a -> Stack (a::g) b c -> Stack g b c
subst1RL   (Var el)  k         = renameStack (contract el) k
subst1RL   (V _)    (Nil un)   = Nil un
subst1RL p@(V _)    (Cons q k) = Cons (subst1R p q) (subst1RL p k)
subst1RL p@(V _)    (C t)      = C $ Let (renameVal weaken p) (renameTerm permute0 t)

-- reduction

stepF : Term g a -> Maybe (Term g a)
stepF (Cut (Lam t)      (Cons q k)        ) = Just $ Cut (Let q t) k
stepF (Cut (Foc q)      (C t)             ) = Just $ Let q t
stepF (Cut (Cont el k)   m                ) = Just $ Cont el (concat k m)

stepF (Let   (Var el)   t                 ) = Just $ renameTerm (contract el) t
stepF (Let p@(V _)     (Lam t)            ) = Just $ Lam $ Let (renameVal weaken p) (renameTerm permute0 t)
stepF (Let p@(V _)     (Foc t)            ) = Just $ Foc $ subst1R p t
stepF (Let p@(V u)     (Cont  Here      k)) = Just $ Cut u (subst1RL p k)
stepF (Let p@(V _)     (Cont (There el) k)) = Just $ Cont el (subst1RL p k)

stepF  _                                    = Nothing
