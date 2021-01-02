module LJ.F.Smallstep

import Data.List
import Subset
import Iter

import LJ.F.Term

%default total
%access public export

concat : LSync g a b -> LSync g b c -> LSync g a c
concat (AxL un)  s2 = s2
concat (IL t s1) s2 = IL t (concat s1 s2)
concat (BL t)    s2 = BL $ HCL t (renameLSync weaken s2)

subst1R : RSync g a -> RSync (a::g) b -> RSync g b
subst1R   (AxR el)  q               = renameRSync (contract el) q
subst1R p@(BR _)   (AxR  Here     ) = p
subst1R p@(BR _)   (AxR (There el)) = AxR el
subst1R p@(BR _)   (BR t)           = BR $ HCR p t

subst1RL : RSync g a -> LSync (a::g) b c -> LSync g b c
subst1RL   (AxR el)  k       = renameLSync (contract el) k
subst1RL p@(BR _)   (AxL un) = AxL un
subst1RL p@(BR _)   (IL q k) = IL (subst1R p q) (subst1RL p k)
subst1RL p@(BR _)   (BL t)   = BL $ HCR (renameRSync weaken p) (renameAsync permute0 t)

-- reduction

stepF : Async g a -> Maybe (Async g a)
stepF (HCL (IR t)     (IL q k)         ) = Just $ HCL (HCR q t) k
stepF (HCL (FR q)     (BL t)           ) = Just $ HCR q t
stepF (HCL (FL el k)   m               ) = Just $ FL el (concat k m)

stepF (HCR   (AxR el)  t               ) = Just $ renameAsync (contract el) t
stepF (HCR p@(BR _)   (IR t)           ) = Just $ IR $ HCR (renameRSync weaken p) (renameAsync permute0 t)
stepF (HCR p@(BR _)   (FR t)           ) = Just $ FR $ subst1R p t
stepF (HCR p@(BR u)   (FL  Here      k)) = Just $ HCL u (subst1RL p k)
stepF (HCR p@(BR _)   (FL (There el) k)) = Just $ FL el (subst1RL p k)

stepF  _                                = Nothing
