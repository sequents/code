module MuPCF.Term

import Data.List
import LambdaMu.Ty

%access public export
%default total

data Term : List Ty -> Ty -> List Ty -> Type where
  Var   : Elem a g -> Term g a d
  Lam   : Term (a::g) b d -> Term g (a~>b) d
  App   : Term g (a~>b) d -> Term g a d -> Term g b d
  Mu    : Term g Bot (a::d) -> Term g a d
  Named : Elem a d -> Term g a d -> Term g Bot d
  Zero  : Term g A d
  Succ  : Term g A d -> Term g A d
  If0   : Term g A d -> Term g a d -> Term (A::g) a d -> Term g a d
  Fix   : Term (a::g) a d -> Term g a d
