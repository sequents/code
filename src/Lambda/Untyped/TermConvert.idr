module Lambda.Untyped.TermConvert

import Lambda.Untyped.TermDB
import Lambda.Untyped.TermNam

%default total
%access public export

toDB : (Name -> Nat) -> TermNam.Term -> TermDB.Term
toDB conv = go []
  where
  go : List Name -> TermNam.Term -> TermDB.Term
  go vs (Var v)   = Var $ fromMaybe (conv v) (elemIndex v vs)
  go vs (Lam n t) = Lam $ go (n::vs) t
  go vs (App t u) = App (go vs t) (go vs u)

fromDB : (Nat -> Name) -> TermDB.Term -> TermNam.Term 
fromDB conv = go []
  where
  go : List Name -> TermDB.Term -> TermNam.Term 
  go ns (Var n) = Var $ fromMaybe (conv n) (index' n ns)
  go ns (Lam t) = let x = fresh ns in
                  Lam x $ go (x::ns) t
  go ns (App t u) = App (go ns t) (go ns u)
