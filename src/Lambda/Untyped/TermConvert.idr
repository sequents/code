module Lambda.Untyped.TermConvert

import public Lambda.Untyped.TermDB
import public Lambda.Untyped.TermNam

%default total
%access public export

toDB : (Name -> Nat) -> TermNam.Term -> TermDB.Term
toDB conv = go []
  where
  go : List Name -> TermNam.Term -> TermDB.Term
  go ns (Var n)   = Var $ fromMaybe (conv n) (elemIndex n ns)
  go ns (Lam n t) = Lam $ go (n::ns) t
  go ns (App t u) = App (go ns t) (go ns u)

fromDB : (Nat -> Name) -> TermDB.Term -> TermNam.Term 
fromDB conv = go []
  where
  go : List Name -> TermDB.Term -> TermNam.Term 
  go ns (Var i) = Var $ fromMaybe (conv i) (index' i ns)
  go ns (Lam t) = let x = fresh ns in
                  Lam x $ go (x::ns) t
  go ns (App t u) = App (go ns t) (go ns u)
