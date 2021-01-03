module LJ.F.Ty

%default total
%access public export

mutual
  data PTy = AP | D NTy

  data NTy = AN | U PTy | Imp PTy NTy

infix 5 ~>
(~>) : PTy -> NTy -> NTy
(~>) = Imp

-- unary negative formula
data UN : NTy -> Type where
  UA : UN  AN
  UU : UN (U p)