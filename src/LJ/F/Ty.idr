module LJ.F.Ty

%default total
%access public export

mutual
  data PTy = AP | D NTy                   -- D for down, called U in CBPV
  data NTy = AN | U PTy | Imp PTy NTy     -- U for up, called F in CBPV

infix 5 ~>
(~>) : PTy -> NTy -> NTy
(~>) = Imp

-- unary negative formula
data UN : NTy -> Type where
  UA : UN  AN
  UU : UN (U p)

-- all positive formulas are unary already