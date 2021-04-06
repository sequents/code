module LJ.F.Ty

%default total

mutual
  public export
  data PTy = AP | D NTy                   -- D for down, called U in CBPV
  public export
  data NTy = AN | U PTy | Imp PTy NTy     -- U for up, called F in CBPV

infix 5 ~>
public export
(~>) : PTy -> NTy -> NTy
(~>) = Imp

-- unary negative formula
public export
data UN : NTy -> Type where
  UA : UN  AN
  UU : UN (U p)

-- all positive formulas are unary already