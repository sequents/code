module OrdNat 

%default total
%access public export

data OrdNat : Nat -> Nat -> Type where
  EQN :              OrdNat  n     n
  LTN : (k : Nat) -> OrdNat  n    (n+k)
  GTN : (k : Nat) -> OrdNat (n+k)  n

ordNatS : OrdNat n m -> OrdNat (S n) (S m)  
ordNatS {n}     {m=n}    EQN    = EQN
ordNatS {n}     {m=n+k} (LTN k) = LTN k
ordNatS {n=m+k} {m}     (GTN k) = GTN k

ordNat : (n, m : Nat) -> OrdNat n m
ordNat  Z     Z    = EQN
ordNat  Z    (S m) = LTN (S m)
ordNat (S n)  Z    = GTN (S n)
ordNat (S n) (S m) = ordNatS $ ordNat n m 
