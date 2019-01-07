module Lambda.Untyped.TermDB

%default total
%access public export

data Term = Var Nat
          | Lam Term
          | App Term Term

Term0 : Term
Term0 = App (Lam $ App (Var Z) (Var Z)) (Lam $ Var Z)

Term1 : Term
Term1 = App (App (Lam $ Var Z) (Lam $ Var Z)) (Lam $ Var Z)

Term2 : Term
Term2 = App (Lam $ Var Z) (App (Lam $ Var Z) (Lam $ Var Z))

false : Term
false = Lam $ Lam $ Var 1

true : Term
true = Lam $ Lam $ Var 0

if2 : Term
if2 = Lam $ Lam $ Lam $ App (App (Var 2) (Var 0)) (Var 1)

zero : Term
zero = Lam $ Lam $ Var 1

succ : Term
succ = Lam $ Lam $ Lam $ App (Var 0) (Var 2)

one : Term 
one = App succ zero

two : Term 
two = App succ one

three : Term
three = App succ two

isZero : Term
isZero = Lam $ App (App (Var 0) true) (Lam false)

const : Term
const = Lam $ Lam $ Var 1

pair : Term
pair = Lam $ Lam $ Lam $ App (App (Var 0) (Var 2)) (Var 1)

fstc : Term
fstc = Lam $ App (Var 0) (Lam $ Lam $ Var 1)

sndc : Term
sndc = Lam $ App (Var 0) (Lam $ Lam $ Var 0)

fix : Term
fix = Lam $ App (Lam $ App (Var 1) $ App (Var 0) (Var 0)) (Lam $ App (Var 1) $ App (Var 0) (Var 0))

add : Term
add = App fix $ Lam $ Lam $ Lam $ App (App (Var 1) (Var 0)) (Lam $ App succ (App (App (Var 3) (Var 0)) (Var 1)))

mul : Term
mul = App fix $ Lam $ Lam $ Lam $ App (App (Var 1) zero) (Lam $ App (App add (Var 1)) (App (App (Var 3) (Var 0)) (Var 1)))

fac : Term
fac = App fix $ Lam $ Lam $ App (App (Var 0) one) (Lam $ App (App mul (Var 1)) (App (Var 2) (Var 0)))

eqnat : Term
eqnat = App fix $ 
            Lam $ Lam $ Lam $ App (App (Var 1) 
                                       (App (App (Var 0) true) (App const false))) 
                                  (Lam $ App (App (Var 1) false) (Lam $ App (App (Var 4) (Var 1)) (Var 0)))

sumto : Term
sumto = App fix $ Lam $ Lam $ App (App (Var 0) zero) (Lam $ App (App add (Var 1)) (App (Var 2) (Var 0)))

n5 : Term
n5 = App (App add two) three

n6 : Term
n6 = App (App add three) three

--

zero' : Term 
zero' = Lam $ Lam $ Var 0

one' : Term 
one' = Lam $ Lam $ App (Var 1) (Var 0)

succ' : Term
succ' = Lam $ Lam $ Lam $ App (Var 1) (App (App (Var 2) (Var 1)) (Var 0))
