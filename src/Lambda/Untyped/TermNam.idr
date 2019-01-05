module Lambda.Untyped.TermNam

%default total
%access public export

Name : Type
Name = (String, Nat)

X : Name
X = ("x", 0)

Y : Name
Y = ("y", 0)

Z : Name
Z = ("z", 0)

T : Name
T = ("t", 0)

Q : Name
Q = ("q", 0)

data Term = Var Name
          | Lam Name Term
          | App Term Term

Term0 : Term 
Term0 = App (Lam X $ App (Var X) (Var X)) (Lam X $ Var X)

Term1 : Term 
Term1 = App (App (Lam X $ Var X) (Lam X $ Var X)) (Lam X $ Var X)

Term2 : Term 
Term2 = App (Lam X $ Var X) (App (Lam X $ Var X) (Lam X $ Var X))

false : Term
false = Lam X $ Lam Y $ Var X

true : Term
true = Lam X $ Lam Y $ Var Y

ifT : Term
ifT = Lam X $ Lam Y $ Lam Z $ App (App (Var X) (Var Z)) (Var Y)

zero : Term
zero = Lam X $ Lam Y $ Var X

succ : Term
succ = Lam X $ Lam Y $ Lam Z $ App (Var Z) (Var X)

one : Term
one = App succ zero

two : Term
two = App succ one

three : Term
three = App succ two

isZero : Term
isZero = Lam X $ App (App (Var X) true) (Lam Y false)

const : Term
const = Lam X $ Lam Y $ Var X

pair : Term
pair = Lam X $ Lam Y $ Lam Z $ App (App (Var Z) (Var X)) (Var Y)

fstc : Term
fstc = Lam X $ App (Var X) (Lam Y $ Lam Z $ Var Y)

sndc : Term
sndc = Lam X $ App (Var X) (Lam Y $ Lam Z $ Var Z)

fix : Term
fix = Lam X $ App (Lam Y $ App (Var X) $ App (Var Y) (Var Y)) (Lam Y $ App (Var X) $ App (Var Y) (Var Y))

add : Term
add = App fix $ Lam T $ Lam X $ Lam Y $ App (App (Var X) (Var Y)) (Lam Z $ App succ (App (App (Var T) (Var Z)) (Var Y)))

mul : Term
mul = App fix $ Lam T $ Lam X $ Lam Y $ App (App (Var X) zero) (Lam Z $ App (App add (Var Y)) (App (App (Var T) (Var Z)) (Var Y)))

fac : Term
fac = App fix $ Lam T $ Lam X $ App (App (Var X) one) (Lam Z $ App (App mul (Var X)) (App (Var T) (Var Z)))

eqnat : Term
eqnat = App fix $ 
            Lam T $ Lam X $ Lam Y $ App (App (Var X) 
                                             (App (App (Var Y) true) (App const false))) 
                                        (Lam Z $ App (App (Var Y) false) (Lam Q $ App (App (Var T) (Var Z)) (Var Q)))

sumto : Term
sumto = App fix $ Lam T $ Lam X $ App (App (Var X) zero) (Lam Z $ App (App add (Var X)) (App (Var T) (Var Z)))

n5 : Term
n5 = App (App add two) three

n6 : Term
n6 = App (App add three) three
