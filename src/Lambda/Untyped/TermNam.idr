module Lambda.Untyped.TermNam

%default total
%access public export

Name : Type
Name = (String, Nat)

nameNum : Name -> Nat
nameNum (s,n) = cast $ 10 * sum (ord <$> unpack s) + cast n

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

fresh : List Name -> Name
fresh []      = X
fresh (v::vs) = map S $ foldr max v vs

data Term = Var Name
          | Lam Name Term
          | App Term Term

-- λx.x, aka I combinator
identity : Term
identity = Lam X $ Var X

-- λx.λy.λz.(x z)(y z), generalized application, aka S combinator
s : Term
s = Lam X $ Lam Y $ Lam Z $ App (App (Var X) (Var Z)) (App (Var Y) (Var Z))

-- λx.λy.x, constant function, aka K combinator
k : Term
k = Lam X $ Lam Y $ Var X

-- λx.λy.λz.x (y z), composition, aka B combinator
b : Term
b = Lam X $ Lam Y $ Lam Z $ App (Var X) (App (Var Y) (Var Z))

-- λx.λy.λz.(x z) y, flip, aka C combinator
c : Term
c = Lam X $ Lam Y $ Lam Z $ App (App (Var X) (Var Z)) (Var Y)

-- λx.λy.(x y) y, duplication, aka W combinator
w : Term
w = Lam X $ Lam Y $ App (App (Var X) (Var Y)) (Var Y)

-- BCI ~ linear logic (no dropping/copying)
-- BCWK ~ SKI

-- (λx.x) (λx.x)
identityApp : Term
identityApp = App (Lam X (Var X)) (Lam X (Var X))

-- (λx.λy.x) y -> λy'.y
renamed : Term
renamed = App (Lam X $ Lam Y $ Var X) (Var Y)

-- (λx.x x) (λx.x)          
Term0 : Term 
Term0 = App (Lam X $ App (Var X) (Var X)) (Lam X $ Var X)

-- ((λx.x) (λx.x)) (λx.x)
Term1 : Term 
Term1 = App (App (Lam X $ Var X) (Lam X $ Var X)) (Lam X $ Var X)

-- (λx.x) ((λx.x) (λx.x))
Term2 : Term 
Term2 = App (Lam X $ Var X) (App (Lam X $ Var X) (Lam X $ Var X))

-- Ω, canonical endless loop
omega : Term
omega = App (Lam X (App (Var X) (Var X))) (Lam X (App (Var X) (Var X)))

-- λx.λy.x
false : Term
false = Lam X $ Lam Y $ Var X

-- λx.λy.y
true : Term
true = Lam X $ Lam Y $ Var Y

-- λx.λy.λz.(x z) y
ifT : Term
ifT = Lam X $ Lam Y $ Lam Z $ App (App (Var X) (Var Z)) (Var Y)

-- Scott encodings

-- λx.λy.x
zero : Term
zero = Lam X $ Lam Y $ Var X

-- λx.λy.λz.z x
succ : Term
succ = Lam X $ Lam Y $ Lam Z $ App (Var Z) (Var X)

pred : Term
pred = Lam X $ App (App (Var X) zero) (Lam X $ Var X)

one : Term
one = App succ zero

two : Term
two = App succ one

three : Term
three = App succ two

isZero : Term
isZero = Lam X $ App (App (Var X) true) (Lam Y false)

pair : Term
pair = Lam X $ Lam Y $ Lam Z $ App (App (Var Z) (Var X)) (Var Y)

fstc : Term
fstc = Lam X $ App (Var X) (Lam Y $ Lam Z $ Var Y)

sndc : Term
sndc = Lam X $ App (Var X) (Lam Y $ Lam Z $ Var Z)

-- λf.(λx.f (x x))(λx.f (x x)), aka Y combinator
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
                                             (App (App (Var Y) true) (App k false))) 
                                        (Lam Z $ App (App (Var Y) false) (Lam Q $ App (App (Var T) (Var Z)) (Var Q)))

sumto : Term
sumto = App fix $ Lam T $ Lam X $ App (App (Var X) zero) (Lam Z $ App (App add (Var X)) (App (Var T) (Var Z)))

n5 : Term
n5 = App (App add two) three

n6 : Term
n6 = App (App add three) three

-- Church encodings

zero' : Term 
zero' = Lam X $ Lam Y $ Var Y

one' : Term 
one' = Lam X $ Lam Y $ App (Var X) (Var Y)

succ' : Term
succ' = Lam X $ Lam Y $ Lam Z $ App (Var Y) (App (App (Var X) (Var Y)) (Var Z))

true' : Term
true' = Lam X $ Lam Y $ Var X

false' : Term
false' = Lam X $ Lam Y $ Var Y

and' : Term
and' = Lam X $ Lam Y $ App (App (Var X) (Var Y)) false'
