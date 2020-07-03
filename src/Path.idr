module Path

%default total
%access public export

-- paths in a graph as a sequence of zero or more edges `e i j` with source nodes and target nodes matching up domino-style
-- aka reflexive-transitive closure
data Path : (i -> i -> Type) -> i -> i -> Type where
  Nil  : Path e i i
  (::) : e i j -> Path e j k -> Path e i k

joinPath : Path e i j -> Path e j k -> Path e i k
joinPath []      jk = jk
joinPath (e::ij) jk = e :: joinPath ij jk

snocPath : Path e i j -> e j k -> Path e i k
snocPath []      ejk = [ejk]
snocPath (e::ij) ejk = e :: snocPath ij ejk

lengthPath : Path e i j -> Nat
lengthPath []     = Z
lengthPath (e::p) = S $ lengthPath p

mapPath : {et : t -> t -> Type} -> {eu : u -> u -> Type} -> {f : t -> u}
       -> ({i, j : t} ->      et i j ->      eu (f i) (f j))
       ->  {i, j : t} -> Path et i j -> Path eu (f i) (f j)
mapPath g []     = []
mapPath g (e::p) = g e :: mapPath g p

foldPath : {et : t -> t -> Type} -> {eu : u -> u -> Type} -> {f : t -> u}
        -> ({i, j, k : t} ->      et i j -> eu (f j) (f k) -> eu (f i) (f k))
        ->  {i, j, k : t} -> Path et i j -> eu (f j) (f k) -> eu (f i) (f k)
foldPath     g []     ujk = ujk
foldPath {u} g (e::p) ujk = g e (foldPath {u} g p ujk)

foldlPath : {et : t -> t -> Type} -> {eu : u -> u -> Type} -> {f : t -> u}
        -> ({i, j, k : t} -> eu (f i) (f j) ->      et j k -> eu (f i) (f k))
        ->  {i, j, k : t} -> eu (f i) (f j) -> Path et j k -> eu (f i) (f k)
foldlPath     g uij []     = uij
foldlPath {u} g uij (e::p) = foldlPath {u} g (g uij e) p
