module Path

%default total
%access public export

-- paths in a graph as a sequence of zero or more edges `e i j` with source nodes and target nodes matching up domino-style
-- aka reflexive-transitive closure
data Path : (i -> i -> Type) -> i -> i -> Type where
  Nil  : Path e i i
  (::) : e i j -> Path e j k -> Path e i k

mapPath : {e1, e2 : t -> t -> Type} -> {f : t -> t}
       -> (g : {i, j : t} -> e1 i j -> e2 (f i) (f j))
       -> {i, j : t} -> Path e1 i j -> Path e2 (f i) (f j)
mapPath g []     = []
mapPath g (e::p) = g e :: mapPath g p

joinPath : {e : t -> t -> Type}
        -> Path e i j -> Path e j k -> Path e i k
joinPath []      y = y
joinPath (x::xs) y = x :: joinPath xs y
