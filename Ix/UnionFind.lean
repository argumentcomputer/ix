structure UnionFind where
  parent : IO.Ref (Array Nat)
  rank : IO.Ref (Array Nat)

namespace UnionFind

def init (n: Nat) : IO UnionFind := do
  let parent <- IO.mkRef (Array.range n)
  let rank <- IO.mkRef (Array.replicate n 0)
  return ⟨parent, rank⟩

partial def find (uf: UnionFind) (x: Nat) : IO Nat := do
  let parent <- uf.parent.get
  let p := parent[x]!
  if p == x then return x
  else do
    let root <- find uf p
    uf.parent.modify fun arr => arr.set! x root
    return root

def union (uf : UnionFind) (x y: Nat) : IO Unit := do
  let rx <- find uf x
  let ry <- find uf y
  if rx == ry then return ()
  let rank <- uf.rank.get
  let rankX := rank[rx]!
  let rankY := rank[ry]!
  if rankX < rankY then
    uf.parent.modify fun arr => arr.set! rx ry
  else if rankX > rankY then
    uf.parent.modify fun arr => arr.set! ry rx
  else
    uf.parent.modify fun arr => arr.set! ry rx
    uf.rank.modify fun arr => arr.set! rx (rankX + 1)

def unionMany (uf: UnionFind) (pairs: Array (Nat × Nat)) : IO Unit := do
  for (x, y) in pairs do
    union uf x y

end UnionFind

