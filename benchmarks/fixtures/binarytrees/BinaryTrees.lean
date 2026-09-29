/-
Compilatr.ix fixture `binarytrees` (total variant) of Lean
`tests/compile_bench/binarytrees.lean` (leanprover/lean4 v4.34.0,
293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; Apache-2.0, see
`benchmarks/fixtures/LICENSES/lean4-LICENSE`). Modified for Compilatr.ix:
`make'` and `sumT` recurse structurally on a `Nat` depth and count instead
of `partial` recursion on `UInt32`; `depth` is well-founded on
`m + 1 - d` instead of `partial`; the `Task.spawn` is replaced by the
direct (single-threaded) value; and the IO `main` is split into a pure
`entry` and a `main` that prints its result in the upstream format. See
`VARIANT.md`.
-/

inductive Tree
  | nil
  | node (l r : Tree)
instance : Inhabited Tree := ⟨.nil⟩

-- This function has an extra argument to suppress the
-- common sub-expression elimination optimization
def make' (n : UInt32) : Nat → Tree
  | 0 => .node .nil .nil
  | d + 1 => .node (make' n d) (make' (n + 1) d)

-- build a tree
def make (d : UInt32) := make' d d.toNat

def check : Tree → UInt32
  | .nil => 0
  | .node l r => 1 + check l + check r

def minN := 4

def out (s : String) (n : Nat) (t : UInt32) : IO Unit :=
  IO.println s!"{s} of depth {n}\t check: {t}"

-- allocate and check lots of trees
def sumT (d : UInt32) : Nat → UInt32 → UInt32
  | 0, t => t
  | i + 1, t =>
    let a := check (make d)
    sumT d i (t + a)

-- generate many trees
def depth (d m : Nat) : List (Nat × Nat × UInt32) :=
  if d ≤ m then
    let n := 2 ^ (m - d + minN)
    (n, d, sumT (.ofNat d) n 0) :: depth (d+2) m
  else []
termination_by m + 1 - d

/-- The pure benchmark entry: the stretch-tree check, the per-depth
`(iterations, depth, check)` rows, and the long-lived-tree check. -/
def entry (n : Nat) : UInt32 × List (Nat × Nat × UInt32) × UInt32 :=
  let maxN := Nat.max (minN + 2) n
  let stretchN := maxN + 1

  -- stretch memory tree
  let c := check (make $ UInt32.ofNat stretchN)

  -- allocate a long lived tree
  let long := make $ UInt32.ofNat maxN

  -- allocate, walk, and deallocate many bottom-up binary trees
  let vs := (depth minN maxN)

  -- confirm the long-lived binary tree still exists
  (c, vs, check long)

def main : List String → IO UInt32
  | [s] => do
    let n := s.toNat!
    let maxN := Nat.max (minN + 2) n
    let stretchN := maxN + 1
    let (c, vs, long) := entry n
    out "stretch tree" stretchN c
    vs.forM (fun (m, d, i) => out s!"{m}\t trees" d i)
    out "long lived tree" maxN long
    return 0
  | _ => return 1
