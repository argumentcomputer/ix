/-! Matches with a catch-all. Lean elaborates `| [], k => e | _, _ => e'` through a definition it
generates, a *sparse casesOn* (`T…._sparseCasesOn_N`, `Lean.Meta.mkSparseCasesOn`), which takes
one argument per named constructor (its arm) and a catch-all continuation; Lean's code generator
compiles it as a `cases`, so the arm of a constructor that is not chosen is not evaluated. IxCC
gives such a definition a `lazy` row (`Table.checkSparseCases`), so that neither SrcEval nor the
compiled code evaluates that arm either.

Each root takes a selector `b` (`0`: the named constructor's arm is taken; otherwise it is not)
and a size `n`, the cost of that arm: a taken arm gives `n`, the catch-all `1`. -/
namespace Sparse

/-- `a + k`, in `k` steps and constant stack (tail recursive). -/
def count : Nat → Nat → Nat
  | 0, a => a
  | k + 1, a => count k (a + 1)

/-- `k`, in `k` steps and `k` frames of stack (not tail recursive). -/
def deep : Nat → Nat
  | 0 => 0
  | k + 1 => deep k + 1

/-- A list of `k` cells. -/
def build : Nat → List Nat → List Nat
  | 0, acc => acc
  | k + 1, acc => build k (k :: acc)

def len : List Nat → Nat → Nat
  | [], a => a
  | _ :: xs, a => len xs (a + 1)

/-- `[]` when `b = 0`, else a one-element list: the constructor comes from the input. -/
def sel : Nat → List Nat
  | 0 => []
  | _ + 1 => [1]

def selO : Nat → Option Nat
  | 0 => none
  | _ + 1 => some 1

inductive Color where
  | red
  | green
  | blue

def selE : Nat → Color
  | 0 => .red
  | 1 => .green
  | _ => .blue

/-- A record matched on its first field, as `Queue.checkf` matches `.queue [] xs`. -/
structure Pair where
  front : List Nat
  size : Nat

/-- An arm for `[]` and a catch-all: a sparse casesOn on `List`. -/
def pickS : List Nat → Nat → Nat
  | [], k => count k 0
  | _, _ => 1

/-- The same function with both constructors named: `List.casesOn`, no sparse casesOn. -/
def pickF : List Nat → Nat → Nat
  | [], k => count k 0
  | _ :: _, _ => 1

/-- `none`'s arm and a catch-all: a sparse casesOn on `Option`. -/
def pickO : Option Nat → Nat → Nat
  | none, k => count k 0
  | _, _ => 1

/-- An enumeration's constructor and a catch-all. -/
def pickE : Color → Nat → Nat
  | .red, k => count k 0
  | _, _ => 1

/-- A nested pattern: `Pair.casesOn`, then a sparse casesOn on the first field. -/
def pickN : Pair → Nat
  | ⟨[], k⟩ => count k 0
  | _ => 1

/-- The arm needs `k` frames of stack. -/
def pickD : List Nat → Nat → Nat
  | [], k => deep k
  | _, _ => 1

/-- The arm allocates `k` cells. -/
def pickH : List Nat → Nat → Nat
  | [], k => len (build k []) 0
  | _, _ => 1

def loopS : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | b, i + 1, acc => loopS b i (acc + pickS (sel b) i)

def loopF : Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | b, i + 1, acc => loopF b i (acc + pickF (sel b) i)

/-- An ordinary function with a sparse casesOn's name: Lean compiles it as any function, its
arguments first, and so does IxCC (its shape is not a sparse casesOn's, so it has no `lazy`
row). -/
def mimic._sparseCasesOn_1 (xs : List Nat) (k : Nat) : Nat :=
  match xs with
  | [] => k
  | _ :: _ => 1

def minS (b n : Nat) : Nat := pickS (sel b) n
def minF (b n : Nat) : Nat := pickF (sel b) n
def minO (b n : Nat) : Nat := pickO (selO b) n
def minE (b n : Nat) : Nat := pickE (selE b) n
def minN (b n : Nat) : Nat := pickN ⟨sel b, n⟩
def minD (b n : Nat) : Nat := pickD (sel b) n
def minH (b n : Nat) : Nat := pickH (sel b) n
def sumS (b n : Nat) : Nat := loopS b n 0
def sumF (b n : Nat) : Nat := loopF b n 0
def minM (b n : Nat) : Nat := mimic._sparseCasesOn_1 (sel b) (count n 0)

end Sparse

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Sparse.minS", [b, n] => toString (Sparse.minS b n)
        | "Sparse.minF", [b, n] => toString (Sparse.minF b n)
        | "Sparse.minO", [b, n] => toString (Sparse.minO b n)
        | "Sparse.minE", [b, n] => toString (Sparse.minE b n)
        | "Sparse.minN", [b, n] => toString (Sparse.minN b n)
        | "Sparse.minD", [b, n] => toString (Sparse.minD b n)
        | "Sparse.minH", [b, n] => toString (Sparse.minH b n)
        | "Sparse.sumS", [b, n] => toString (Sparse.sumS b n)
        | "Sparse.sumF", [b, n] => toString (Sparse.sumF b n)
        | "Sparse.minM", [b, n] => toString (Sparse.minM b n)
        | _, _ => s!"unknown root {root} {args}"
