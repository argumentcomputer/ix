/-
Lean port of CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/qsort.cml`
(CakeML/cakeml 530c7deec135ad421cce7ca768eed2f5801261b2). BSD-3-Clause; see
`benchmarks/fixtures/LICENSES/cakeml-LICENSE`.
Modified for Compilatr.ix: translated from CakeML to Lean, with well-founded
recursion on the list length for `qsort` (a termination proof over `part`),
and a printed length and checksum in place of the unused `val test`; see
`VARIANT.md`.
-/

namespace ListQsort

def part (p : α → Bool) : List α → List α × List α → List α × List α
  | [], (l1, l2) => (l1, l2)
  | h :: rst, (l1, l2) => if p h then part p rst (h :: l1, l2) else part p rst (l1, h :: l2)

def partition (p : α → Bool) (l : List α) : List α × List α := part p l ([], [])

def append : List α → List α → List α
  | [], l2 => l2
  | x :: xs, l2 => x :: append xs l2

theorem part_length (p : α → Bool) : ∀ (l l1 l2 : List α),
    (part p l (l1, l2)).1.length + (part p l (l1, l2)).2.length =
      l.length + l1.length + l2.length
  | [], _, _ => by simp [part]
  | h :: rst, l1, l2 => by
    by_cases hp : p h
    · simp only [part, hp, ite_true, part_length p rst, List.length_cons]; omega
    · simp only [part, hp, Bool.false_eq_true, ite_false, part_length p rst, List.length_cons]; omega

def qsort (r : α → α → Bool) : List α → List α
  | [] => []
  | h :: t =>
    match hp : partition (fun y => r y h) t with
    | (l1, l2) => append (qsort r l1) (append [h] (qsort r l2))
termination_by l => l.length
decreasing_by
  all_goals
    have := part_length (fun y => r y h) t [] []
    simp only [partition] at hp
    simp only [hp, List.length_nil] at this
    simp only [List.length_cons]
    omega

def mkList : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: mkList n

def useQsort (n : Nat) : List Nat :=
  qsort (fun x y => x ≤ y) (append (mkList n) (mkList n))

/-- Order-sensitive checksum of the result (not part of the CakeML program). -/
def checksum : Nat → List Nat → Nat
  | h, [] => h
  | h, x :: xs => checksum ((h * 31 + x) % 1000000007) xs

end ListQsort

/-- The pure benchmark entry: the length and checksum `main` prints. -/
def entry (n : Nat) : Nat × Nat :=
  let r := ListQsort.useQsort n
  (r.length, ListQsort.checksum 0 r)

def main : List String → IO UInt32
  | [n] => do
    let (len, sum) := entry n.toNat!
    IO.println s!"{len} {sum}"
    pure 0
  | _ => do IO.eprintln "usage: list-qsort N"; pure 1
