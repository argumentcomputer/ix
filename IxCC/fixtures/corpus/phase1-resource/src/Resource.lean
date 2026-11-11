/-!
The Phase 1 resource corpus (phase 1 plan, MT.3; research §9.4.2): programs
whose runs fail at the limits a run is given, deterministically, with the
statuses of 04 §6: 1 heap (the region), 2 stack (the stack), 4 trap; natively, the region
and the stack are the test executable's layout.

* **Heap.** Phase 1 cells are immortal and bump-allocated: a cell of `k`
  fields takes `8 (k + 1)` bytes, and objects start 640 bytes into the
  region. A run that allocates `n` cells of two fields fits a region of `R`
  bytes exactly when `24 n ≤ R − 640`, so the threshold is exact.
* **Stack.** A non-tail call pushes at least its return address, so a
  recursion of depth `d` needs more than `8 d` bytes of the stack budget
  (the machines' budget is the stack less 4 KiB): one bound must succeed and the
  other must fail. Tail calls do not grow the stack.
* **Trap.** A trap is unreachable from a well-typed call: these roots take
  an argument of an empty type (or a proof of `False`), which the entry
  wrapper receives as a word anyway.

The oracle driver at the end is not part of any closure.
-/

namespace Resource

/-! ## Heap -/

/-- `n` cons cells (two fields each), built by a tail call. -/
def build : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc => build n (n :: acc)

def len : List Nat → Nat → Nat
  | [], k => k
  | _ :: xs, k => len xs (k + 1)

/-- Allocates exactly `n` cells of 24 bytes and returns `n`. -/
def heapList (n : Nat) : Nat := len (build n []) 0

/-- A pair per iteration (MT.2 finding: a loop with two mutable variables
allocates its state as a cell each iteration). -/
def twoVars (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for _ in [0:n] do
    a := a + 1
    b := b + 2
  return a + b

/-- The same loop with one mutable variable allocates nothing. -/
def oneVar (n : Nat) : Nat := Id.run do
  let mut a := 0
  for _ in [0:n] do
    a := a + 3
  return a

/-! ## Stack -/

/-- Non-tail recursion of depth `n`. -/
def depth : Nat → Nat
  | 0 => 0
  | n + 1 => depth n + 1

/-- Tail recursion: constant stack. -/
def countdown : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countdown n (acc + 2)

def tail (n : Nat) : Nat := countdown n 0

mutual
/-- Mutual tail calls: constant stack. -/
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n

def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

/-! ## Trap -/

def trapEmpty (e : Empty) : Nat := nomatch e

def trapFalse (h : False) : Nat := h.elim

def trapAbsurd (n : Nat) (h : n ≠ n) : Nat := absurd rfl h

end Resource

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Resource.heapList", [n] => toString (Resource.heapList n)
        | "Resource.twoVars", [n] => toString (Resource.twoVars n)
        | "Resource.oneVar", [n] => toString (Resource.oneVar n)
        | "Resource.depth", [n] => toString (Resource.depth n)
        | "Resource.tail", [n] => toString (Resource.tail n)
        | "Resource.isEven", [n] => toString (Resource.isEven n)
        | "Resource.isOdd", [n] => toString (Resource.isOdd n)
        | _, _ => s!"unknown root {root} {args}"
