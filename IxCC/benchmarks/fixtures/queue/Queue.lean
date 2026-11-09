/-
Lean port of CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/queue.cml`
(CakeML/cakeml 530c7deec135ad421cce7ca768eed2f5801261b2). BSD-3-Clause; see
`benchmarks/fixtures/LICENSES/cakeml-LICENSE`.
Modified for IxCC: translated from CakeML to Lean, with a default for
the partial `head`, and a printed result in place of the unused `val test`;
see `VARIANT.md`.
-/

set_option backward.match.sparseCases false

namespace Queue

inductive Q (α : Type) where
  | queue : List α → List α → Q α

def empty : Q α := .queue [] []

def isEmpty : Q α → Bool
  | .queue [] _ => true
  | _ => false

def reverseAux : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseAux xs (x :: acc)

def reverse (xs : List α) : List α := reverseAux xs []

def checkf : Q α → Q α
  | .queue [] xs => .queue (reverse xs) []
  | q => q

def snoc : Q α → α → Q α
  | .queue f r, x => checkf (.queue f (x :: r))

/-- CakeML's `head` has no case for an empty front list (it raises `Bind`);
the port returns `default` there, which `runQueue` never reaches for `n > 0`. -/
def head [Inhabited α] : Q α → α
  | .queue (x :: _) _ => x
  | _ => default

/-- CakeML's `tail` is partial in the same way; the empty case is unreachable
from `useQueue`. -/
def tail : Q α → Q α
  | .queue (_ :: f) r => checkf (.queue f r)
  | q => q

def useQueue : Nat → Q Nat → Q Nat
  | 0, q => q
  | n + 1, q => useQueue n (tail (snoc (snoc q n) n))

def runQueue (n : Nat) : Nat := head (useQueue n empty)

end Queue

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := Queue.runQueue n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: queue N"; pure 1
