import IxAICore.Rng

/-!
# The formula domain

States are formulas of a small propositional logic. Every question asked about them has a
decision procedure, so every label in the domain is computed rather than annotated.
-/

namespace IxAICore

inductive Formula where
  | atom (n : Nat)
  | top
  | imp (a b : Formula)
  | and (a b : Formula)
  deriving DecidableEq, Repr, Inhabited

namespace Formula

def eval (v : Nat → Bool) : Formula → Bool
  | atom n => v n
  | top => true
  | imp a b => !a.eval v || b.eval v
  | and a b => a.eval v && b.eval v

/-- The number of the 8 assignments to `P0 … P2` that satisfy the formula. -/
def models (f : Formula) : Nat :=
  ((List.range 8).filter fun bits => f.eval fun n => (bits >>> n) % 2 == 1).length

def valid (f : Formula) : Bool := f.models == 8

def size : Formula → Nat
  | imp a b | and a b => a.size + b.size + 1
  | _ => 1

def depth : Formula → Nat
  | imp a b | and a b => max a.depth b.depth + 1
  | _ => 0

def atomCount (k : Nat) : Formula → Nat
  | atom n => if n == k then 1 else 0
  | imp a b | and a b => a.atomCount k + b.atomCount k
  | top => 0

def impCount : Formula → Nat
  | imp a b => a.impCount + b.impCount + 1
  | and a b => a.impCount + b.impCount
  | _ => 0

/-- The conclusion at the end of the implication spine. -/
def head : Formula → Formula
  | imp _ b => b.head
  | f => f

/-- Whether the conclusion also occurs as a hypothesis on the spine. -/
def headAssumed : Formula → Bool
  | imp a b => a == b.head || b.headAssumed
  | _ => false

def features (f : Formula) : List Int :=
  [f.atomCount 0, f.atomCount 1, f.atomCount 2, f.impCount, f.size, f.depth,
   if f.headAssumed then 1 else 0, if f.head == top then 1 else 0]

def leaf (k : Nat) : Formula := if k == 3 then top else atom k

/-- A random formula of depth at most `d`. Both subformulas are always drawn, so every branch
consumes the same randomness. -/
def gen : Nat → Rng → Formula × Rng
  | 0, r => let (k, r) := r.below 4; (leaf k, r)
  | d + 1, r =>
    let (k, r) := r.below 5
    let (a, r) := gen d r
    let (b, r) := gen d r
    (if k < 2 then a else if k == 4 then and a b else imp a b, r)

end Formula

def genFormulas (depth : Nat) : Nat → Rng → List Formula × Rng
  | 0, r => ([], r)
  | n + 1, r =>
    let (f, r) := Formula.gen depth r
    let (fs, r) := genFormulas depth n r
    (f :: fs, r)

end IxAICore
