import IxAI.Stmt
import IxAICommon.Merkle
import IxAI.Num
import IxAI.Model

/-!
# A dataset with decided labels

Each example is a formula of the toy logic with a label computed by a decision procedure
(truth-table validity), so labels are facts rather than annotations. The dataset is committed by a
Merkle root, and the dataset claim says every committed item's features and label are what the
specification computes from its formula.

Randomness is a specified xorshift64* generator, so the dataset and the training schedule are
functions of a seed and any implementation can reproduce them exactly.
-/

namespace IxAI

/-- xorshift64*. Specified on `UInt64`, so every implementation agrees bit for bit. -/
structure Rng where
  state : UInt64
  deriving Repr

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.state
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 0x2545F4914F6CDD1D, ⟨x⟩)

/-- A value in `[0, n)`. -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (v.toNat % n, r)

def Rng.seeded (seed : UInt64) : Rng := ⟨if seed == 0 then 0x9E3779B97F4A7C15 else seed⟩

def numAtoms : Nat := 3

def Stmt.eval (v : Nat → Bool) : Stmt → Bool
  | .atom n => v n
  | .top => true
  | .imp a b => !a.eval v || b.eval v
  | .and a b => a.eval v && b.eval v

/-- Classical validity over the atoms `P0 … P2`, by truth table. -/
def Stmt.valid (s : Stmt) : Bool :=
  (List.range (2 ^ numAtoms)).all fun bits => s.eval fun n => (bits >>> n) % 2 == 1

def Stmt.size : Stmt → Nat
  | .imp a b | .and a b => a.size + b.size + 1
  | _ => 1

def Stmt.depth : Stmt → Nat
  | .imp a b | .and a b => max a.depth b.depth + 1
  | _ => 0

def Stmt.atomCount (k : Nat) : Stmt → Nat
  | .atom n => if n == k then 1 else 0
  | .imp a b | .and a b => a.atomCount k + b.atomCount k
  | .top => 0

def Stmt.impCount : Stmt → Nat
  | .imp a b => a.impCount + b.impCount + 1
  | .and a b => a.impCount + b.impCount
  | _ => 0

/-- The conclusion at the end of the implication spine. -/
def Stmt.head : Stmt → Stmt
  | .imp _ b => b.head
  | s => s

/-- Whether the head also occurs as a hypothesis on the spine: a strong hint of validity. -/
def Stmt.headAssumed : Stmt → Bool
  | .imp a b => a == b.head || b.headAssumed
  | _ => false

/-- Features: three atom counts, implication count, size, depth, head-is-assumed, head-is-⊤. -/
def Stmt.features (s : Stmt) : List Int :=
  (List.range numAtoms).map (fun k => (s.atomCount k : Int)) ++
    [(s.impCount : Int), (s.size : Int), (s.depth : Int), if s.headAssumed then 1 else 0,
      if s.head == .top then 1 else 0]

def numFeatures : Nat := numAtoms + 5

def genLeaf (r : Rng) : Stmt × Rng :=
  let (k, r) := r.below (numAtoms + 1)
  (if k == numAtoms then .top else .atom k, r)

/-- A random formula of depth at most `depth`. Both subformulas are always drawn, so the
generator consumes the same randomness on every branch. -/
def genStmt (depth : Nat) (r : Rng) : Stmt × Rng :=
  match depth with
  | 0 => genLeaf r
  | d + 1 =>
    let (k, r) := r.below 5
    let (a, r) := genStmt d r
    let (b, r) := genStmt d r
    (if k < 2 then a else if k == 4 then .and a b else .imp a b, r)

structure Item where
  stmt : Stmt
  features : List Int
  label : Bool
  deriving Repr, DecidableEq

def Item.ofStmt (s : Stmt) : Item := ⟨s, s.features, s.valid⟩

/-- The item is what the specification computes from its formula. -/
def Item.wellFormed (i : Item) : Bool := i.features == i.stmt.features && i.label == i.stmt.valid

instance : Enc Item := ⟨fun b i => Enc.enc (Enc.enc (Enc.enc b i.stmt) i.features) i.label⟩

def Item.leaf (i : Item) : Digest := digestOf "item" i

def Item.example {α : Type} [Arith α] (i : Item) : Example α :=
  ⟨i.features.map (Arith.ofInt ·), Arith.ofInt (if i.label then 1 else -1)⟩

structure Dataset where
  items : Array Item
  deriving Repr

def Dataset.generate (seed : UInt64) (n depth : Nat) : Dataset := Id.run do
  let mut r := Rng.seeded seed
  let mut items := #[]
  for _ in [0:n] do
    let (s, r') := genStmt depth r
    r := r'
    items := items.push (Item.ofStmt s)
  return ⟨items⟩

/-- The dataset root: the length-binding Merkle root (`merkleRootV2`) of the item leaves. -/
def Dataset.root (d : Dataset) : Digest := merkleRootV2 (d.items.toList.map Item.leaf)

/-- The dataset claim: every item is well formed. With a real proof system this is one Eval
certificate that every consumer of the dataset verifies instead of relabelling. -/
def Dataset.check (d : Dataset) : Bool := d.items.all Item.wellFormed

def Dataset.positives (d : Dataset) : Nat := d.items.toList.countP (·.label)

end IxAI
