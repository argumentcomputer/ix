/-! # Lean sources of the reader's fidelity test

Ordinary Lean declarations, checked by Lean's kernel, that
`Tests.Ix.Kernel.ReaderRoundtrip` loads from this module's `.olean`,
compiles with Ix's compiler, reads through the Ixon reader
(`Ix.Kernel.IxonReader`) and compares constant by constant against a
direct translation of the Lean constants (`Tests.Ix.Kernel.ReaderFidelity`).
The module imports only `Init`, so the test's closure is these declarations
and the part of `Init` they reach. It covers every record shape the reader
regroups: nested, mutual, indexed, reflexive and structure-like inductives,
quotients, `Nat` and `String` literals, mutual and well-founded definitions,
`let`, projections, universe-polymorphic levels the compiler canonicalizes,
theorems, opaques, axioms, and the `partial`/`unsafe` definitions the
reader declines. -/

namespace Tests.Ix.Kernel.ReaderFidelityDefs

universe u v w

/-! ## Inductives -/

/-- An enumeration. -/
inductive Color where
  | red | green | blue

/-- A structure: projections, a projection function's value, η. -/
structure Point (α : Type u) where
  x : α
  y : α

/-- A structure extending another, with a dependent field. -/
structure Point3 (α : Type u) extends Point α where
  z : α
  zx : z = x → True

/-- An indexed family. -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

/-- A reflexive inductive (a field is a function into the type). -/
inductive WTree where
  | leaf : WTree
  | sup : (Nat → WTree) → WTree

/-- A nested inductive (through `List`). -/
inductive Rose (α : Type u) where
  | node : α → List (Rose α) → Rose α

/-- Nested through `Array` and `Option`. -/
inductive ATree where
  | node : Array ATree → Option ATree → ATree

-- Mutual inductives.
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ {n : Nat} : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ {n : Nat} : Even n → Odd (n + 1)
end

-- A mutual block of data types.
mutual
  inductive Tm where
    | var : Nat → Tm
    | app : Tm → Args → Tm
  inductive Args where
    | nil : Args
    | cons : Tm → Args → Args
end

/-- A nested structure: its block goes through the in-process modeller, and
its projection functions are rewritten to recursor form. -/
structure Node where
  val : Nat
  kids : List Node

/-- A proposition with one constructor and no fields (a K-like recursor). -/
inductive Trivial : Prop where
  | intro

/-- A structure-like proposition (no large elimination beyond `Prop`). -/
structure Both (p q : Prop) : Prop where
  left : p
  right : q

/-- Universe levels the compiler stores as canonical forms. -/
structure Pair (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

/-! ## Definitions -/

def twice {α : Sort u} (f : α → α) (a : α) : α := f (f a)

abbrev NatPair := Pair Nat Nat

/-- A `let` and a projection in a value. -/
def sumPoint (p : Point Nat) : Nat :=
  let a := p.x
  let b := p.2
  a + b

/-- Structural recursion over an indexed family. -/
def Vec.length {α : Type u} : {n : Nat} → Vec α n → Nat
  | _, .nil => 0
  | _, .cons _ v => v.length + 1

/-- Structural recursion over a nested inductive. -/
def Rose.size {α : Type u} : Rose α → Nat
  | .node _ cs => 1 + sizes cs
where
  sizes : List (Rose α) → Nat
    | [] => 0
    | c :: cs => c.size + sizes cs

-- Mutual structural recursion.
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

-- Mutual recursion over a mutual block.
mutual
  def Tm.size : Tm → Nat
    | .var _ => 1
    | .app f as => f.size + as.size + 1
  def Args.size : Args → Nat
    | .nil => 0
    | .cons t as => t.size + as.size + 1
end

/-- Well-founded recursion. -/
def log2 (n : Nat) : Nat :=
  if h : n < 2 then 0 else log2 (n / 2) + 1
termination_by n
decreasing_by omega

/-- Recursion through a reflexive inductive. -/
def WTree.depthAt : WTree → Nat → Nat
  | .leaf, _ => 0
  | .sup f, n => (f n).depthAt n + 1

/-- Quotients. -/
def parity (n : Nat) : Bool := n % 2 == 0

def natRel (a b : Nat) : Prop := parity a = parity b

def ParityQ : Type := Quot natRel

def ParityQ.mk (n : Nat) : ParityQ := Quot.mk natRel n

def ParityQ.toBool (q : ParityQ) : Bool := Quot.lift parity (fun _ _ h => h) q

theorem ParityQ.toBool_mk (n : Nat) : (ParityQ.mk n).toBool = parity n := rfl

/-! ## Literals -/

def smallNat : Nat := 42
def bigNat : Nat := 340282366920938463463374607431768211457
def greeting : String := "héllo, wörld ∀"
def letter : Char := 'λ'
theorem bigNat_pos : 0 < bigNat := by decide

/-! ## Theorems, opaques, axioms -/

theorem twice_id {α : Sort u} (a : α) : twice id a = a := rfl

theorem isEven_two : isEven 2 = true := rfl

theorem even_two : Even 2 := .succ (.succ .zero)

opaque secret : Nat

axiom fidelityAxiom (n : Nat) : n = n

/-- Levels the compiler canonicalizes: `max v u` and `imax` spellings. -/
def levelMax {α : Sort u} {β : Sort v} (a : α) (b : β) : Pair α β := ⟨a, b⟩

def levelImax (α : Sort u) (P : α → Sort v) : Sort (imax u v) := (a : α) → P a

/-! ## Declined by the reader -/

partial def spin (n : Nat) : Nat := spin (n + 1)

unsafe def unsafeId (n : Nat) : Nat := n

end Tests.Ix.Kernel.ReaderFidelityDefs
