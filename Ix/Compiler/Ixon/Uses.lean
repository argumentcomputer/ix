/-!
# The usage algebra

First real module of Compilatr.ix: the `Uses` algebra and `Owned`
result modes that Ixon v2 binders (`all`, `lam`) carry as data. Design
rationale lives in `docs/compiler/compiler-design.md` under ownership, borrowing,
and reuse; the short version:

- `Uses` is one enum in the data model, but the checker reads it along
  two axes: `erased` is the multiplicative *grade* axis (QTT 0,
  erasure — the one place `mul` survives), while `linear`/`affine` vs
  `many` is the *ownership-mode* axis (unique vs RC'd-shared),
  composed additively under CBV with flow-sensitive move/freeze
  transitions and no dereliction.
- The vanilla Lean 4 fragment is `many` binders with `shared` results.
-/

namespace Ix.Compiler.Ixon

/-- Binder usage. Cf. yatima-lang-alpha's `core/src/uses.rs`. -/
inductive Uses where
  /-- "0": runtime-irrelevant; free to appear in types. -/
  | erased
  /-- "1": consumed exactly once; unique from birth; reuse licensed. -/
  | linear
  /-- "≤1": consumed at most once; unique; droppable (Rust's move). -/
  | affine
  /-- "ω": unrestricted; the RC'd shared world. Lean 4's only mode. -/
  | many
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq Uses where
  rfl := by intro uses; cases uses <;> rfl

instance : LawfulBEq Uses where
  eq_of_beq := by
    intro left right h
    cases left <;> cases right <;>
      first | rfl | exact Bool.noConfusion h

namespace Uses

/-- Parallel combination: the same variable used in two sibling
positions. Any two runtime uses collapse to `many`. -/
def add : Uses → Uses → Uses
  | .erased, u | u, .erased => u
  | _, _ => .many

instance : Add Uses := ⟨add⟩

/-- Multiplicative scaling. Under compiled CBV this survives only at
the erasure boundary; nonzero modes compose additively with
flow-sensitive ownership transitions instead. -/
def mul : Uses → Uses → Uses
  | .erased, _ | _, .erased => .erased
  | .linear, u | u, .linear => u
  | .affine, .affine => .affine
  | _, _ => .many

/- `mul` is retained as the specification algebra needed by the future theory
bridge. Executable CBV checking invokes it only with the `.erased` grade via
`UsageCheck.UseVec.zeroScale`; using nonzero multiplication to compose closure
captures would be unsound before one-shot closure multiplicities exist. -/

instance : Mul Uses := ⟨mul⟩

/-- Binder check: does declared usage `d` accept computed usage `c`?
`linear` does not cover `erased`: unused linear binders are errors
(no silent leaks). There is deliberately no rule letting `many`
satisfy a `linear`/`affine` demand (no dereliction); re-entry to the
unique world is only via the `clone` family. -/
def covers : Uses → Uses → Bool
  | .many, _ => true
  | .affine, .erased | .affine, .affine | .affine, .linear => true
  | .linear, .linear => true
  | .erased, .erased => true
  | _, _ => false

/-! ## The usage semiring laws -/

protected theorem add_comm (a b : Uses) : a.add b = b.add a := by
  cases a <;> cases b <;> rfl

protected theorem add_assoc (a b c : Uses) :
    (a.add b).add c = a.add (b.add c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] protected theorem add_erased (a : Uses) : a.add .erased = a := by
  cases a <;> rfl

@[simp] protected theorem erased_add (a : Uses) : Uses.add .erased a = a := by
  cases a <;> rfl

protected theorem mul_comm (a b : Uses) : a.mul b = b.mul a := by
  cases a <;> cases b <;> rfl

protected theorem mul_assoc (a b c : Uses) :
    (a.mul b).mul c = a.mul (b.mul c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] protected theorem mul_linear (a : Uses) : a.mul .linear = a := by
  cases a <;> rfl

@[simp] protected theorem linear_mul (a : Uses) : Uses.mul .linear a = a := by
  cases a <;> rfl

@[simp] protected theorem mul_erased (a : Uses) : a.mul .erased = .erased := by
  cases a <;> rfl

@[simp] protected theorem erased_mul (a : Uses) : Uses.mul .erased a = .erased := by
  cases a <;> rfl

/-- Scaling distributes over parallel combination. -/
protected theorem mul_add (a b c : Uses) :
    a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `covers` is reflexive: every declared usage accepts itself. -/
protected theorem covers_refl (a : Uses) : a.covers a = true := by
  cases a <;> rfl

/-! ## Bit representation (Ixon mode bytes) -/

def toBits : Uses → UInt8
  | .erased => 0
  | .linear => 1
  | .affine => 2
  | .many => 3

def ofBits? : UInt8 → Option Uses
  | 0 => some .erased
  | 1 => some .linear
  | 2 => some .affine
  | 3 => some .many
  | _ => none

protected theorem ofBits?_toBits (u : Uses) : ofBits? u.toBits = some u := by
  cases u <;> rfl

end Uses

/-- Result ownership of an arrow: may the caller treat the returned
value as unique, or is it (possibly) shared — a top-level constant, a
projection of shared data? `shared` is the default; `unique` is
opt-in. -/
inductive Owned where
  | unique
  | shared
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

instance : ReflBEq Owned where
  rfl := by intro owned; cases owned <;> rfl

instance : LawfulBEq Owned where
  eq_of_beq := by
    intro left right h
    cases left <;> cases right <;>
      first | rfl | exact Bool.noConfusion h

namespace Owned

def toBits : Owned → UInt8
  | .unique => 0
  | .shared => 1

def ofBits? : UInt8 → Option Owned
  | 0 => some .unique
  | 1 => some .shared
  | _ => none

protected theorem ofBits?_toBits (o : Owned) : ofBits? o.toBits = some o := by
  cases o <;> rfl

end Owned

/-! Elaboration-time sanity checks. -/

#guard Uses.add .linear .linear == .many
#guard Uses.add .affine .affine == .many
#guard Uses.mul .erased .many == .erased
#guard Uses.mul .affine .affine == .affine
#guard Uses.covers .affine .erased
#guard Uses.covers .many .linear
#guard !(Uses.covers .linear .erased)
#guard !(Uses.covers .linear .many)
#guard !(Uses.covers .erased .linear)

end Ix.Compiler.Ixon
