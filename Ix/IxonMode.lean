module
public import Ix.Common

/-!
# Ixon binder modes

Ixon v2 carries substructural intent directly on binder nodes.  Ordinary
Lean compilation inhabits the conservative fragment: every lambda/forall
binder is `.many`, and every forall result is `.shared`.
-/

public section

namespace Ixon

/-- Binder usage stored on Ixon lambda and forall nodes. -/
inductive Uses where
  | erased
  | linear
  | affine
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

/-- Parallel combination of two uses of the same binder. -/
def add : Uses → Uses → Uses
  | .erased, uses | uses, .erased => uses
  | _, _ => .many

instance : Add Uses := ⟨add⟩

/-- Usage scaling. Runtime-irrelevant use is absorbing. -/
def mul : Uses → Uses → Uses
  | .erased, _ | _, .erased => .erased
  | .linear, uses | uses, .linear => uses
  | .affine, .affine => .affine
  | _, _ => .many

instance : Mul Uses := ⟨mul⟩

/-- Whether a declared mode admits a computed use. -/
def covers : Uses → Uses → Bool
  | .many, _ => true
  | .affine, .erased | .affine, .affine | .affine, .linear => true
  | .linear, .linear => true
  | .erased, .erased => true
  | _, _ => false

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

@[simp] theorem ofBits?_toBits (uses : Uses) :
    ofBits? uses.toBits = some uses := by
  cases uses <;> rfl

end Uses

/-- Ownership available to the caller for a forall result. -/
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

@[simp] theorem ofBits?_toBits (owned : Owned) :
    ofBits? owned.toBits = some owned := by
  cases owned <;> rfl

end Owned

end Ixon

end
