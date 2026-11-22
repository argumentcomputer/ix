import IxC.Ixon.Types.Modes

/-!
# The usage algebra

The 3-element Ixon v5 `Usage` algebra (`many`, `once`, `erased`) imported from
`IxC.Ixon.Types.Modes`, together with parallel combination (`add`),
multiplicative scaling (`mul`), branch join (`join`), coverage (`covers`), and
runtime-use count semantics (`admits`).
-/

namespace Ixon.Usage

/-- Parallel combination: the same variable used in two sibling
positions. Any two runtime uses collapse to `many`. -/
def add : Usage → Usage → Usage
  | .erased, u | u, .erased => u
  | _, _ => .many

instance : Add Usage := ⟨add⟩

/-- Multiplicative scaling. Runtime-irrelevant use is absorbing; `once` is the
multiplicative unit. -/
def mul : Usage → Usage → Usage
  | .erased, _ | _, .erased => .erased
  | .once, u | u, .once => u
  | .many, .many => .many

instance : Mul Usage := ⟨mul⟩

/-- Binder check: does declared usage `d` accept computed usage `c`?
`once` accepts at most one use (`erased` or `once`), `erased` accepts only
`erased`, and `many` accepts any usage. -/
def covers : Usage → Usage → Bool
  | .many, _ => true
  | .once, .erased | .once, .once => true
  | .erased, .erased => true
  | _, _ => false

/-- Alternative paths join their possible demands. -/
def join : Usage → Usage → Usage
  | .erased, .erased => .erased
  | .many, _ | _, .many => .many
  | _, _ => .once

/-- Runtime-use count admitted by a usage grade: `erased` admits 0, `once`
admits at most 1, `many` admits any count. -/
def admits : Usage → Nat → Prop
  | .erased, n => n = 0
  | .once, n => n ≤ 1
  | .many, _ => True

/-! ## The usage semiring laws -/

protected theorem add_comm (a b : Usage) : a.add b = b.add a := by
  cases a <;> cases b <;> rfl

protected theorem add_assoc (a b c : Usage) :
    (a.add b).add c = a.add (b.add c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] protected theorem add_erased (a : Usage) : a.add .erased = a := by
  cases a <;> rfl

@[simp] protected theorem erased_add (a : Usage) : Usage.add .erased a = a := by
  cases a <;> rfl

protected theorem mul_comm (a b : Usage) : a.mul b = b.mul a := by
  cases a <;> cases b <;> rfl

protected theorem mul_assoc (a b c : Usage) :
    (a.mul b).mul c = a.mul (b.mul c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] protected theorem mul_once (a : Usage) : a.mul .once = a := by
  cases a <;> rfl

@[simp] protected theorem once_mul (a : Usage) : Usage.mul .once a = a := by
  cases a <;> rfl

@[simp] protected theorem mul_erased (a : Usage) : a.mul .erased = .erased := by
  cases a <;> rfl

@[simp] protected theorem erased_mul (a : Usage) : Usage.mul .erased a = .erased := by
  cases a <;> rfl

/-- Scaling distributes over parallel combination. -/
protected theorem mul_add (a b c : Usage) :
    a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `covers` is reflexive: every declared usage accepts itself. -/
protected theorem covers_refl (a : Usage) : a.covers a = true := by
  cases a <;> rfl

theorem covers_sound (declared actual : Usage) (n : Nat)
    (h : declared.covers actual = true) (hn : actual.admits n) :
    declared.admits n := by
  cases declared <;> cases actual <;> simp_all [covers, admits]

theorem join_left (a b : Usage) (n : Nat) (h : a.admits n) :
    (a.join b).admits n := by
  cases a <;> cases b <;> simp_all [join, admits]

theorem join_right (a b : Usage) (n : Nat) (h : b.admits n) :
    (a.join b).admits n := by
  cases a <;> cases b <;> simp_all [join, admits]

theorem add_sound (a b : Usage) (m n : Nat)
    (ha : a.admits m) (hb : b.admits n) : (add a b).admits (m + n) := by
  cases a <;> cases b <;> simp_all [add, admits]

theorem mul_sound (a b : Usage) (m n : Nat)
    (ha : a.admits m) (hb : b.admits n) : (mul a b).admits (m * n) := by
  cases a <;> cases b <;> simp_all [mul, admits]
  simpa using Nat.mul_le_mul ha hb

end Ixon.Usage

namespace IxCC.Ixon

abbrev Usage := _root_.Ixon.Usage

namespace Usage
export _root_.Ixon.Usage (many once erased add mul covers join admits
  add_comm add_assoc add_erased erased_add
  mul_comm mul_assoc mul_once once_mul mul_erased erased_mul mul_add
  covers_refl covers_sound join_left join_right add_sound mul_sound)
end Usage

/-! Elaboration-time sanity checks. -/

#guard Usage.add .once .once == .many
#guard Usage.mul .erased .many == .erased
#guard Usage.mul .once .once == .once
#guard Usage.covers .once .erased
#guard Usage.covers .many .once
#guard !(Usage.covers .once .many)
#guard !(Usage.covers .erased .once)

end IxCC.Ixon
