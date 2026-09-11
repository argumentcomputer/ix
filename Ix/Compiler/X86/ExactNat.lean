import Ix.Compiler.X86.Execution

/-! Exact unsigned scalar arithmetic. The external Nat interface checks its
conversion before entering native code. A native ADD reports overflow; a SUB
uses an unsigned comparison to implement Nat's truncation at zero. Neither
contract treats a wrapped machine result as an exact natural number. -/

namespace Ix.Compiler.X86.ExactNat

def encode (value : Nat) : Option Word :=
  if value < UInt64.size then some (UInt64.ofNat value) else none

theorem encode_some_iff {value : Nat} {word : Word} :
    encode value = some word ↔ word.toNat = value := by
  constructor
  · intro accepted
    unfold encode at accepted
    split at accepted
    next bound =>
      cases Option.some.inj accepted
      exact UInt64.toNat_ofNat_of_lt' bound
    next => contradiction
  · intro represented
    have bound : value < UInt64.size := represented ▸ word.toNat_lt_size
    simp only [encode, if_pos bound, Option.some.injEq]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' bound, represented]

theorem encode_none_iff (value : Nat) :
    encode value = none ↔ UInt64.size ≤ value := by
  simp [encode]

@[simp] theorem encode_toNat (word : Word) : encode word.toNat = some word :=
  encode_some_iff.mpr rfl

/-- This is the unsigned carry test emitted after ADD. -/
def overflow (left right : Word) : Bool := decide (left + right < left)

theorem overflow_iff (left right : Word) :
    overflow left right = true ↔ UInt64.size ≤ left.toNat + right.toNat := by
  have hl := left.toNat_lt_size
  have hr := right.toNat_lt_size
  simp only [overflow, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  change (left.toNat + right.toNat) % UInt64.size < left.toNat ↔ _
  simp only [UInt64.size] at *
  omega

def add (left right : Word) : Option Word :=
  if overflow left right then none else some (left + right)

theorem add_none_iff (left right : Word) :
    add left right = none ↔ UInt64.size ≤ left.toNat + right.toNat := by
  simp only [add]
  split <;> simp_all [overflow_iff]

theorem add_some_iff {left right result : Word} :
    add left right = some result ↔ result.toNat = left.toNat + right.toNat := by
  constructor
  · intro accepted
    unfold add at accepted
    split at accepted
    next => contradiction
    next noOverflow =>
      cases Option.some.inj accepted
      have bound : left.toNat + right.toNat < UInt64.size := by
        exact Nat.lt_of_not_ge (fun h => noOverflow ((overflow_iff left right).mpr h))
      exact (UInt64.toNat_add left right).trans (Nat.mod_eq_of_lt bound)
  · intro represented
    have bound : left.toNat + right.toNat < UInt64.size := represented ▸ result.toNat_lt_size
    have noOverflow : overflow left right = false := by
      have := overflow_iff left right
      cases h : overflow left right <;> simp_all <;> omega
    simp only [add, noOverflow, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt bound, represented]

/-- Truncated Nat subtraction, including the underflow case. -/
def sub (left right : Word) : Word :=
  if left < right then 0 else left - right

theorem sub_toNat (left right : Word) :
    (sub left right).toNat = left.toNat - right.toNat := by
  unfold sub
  split
  next less =>
    have less := UInt64.lt_iff_toNat_lt.mp less
    simp only [UInt64.toNat_zero]
    omega
  next ge =>
    exact UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      exact Nat.le_of_not_gt (fun h => ge (UInt64.lt_iff_toNat_lt.mpr h))))

theorem successor_exact {value : Word} (bound : value.toNat + 1 < UInt64.size) :
    (value + 1).toNat = value.toNat + 1 := by
  simpa only [UInt64.toNat_one] using
    (UInt64.toNat_add value 1).trans (Nat.mod_eq_of_lt bound)

theorem predecessor_exact {value : Word} (positive : value ≠ 0) :
    (value - 1).toNat = value.toNat - 1 := by
  have nonzero : value.toNat ≠ 0 := by
    intro h
    exact positive (UInt64.toNat_inj.mp h)
  have : (1 : Word) ≤ value := UInt64.le_iff_toNat_le.mpr (by
    change 1 ≤ value.toNat
    omega)
  simpa only [UInt64.toNat_one] using UInt64.toNat_sub_of_le value 1 this

end Ix.Compiler.X86.ExactNat
