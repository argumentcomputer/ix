/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Application

/-! The simultaneous walker used by production beta reduction agrees with
single substitution when exactly one lambda argument is consumed. -/

namespace Ix.Kernel

/-- The two pure walker specifications coincide for one replacement,
including index shifting above the removed binder. -/
theorem KExpr.simulSubstSpec_singleton {body argument : KExpr .anon} {depth : UInt64}
    (bound : depth.toNat + body.size + 1 < UInt64.size) :
    KExpr.simulSubstSpec body #[argument] depth = KExpr.substSpec body argument depth := by
  induction body generalizing depth with
  | var index name info =>
      simp only [KExpr.size] at bound
      have next : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show depth.toNat + 1 < UInt64.size by omega)]
      have window : (index ≥ depth && index < depth + 1) = true ↔ index = depth := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
          UInt64.lt_iff_toNat_lt, next]
        constructor
        · intro h; exact UInt64.toNat_inj.mp (by omega)
        · intro h; subst index; omega
      have above : index ≥ depth + 1 ↔ index > depth := by
        simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, next]
        omega
      by_cases equal : index = depth
      · subst index
        have smaller : depth < depth + 1 := UInt64.lt_iff_toNat_lt.mpr (by rw [next]; omega)
        simp [KExpr.simulSubstSpec, KExpr.substSpec, smaller]
      · have outside := mt window.mp equal
        have nameEq : name = anonName (m := .anon) := Subsingleton.elim _ _
        simp [KExpr.simulSubstSpec, KExpr.substSpec, equal, outside, above, nameEq]
  | app fn arg info ihFn ihArg =>
      simp only [KExpr.size] at bound
      simp [KExpr.simulSubstSpec, KExpr.substSpec,
        ihFn (depth := depth) (by omega), ihArg (depth := depth) (by omega)]
  | lam name bi domain body info ihDomain ihBody | all name bi domain body info ihDomain ihBody =>
      simp only [KExpr.size] at bound
      have next : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show depth.toNat + 1 < UInt64.size by omega)]
      simp [KExpr.simulSubstSpec, KExpr.substSpec, ihDomain (depth := depth) (by omega),
        ihBody (depth := depth + 1) (by rw [next]; omega)]
  | letE name type value body nondep info ihType ihValue ihBody =>
      simp only [KExpr.size] at bound
      have next : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show depth.toNat + 1 < UInt64.size by omega)]
      simp [KExpr.simulSubstSpec, KExpr.substSpec,
        ihType (depth := depth) (by omega), ihValue (depth := depth) (by omega),
        ihBody (depth := depth + 1) (by rw [next]; omega)]
  | prj ref field major info ih =>
      simp only [KExpr.size] at bound
      simp [KExpr.simulSubstSpec, KExpr.substSpec, ih (depth := depth) (by omega)]
  | _ => rfl

namespace Consistency

open Theory Theory.Model

universe u

/-- The actual memoized simultaneous substitution used by a one-argument
beta step reads the model substitution and preserves intern coherence. -/
theorem simulSubst_singleton_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body argument : KExpr .anon} {source value : VExpr β} {table : InternTable .anon}
    (bodyConstructed : body.Constructed) (argumentConstructed : argument.Constructed)
    (bodyBound : body.size + 1 < UInt64.size) (argumentBound : argument.size < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.SimulSubstReach #[argument] body 0 term)
    (bodyReads : readScopedExpr? resolve locals body 1 = some source)
    (argumentReads : readScopedExpr? resolve locals argument = some value) :
    readScopedExpr? resolve locals (simulSubst body #[argument] 0 table).1 =
      some (source.inst value) ∧ (simulSubst body #[argument] 0 table).2.WF := by
  obtain ⟨result, preserved, _⟩ := simulSubst_spec faithful bodyConstructed
    (by
      intro index small
      have : index = 0 := by simpa using small
      subst index
      exact argumentConstructed)
    (by
      intro index small
      have : index = 0 := by simpa using small
      subst index
      exact argumentBound)
    (by simpa using bodyBound) (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)
  refine ⟨?_, preserved⟩
  rw [result, KExpr.simulSubstSpec_singleton (by simpa using bodyBound)]
  exact readScopedExpr?_substSpec (depth := 0) (by simpa using bodyBound)
    argumentBound bodyReads argumentReads

end Consistency
end Ix.Kernel
