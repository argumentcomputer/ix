/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Application
import Ix.Theory.Model.BetaSubstitution

/-! Read simultaneous substitution in one structural pass, using the
original body and argument bounds rather than bounds on generated trees. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

theorem readScopedExpr?_simulSubstSpec {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body : KExpr .anon} {source : AExpr β} {substs : Array (KExpr .anon)}
    {arguments : List (AExpr β)} {depth : UInt64}
    (sizeAgrees : substs.size = arguments.length)
    (bound : depth.toNat + body.size + substs.size < UInt64.size)
    (argumentBounds : ∀ index, index < substs.size → substs[index]!.size < UInt64.size)
    (bodyReads : readScopedExpr? resolve locals body (depth.toNat + arguments.length) = some source.erase)
    (argumentReads : ∀ index (small : index < substs.size),
      readScopedExpr? resolve locals substs[index]! =
        some (arguments[arguments.length - index - 1]'(by omega)).erase) :
    readScopedExpr? resolve locals (KExpr.simulSubstSpec body substs depth) depth.toNat =
      some (source.instRevAt arguments depth.toNat).erase := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at bodyReads
      split at bodyReads
      next inScope =>
        cases source <;> cases bodyReads
        have sizeNat : substs.size.toUInt64.toNat = substs.size := by
          change substs.size % UInt64.size = substs.size
          apply Nat.mod_eq_of_lt
          simp only [KExpr.size] at bound
          omega
        have upper : (depth + substs.size.toUInt64).toNat = depth.toNat + substs.size := by
          rw [UInt64.toNat_add, sizeNat]
          exact Nat.mod_eq_of_lt (show depth.toNat + substs.size < UInt64.size by
            simp only [KExpr.size] at bound
            omega)
        by_cases below : index.toNat < depth.toNat
        · have outside : ¬ index ≥ depth := by simpa only [UInt64.le_iff_toNat_le] using Nat.not_le.mpr below
          have outsideUpper : ¬ index ≥ depth + substs.size.toUInt64 := by
            intro contrary
            have inequality := UInt64.le_iff_toNat_le.mp contrary
            rw [upper] at inequality
            omega
          simp [KExpr.simulSubstSpec, outside, outsideUpper, readScopedExpr?, below,
            AExpr.instRevAt_bvar_below arguments index.toNat depth.toNat below, AExpr.erase]
        · have inRange : (index ≥ depth && index < depth + substs.size.toUInt64) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
              UInt64.lt_iff_toNat_lt, upper]
            constructor <;> omega
          have offset : (index - depth).toNat = index.toNat - depth.toNat :=
            UInt64.toNat_sub_of_le index depth (UInt64.le_iff_toNat_le.mpr (by omega))
          have small : index.toNat - depth.toNat < substs.size := by omega
          rw [KExpr.simulSubstSpec, if_pos inRange, offset]
          have lifted := readScopedExpr?_liftSpec (depth := 0) (shift := depth)
            (by simpa using argumentBounds _ small) (argumentReads _ small)
          have selected := AExpr.instRevAt_bvar_selected arguments
            (index.toNat - depth.toNat) depth.toNat (by omega)
          rw [show depth.toNat + (index.toNat - depth.toNat) = index.toNat by omega] at selected
          rw [selected, AExpr.erase_liftN]
          simpa only [UInt64.toNat_zero, Nat.zero_add] using lifted
      · contradiction
  | fvar id name info =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨index, found, bodyReads⟩ := Option.map_eq_some_iff.mp bodyReads
      cases source <;> cases bodyReads
      rw [AExpr.instRevAt_bvar_above arguments _ _ (by omega)]
      simp [KExpr.simulSubstSpec, readScopedExpr?, found, AExpr.erase,
        show depth.toNat + arguments.length + index - arguments.length = depth.toNat + index by omega]
  | sort level info =>
      cases source <;> cases bodyReads
      simp [KExpr.simulSubstSpec, readScopedExpr?, AExpr.erase]
  | nat value blob info =>
      cases source <;> cases bodyReads
      simp [KExpr.simulSubstSpec, readScopedExpr?, AExpr.erase]
  | const id levels info =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      cases source <;> cases bodyReads
      simp [KExpr.simulSubstSpec, readScopedExpr?, resolved, AExpr.erase]
  | str _ _ _ => contradiction
  | letE name domain value body nonDep info ihDomain ihValue ihBody =>
      obtain ⟨A, v, b, domainReads, valueReads, innerReads, erased⟩ := readScopedExpr?_let_parts bodyReads
      obtain ⟨domainSource, rfl⟩ := AExpr.erase_surjective A
      obtain ⟨valueSource, rfl⟩ := AExpr.erase_surjective v
      obtain ⟨bodySource, rfl⟩ := AExpr.erase_surjective b
      simp only [KExpr.size] at bound
      have next : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show depth.toNat + 1 < UInt64.size by omega)]
      have innerOut := ihBody (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using innerReads) argumentReads
      simp only [next] at innerOut
      simp only [AExpr.erase_instRevAt, erased, VExpr.instRevAt_inst_zero]
      simp [KExpr.simulSubstSpec, AExpr.erase_instRevAt,
        ihDomain (depth := depth) (by omega) domainReads argumentReads,
        ihValue (depth := depth) (by omega) valueReads argumentReads, innerOut]
  | app fn arg info ihFn ihArg =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨f, fnReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨a, argReads, bodyReads⟩ := bind_success bodyReads
      cases source <;> cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.simulSubstSpec, AExpr.erase,
        ihFn (depth := depth) (by omega) fnReads argumentReads,
        ihArg (depth := depth) (by omega) argReads argumentReads]
  | lam name bi domain body info ihDomain ihBody | all name bi domain body info ihDomain ihBody =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨A, domainReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨B, innerReads, bodyReads⟩ := bind_success bodyReads
      cases source <;> cases bodyReads
      simp only [KExpr.size] at bound
      have next : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show depth.toNat + 1 < UInt64.size by omega)]
      have innerOut := ihBody (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using innerReads) argumentReads
      simp only [next] at innerOut
      simp [KExpr.simulSubstSpec, AExpr.erase,
        ihDomain (depth := depth) (by omega) domainReads argumentReads, innerOut]
  | prj id field major info ih =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      obtain ⟨value, valueReads, bodyReads⟩ := bind_success bodyReads
      cases source <;> cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.simulSubstSpec, resolved, AExpr.erase,
        ih (depth := depth) (by omega) valueReads argumentReads]

/-- The memoized production walker returns the reading established by the
single structural pass and preserves intern coherence. -/
theorem simulSubst_readScopedExpr? {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body : KExpr .anon} {source : AExpr β} {substs : Array (KExpr .anon)}
    {arguments : List (AExpr β)} {table : InternTable .anon}
    (sizeAgrees : substs.size = arguments.length)
    (bodyConstructed : body.Constructed)
    (argumentConstructed : ∀ index, index < substs.size → substs[index]!.Constructed)
    (bodyBound : body.size + substs.size < UInt64.size)
    (argumentBounds : ∀ index, index < substs.size → substs[index]!.size < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.SimulSubstReach substs body 0 term)
    (bodyReads : readScopedExpr? resolve locals body arguments.length = some source.erase)
    (argumentReads : ∀ index (small : index < substs.size),
      readScopedExpr? resolve locals substs[index]! =
        some (arguments[arguments.length - index - 1]'(by omega)).erase) :
    readScopedExpr? resolve locals (simulSubst body substs 0 table).1 = some (source.instRev arguments).erase ∧
      (simulSubst body substs 0 table).2.WF := by
  obtain ⟨result, preserved, _⟩ := simulSubst_spec faithful bodyConstructed argumentConstructed
    argumentBounds (by simpa using bodyBound) (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)
  refine ⟨?_, preserved⟩
  rw [result]
  simpa only [UInt64.toNat_zero, Nat.zero_add, AExpr.instRevAt_zero] using
    (readScopedExpr?_simulSubstSpec (depth := 0) sizeAgrees (by simpa using bodyBound)
      argumentBounds (by simpa using bodyReads) argumentReads)

end Ix.Kernel.Consistency
