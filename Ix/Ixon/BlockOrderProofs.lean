/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.BlockOrder
import Ix.Ixon.ProjectionProofs

namespace Ix.Ixon.BlockOrder

open Kernel

/-- An independently counted refinement derivation. A terminal derivation
must exhibit an unchanged complete pass; a changing pass cannot be terminal.
No rule converts exhaustion into a result. -/
inductive Refinement (block : Block) (comparison : Nat) : Nat → Classes → Classes → Prop where
  | fixed {classes} (step : refineStep block comparison classes = .ok classes) :
      Refinement block comparison 1 classes classes
  | next {classes next result rounds}
      (step : refineStep block comparison classes = .ok next)
      (changed : next ≠ classes) (tail : Refinement block comparison rounds next result) :
      Refinement block comparison (rounds + 1) classes result

theorem Refinement.positive {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) : 0 < rounds := by
  cases h <;> omega

theorem Refinement.fixedPoint {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) :
    refineStep block comparison result = .ok result := by
  induction h with
  | fixed step => exact step
  | next _ _ _ ih => exact ih

theorem refine_sound {block comparison fuel initial result}
    (h : refine block comparison fuel initial = .ok result) :
    ∃ rounds, rounds ≤ fuel ∧ Refinement block comparison rounds initial result := by
  induction fuel generalizing initial with
  | zero => simp [refine] at h
  | succ fuel ih =>
    cases step : refineStep block comparison initial with
    | error error => simp [refine, step, bind, Except.bind] at h
    | ok next =>
      by_cases same : next = initial
      · subst next
        simp [refine, step, bind, Except.bind, pure, Except.pure] at h
        subst result
        exact ⟨1, by omega, .fixed step⟩
      · simp [refine, step, same, bind, Except.bind] at h
        obtain ⟨rounds, bound, trace⟩ := ih h
        exact ⟨rounds + 1, by omega, .next step same trace⟩

theorem Refinement.complete {block comparison rounds initial result}
    (h : Refinement block comparison rounds initial result) {fuel : Nat} (bound : rounds ≤ fuel) :
    refine block comparison fuel initial = .ok result := by
  induction h generalizing fuel with
  | fixed step =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [refine, step, bind, Except.bind, pure, Except.pure]
  | next step changed tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [refine, step, changed, bind, Except.bind]
      exact ih (by omega)

theorem refine_ok_iff (block : Block) (comparison fuel : Nat) (initial result : Classes) :
    refine block comparison fuel initial = .ok result ↔
      ∃ rounds, rounds ≤ fuel ∧ Refinement block comparison rounds initial result :=
  ⟨refine_sound, fun ⟨_, bound, trace⟩ => trace.complete bound⟩

theorem refine_fixedPoint {block comparison fuel initial result}
    (h : refine block comparison fuel initial = .ok result) :
    refineStep block comparison result = .ok result := by
  obtain ⟨_, _, trace⟩ := refine_sound h
  exact trace.fixedPoint

theorem refine_mono {block comparison small large initial result}
    (h : refine block comparison small initial = .ok result) (bound : small ≤ large) :
    refine block comparison large initial = .ok result := by
  obtain ⟨_, used, trace⟩ := refine_sound h
  exact trace.complete (Nat.le_trans used bound)

/-- The stored order must be the recomputed list of ordered singletons.
This predicate records physical preparation, deterministic seeding, and a
finite refinement derivation, independently of the bounded loop's verdict. -/
def Canonical (limits : Limits) (owner : Address) (source : _root_.Ixon.Constant)
    (blobs : Ingress.Blobs) : Prop :=
  ∃ block initial rounds, prepare owner source blobs = .ok block ∧ seed block = .ok initial ∧
    rounds ≤ limits.refinement ∧
    Refinement block limits.comparison rounds initial (orderedSingletons block.entries.size)

theorem canonicalClasses_ok_iff (limits : Limits) (block : Block) (classes : Classes) :
    canonicalClasses limits block = .ok classes ↔
      ∃ initial rounds, seed block = .ok initial ∧ rounds ≤ limits.refinement ∧
        Refinement block limits.comparison rounds initial classes := by
  cases seeded : seed block with
  | error error => simp [canonicalClasses, seeded, bind, Except.bind]
  | ok initial => simp [canonicalClasses, seeded, bind, Except.bind, refine_ok_iff]

theorem checkBlock_ok_iff (limits : Limits) (owner : Address) (source : _root_.Ixon.Constant)
    (blobs : Ingress.Blobs) : checkBlock limits owner source blobs = .ok () ↔
      Canonical limits owner source blobs := by
  cases prepared : prepare owner source blobs with
  | error error => simp [checkBlock, Canonical, prepared, bind, Except.bind]
  | ok block =>
    have run : checkBlock limits owner source blobs = .ok () ↔
        canonicalClasses limits block = .ok (orderedSingletons block.entries.size) := by
      cases sorted : canonicalClasses limits block with
      | error error => simp [checkBlock, prepared, sorted, bind, Except.bind]
      | ok result =>
        by_cases same : result = orderedSingletons block.entries.size <;>
          simp [checkBlock, prepared, sorted, same, bind, Except.bind, pure, Except.pure, throw]
    rw [run, canonicalClasses_ok_iff]
    simp [Canonical, prepared]

def OrderedRecord (limits : Limits) (blobs : Ingress.Blobs) (pair : Address × _root_.Ixon.Constant) : Prop :=
  match pair.2.info with
  | .muts _ => Canonical limits pair.1 pair.2 blobs
  | _ => True

def Ordered (limits : Limits) (blobs : Ingress.Blobs) (input : Ingress.Constants) : Prop :=
  ∀ pair ∈ input, OrderedRecord limits blobs pair

theorem checkConstants_ok_iff (limits : Limits) (blobs : Ingress.Blobs) (input : Ingress.Constants) :
    checkConstants limits blobs input = .ok () ↔ Ordered limits blobs input := by
  induction input with
  | nil => simp [checkConstants, Ordered]
  | cons pair rest ih =>
    rcases pair with ⟨owner, source⟩
    have orderedCons : Ordered limits blobs ((owner, source) :: rest) ↔
        OrderedRecord limits blobs (owner, source) ∧ Ordered limits blobs rest := by
      simp only [Ordered, List.mem_cons, forall_eq_or_imp]
    rw [orderedCons, ← ih]
    cases info : source.info <;>
      simp only [checkConstants, info, OrderedRecord, Bool.false_eq_true,
        ite_false, ite_true, bind, Except.bind, true_and]
    cases checked : checkBlock limits owner source blobs with
    | error error => simp [checked, ← checkBlock_ok_iff]
    | ok value => cases value; simp [checked, ← checkBlock_ok_iff]

universe v

theorem checkBytes_run_iff (maxProjections : Nat) (limits : Admission.Limits) (orderLimits : Limits)
    (cfg : Config) (records : Admission.Records) (blobs : Ingress.Blobs)
    (family : Option (ConstRef Address)) (env : Env Address) :
    checkBytes.{v} maxProjections limits orderLimits cfg records blobs family = .ok env ↔
      Admission.preflight limits records blobs = .ok () ∧ ∃ input output,
        Admission.decodeRecords limits records = .ok input ∧
        Projection.reconstruct maxProjections input = .ok output ∧
        checkConstants orderLimits blobs input = .ok () ∧
        Kernel.checkEnv.{v} cfg output blobs family = .ok env := by
  cases flight : Admission.preflight limits records blobs with
  | error error => simp [checkBytes, flight, Except.mapError, bind, Except.bind]
  | ok value =>
    cases value
    cases decoded : Admission.decodeRecords limits records with
    | error error => simp [checkBytes, flight, decoded, Except.mapError, bind, Except.bind]
    | ok input =>
      cases expanded : Projection.reconstruct maxProjections input with
      | error error => simp [checkBytes, flight, decoded, expanded, Except.mapError, bind, Except.bind]
      | ok output =>
        cases ordered : checkConstants orderLimits blobs input with
        | error error => simp [checkBytes, flight, decoded, expanded, ordered, Except.mapError, bind, Except.bind]
        | ok value =>
          cases value
          cases checked : Kernel.checkEnv.{v} cfg output blobs family <;>
            simp [checkBytes, flight, decoded, expanded, ordered, checked, Except.mapError, bind, Except.bind]

theorem checkBytes_ok_iff (maxProjections : Nat) (limits : Admission.Limits) (orderLimits : Limits)
    (cfg : Config) (records : Admission.Records) (blobs : Ingress.Blobs)
    (family : Option (ConstRef Address)) (env : Env Address) :
    checkBytes.{v} maxProjections limits orderLimits cfg records blobs family = .ok env ↔
      Verify.Admission.WithinBatch limits records blobs ∧ ∃ input output,
        Verify.Admission.RecordsRead limits records input ∧
        Projection.Expanded maxProjections input output ∧ Ordered orderLimits blobs input ∧
        Kernel.checkEnv.{v} cfg output blobs family = .ok env := by
  simp only [checkBytes_run_iff, Verify.Admission.preflight_ok_iff,
    Verify.Admission.decodeRecords_ok_iff, Projection.reconstruct_ok_iff, checkConstants_ok_iff]

theorem checkBytes_reading {maxProjections limits orderLimits cfg records blobs family env}
    (h : checkBytes.{v} maxProjections limits orderLimits cfg records blobs family = .ok env) :
    ∃ input output, Verify.Admission.RecordsRead limits records input ∧
      Projection.Expanded maxProjections input output ∧ Ordered orderLimits blobs input ∧
      Ingress.Installed output blobs family none env := by
  obtain ⟨_, input, output, reading, expanded, ordered, checked⟩ := (checkBytes_ok_iff _ _ _ _ _ _ _ _).mp h
  exact ⟨input, output, reading, expanded, ordered, Kernel.checkEnv_reading checked⟩

theorem checkBytes_has_model (V : Type v) [Model.SetTheory V]
    {maxProjections limits orderLimits cfg records blobs family env}
    (h : checkBytes.{v} maxProjections limits orderLimits cfg records blobs family = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨_, _, _, _, _, _, checked⟩ := (checkBytes_ok_iff _ _ _ _ _ _ _ _).mp h
  exact Kernel.checkEnv_has_model V checked

/-- On a read, expanded, canonically ordered input, every final kernel
outcome and its exact reason survive unchanged, including exhaustion. -/
theorem checkBytes_of_ordered {maxProjections limits orderLimits cfg records input output blobs family}
    (within : Verify.Admission.WithinBatch limits records blobs)
    (reading : Verify.Admission.RecordsRead limits records input)
    (expanded : Projection.Expanded maxProjections input output)
    (ordered : Ordered orderLimits blobs input) :
    checkBytes.{v} maxProjections limits orderLimits cfg records blobs family =
      (Kernel.checkEnv.{v} cfg output blobs family).mapError (fun error => .admission (.kernel error)) := by
  have flight := (Verify.Admission.preflight_ok_iff _ _ _).mpr within
  have decoded := (Verify.Admission.decodeRecords_ok_iff _ _ _).mpr reading
  have reconstructed := (Projection.reconstruct_ok_iff _ _ _).mpr expanded
  have order := (checkConstants_ok_iff _ _ _).mpr ordered
  simp [checkBytes, flight, decoded, reconstructed, order, Except.mapError, bind, Except.bind]

end Ix.Ixon.BlockOrder
