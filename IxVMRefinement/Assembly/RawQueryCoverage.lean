import IxVMRefinement.L1.TraceRecords
import IxVMRefinement.Assembly.AdmittedOverlay
import IxVMRefinement.Claim.Phase

/-! # Actual claim-phase coverage for raw record queries

The claim phase already retains every canonical constant hashed by its root trace. The full
admitted overlay preserves those records while adding selected role and fallback data. These
facts construct the raw-query contract without a separate query-coverage assumption.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- A decoded stored record supplies its canonical source object. -/
theorem canonicalRecordAt_of_recordAt {env : Ixon.Env}
    (decoded : L1.EnvDecoded env) {address : _root_.Address} {value : Ixon.Constant}
    (record : Ix.Cert.recordAt env address = some value) :
    ∃ source : L1.CanonicalRecordAt env address, source.value = value := by
  unfold Ix.Cert.recordAt at record
  cases saved : env.consts.get? address with
  | none => rw [saved] at record; cases record
  | some entry =>
    simp only [saved, Option.bind_some] at record
    obtain ⟨actual, cached, exactRead⟩ := decoded address entry saved
    have same := Option.some.inj (cached.symm.trans record)
    subst actual
    exact ⟨⟨entry, value, saved, cached, exactRead⟩, rfl⟩

/-- Literal record preservation transports actual trace coverage into a decoded overlay. -/
theorem canonicalHashCoverage_frame {env target : Ixon.Env} {calls : List (Call F)}
    (coverage : L1.CanonicalHashCoverage env calls) (decoded : L1.EnvDecoded target)
    (preserved : ∀ address value, Ix.Cert.recordAt env address = some value →
      Ix.Cert.recordAt target address = some value) :
    L1.CanonicalHashCoverage target calls := by
  intro bytes value hashed size read
  obtain ⟨source, same⟩ := coverage bytes value hashed size read
  have record := source.recordAt
  rw [same] at record
  exact canonicalRecordAt_of_recordAt decoded (preserved _ _ record)

/-- The actual claim-phase witness supplies exact canonical coverage of its root hashes. -/
theorem walked_canonicalHashCoverage {calls : List (Call F)} {table : Ix.Kernel.RoleTable}
    {trace : Ixon.Env} {seeds : List _root_.Address}
    (walked : Claim.WalkedL6 calls table trace seeds) :
    L1.CanonicalHashCoverage trace calls := by
  obtain ⟨_, _, _, _, _, complete, _⟩ := walked
  intro bytes value hashed size exactRead
  obtain ⟨entry, stored, bytesEq, cached⟩ := complete bytes value hashed size
    (L1.deConstant_of_deConstantExact exactRead) exactRead
  refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
  rw [bytesEq]
  exact exactRead

/-- The claim-phase exact record cache is the L1 decoded-environment invariant. -/
theorem walked_envDecoded {calls : List (Call F)} {table : Ix.Kernel.RoleTable}
    {trace : Ixon.Env} {seeds : List _root_.Address}
    (walked : Claim.WalkedL6 calls table trace seeds) : L1.EnvDecoded trace := by
  obtain ⟨_, _, _, exactRecords, _⟩ := walked
  intro address entry stored
  obtain ⟨_, value, cached, _, exactRead⟩ := exactRecords address entry stored
  exact ⟨value, cached, exactRead⟩

/-- Every actual trace record is retained by the complete admitted metadata overlay. -/
theorem admittedCore_trace_recordAt {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {address : _root_.Address} {value : Ixon.Constant}
    (record : Ix.Cert.recordAt trace address = some value) :
    Ix.Cert.recordAt (admittedCore witness trace (fun _ => True)) address = some value := by
  change Ix.Cert.recordAt (subEnv trace _ _) address = some value
  exact recordAt_subEnv_of_keep trace _ _ (.inl (.inr trivial)) record

/-- Keeping the actual trace in the admitted overlay preserves complete raw hash coverage. -/
theorem admitted_canonicalHashCoverage {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {calls : List (Call F)} {table : Ix.Kernel.RoleTable} {trace : Ixon.Env}
    {seeds : List _root_.Address} (walked : Claim.WalkedL6 calls table trace seeds) :
    L1.CanonicalHashCoverage (admittedCore witness trace (fun _ => True)) calls := by
  apply canonicalHashCoverage_frame (walked_canonicalHashCoverage walked)
    (admittedCore_decoded witness (fun _ => True) (walked_envDecoded walked))
  intro address value record
  exact admittedCore_trace_recordAt witness record

/-- Construct raw query facts from the actual root observation, claim-phase witness and
admitted reader data. Only the public collision alternative and existing memory bound are used. -/
theorem admitted_trace_raw_records {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {calls : List (Call F)} {trace : Ixon.Env} {seeds : List _root_.Address}
    (walked : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace)
    (bounded : IxVM.Consistency.Bounded calls)
    {name : String} {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (observed : ObsFn Core.W name args before result after calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls) :
    Core.RawRecordFacts (L1.traceRecordCtx
      ⟨admittedCore witness trace (fun _ => True), env, witness.table, lim⟩ calls) :=
  L1.rawRecordFacts_of_hashed_trace observed
    (admittedCore_good witness (fun _ => True) env lim claimBytes loaded bounded noCollision)
    (admitted_canonicalHashCoverage witness walked)

end IxVM.Refinement.Assembly
