import Ix.Compile.SourceInput
import Ix.Cert.SourcePrepass

namespace Ix.Cert.SourceInput
open Ix.Compile.SourceInput

theorem canonical_some (raw : Raw) : canonical? raw = some (Canon.constS raw.2) := by
  rw [canonical?, Canon.canonChunkCorrect]
  simp

/-- The original fallback is total on every raw winner; no body retention or
declaration-kind premise is needed. -/
theorem lookup_spec (s : Carrier) (name : Ix.Name) :
    s.lookup? name = (s.byName.get? name).map (fun raw => Canon.constS raw.2) := by
  unfold Carrier.lookup?
  cases s.byName.get? name <;> simp [canonical_some]

/-- The actual prepass supplies the SAME whole canonical input specification,
including the original winner semantics for every query. -/
theorem produced_lookup (raw : Array Raw) (name : Ix.Name) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw)).lookup? name =
      (SourceGraph.full (SourceStream.canonical raw)).consts.get? name := by
  rw [lookup_spec]
  exact (SourcePrepass.canonical_lookup raw name).symm

theorem produced_representative (raw : Array Raw) (name : Ix.Name) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw)).representative? name =
      (SourceGraph.full (SourceStream.canonical raw)).consts.getKey? name :=
  (SourcePrepass.canonical_key raw name).symm

theorem canonicalAt_of_winner {s : Carrier} {name : Ix.Name} {raw : Raw}
    (winner : s.byName.get? name = some raw) :
    s.canonicalAt name = if raw.1 == raw.2.name then .ok (Canon.constS raw.2)
      else .error (.headerMismatch name raw.1 raw.2.name) := by
  rw [Std.HashMap.get?_eq_getElem?] at winner
  simp [Carrier.canonicalAt, winner, canonical_some, pure, Except.pure, bind, Except.bind]
  rfl

/-- Every declared original is accounted for: its exact complete form or an
explicit inconsistent-tuple refusal. Missing/canon failure cannot hide it.
The header guard is not a premise added to a final semantic theorem. -/
theorem declared_coverage (input : Array Raw) (name : Ix.Name) (ci : Ix.ConstantInfo)
    (declared : (SourceGraph.full (SourceStream.canonical input)).consts.get? name = some ci) :
    ∃ raw, (Ix.Compile.SourceGraph.Prepass.run input).leanByIx.get? name = some raw ∧
      ci = Canon.constS raw.2 ∧
      (ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)).valueAt name =
        if raw.1 == raw.2.name then .ok (formOf ci)
        else .error (.headerMismatch name raw.1 raw.2.name) := by
  rw [SourcePrepass.canonical_lookup] at declared
  obtain ⟨raw, winner, same⟩ := Option.map_eq_some_iff.mp declared
  refine ⟨raw, winner, same.symm, ?_⟩
  unfold Carrier.valueAt
  rw [canonicalAt_of_winner (s := ofPrepass _) winner, same]
  split <;> rfl

theorem canonicalAt_origin {s : Carrier} {name : Ix.Name} {ci : Ix.ConstantInfo}
    (accepted : s.canonicalAt name = .ok ci) :
    ∃ raw, s.byName.get? name = some raw ∧ raw.1 = raw.2.name ∧ ci = Canon.constS raw.2 := by
  cases winner : s.byName.get? name with
  | none =>
    rw [Std.HashMap.get?_eq_getElem?] at winner
    simp [Carrier.canonicalAt, winner] at accepted
  | some raw =>
    rw [canonicalAt_of_winner winner] at accepted
    split at accepted
    · rename_i same
      exact ⟨raw, rfl, beq_iff_eq.mp same, (Except.ok.inj accepted).symm⟩
    · cases accepted

/-- Successful values retain the original full declaration, body and header;
the Source universe-parameter array is never replaced by a target array. -/
theorem valueAt_origin {s : Carrier} {name : Ix.Name} {form : Form}
    (accepted : s.valueAt name = .ok form) :
    ∃ raw, s.byName.get? name = some raw ∧ raw.1 = raw.2.name ∧
      form = formOf (Canon.constS raw.2) := by
  unfold Carrier.valueAt at accepted
  cases read : s.canonicalAt name with
  | error e =>
    have impossible : (Except.error e : Except Error Form) = .ok form := by
      simpa only [Functor.map, Except.map, read] using accepted
    cases impossible
  | ok ci =>
    have same : formOf ci = form := by simpa only [Functor.map, Except.map, read, Except.ok.injEq] using accepted
    obtain ⟨raw, winner, named, origin⟩ := canonicalAt_origin read
    exact ⟨raw, winner, named, same.symm.trans (congrArg formOf origin)⟩

/-- A successful produced form is an actual member of the complete original
Source specification, not a member of the transformed or retained code map. -/
theorem produced_value_member {input : Array Raw} {name : Ix.Name} {form : Form}
    (accepted : (ofPrepass (Ix.Compile.SourceGraph.Prepass.run input)).valueAt name = .ok form) :
    (SourceGraph.full (SourceStream.canonical input)).consts.get? name = some form.original ∧
      form = formOf form.original := by
  obtain ⟨raw, winner, _, origin⟩ := valueAt_origin accepted
  subst form
  constructor
  · rw [SourcePrepass.canonical_lookup]
    change (Ix.Compile.SourceGraph.Prepass.run input).leanByIx.get? name = some raw at winner
    rw [winner]
    rfl
  · rfl

theorem form_header (ci : Ix.ConstantInfo) : (formOf ci).header = ci.getCnst := rfl

theorem definition_body (d : Ix.DefinitionVal) :
    (formOf (.defnInfo d)).body = .value .defn d.value := rfl

theorem theorem_body (d : Ix.TheoremVal) :
    (formOf (.thmInfo d)).body = .value .thm d.value := rfl

theorem opaque_body (d : Ix.OpaqueVal) :
    (formOf (.opaqueInfo d)).body = .value .opaq d.value := rfl

/-- info: 'Ix.Cert.SourceInput.produced_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms produced_lookup
/-- info: 'Ix.Cert.SourceInput.declared_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms declared_coverage
/-- info: 'Ix.Cert.SourceInput.produced_value_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms produced_value_member

end Ix.Cert.SourceInput
