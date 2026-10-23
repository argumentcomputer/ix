import IxSharingVerify.FamilyDomain
import Ix.CompileCert.SharingRoots

/-! The actual experimental constant wrapper preserves unchanged fields,
writes its ordered roots back exactly and reports serialized VARIABLE bytes.
This is not the total serialized constant size or a totality/compatibility claim. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.Tiered
open Ix.Sharing.Verify.SharingExact (Desc bind_eq_ok termOf)
open Ix.Sharing.Verify.CanonicalMeaning (SharingMeaning)

theorem normalizeFamily_parts {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) :
    ∃ expanded info, expand limits input.sharing (constantInfoRoots input.info) true = .ok expanded ∧
      familyExpanded cfg layout limits expanded = .ok result ∧
      withRoots input.info result.result.roots = .ok info ∧
      output = { input with info, sharing := result.result.sharing } := by
  unfold normalizeFamily at run
  obtain ⟨expanded, expandedRun, run⟩ := bind_eq_ok run
  obtain ⟨result', normalized, run⟩ := bind_eq_ok run
  obtain ⟨info, written, run⟩ := bind_eq_ok run
  cases Except.ok.inj run
  exact ⟨expanded, info, expandedRun, normalized, written, rfl⟩

/-- `erase` replaces only expression roots by placeholders; its equality
therefore preserves every non-root payload field, for every payload kind. -/
theorem normalizeFamily_fields {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) :
    output.refs = input.refs ∧ output.univs = input.univs ∧ output.sharing = result.result.sharing ∧
      constantInfoRoots output.info = result.result.roots ∧
      Ix.CompileCert.SharingRoots.erase output.info = Ix.CompileCert.SharingRoots.erase input.info := by
  obtain ⟨_, _, _, _, written, rfl⟩ := normalizeFamily_parts run
  have kept := Ix.CompileCert.SharingRoots.withRoots_inv written
  exact ⟨rfl, rfl, rfl, kept.1, kept.2⟩

theorem normalizeFamily_format {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) :
    FormatOK output.sharing (constantInfoRoots output.info) := by
  obtain ⟨_, _, _, normalized, _, _⟩ := normalizeFamily_parts run
  obtain ⟨_, _, sharing, roots, _⟩ := normalizeFamily_fields run
  rw [sharing, roots]
  exact (familyExpanded_output_of_success normalized).format

/-- Only unchanged headers and tables need input wire premises; the new
roots and sharing table are covered by actual output guards. -/
theorem normalizeFamily_wire_headers {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (headers : ConstantInfoHeaderWF input.info)
    (refsCount : input.refs.size < UInt64.size) (refs : ∀ r ∈ input.refs, r.hash.size = 32)
    (univsCount : input.univs.size < UInt64.size) (univs : ∀ u ∈ input.univs, u.wireWF)
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) : output.wireWF := by
  obtain ⟨_, _, _, normalized, written, rfl⟩ := normalizeFamily_parts run
  have format := (familyExpanded_output_of_success normalized).format
  refine ⟨withRoots_wireWF_headers written headers (fun e he => format.2.1 e (Array.mem_toList_iff.mpr he)),
    format.2.2.1, fun e he => format.1 e (Array.mem_toList_iff.mpr he), refsCount, refs, univsCount, univs⟩

theorem normalizeFamily_wire {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult} (wire : input.wireWF)
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) : output.wireWF :=
  normalizeFamily_wire_headers (ConstantInfoHeaderWF.of_wire wire.1)
    wire.2.2.2.1 wire.2.2.2.2.1 wire.2.2.2.2.2.1 wire.2.2.2.2.2.2 run

/-- This is the table-count plus serialized table/root EXPRESSION bytes.
It excludes unchanged constant headers, references and universe tables. -/
theorem normalizeFamily_variableBytes {cfg : Config} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (run : normalizeFamily cfg .tagN input limits = .ok (output, result)) :
    result.result.variableBytes = tag0Size output.sharing.size +
        (output.sharing ++ constantInfoRoots output.info).foldl (fun n e => n + (Ixon.serExpr e).size) 0 ∧
      result.result.modelBytes = result.result.variableBytes := by
  obtain ⟨_, _, _, normalized, _, _⟩ := normalizeFamily_parts run
  obtain ⟨_, _, sharing, roots, _⟩ := normalizeFamily_fields run
  rw [sharing, roots]
  exact familyExpanded_serialized normalized

/-- Both tables unfold to the same ordered roots, including input sharing.
This is semantic preservation, not representation independence or idempotence. -/
theorem normalizeFamily_meaning {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult}
    (run : normalizeFamily cfg layout input limits = .ok (output, result)) :
    ∃ sources, SharingMeaning sources input.sharing (constantInfoRoots input.info) ∧
      SharingMeaning sources output.sharing (constantInfoRoots output.info) := by
  obtain ⟨expanded, _, expandedRun, normalized, _, _⟩ := normalizeFamily_parts run
  refine ⟨expanded.roots.map (termOf expanded.dag.nodes), expand_shared_meaning expandedRun, ?_⟩
  obtain ⟨_, _, sharing, roots, _⟩ := normalizeFamily_fields run
  rw [sharing, roots]
  exact familyExpanded_meaning normalized

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyExpanded_domain [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyExpanded_output_of_success [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_fields [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_format [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_wire_headers [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_wire [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_variableBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.tableResult_meaning [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.expand_shared_meaning [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyExpanded_meaning [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_meaning [propext, Classical.choice, Quot.sound]
