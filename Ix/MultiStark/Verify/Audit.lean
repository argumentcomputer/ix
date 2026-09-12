import Ix.Tc.Verify.Audit.Basic
import Ix.MultiStark.Verify
import Ix.MultiStark.Verify.Proofs
import Ix.Ixby.Claim.Stage2

/-! Exact trust manifest for the pure Stage 2 components implemented so far.
The public roots cover binding, graph/OOD/transcript phases, and MMCS row/leaf
construction, NOT a completed Stage 2 soundness/refinement theorem. No native,
pending, upstream-implementation, or sorry allowances are permitted. -/

namespace MultiStark.Verify.Audit

open Lean Lean.Elab.Command Ix.Tc.Verify.Audit

private def standard : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def roots : Array RootAllowance := ((#[
  ``ClosedCheckEnv.bytes_size,
  ``AggregateConfig.allowedIdentity_size,
  ``packDigest_size,
  ``AggregateConfig.expectedClaim_size,
  ``Transcript.sampleField_sound,
  ``Transcript.sampleField_complete,
  ``Proofs.bind_ok_iff, ``Proofs.map_ok_iff, ``Proofs.evalNode_refines,
  ``Proofs.sweepFrom_refines, ``Proofs.sweep_refines,
  ``Proofs.sampleBits_refines, ``Proofs.sampleField_sound_count,
  ``Proofs.action_bind_ok_iff, ``Proofs.action_map_ok_iff,
  ``Proofs.observeChunks_refines, ``Proofs.observeNats_refines, ``Proofs.observeExt_refines,
  ``Proofs.observeExts_refines, ``Proofs.observeFields_refines, ``Proofs.observeCap_refines,
  ``Proofs.observeClaimList_refines, ``Proofs.observeClaims_refines, ``Proofs.observeParameters_refines,
  ``Proofs.seed_refines, ``Proofs.beforeLookup_refines,
  ``Proofs.observePointList_refines, ``Proofs.observeMatrixList_refines, ``Proofs.observeRoundList_refines,
  ``Proofs.observeOpenings_refines, ``Proofs.fri_shape_refines, ``Proofs.queryIndices_refines,
  ``Proofs.queryDraws_length, ``Proofs.queryDraws_bounded,
  ``Proofs.twoAdicGenerator_refines,
  ``Proofs.readRefs_refines, ``Proofs.roots_refines, ``Proofs.readCoordinates_refines,
  ``Proofs.lookupMessage_refines, ``Proofs.lookupEntries_refines, ``Proofs.groupEquation_refines,
  ``Proofs.lookupTarget_refines, ``Proofs.lookupGroupsFrom_refines, ``Proofs.lookupValues_refines,
  ``Proofs.recombineQuotient_refines,
  ``Proofs.mmcs_hashRow_refines, ``Proofs.mmcs_compress_refines, ``Proofs.mmcs_geometry_refines,
  ``Proofs.checkQueryRows_refines, ``Proofs.checkRowList_refines, ``Proofs.checkRows_refines] : Array Lean.Name).map fun root =>
    { root, standardAxioms := #[``propext, ``Quot.sound] }) ++
  ((#[``Proofs.mapError_ok_iff, ``Proofs.pure_ok_iff, ``Proofs.getAt_ok_iff,
    ``Proofs.observeBytes_refines, ``Proofs.action_pure_ok_iff, ``Proofs.action_throw_ok_iff,
    ``Proofs.observeNat_refines, ``Proofs.ensure_ok_iff,
    ``Proofs.generator_table, ``Proofs.generator_order, ``Proofs.generator_normalization_nonzero,
    ``Proofs.extension_beq_iff_eq, ``Proofs.listArray_exists_iff, ``Proofs.references_length,
    ``Proofs.claimFingerprint_refines, ``Proofs.quotientFrom_refines, ``Proofs.balanced_refines,
    ``Proofs.mmcs_getAt_refines] : Array Lean.Name).map fun root =>
    { root, standardAxioms := #[``propext] }) ++
  ((#[``verifyTyped_iff, ``stage2Verify_iff, ``claimWrapper_some_iff,
    ``claimBytesWrapper_some_iff, ``stage2VerifyBytes_binding,
    ``Proofs.checkWitness_refines, ``Proofs.sampleField_complete_count, ``Proofs.sampleField_refines,
    ``Proofs.sampleExt_refines, ``Proofs.prefixReplay_refines, ``Proofs.replay_refines,
    ``Proofs.commitPhase_refines, ``Proofs.fri_replayAction_refines, ``Proofs.fri_replay_refines,
    ``Proofs.fri_replay_query_count, ``Proofs.fri_replay_query_bounds,
    ``Proofs.inverseBase_refines, ``Proofs.inverse_refines, ``Proofs.divide_refines,
    ``Proofs.selectors_refines, ``Proofs.initialAccumulatorFrom_refines, ``Proofs.initialAccumulator_refines,
    ``Proofs.ood_evaluate_refines, ``Proofs.ood_checkFrom_refines, ``Proofs.ood_check_refines,
    ``Proofs.digest_beq_iff_eq, ``Proofs.checkSameRows_refines, ``Proofs.layerRowsFrom_refines,
    ``Proofs.layerRows_refines, ``Proofs.freshLeaf_refines, ``Proofs.leafStep_refines,
    ``Proofs.leavesFrom_refines, ``Proofs.leaves_refines,
    ``Ix.Ixby.Claim.Stage2.source_claim_binding,
    ``Ix.Ixby.Claim.Stage2.terminal_verified_claim_or_collision] : Array Lean.Name).map fun root =>
    { root, standardAxioms := standard }) ++
  #[{ root := ``Proofs.unit_exists_iff, standardAxioms := #[] }]

def checkFrontier : CommandElabM Unit := do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  for moduleName in modules do
    if (`Ix.Aiur).isPrefixOf moduleName || moduleName == `Blake3.Rust ||
        moduleName == `Ix.Claim ||
        ((`Ix.MultiStark).isPrefixOf moduleName && !(`Ix.MultiStark.Verify).isPrefixOf moduleName) then
      throwError m!"Pure Stage 2 audit imports a native/DSL boundary: {moduleName}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless (`Ix.MultiStark.Verify).isPrefixOf modules[index.toNat]! ||
        modules[index.toNat]! == `Ix.Ixby.Claim.Stage2 do continue
    match info with
    | .axiomInfo _ => throwError m!"Pure Stage 2 source declares an axiom: {name}"
    | .thmInfo _ =>
      count := count + 1
      for axiomName in ← Lean.collectAxioms name do
        unless standard.contains axiomName do
          throwError m!"Pure Stage 2 theorem {name} uses nonstandard axiom {axiomName}"
    | _ => pure ()
  logInfo m!"Pure Stage 2 source axiom frontier passed for {count} theorem declarations"

run_cmd Ix.Tc.Verify.Audit.check roots "Pure Stage 2 components"
run_cmd checkFrontier

end MultiStark.Verify.Audit
