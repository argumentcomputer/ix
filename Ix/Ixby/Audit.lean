import Ix.Tc.Verify.Audit.Basic
import Ix.Ixby

/-!
# IxBy theorem trust manifest

Run with `lake build --wfail Ix.Ixby.Audit`. This audit is deliberately not
imported by the pure `Ix.Ixby` API or by the host proving adapter.

The exact allowances below cover the current logical/reference, codec, and
claim-composition proof roots. Retired backend adapters are not imported. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted: no upstream,
native, pending, or sorry allowances. Updating a proof's exact dependency set
requires an explicit manifest change.

The complementary source-module scan also rejects nonstandard axioms in
private/generated/unlisted theorems, and rejects new global axioms even when
no manifest root uses them. Its scope is the imported IxBy proof surface;
new proof modules must be imported here to join that surface.

The reused audit helper is a Lean-only leaf module; it imports no checker
proofs, compiler verification, or proving FFI. These checks audit logical
dependencies, not the separate native/compiler/AIR soundness obligations.
-/

namespace Ix.Ixby.Audit

open Lean Lean.Elab.Command Ix.Tc.Verify.Audit

private def standard : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
private def noChoice : Array Lean.Name := #[``propext, ``Quot.sound]

private def withAxioms (axioms : Array Lean.Name) (names : Array Lean.Name) : Array RootAllowance :=
  names.map fun root => { root, standardAxioms := axioms }

private def roots : Array RootAllowance :=
  withAxioms standard #[
    ``certified_execution,
    ``Codec.Execution.reference_evaluates,
    ``Codec.evaluates_execution,
    ``Claim.exec_public,
    ``Claim.Opening.bindings_or_collision,
    ``Claim.byte_refinement_of_value_refinement,
    ``Claim.Opening.source_or_collision,
    ``Claim.terminal_exec,
    ``Claim.terminal_source_or_collision,
    ``evaluates_deterministic,
    ``execute_add_fuel,
    ``Profile.execute_refines,
    ``refinement_of_forward_and_termination,
    ``run_add_fuel
  ] ++
  withAxioms noChoice #[
    ``Claim.public_bind,
    ``Blake3.hash_size
  ] ++
  withAxioms #[``propext] #[
    ``Goldilocks.reduce_canonical
  ] ++
  withAxioms #[] #[
    ``Codec.primitiveOpcode_decodes,
    ``Goldilocks.reduce_val
  ]

/-- Cover newly added and private/generated proof declarations as well as the
named manifest. Attribute declarations by source module, not their namespace,
so a macro cannot move an unexpected axiom outside the scanned namespace. -/
def checkAxiomFrontier : CommandElabM Unit := do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`Ix.Ixby).isPrefixOf modules[idx.toNat]! do continue
    match info with
    | .axiomInfo _ => throwError m!"IxBy source declares an axiom: {name}"
    | .thmInfo _ =>
      count := count + 1
      for axiomName in ← Lean.collectAxioms name do
        unless standard.contains axiomName do
          throwError m!"IxBy theorem {name} uses nonstandard axiom {axiomName}"
    | _ => pure ()
  logInfo m!"IxBy source axiom frontier passed for {count} theorem declarations"

run_cmd Ix.Tc.Verify.Audit.check roots "IxBy"
run_cmd checkAxiomFrontier

end Ix.Ixby.Audit
