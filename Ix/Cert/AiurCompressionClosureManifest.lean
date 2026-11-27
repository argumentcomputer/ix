import IxCK.Kernel.Audit.ClosureManifest
import Ix.Cert.AiurCompression.Audit

/-! # Definitional Closure Manifest of the Aiur Compression Statements, Pinned

`Ix.Cert.AiurCompression.Audit` freezes the printed statements of its theorems
(`#guard_msgs` on `#check`), which name definitions and hypothesis records by
name only: a change to the body of a definition or to the fields of a
structure a statement names leaves every such pin passing. This manifest pins
their meaning. Its roots are exactly the constants that audit's `#check`
commands name; every definition, inductive, constructor, recursor and statement
type reachable from them is canonically serialized and hashed with SHA-256
(`IxCK.Kernel.Audit.ClosureManifest`); theorem proofs are not entered. Any change
to the definitional closure changes the digest and fails the build of this
module.

Updating it (only with a reviewed change to the statements or the definitions
they name): build this module with
`IX_AIUR_COMPRESSION_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/aiur-compression-closure-manifest.txt`,
then update `pinnedDigest` below with the reported SHA-256 digest and commit both.
-/

namespace Ix.Cert.AiurCompressionClosureManifest

/-- The constants `Ix.Cert.AiurCompression.Audit` pins by `#check`. -/
def roots : Array Lean.Name := #[
  ``Ix.Cert.AiurCompression.aiur_compression_l3_bn254_sound,
  ``Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest,
  ``Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_consistent,
  ``Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_singleLayer_consistent,
  ``Ix.Cert.AiurCompression.Consistency.toyPairing_nontrivial,
  ``Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique,
  ``Ix.Cert.AiurCompression.aiur_scs_outer_sound,
  ``Ix.Cert.AiurCompression.aiurScs_rejects_wrong_public_limb,
  ``Ix.Cert.AiurCompression.aiurScs_rejects_noncanonical_output,
  ``Ix.Cert.AiurCompression.negControl_wrong_root_key_pin,
  ``Ix.Cert.AiurCompression.negControl_tampered_statement_words,
  ``Ix.Cert.AiurCompression.negControl_unpinned_manifest,
  ``Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering,
  ``Ix.Cert.AiurCompression.negControl_bls12381_torsion_rejected,
  ``Ix.Cert.AiurCompression.compressWrapProgram_exact_pinned,
  ``Ix.Cert.AiurCompression.compressGLProgram_exact_pinned,
  ``Ix.Cert.AiurCompression.kzgPackedTerminal_exact_pinned,
  ``Ix.Cert.AiurCompression.compressBN_exact_pinned,
  ``Ix.Cert.AiurCompression.compressBNPacked_exact_pinned,
  ``Ix.Cert.AiurCompression.kzgPackedDeserialize_exact_pinned,
  ``Ix.Cert.AiurCompression.finalSource_ok_spec,
  ``Ix.Cert.AiurCompression.exactPin_rejects_dropped_anchor_check,
  ``Ix.Cert.AiurCompression.moduleFunctionsExactPinned_implies_digest_eq,
  ``Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec,
  ``Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision,
  ``Ix.Cert.AiurCompression.rootClaimsBytesOfClaim_binds_or_collision,
  ``Ix.Cert.AiurCompression.WrapPolicySpec.claimsBytes_injective,
  ``Ix.Cert.AiurCompression.PackedPolicy.encode_injective,
  ``Ix.Cert.AiurCompression.manifestPinned_chain_integrity,
  ``Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound,
  ``Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound,
  ``Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous,
  ``Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound,
  ``Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound,
  ``Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous
]

/-- The committed text of the manifest, relative to the repository root. -/
def manifestPath : System.FilePath := "Tests/Fixtures/aiur-compression-closure-manifest.txt"

/-- The SHA-256 digest of the manifest's text (its lines, each followed by a newline).
Regenerate with `IX_AIUR_COMPRESSION_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/aiur-compression-closure-manifest.txt`. -/
def pinnedDigest : String := "c4ee3d97cd3dd98bee4aca78833a1f498d055a7d999e06750b7d207d1a7c4d12"

open Lean Elab Command in
elab "#check_closure_manifest" : command =>
  Ix.Kernel.Audit.ClosureManifest.checkClosureManifest
    roots manifestPath pinnedDigest "IX_AIUR_COMPRESSION_CLOSURE_MANIFEST_WRITE"

#check_closure_manifest

end Ix.Cert.AiurCompressionClosureManifest
