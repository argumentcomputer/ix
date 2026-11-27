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
  ``Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps.inconsistent,
  ``Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps.inconsistent,
  ``Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest,
  ``Ix.Cert.AiurCompression.bls12381AiurEscape_false_on_honest,
  ``Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique,
  ``Ix.Cert.AiurCompression.negControl_wrong_root_key_pin,
  ``Ix.Cert.AiurCompression.negControl_tampered_statement_words,
  ``Ix.Cert.AiurCompression.negControl_cross_curve_downgrade,
  ``Ix.Cert.AiurCompression.negControl_protocol_downgrade,
  ``Ix.Cert.AiurCompression.negControl_unpinned_manifest,
  ``Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering,
  ``Ix.Cert.AiurCompression.compressWrapProgram_ast_pinned,
  ``Ix.Cert.AiurCompression.compressGLProgram_ast_pinned,
  ``Ix.Cert.AiurCompression.kzgPackedTerminal_ast_pinned,
  ``Ix.Cert.AiurCompression.compressBN_previous_ast_pinned,
  ``Ix.Cert.AiurCompression.compressBNPacked_fold_ast_pinned,
  ``Ix.Cert.AiurCompression.kzgPackedDeserialize_formats_ast_pinned,
  ``Ix.Cert.AiurCompression.finalSource_ok_spec,
  ``Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec,
  ``Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision,
  ``Ix.Cert.AiurCompression.PackedPolicy.encode_injective,
  ``Ix.Cert.AiurCompression.manifestPinned_chain_integrity,
  ``Ix.Cert.AiurCompression.aiurCompression128_v6_ud_bls12381_ok,
  ``Ix.Cert.AiurCompression.aiurCompression128_v6_johnson128_bls12381_ok,
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
def pinnedDigest : String := "c8b8b68c798b2d7de7ceceb26e42f2bd0823f7f60a1bb0c518bffb89f9393e24"

open Lean Elab Command in
elab "#check_closure_manifest" : command =>
  Ix.Kernel.Audit.ClosureManifest.checkClosureManifest
    roots manifestPath pinnedDigest "IX_AIUR_COMPRESSION_CLOSURE_MANIFEST_WRITE"

#check_closure_manifest

end Ix.Cert.AiurCompressionClosureManifest
