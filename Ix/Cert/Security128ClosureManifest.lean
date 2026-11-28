import IxCK.Kernel.Audit.Axioms
import IxCK.Kernel.Audit.ClosureManifest
import Ix.Cert.MultiStark.Security128Audit
import Ix.Cert.Aggr.Security128Audit
import Ix.Cert.Compression.Security128Audit

/-! # Definitional Closure Manifest of the 128-Bit Security Audit Stack, Pinned

Pins the kernel-level definitional closure of every positive 128-bit security
theorem and constructive negative control across:
* `Ix.Cert.MultiStark.Security128Audit`
* `Ix.Cert.Aggr.Security128Audit`
* `Ix.Cert.Compression.Security128Audit`

Every definition, inductive, constructor, recursor, and referenced statement type
reachable from these roots is canonically serialized and hashed with SHA-256;
theorem proofs are not entered. Any change to the meaning of any 128-bit security
floor, parameter profile, curve modulus, or negative control changes the digest
and fails the build of this module.

Also verifies via `#guard_module_axioms` that every safe declaration in all three
`*Security128Audit` modules depends solely on `[propext, Classical.choice, Quot.sound]`.

Updating it (only with a reviewed change to the 128-bit security statements): build
this module with
`IX_SECURITY128_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/security-128-closure-manifest.txt`,
then update `pinnedDigest` below with the reported SHA-256 digest and commit both.
-/

#guard_module_axioms
  Ix.Cert.MultiStark.Security128Audit
  Ix.Cert.Aggr.Security128Audit
  Ix.Cert.Aggr.MonolithicRom
  Ix.Cert.Compression.Security128Audit
  Ix.Cert.Compression.StarkShrinker
  Ix.Cert.Compression.StarkShrinkerZk
  Ix.Cert.Compression.Bls12381.Field
  Ix.Cert.Compression.Bls12381.CurveMsm
  Ix.Cert.Compression.Bls12381.RecursiveKzg
  Ix.Cert.Compression.Bls12381.OuterRelation
  Ix.Cert.Compression.Bls12381.EndToEnd

namespace Ix.Cert.Security128ClosureManifest

/-- Pinned 128-bit security audit roots across MultiStark, Aggregation, and Compression
whose definitional closure is SHA-256 pinned: numerical parameter/digest inequalities,
negative controls, `CertiFRI`'s Horner-batched, binary tensor-batched, and multi-arity
(`2^a` / 8-ary) FRI + `GoldilocksExt3` pruned-MMCS STARK soundness and `v6-zk` HVZK
theorems, concrete `DynamicRom` `Fp^3` instantiations, abstract `MonolithicRom` /
`StarkShrinker` schemas, and schematic `Bls12381` stage models (not theorems about the
shipped Rust `v6` verifier, shrinker, or hand-written compression circuits). -/
def roots : Array Lean.Name := #[
  ``Ix.Cert.MultiStark.Security128.goldilocks_fp3_card_ge_2_pow_191,
  ``Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128,
  ``Ix.Cert.MultiStark.Security128.johnson_118_pow20_query_error_le_128,
  ``Ix.Cert.MultiStark.Security128.sponge_blake2b512_classical_collision_le_128,
  ``Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_128,
  ``Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_170,
  ``Ix.Cert.MultiStark.Security128.sponge_blake2b512_cns_quantum_204,
  ``Ix.Cert.MultiStark.Security128.sponge_blake2b512_grover_preimage_256,
  ``Ix.Cert.MultiStark.Security128.fp3_blake2b512_total_budget_le_128,
  ``Ix.Cert.MultiStark.Security128.v6_positive_128_profiles,
  ``Ix.Cert.MultiStark.Security128.negControl_fp2_rejected_128,
  ``Ix.Cert.MultiStark.Security128.negControl_v5_default_100_20_rejected_128,
  ``Ix.Cert.MultiStark.Security128.negControl_deceptive_4_55_0_rejected_128,
  ``Ix.Cert.MultiStark.Security128.negControl_digest32_rejected_128,
  ``Ix.Cert.MultiStark.Security128.negControl_digest48_xof_rejected_128,
  ``Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensor_fp3_ud,
  ``Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensorMulti_fp3_ud,
  ``CertiFri.P3.Blake2b.kat_empty_hex,
  ``CertiFri.P3.Blake2b.kat_abc_hex,
  ``CertiFri.P3.Blake2b.kat_exact128_hex,
  ``CertiFri.P3.Blake2b.kat_hashPair64_exact128,
  ``CertiFri.P3.Blake2b.kat_multi129_hex,
  ``CertiFri.P3.Blake2b.kat_personal_abc_hex,
  ``CertiFri.P3.Blake2b512Domain.initState_injective,
  ``CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk,
  ``CertiFri.P3.card_digest64,
  ``CertiFri.P3.Exec.curveListCA_fp3,
  ``CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128,
  ``CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional,
  ``CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional,
  ``CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional,
  ``CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional,
  ``CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional,
  ``CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128,
  ``CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128,
  ``CertiFri.P3.Blake3Domain.mode_injective,
  ``CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk,
  ``CertiFri.P3.GoldilocksExt3.starkModel,
  ``CertiFri.P3.GoldilocksExt3.rbrSound_starkTensor_ud,
  ``CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensor_johnson,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64,
  ``CertiFri.P3.GoldilocksExt3.rbrSound_starkTensorMulti_ud,
  ``CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced,
  ``CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk,
  ``CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake3,
  ``CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake2b512,
  ``CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake3,
  ``CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32,
  ``CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64,
  ``CertiFri.P3.Exec.v6Zk_alg_perfect_hvzk,
  ``CertiFri.P3.Exec.v6Zk_hvzk,
  ``CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk,
  ``CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_salt32,
  ``CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk,
  ``CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk_salt32,
  ``CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_with_tensor4_span,
  ``Ix.Cert.Aggr.Security128.securityEnvelope128Ok_implies_v5,
  ``Ix.Cert.Aggr.Security128.securityEnvelope128Ok_iff_profile,
  ``Ix.Cert.Aggr.Security128.v6_shape17_envelopes_ok,
  ``Ix.Cert.Aggr.Security128.aggr_shared_log_rom_bound_128,
  ``Ix.Cert.Aggr.Security128.aggr_johnson_128_union_headroom,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_fp2,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_protocol,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_32b_digest,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_48b_xof,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_weak_envelope,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_default_100_20,
  ``Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_deceptive_4_55_0,
  ``Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound,
  ``Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound,
  ``Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_rate_128,
  ``Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_blake2b512_concrete_prob_128,
  ``Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20,
  ``Ix.Cert.Compression.Security128.bls12381_curve_identities,
  ``Ix.Cert.Compression.Security128.bls12381_field_bounds,
  ``Ix.Cert.Compression.Security128.stark128Blake2b512_profile_ok,
  ``Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok,
  ``Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380,
  ``Ix.Cert.Compression.Security128.negControl_bn254_rejected_128,
  ``Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected,
  ``Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128,
  ``Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128,
  ``Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128,
  -- Schematic stage-isolated model over arbitrary circuits, not shipped Rust circuits.
  ``Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound,
  ``Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound,
  ``Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup,
  ``Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound
]

/-- The committed text of the manifest, relative to the repository root. -/
def manifestPath : System.FilePath := "Tests/Fixtures/security-128-closure-manifest.txt"

/-- The SHA-256 digest of the manifest's text (its lines, each followed by a newline).
Regenerate with `IX_SECURITY128_CLOSURE_MANIFEST_WRITE=Tests/Fixtures/security-128-closure-manifest.txt`. -/
def pinnedDigest : String := "86d4629a116fa06010e61267b146eb96b707e409f46ddc778117bed4027dcc6b"

open Lean Elab Command in
elab "#check_closure_manifest" : command =>
  Ix.Kernel.Audit.ClosureManifest.checkClosureManifest
    roots manifestPath pinnedDigest "IX_SECURITY128_CLOSURE_MANIFEST_WRITE"

#check_closure_manifest

end Ix.Cert.Security128ClosureManifest
