import IxC.Kernel.Audit.Axioms
import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.FriVerifier
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.NativeCurveMsm
import Ix.Cert.Compression.RecursiveKzg
import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.EndToEnd

/-! # Certified Proof Compression Pipeline (`Ix.Cert.Compression`)

This umbrella module re-exports all eight modules of the certified proof-compression
pipeline and verifies their axiom boundaries:

1. `Ix.Cert.Compression.Plonkish`:
   Width-3 Plonkish intermediate representation (`Wire`, `Gate`, `TableSpec`, `LookupConstraint`,
   `Blake3Constraint`, `Circuit`), witness satisfiability (`Circuit.Satisfies`), and soundness
   of table trace merging (`mergeTableTraces_sound`) and sharded `multi-stark` lowering
   (`lowerToMultiStarkSharded_sound`).
2. `Ix.Cert.Compression.Foreign`:
   Goldilocks-in-`BN254::Fr` circuit-to-circuit compiler (`crates/proof-compression/src/foreign.rs`),
   primality certificate `bn254FrModulus_prime`, canonical 16-bit limb decomposition check
   (`canonical_iff_lt_goldilocksP`), direct and quotient gate soundness (`direct_gate_sound`,
   `quotient_gate_sound`), and universal compiler soundness (`foreign_compile_sound`,
   `foreign_compile_sound_lifted`).
3. `Ix.Cert.Compression.FriVerifier`:
   Stage-0 `FixedRoot` memory-segment range and `MEMSEG` boundary message soundness
   (`constrainMemoryEnd_sound`), Stage-1 fixed-shape batch STARK verifier circuit over
   Goldilocks (`friVerifierCircuit`), universal Stage-1 soundness (`fri_verifier_circuit_sound`),
   and Stage-2 first KZG circuit soundness (`first_kzg_circuit_sound`, `first_kzg_circuit_sound_raw`).
4. `Ix.Cert.Compression.NativeField`:
   Stage-3 non-native `BN254::Fq` 4×80-bit limb arithmetic in `BN254::Fr`
   (`crates/proof-compression/src/recursive/native_field.rs`), 20-bit lookup range bounds
   (`range20_limb80_bound`, `range20_carry89_bound`), paired-limb no-overflow
   (`paired_limb_no_overflow`), general modular relation soundness (`fq_relation_sound`,
   `fq_relation_four_pairs_sound`), and arithmetic/canonicality corollaries (`fq_add_sound`,
   `fq_sub_sound`, `fq_mul_sound`, `fq_inv_or_zero_sound`, `fq_equal_sound`,
   `fq_canonical_lt_q_sound`).
5. `Ix.Cert.Compression.NativeCurveMsm`:
   Stage-3 `BN254::G1` short-Weierstrass curve arithmetic and 4-bit windowed Straus MSM
   (`crates/proof-compression/src/recursive/native_curve.rs`, `native_msm.rs`), including
   `pointInput_sound`, `affine_add_sound`, `affine_double_sound`, `add_complete_sound`,
   `straus_loop_invariant`, `msm_sound`, and `msm_shifted_correction_sound`.
6. `Ix.Cert.Compression.RecursiveKzg`:
   Stage-3 Recursive KZG STARK verifier in `BN254::Fr` (`native_transcript.rs`,
   `native_verifier.rs`, `pairing.rs`), including `nativeTranscript_sample_lt_fr`,
   `decode_encode_pairing_limbs`, and universal Stage-3 soundness `recursive_kzg_circuit_sound`.
7. `Ix.Cert.Compression.OuterRelation`:
   Stage-4 declarative Outer Relation, 6-op scalar IR (`OuterIR`), and terminal BN254
   PLONK/Groth16 wrapper soundness (`final_export/ir.rs`, `tools/gnark/circuit.go`),
   including `OuterIR.inverseOrZero_sound`, `outer_ir_quotient_assertion_sound`,
   `outer_ir_build_sound`, `unpack_pack_digest_half`, `reconstructClaimFromPublics_eq`,
   `outer_wrapper_sound`, and `outer_to_stage2_kzg_sound`.
8. `Ix.Cert.Compression.EndToEnd`:
   End-to-end compression soundness connecting Stages 4 → 3 → 2 → 1 → 0 through
   `MultiStark::ix_aggr` and `Ix.Cert.IxVM.CircuitCorrespondence` to `IxC` kernel acceptance,
   ZFC `StrongModel` and `ValueModel` existence, logical consistency (`no_proof_of_False`),
   and quotient/nominal compiler commutation.
-/

#guard_module_axioms
  Ix.Cert.Compression.Plonkish
  Ix.Cert.Compression.Foreign
  Ix.Cert.Compression.FriVerifier
  Ix.Cert.Compression.NativeField
  Ix.Cert.Compression.NativeCurveMsm
  Ix.Cert.Compression.RecursiveKzg
  Ix.Cert.Compression.OuterRelation
  Ix.Cert.Compression.EndToEnd

#guard_kernel_axioms Ix.Cert.Compression.compressed_kzg_accepts_imp_normalized_root [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_plonk_accepts_imp_normalized_root [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_groth16_accepts_imp_normalized_root [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_accepts_iff_ixonAcceptsRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_valueModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_compile_commutes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.Compression.compressed_proof_compile_commutes_nominal [propext, Classical.choice, Quot.sound]
