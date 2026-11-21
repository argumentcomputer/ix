import Ix.Cert.Compression.EndToEnd

/-! # Workstream 1C Proof-Compression Audit Surface (`Ix.Cert.Compression.Audit`)

Verifies that every headline theorem in the certified BN254 proof-compression
stack depends ONLY on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`,
zero `bv_decide`, zero custom axioms).
-/

-- 1C-i: Plonkish IR, Sharded Lowering, and Goldilocks-in-BN254 Foreign Compiler
#check @Ix.Cert.Compression.Plonkish.lowerToMultiStarkSharded_sound
#check @Ix.Cert.Compression.Foreign.bn254FrModulus_prime
#check @Ix.Cert.Compression.Foreign.foreign_compile_sound
#check @Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted
/-- info: 'Ix.Cert.Compression.Foreign.bn254FrModulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.Foreign.bn254FrModulus_prime
/-- info: 'Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted

-- 1C-ii: In-Circuit Goldilocks FRI Verifier & Foreign BN254 Lifting
#check @Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound
#check @Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound
/-- info: 'Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound

-- 1C-iii: Non-Native BN254::Fq, Concrete Mathlib BN254::G1, 4-bit Straus MSM, & Recursive KZG
#check @Ix.Cert.Compression.NativeCurveMsm.bn254G1
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_affineDoubleSpec_eq
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_sameX_neY_imp_neg
#check @Ix.Cert.Compression.NativeCurveMsm.msm_sound
#check @Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card
#check @Ix.Cert.Compression.RecursiveKzg.kzg_pairing_sound_at_bn254G1
#check @Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound
/-- info: 'Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq
/-- info: 'Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card
/-- info: 'Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound

-- 1C-iv: Canonical "ix/outer-ir/v1" BLAKE3 3-Way Parity & Gnark Outer-IR Soundness
#check @Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go
#check @Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go
#check @Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound
/-- info: 'Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go
/-- info: 'Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go
/-- info: 'Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound

-- 1C-v: Full Multi-Stage Proof-Compression Composition
#check @Ix.Cert.Compression.compression_pipeline_sound
/-- info: 'Ix.Cert.Compression.compression_pipeline_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.compression_pipeline_sound
