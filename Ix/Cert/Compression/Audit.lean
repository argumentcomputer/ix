import Ix.Cert.Compression.EndToEnd

/-! # Workstream 1C Proof-Compression Audit Surface (`Ix.Cert.Compression.Audit`)

Verifies that every headline theorem in the certified BN254 proof-compression
stack depends ONLY on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`,
zero `bv_decide`, zero custom axioms).
-/

-- 1C-i: Plonkish IR, Sharded Lowering, and Goldilocks-in-BN254 Foreign Compiler
/--
info: @Ix.Cert.Compression.Plonkish.lowerToMultiStarkSharded_sound : ∀ {F : Type} [inst : Field F]
  (c : Ix.Cert.Compression.Plonkish.Circuit F) (namespaceTag : F) (maxLogHeight tableHeight : ℕ) (pub : List F)
  (w : Ix.Cert.Compression.Plonkish.Wire → F),
  (Ix.Cert.Compression.Plonkish.lowerToMultiStarkSharded c namespaceTag maxLogHeight tableHeight).Satisfies pub w →
    c.Satisfies pub w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Plonkish.lowerToMultiStarkSharded_sound

/-- info: Ix.Cert.Compression.Foreign.bn254FrModulus_prime : Nat.Prime Ix.Cert.Compression.Foreign.bn254FrModulus -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Foreign.bn254FrModulus_prime

/--
info: Ix.Cert.Compression.Foreign.foreign_compile_sound : ∀
  (c : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (pub_fr : List Ix.Cert.Compression.Foreign.BN254Fr)
  (w_fr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
  (Ix.Cert.Compression.Foreign.foreignCompile c).Satisfies pub_fr w_fr →
    c.Satisfies
      (List.map
        (fun x => Ix.Cert.Compression.Foreign.GoldilocksF.ofNat (x.val % Ix.Cert.Compression.Foreign.goldilocksP))
        pub_fr)
      fun i => Ix.Cert.Compression.Foreign.GoldilocksF.ofNat ((w_fr i).val % Ix.Cert.Compression.Foreign.goldilocksP)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Foreign.foreign_compile_sound

/--
info: Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted : ∀
  (c : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (pub : List Ix.Cert.Compression.Foreign.GoldilocksF)
  (w_fr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
  (Ix.Cert.Compression.Foreign.foreignCompile c).Satisfies (Ix.Cert.Compression.Foreign.liftPublicInputs pub) w_fr →
    c.Satisfies pub fun i =>
      Ix.Cert.Compression.Foreign.GoldilocksF.ofNat ((w_fr i).val % Ix.Cert.Compression.Foreign.goldilocksP)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted

/-- info: 'Ix.Cert.Compression.Foreign.bn254FrModulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.Foreign.bn254FrModulus_prime
/-- info: 'Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.Foreign.foreign_compile_sound_lifted

-- 1C-ii: In-Circuit Goldilocks FRI Verifier & Foreign BN254 Lifting
/--
info: Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound : ∀
  (base : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (layout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
  (∀ s ∈ layout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
    ∀ (pub : List Ix.Cert.Compression.Foreign.GoldilocksF)
      (w : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.GoldilocksF),
      (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit base layout).Satisfies pub w →
        Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied base layout pub w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound

/--
info: Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound : ∀
  (base : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (layout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
  (∀ s ∈ layout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
    ∀ (pub : List Ix.Cert.Compression.Foreign.GoldilocksF)
      (w_fr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
      (Ix.Cert.Compression.Foreign.foreignCompile
              (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit base layout)).Satisfies
          (Ix.Cert.Compression.Foreign.liftPublicInputs pub) w_fr →
        Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied base layout pub
          (Ix.Cert.Compression.Foreign.projectGoldilocksWire w_fr)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound

/-- info: 'Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.FriVerifier.foreign_friVerifier_sound

-- 1C-iii: Non-Native BN254::Fq, Concrete Mathlib BN254::G1, 4-bit Straus MSM, & Recursive KZG
/-- info: Ix.Cert.Compression.NativeCurveMsm.bn254G1 : Ix.Cert.Compression.NativeCurveMsm.BN254G1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeCurveMsm.bn254G1

/--
info: @Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq : ∀
  {p1 p2 p3 : Ix.Cert.Compression.NativeCurveMsm.AffineCoords} {slope : Ix.Cert.Compression.NativeField.FqLimbs},
  Ix.Cert.Compression.NativeCurveMsm.OnCurve p1 →
    Ix.Cert.Compression.NativeCurveMsm.OnCurve p2 →
      Ix.Cert.Compression.NativeCurveMsm.OnCurve p3 →
        Ix.Cert.Compression.NativeCurveMsm.AffineAddSpec p1 p2 p3 slope →
          Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p3 =
            Ix.Cert.Compression.NativeCurveMsm.bn254G1.add (Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p1)
              (Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p2)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq

/--
info: @Ix.Cert.Compression.NativeCurveMsm.bn254_affineDoubleSpec_eq : ∀
  {p1 p3 : Ix.Cert.Compression.NativeCurveMsm.AffineCoords} {slope : Ix.Cert.Compression.NativeField.FqLimbs},
  Ix.Cert.Compression.NativeCurveMsm.OnCurve p1 →
    Ix.Cert.Compression.NativeCurveMsm.OnCurve p3 →
      Ix.Cert.Compression.NativeField.evalLimbsInt p1.y % ↑Ix.Cert.Compression.NativeField.bn254FqModulus ≠ 0 →
        Ix.Cert.Compression.NativeCurveMsm.AffineDoubleSpec p1 p3 slope →
          Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p3 =
            Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul 2 (Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_affineDoubleSpec_eq

/--
info: @Ix.Cert.Compression.NativeCurveMsm.bn254_sameX_neY_imp_neg : ∀
  {p1 p2 : Ix.Cert.Compression.NativeCurveMsm.AffineCoords},
  Ix.Cert.Compression.NativeCurveMsm.OnCurve p1 →
    Ix.Cert.Compression.NativeCurveMsm.OnCurve p2 →
      (Ix.Cert.Compression.NativeField.evalLimbsInt p1.x - Ix.Cert.Compression.NativeField.evalLimbsInt p2.x) %
            ↑Ix.Cert.Compression.NativeField.bn254FqModulus =
          0 →
        (Ix.Cert.Compression.NativeField.evalLimbsInt p1.y - Ix.Cert.Compression.NativeField.evalLimbsInt p2.y) %
              ↑Ix.Cert.Compression.NativeField.bn254FqModulus ≠
            0 →
          Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p2 =
            Ix.Cert.Compression.NativeCurveMsm.bn254G1.neg (Ix.Cert.Compression.NativeCurveMsm.bn254G1.fromAffine p1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeCurveMsm.bn254_sameX_neY_imp_neg

/--
info: Ix.Cert.Compression.NativeCurveMsm.msm_sound : ∀ (G : Ix.Cert.Compression.NativeCurveMsm.BN254G1)
  (points : List G.Point) (h : G.Point) (rounds : List (List ℕ)),
  rounds.length = 64 →
    (∀ row ∈ rounds, row.length = points.length) →
      have acc64 := Ix.Cert.Compression.NativeCurveMsm.strausLoop G points h rounds;
      have scalars := Ix.Cert.Compression.NativeCurveMsm.foldWindowRows points.length rounds;
      acc64 = G.add (G.smul (16 ^ 64) h) (Ix.Cert.Compression.NativeCurveMsm.msmEval G scalars points) ∧
        G.add acc64 (G.neg (G.smul (16 ^ 64) h)) = Ix.Cert.Compression.NativeCurveMsm.msmEval G scalars points
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeCurveMsm.msm_sound

/--
info: @Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card : ∀
  {fs : List (Polynomial Ix.Cert.Compression.Foreign.BN254Fr)} {ys : List Ix.Cert.Compression.Foreign.BN254Fr}
  (z : Ix.Cert.Compression.Foreign.BN254Fr) (hlen : fs.length = ys.length),
  (∃ i, ∃ (hi : i < fs.length), Polynomial.eval z fs[i] ≠ ys[i]) →
    {γ |
          Ix.Cert.Compression.RecursiveKzg.hornerFr γ (List.zipWith (fun f y => Polynomial.eval z f - y) fs ys) =
            0}.card ≤
      fs.length - 1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card

/--
info: Ix.Cert.Compression.NativeField.fq_canonical_lt_q_sound : ∀ (v d : Ix.Cert.Compression.NativeField.FqLimbs)
  (b0 b1 b2 b3 : ℕ),
  v.LimbsLtRadix →
    d.LimbsLtRadix →
      b0 = 0 ∨ b0 = 1 →
        b1 = 0 ∨ b1 = 1 →
          b2 = 0 ∨ b2 = 1 →
            b3 = 0 ∨ b3 = 1 →
              ↑Ix.Cert.Compression.NativeField.fqModulusMinusOneLimbs.l0 - ↑v.l0 - 0 + 2 ^ 80 * ↑b0 - ↑d.l0 = 0 →
                ↑Ix.Cert.Compression.NativeField.fqModulusMinusOneLimbs.l1 - ↑v.l1 - ↑b0 + 2 ^ 80 * ↑b1 - ↑d.l1 = 0 →
                  ↑Ix.Cert.Compression.NativeField.fqModulusMinusOneLimbs.l2 - ↑v.l2 - ↑b1 + 2 ^ 80 * ↑b2 - ↑d.l2 = 0 →
                    ↑Ix.Cert.Compression.NativeField.fqModulusMinusOneLimbs.l3 - ↑v.l3 - ↑b2 + 2 ^ 80 * ↑b3 - ↑d.l3 =
                        0 →
                      b3 = 0 → v.Canonical
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.NativeField.fq_canonical_lt_q_sound

/--
info: Ix.Cert.Compression.RecursiveKzg.kzg_pairing_sound_at_bn254G1 : ∀ (τ z : Ix.Cert.Compression.Foreign.BN254Fr)
  (F Q : Polynomial Ix.Cert.Compression.Foreign.BN254Fr),
  Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul Ix.Cert.Compression.Foreign.bn254FrModulus
        Ix.Cert.Compression.NativeCurveMsm.bn254G1.generator =
      Ix.Cert.Compression.NativeCurveMsm.bn254G1.zero →
    Ix.Cert.Compression.NativeCurveMsm.bn254G1.add
          (Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul (Polynomial.eval τ F).val
            Ix.Cert.Compression.NativeCurveMsm.bn254G1.generator)
          (Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul z.val
            (Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul (Polynomial.eval τ Q).val
              Ix.Cert.Compression.NativeCurveMsm.bn254G1.generator)) =
        Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul τ.val
          (Ix.Cert.Compression.NativeCurveMsm.bn254G1.smul (Polynomial.eval τ Q).val
            Ix.Cert.Compression.NativeCurveMsm.bn254G1.generator) →
      Polynomial.eval τ (F - (Polynomial.X - Polynomial.C z) * Q) = 0
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.RecursiveKzg.kzg_pairing_sound_at_bn254G1

/--
info: Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound : ∀
  (base : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.BN254Fr)
  (layout : Ix.Cert.Compression.RecursiveKzg.FiveChannelLayout) (pub : List Ix.Cert.Compression.Foreign.BN254Fr)
  (w : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
  (Ix.Cert.Compression.RecursiveKzg.buildRecursiveKzgCircuit base layout).Satisfies pub w →
    Ix.Cert.Compression.RecursiveKzg.FiveChannelSatisfied base layout pub w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound

/-- info: 'Ix.Cert.Compression.NativeField.fq_canonical_lt_q_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.NativeField.fq_canonical_lt_q_sound
/-- info: 'Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.NativeCurveMsm.bn254_affineAddSpec_eq
/-- info: 'Ix.Cert.Compression.RecursiveKzg.kzg_pairing_sound_at_bn254G1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.RecursiveKzg.kzg_pairing_sound_at_bn254G1
/-- info: 'Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.RecursiveKzg.kzg_batched_horner_bad_card
/-- info: 'Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.RecursiveKzg.recursiveKzgCircuit_sound

-- 1C-iv: Canonical "ix/outer-ir/v1" BLAKE3 3-Way Parity, Folded Pairing & Gnark Outer-IR Soundness
/--
info: Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go : { nodes := [], assertions := [],
      coefficients := [], witnesses := [] }.digest =
  [2, 217, 80, 48, 233, 36, 214, 43, 101, 220, 177, 23, 52, 150, 127, 84, 12, 221, 217, 3, 55, 213, 129, 132, 217, 15,
    2, 25, 125, 245, 167, 153]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go

/--
info: Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go : Ix.Cert.Compression.OuterRelation.allOpsGoldenProgram.digest =
  [56, 65, 212, 110, 107, 87, 48, 208, 241, 217, 250, 186, 22, 7, 42, 44, 60, 174, 214, 108, 100, 248, 227, 46, 229,
    235, 219, 105, 165, 122, 43, 40]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go

/--
info: @Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound : ∀
  {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey} {inp : Ix.Cert.Compression.OuterRelation.OuterInputs}
  {PairingCheck : Ix.Cert.Compression.OuterRelation.OuterOutputs → Prop}
  (acc : Ix.Cert.Compression.OuterRelation.GnarkOuterAccepted vk inp PairingCheck),
  acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode ∨
    ∃ out, vk.expectedProgram.Satisfied inp out ∧ PairingCheck out
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound

/--
info: @Ix.Cert.Compression.OuterRelation.folded_pairing_bad_card : ∀ {GT : Type} [inst : CommGroup GT]
  [inst_1 : DecidableEq GT],
  (∀ (x : GT), x ^ Ix.Cert.Compression.Foreign.bn254FrModulus = 1) →
    ∀ {A B : GT}, ¬(A = 1 ∧ B = 1) → {ρ | A * B ^ ρ.val = 1}.card ≤ 1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.folded_pairing_bad_card

/--
info: Ix.Cert.Compression.OuterRelation.foldedPairingCheck_bad_card : ∀
  (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (left right d0 d1 : bp.G1),
  ¬(bp.outerPairingVal outerKeys left right = 1 ∧ bp.deferredPairingVal deferredKeys d0 d1 = 1) →
    {ρ | Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ}.card ≤ 1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.foldedPairingCheck_bad_card

/--
info: @Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound : ∀
  {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey} {inp : Ix.Cert.Compression.OuterRelation.OuterInputs}
  (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (leftOf rightOf : Ix.Cert.Compression.OuterRelation.OuterOutputs → bp.G1) (d0 d1 : bp.G1)
  (ρ : Ix.Cert.Compression.Foreign.BN254Fr)
  (acc :
    Ix.Cert.Compression.OuterRelation.GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1
        ρ),
  acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode ∨
    ∃ out,
      vk.expectedProgram.Satisfied inp out ∧
        (bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1 ∧ bp.deferredPairingVal deferredKeys d0 d1 = 1 ∨
          Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0
              d1 ρ ∧
            {ρ' |
                  Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys (leftOf out)
                    (rightOf out) d0 d1 ρ'}.card ≤
              1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound

/-- info: 'Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.empty_program_digest_matches_rust_go
/-- info: 'Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.allOps_golden_digest_matches_rust_go
/-- info: 'Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.gnark_outer_relation_sound
/-- info: 'Ix.Cert.Compression.OuterRelation.foldedPairingCheck_bad_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.foldedPairingCheck_bad_card
/-- info: 'Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound

-- 1C-v: Full Multi-Stage Proof-Compression Composition (Stage-Isolated Scaffold)
/--
info: @Ix.Cert.Compression.compression_pipeline_sound : ∀ {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.OuterRelation.OuterInputs}
  {PairingCheck : Ix.Cert.Compression.OuterRelation.OuterOutputs → Prop}
  (acc : Ix.Cert.Compression.OuterRelation.GnarkOuterAccepted vk inp PairingCheck)
  (kzgBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.BN254Fr)
  (kzgLayout : Ix.Cert.Compression.RecursiveKzg.FiveChannelLayout) (kzgPub : List Ix.Cert.Compression.Foreign.BN254Fr)
  (wKzg : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
  (Ix.Cert.Compression.RecursiveKzg.buildRecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg →
    ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
      (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
      (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
        ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
          (wFriFr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
          (Ix.Cert.Compression.Foreign.foreignCompile
                  (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout)).Satisfies
              (Ix.Cert.Compression.Foreign.liftPublicInputs friPub) wFriFr →
            ∀ {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
              IxVM.Refinement.CircuitSound P →
                ∀ {id : String → Except String ℕ}
                  {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
                  (compiled : Aiur.Optimized.GenericArtifact specialized)
                  (physical : Aiur.Optimized.Physical.Prepared compiled.artifact) {cfg : Aiur.Optimized.Depth.Config},
                  Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg →
                    cfg.bits ≤ 24 →
                      ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
                        plan.WellFormedActivation →
                          ∀ {rom : Aiur.WidthROM IxVM.F},
                            rom.entries.length ≤ 2 ^ 39 →
                              ∀ (ivlsOf : ℕ → List (ℕ × ℕ)),
                                (∀ (w : ℕ), Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w)) →
                                  (∀ (w : ℕ),
                                      ∑ x,
                                            (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x))
                                                rom.entries).length +
                                          1 <
                                        CertiFri.P3.Goldilocks.order) →
                                    (∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
                                        ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                                              ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1))
                                                    rom.entries).length +
                                            Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                                          0) →
                                      ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)}
                                        {output : Aiur.WireValue IxVM.F} {result : Aiur.Value IxVM.F},
                                        Aiur.Circuit.Erasure.Signed compiled.system
                                            { channel := IxVM.Refinement.verifyClaim, args := wires,
                                              result := output } →
                                          ∀ {root : Aiur.Circuit.Message IxVM.F},
                                            Aiur.Optimized.Depth.erase cfg root =
                                                Aiur.Circuit.Erasure.message compiled.system
                                                  { channel := IxVM.Refinement.verifyClaim, args := wires,
                                                    result := output } →
                                              root.channel ∉ cfg.names →
                                                ∀ (rows : List (Aiur.Circuit.Row IxVM.F)),
                                                  rows.length ≤ 2 ^ 39 →
                                                    ∀
                                                      (inspected :
                                                        List
                                                          (Option
                                                            (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F)))),
                                                      (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                            (Aiur.Circuit.Erasure.rawROM rom) root =
                                                          Except.ok () →
                                                        List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom))
                                                              rows =
                                                            Except.ok inspected →
                                                          (Aiur.Circuit.Balance.required
                                                                  (fun c =>
                                                                    decide
                                                                      ((Aiur.Optimized.Depth.system cfg
                                                                            physical.system).MapClaim
                                                                        c))
                                                                  root
                                                                  (Aiur.Optimized.Grouping.activeRules
                                                                    inspected)).length <
                                                              CertiFri.P3.Goldilocks.order →
                                                            ∀
                                                              (provWeight :
                                                                Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F) →
                                                                  Ix.Cert.MultiStark.Fp),
                                                              (∀
                                                                  claim ∈
                                                                    Aiur.Circuit.Balance.required
                                                                      (fun c =>
                                                                        decide
                                                                          ((Aiur.Optimized.Depth.system cfg
                                                                                physical.system).MapClaim
                                                                            c))
                                                                      root
                                                                      (Aiur.Optimized.Grouping.activeRules inspected),
                                                                  (List.map provWeight
                                                                        (List.filter (fun r => decide (r.1 = claim))
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected))).sum =
                                                                    ↑(List.countP (fun x => decide (x = claim))
                                                                        (Aiur.Circuit.Balance.required
                                                                          (fun c =>
                                                                            decide
                                                                              ((Aiur.Optimized.Depth.system cfg
                                                                                    physical.system).MapClaim
                                                                                c))
                                                                          root
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected)))) →
                                                                Aiur.DecodesValues specialized.program.enums wires
                                                                    (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                                                                  Aiur.WireValue.decode specialized.program.enums
                                                                        output =
                                                                      some result →
                                                                    acc.outerProgram.encode ≠
                                                                          vk.expectedProgram.encode ∧
                                                                        Blake3.Pure.digest acc.outerProgram.encode =
                                                                          Blake3.Pure.digest vk.expectedProgram.encode ∨
                                                                      (∃ out,
                                                                          vk.expectedProgram.Satisfied inp out ∧
                                                                            PairingCheck out) ∧
                                                                        Ix.Cert.Compression.RecursiveKzg.FiveChannelSatisfied
                                                                            kzgBase kzgLayout kzgPub wKzg ∧
                                                                          Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied
                                                                              friBase friLayout friPub
                                                                              (Ix.Cert.Compression.Foreign.projectGoldilocksWire
                                                                                wFriFr) ∧
                                                                            ∃ value heap calls,
                                                                              Aiur.Generic.SourceSemantics.ObsFn
                                                                                  IxVM.source.world
                                                                                  IxVM.Refinement.verifyClaim
                                                                                  [IxVM.Refinement.digestValue d] []
                                                                                  value heap calls ∧
                                                                                Aiur.Generic.SourceSemantics.CallsInROM
                                                                                    (compiled.traceROM rom) calls ∧
                                                                                  P calls d
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Ix.Cert.Compression.compression_pipeline_sound

/--
info: @Ix.Cert.Compression.compression_pipeline_folded_pairing_sound : ∀
  {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey} {inp : Ix.Cert.Compression.OuterRelation.OuterInputs}
  (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (leftOf rightOf : Ix.Cert.Compression.OuterRelation.OuterOutputs → bp.G1) (d0 d1 : bp.G1)
  (ρ : Ix.Cert.Compression.Foreign.BN254Fr)
  (acc :
    Ix.Cert.Compression.OuterRelation.GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ)
  (kzgBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.BN254Fr)
  (kzgLayout : Ix.Cert.Compression.RecursiveKzg.FiveChannelLayout) (kzgPub : List Ix.Cert.Compression.Foreign.BN254Fr)
  (wKzg : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
  (Ix.Cert.Compression.RecursiveKzg.buildRecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg →
    ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
      (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
      (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
        ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
          (wFriFr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Foreign.BN254Fr),
          (Ix.Cert.Compression.Foreign.foreignCompile
                  (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout)).Satisfies
              (Ix.Cert.Compression.Foreign.liftPublicInputs friPub) wFriFr →
            ∀ {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
              IxVM.Refinement.CircuitSound P →
                ∀ {id : String → Except String ℕ}
                  {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
                  (compiled : Aiur.Optimized.GenericArtifact specialized)
                  (physical : Aiur.Optimized.Physical.Prepared compiled.artifact) {cfg : Aiur.Optimized.Depth.Config},
                  Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg →
                    cfg.bits ≤ 24 →
                      ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
                        plan.WellFormedActivation →
                          ∀ {rom : Aiur.WidthROM IxVM.F},
                            rom.entries.length ≤ 2 ^ 39 →
                              ∀ (ivlsOf : ℕ → List (ℕ × ℕ)),
                                (∀ (w : ℕ), Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w)) →
                                  (∀ (w : ℕ),
                                      ∑ x,
                                            (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x))
                                                rom.entries).length +
                                          1 <
                                        CertiFri.P3.Goldilocks.order) →
                                    (∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
                                        ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                                              ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1))
                                                    rom.entries).length +
                                            Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                                          0) →
                                      ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)}
                                        {output : Aiur.WireValue IxVM.F} {result : Aiur.Value IxVM.F},
                                        Aiur.Circuit.Erasure.Signed compiled.system
                                            { channel := IxVM.Refinement.verifyClaim, args := wires,
                                              result := output } →
                                          ∀ {root : Aiur.Circuit.Message IxVM.F},
                                            Aiur.Optimized.Depth.erase cfg root =
                                                Aiur.Circuit.Erasure.message compiled.system
                                                  { channel := IxVM.Refinement.verifyClaim, args := wires,
                                                    result := output } →
                                              root.channel ∉ cfg.names →
                                                ∀ (rows : List (Aiur.Circuit.Row IxVM.F)),
                                                  rows.length ≤ 2 ^ 39 →
                                                    ∀
                                                      (inspected :
                                                        List
                                                          (Option
                                                            (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F)))),
                                                      (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                            (Aiur.Circuit.Erasure.rawROM rom) root =
                                                          Except.ok () →
                                                        List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom))
                                                              rows =
                                                            Except.ok inspected →
                                                          (Aiur.Circuit.Balance.required
                                                                  (fun c =>
                                                                    decide
                                                                      ((Aiur.Optimized.Depth.system cfg
                                                                            physical.system).MapClaim
                                                                        c))
                                                                  root
                                                                  (Aiur.Optimized.Grouping.activeRules
                                                                    inspected)).length <
                                                              CertiFri.P3.Goldilocks.order →
                                                            ∀
                                                              (provWeight :
                                                                Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F) →
                                                                  Ix.Cert.MultiStark.Fp),
                                                              (∀
                                                                  claim ∈
                                                                    Aiur.Circuit.Balance.required
                                                                      (fun c =>
                                                                        decide
                                                                          ((Aiur.Optimized.Depth.system cfg
                                                                                physical.system).MapClaim
                                                                            c))
                                                                      root
                                                                      (Aiur.Optimized.Grouping.activeRules inspected),
                                                                  (List.map provWeight
                                                                        (List.filter (fun r => decide (r.1 = claim))
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected))).sum =
                                                                    ↑(List.countP (fun x => decide (x = claim))
                                                                        (Aiur.Circuit.Balance.required
                                                                          (fun c =>
                                                                            decide
                                                                              ((Aiur.Optimized.Depth.system cfg
                                                                                    physical.system).MapClaim
                                                                                c))
                                                                          root
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected)))) →
                                                                Aiur.DecodesValues specialized.program.enums wires
                                                                    (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                                                                  Aiur.WireValue.decode specialized.program.enums
                                                                        output =
                                                                      some result →
                                                                    acc.outerProgram.encode ≠
                                                                          vk.expectedProgram.encode ∧
                                                                        Blake3.Pure.digest acc.outerProgram.encode =
                                                                          Blake3.Pure.digest vk.expectedProgram.encode ∨
                                                                      (∃ out,
                                                                          vk.expectedProgram.Satisfied inp out ∧
                                                                            (bp.outerPairingVal outerKeys (leftOf out)
                                                                                    (rightOf out) =
                                                                                  1 ∧
                                                                                bp.deferredPairingVal deferredKeys d0
                                                                                    d1 =
                                                                                  1 ∨
                                                                              Ix.Cert.Compression.OuterRelation.FoldedPairingCheck
                                                                                  bp outerKeys deferredKeys (leftOf out)
                                                                                  (rightOf out) d0 d1 ρ ∧
                                                                                {ρ' |
                                                                                      Ix.Cert.Compression.OuterRelation.FoldedPairingCheck
                                                                                        bp outerKeys deferredKeys
                                                                                        (leftOf out) (rightOf out) d0 d1
                                                                                        ρ'}.card ≤
                                                                                  1)) ∧
                                                                        Ix.Cert.Compression.RecursiveKzg.FiveChannelSatisfied
                                                                            kzgBase kzgLayout kzgPub wKzg ∧
                                                                          Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied
                                                                              friBase friLayout friPub
                                                                              (Ix.Cert.Compression.Foreign.projectGoldilocksWire
                                                                                wFriFr) ∧
                                                                            ∃ value heap calls,
                                                                              Aiur.Generic.SourceSemantics.ObsFn
                                                                                  IxVM.source.world
                                                                                  IxVM.Refinement.verifyClaim
                                                                                  [IxVM.Refinement.digestValue d] []
                                                                                  value heap calls ∧
                                                                                Aiur.Generic.SourceSemantics.CallsInROM
                                                                                    (compiled.traceROM rom) calls ∧
                                                                                  P calls d
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Ix.Cert.Compression.compression_pipeline_folded_pairing_sound

/-- info: 'Ix.Cert.Compression.compression_pipeline_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.Compression.compression_pipeline_sound
/-- info: 'Ix.Cert.Compression.compression_pipeline_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Compression.compression_pipeline_folded_pairing_sound
