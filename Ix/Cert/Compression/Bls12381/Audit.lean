import Ix.Cert.Compression.Bls12381.EndToEnd

/-! # BLS12-381 Proof-Compression Audit Surface (`Ix.Cert.Compression.Bls12381.Audit`)

Pins every headline theorem signature and axiom dependency of the certified BLS12-381
proof-compression stack with `#guard_msgs`, certifying strictly standard Lean axioms
(`⊆ [propext, Classical.choice, Quot.sound]`, zero `sorry`, zero custom `axiom`,
zero `native_decide`, zero `bv_decide`).
-/

-- 1. Field Primality, 5×80-Bit Non-Native Fq Arithmetic & Foreign-Field FRI Verifier
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus_prime : Nat.Prime
  Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus_prime
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus_prime : Nat.Prime
  Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus_prime
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381_paired_limb_no_overflow : ∀ (eqEven eqOdd carryIn carryOut : ℤ),
  -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ eqEven →
    eqEven ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
      -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ eqOdd →
        eqOdd ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
          -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carryIn →
            carryIn ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
              -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carryOut →
                carryOut ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
                  (eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut) %
                        ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                      0 →
                    eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut = 0
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381_paired_limb_no_overflow
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381_fq_relation_five_pairs_sound : ∀
  (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 carry0 carry1 carry2 carry3 lhs qVal : ℤ),
  -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t0 →
    t0 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
      -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t1 →
        t1 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
          -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t2 →
            t2 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
              -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t3 →
                t3 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                  -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t4 →
                    t4 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                      -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t5 →
                        t5 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                          -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t6 →
                            t6 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                              -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t7 →
                                t7 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                                  -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t8 →
                                    t8 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                                      -Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound ≤ t9 →
                                        t9 ≤ Ix.Cert.Compression.Bls12381.Field.bls12381CoefficientBound →
                                          -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carry0 →
                                            carry0 ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
                                              -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carry1 →
                                                carry1 ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
                                                  -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carry2 →
                                                    carry2 ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
                                                      -Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS ≤ carry3 →
                                                        carry3 ≤ Ix.Cert.Compression.Bls12381.Field.CARRY_BIAS →
                                                          (t0 + 2 ^ 80 * t1 + 0 - 2 ^ 160 * carry0) %
                                                                ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                                                              0 →
                                                            (t2 + 2 ^ 80 * t3 + carry0 - 2 ^ 160 * carry1) %
                                                                  ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                                                                0 →
                                                              (t4 + 2 ^ 80 * t5 + carry1 - 2 ^ 160 * carry2) %
                                                                    ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                                                                  0 →
                                                                (t6 + 2 ^ 80 * t7 + carry2 - 2 ^ 160 * carry3) %
                                                                      ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                                                                    0 →
                                                                  (t8 + 2 ^ 80 * t9 + carry3 - 2 ^ 160 * 0) %
                                                                        ↑Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus =
                                                                      0 →
                                                                    t0 + 2 ^ 80 * t1 + 2 ^ 160 * t2 + 2 ^ 240 * t3 +
                                                                                    2 ^ 320 * t4 +
                                                                                  2 ^ 400 * t5 +
                                                                                2 ^ 480 * t6 +
                                                                              2 ^ 560 * t7 +
                                                                            2 ^ 640 * t8 +
                                                                          2 ^ 720 * t9 =
                                                                        lhs -
                                                                          qVal *
                                                                            ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus →
                                                                      lhs =
                                                                          qVal *
                                                                            ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus ∧
                                                                        lhs %
                                                                            ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus =
                                                                          0
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381_fq_relation_five_pairs_sound
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381_fq_canonical_lt_q_sound : ∀
  (v d : Ix.Cert.Compression.Bls12381.Field.Bls12381FqLimbs) (b0 b1 b2 b3 b4 : ℕ),
  v.LimbsLtRadix →
    d.LimbsLtRadix →
      b0 = 0 ∨ b0 = 1 →
        b1 = 0 ∨ b1 = 1 →
          b2 = 0 ∨ b2 = 1 →
            b3 = 0 ∨ b3 = 1 →
              b4 = 0 ∨ b4 = 1 →
                ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulusMinusOneLimbs.l0 - ↑v.l0 - 0 + 2 ^ 80 * ↑b0 -
                      ↑d.l0 =
                    0 →
                  ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulusMinusOneLimbs.l1 - ↑v.l1 - ↑b0 + 2 ^ 80 * ↑b1 -
                        ↑d.l1 =
                      0 →
                    ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulusMinusOneLimbs.l2 - ↑v.l2 - ↑b1 + 2 ^ 80 * ↑b2 -
                          ↑d.l2 =
                        0 →
                      ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulusMinusOneLimbs.l3 - ↑v.l3 - ↑b2 +
                              2 ^ 80 * ↑b3 -
                            ↑d.l3 =
                          0 →
                        ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulusMinusOneLimbs.l4 - ↑v.l4 - ↑b3 +
                                2 ^ 80 * ↑b4 -
                              ↑d.l4 =
                            0 →
                          b4 = 0 → v.Canonical
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381_fq_canonical_lt_q_sound
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_compile_sound_lifted : ∀
  (c : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (pub : List Ix.Cert.Compression.Foreign.GoldilocksF)
  (w_fr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  (Ix.Cert.Compression.Bls12381.Field.bls12381ForeignCompile c).Satisfies
      (Ix.Cert.Compression.Bls12381.Field.bls12381LiftPublicInputs pub) w_fr →
    c.Satisfies pub (Ix.Cert.Compression.Bls12381.Field.bls12381ProjectGoldilocksWire w_fr)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_compile_sound_lifted
/--
info: Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_friVerifier_sound : ∀
  (base : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
  (layout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
  (∀ s ∈ layout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
    ∀ (pub : List Ix.Cert.Compression.Foreign.GoldilocksF)
      (w_fr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
      (Ix.Cert.Compression.Bls12381.Field.bls12381ForeignCompile
              (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit base layout)).Satisfies
          (Ix.Cert.Compression.Bls12381.Field.bls12381LiftPublicInputs pub) w_fr →
        Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied base layout pub
          (Ix.Cert.Compression.Bls12381.Field.bls12381ProjectGoldilocksWire w_fr)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_friVerifier_sound

/-- info: 'Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus_prime
/-- info: 'Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus_prime
/--
info: 'Ix.Cert.Compression.Bls12381.Field.bls12381_fq_relation_five_pairs_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381_fq_relation_five_pairs_sound
/--
info: 'Ix.Cert.Compression.Bls12381.Field.bls12381_fq_canonical_lt_q_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381_fq_canonical_lt_q_sound
/--
info: 'Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_compile_sound_lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_compile_sound_lifted
/--
info: 'Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_friVerifier_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.Field.bls12381_foreign_friVerifier_sound

-- 2. Concrete Mathlib BLS12-381 G1 Curve, 64-Round Straus MSM & Mandatory Subgroup Check
/-- info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1 : Ix.Cert.Compression.Bls12381.CurveMsm.BLS12381G1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1
/--
info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineAddSpec_eq : ∀
  {p1 p2 p3 : Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineCoords}
  {slope : Ix.Cert.Compression.Bls12381.Field.Bls12381FqLimbs},
  Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p1 →
    Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p2 →
      Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p3 →
        Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineAddSpec p1 p2 p3 slope →
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p3 =
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.add
              (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p1)
              (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p2)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineAddSpec_eq
/--
info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineDoubleSpec_eq : ∀
  {p1 p3 : Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineCoords}
  {slope : Ix.Cert.Compression.Bls12381.Field.Bls12381FqLimbs},
  Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p1 →
    Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p3 →
      Ix.Cert.Compression.Bls12381.Field.evalLimbsInt p1.y % ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus ≠ 0 →
        Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineDoubleSpec p1 p3 slope →
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p3 =
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.smul 2
              (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineDoubleSpec_eq
/--
info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_sameX_neY_imp_neg : ∀
  {p1 p2 : Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineCoords},
  Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p1 →
    Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve p2 →
      (Ix.Cert.Compression.Bls12381.Field.evalLimbsInt p1.x - Ix.Cert.Compression.Bls12381.Field.evalLimbsInt p2.x) %
            ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus =
          0 →
        (Ix.Cert.Compression.Bls12381.Field.evalLimbsInt p1.y - Ix.Cert.Compression.Bls12381.Field.evalLimbsInt p2.y) %
              ↑Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus ≠
            0 →
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p2 =
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.neg
              (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.fromAffine p1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_sameX_neY_imp_neg
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_sound : ∀ (G : Ix.Cert.Compression.Bls12381.CurveMsm.BLS12381G1)
  (points : List G.Point) (h : G.Point) (rounds : List (List ℕ)),
  rounds.length = 64 →
    (∀ row ∈ rounds, row.length = points.length) →
      have acc64 := Ix.Cert.Compression.Bls12381.CurveMsm.bls12381StrausLoop G points h rounds;
      have scalars := Ix.Cert.Compression.Bls12381.CurveMsm.bls12381FoldWindowRows points.length rounds;
      acc64 = G.add (G.smul (16 ^ 64) h) (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381MsmEval G scalars points) ∧
        G.add acc64 (G.neg (G.smul (16 ^ 64) h)) =
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381MsmEval G scalars points
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_sound
/--
info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound : ∀
  {P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Curve.Point},
  Ix.Cert.Compression.Bls12381.CurveMsm.EndoSubgroupChecked P → Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup P
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound
/--
info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineSubgroupSpec_sound : ∀
  {p xp x2p : Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineCoords},
  Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381AffineSubgroupSpec p xp x2p →
    Ix.Cert.Compression.Bls12381.CurveMsm.EndoSubgroupChecked
        (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381FromAffine p) ∧
      Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381FromAffine p)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineSubgroupSpec_sound
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Generator_inPrimeSubgroup : Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup
  Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Generator
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Generator_inPrimeSubgroup
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_inPrimeSubgroup : ∀
  (G : Ix.Cert.Compression.Bls12381.CurveMsm.BLS12381G1) (scalars : List ℕ) (points : List G.Point),
  (∀ P ∈ points, G.InPrimeSubgroup P) →
    G.InPrimeSubgroup (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381MsmEval G scalars points)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_inPrimeSubgroup
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.three_dvd_bls12381G1Cofactor : 3 ∣
  Ix.Cert.Compression.Bls12381.Field.bls12381G1Cofactor
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.three_dvd_bls12381G1Cofactor
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup : ¬Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup
    Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup
/--
info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_fails_endoCheck : ¬Ix.Cert.Compression.Bls12381.CurveMsm.EndoSubgroupChecked
    Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_fails_endoCheck

/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineAddSpec_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineAddSpec_eq
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineDoubleSpec_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineDoubleSpec_eq
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_sameX_neY_imp_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_sameX_neY_imp_neg
/-- info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_sound
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineSubgroupSpec_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_affineSubgroupSpec_sound
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Generator_inPrimeSubgroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Generator_inPrimeSubgroup
/-- info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_inPrimeSubgroup' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_msm_inPrimeSubgroup
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup
/--
info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_fails_endoCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_fails_endoCheck

-- 3. 5-Channel Recursive KZG Verifier & Subgroup-Checked Pairing Soundness
/--
info: @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_batched_horner_bad_card : ∀
  {fs : List (Polynomial Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)}
  {ys : List Ix.Cert.Compression.Bls12381.Field.BLS12381Fr} (z : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (hlen : fs.length = ys.length),
  (∃ i, ∃ (hi : i < fs.length), Polynomial.eval z fs[i] ≠ ys[i]) →
    {γ |
          Ix.Cert.Compression.Bls12381.RecursiveKzg.hornerBlsFr γ
              (List.zipWith (fun f y => Polynomial.eval z f - y) fs ys) =
            0}.card ≤
      fs.length - 1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_batched_horner_bad_card
/--
info: @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381G1_smul_inj_fr : ∀
  {a b : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr},
  Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.smul a.val
        Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.generator =
      Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.smul b.val
        Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.generator →
    a = b
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381G1_smul_inj_fr
/--
info: Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairing_sound_at_bls12381G1 : ∀
  (τ z : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr) (F Q : Polynomial Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (comm W : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point),
  comm = Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381KzgCommit τ F →
    W = Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381KzgCommit τ Q →
      Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck comm W z τ →
        Polynomial.eval τ (F - (Polynomial.X - Polynomial.C z) * Q) = 0
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairing_sound_at_bls12381G1
/--
info: Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairingCheck_rejects_torsion : ∀
  (P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point) (z τ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck
        Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint P z τ ∧
    ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck P
        Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint z τ
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairingCheck_rejects_torsion
/--
info: Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_pairing_msm_sound : ∀
  (points : List Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point)
  (h : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point) (rounds : List (List ℕ)),
  rounds.length = 64 →
    (∀ row ∈ rounds, row.length = points.length) →
      (∀ P ∈ points, Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup P) →
        have acc64 :=
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381StrausLoop Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1
            points h rounds;
        have scalars := Ix.Cert.Compression.Bls12381.CurveMsm.bls12381FoldWindowRows points.length rounds;
        have res :=
          Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.add acc64
            (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.neg
              (Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.smul (16 ^ 64) h));
        res =
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381MsmEval Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1
              scalars points ∧
          Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup res
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_pairing_msm_sound
/--
info: Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_recursiveKzgCircuit_sound : ∀
  (base : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (layout : Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelLayout)
  (pub : List Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (w : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  (Ix.Cert.Compression.Bls12381.RecursiveKzg.buildBls12381RecursiveKzgCircuit base layout).Satisfies pub w →
    Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelSatisfied base layout pub w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_recursiveKzgCircuit_sound

/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_batched_horner_bad_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_batched_horner_bad_card
/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381G1_smul_inj_fr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381G1_smul_inj_fr
/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairing_sound_at_bls12381G1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairing_sound_at_bls12381G1
/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairingCheck_rejects_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairingCheck_rejects_torsion
/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_pairing_msm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_pairing_msm_sound
/--
info: 'Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_recursiveKzgCircuit_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_recursiveKzgCircuit_sound

-- 4. BLS12-381 "ix/outer-ir/v1" Outer Relation & Subgroup-Enforced Folded Pairing
/--
info: Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_empty_program_digest_matches_rust_go : { nodes := [],
      assertions := [], coefficients := [], witnesses := [] }.digest =
  [2, 217, 80, 48, 233, 36, 214, 43, 101, 220, 177, 23, 52, 150, 127, 84, 12, 221, 217, 3, 55, 213, 129, 132, 217, 15,
    2, 25, 125, 245, 167, 153]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_empty_program_digest_matches_rust_go
/--
info: @Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterProgram.encode_injective : ∀
  {p1 p2 : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterProgram},
  p1.FitsU32 → p2.FitsU32 → p1.encode = p2.encode → p1 = p2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterProgram.encode_injective
/--
info: @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_outer_relation_sound : ∀
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs}
  {PairingCheck : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs → Prop}
  (acc : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkOuterAccepted vk inp PairingCheck),
  acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode ∨
    ∃ out, vk.expectedProgram.Satisfied inp out ∧ PairingCheck out
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_outer_relation_sound
/--
info: @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_folded_pairing_bad_card : ∀ {GT : Type} [inst : CommGroup GT]
  [inst_1 : DecidableEq GT],
  (∀ (x : GT), x ^ Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus = 1) →
    ∀ {A B : GT}, ¬(A = 1 ∧ B = 1) → {ρ | A * B ^ ρ.val = 1}.card ≤ 1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_folded_pairing_bad_card
/--
info: Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_bad_card : ∀
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (left right d0 d1 : bp.G1),
  ¬(bp.AllInPrimeSubgroupG1 left right d0 d1 ∧
        bp.outerPairingVal outerKeys left right = 1 ∧ bp.deferredPairingVal deferredKeys d0 d1 = 1) →
    {ρ |
          Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0
            d1 ρ}.card ≤
      1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_bad_card
/--
info: Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_rejects_nonSubgroup : ∀
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (left right d0 d1 : bp.G1) (ρ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  ¬bp.AllInPrimeSubgroupG1 left right d0 d1 →
    ¬Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys left right d0 d1 ρ
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_rejects_nonSubgroup
/--
info: @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound : ∀
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs}
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (leftOf rightOf : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1)
  (ρ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (acc :
    Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out)
        (rightOf out) d0 d1 ρ),
  acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode ∨
    ∃ out,
      vk.expectedProgram.Satisfied inp out ∧
        bp.AllInPrimeSubgroupG1 (leftOf out) (rightOf out) d0 d1 ∧
          (bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1 ∧ bp.deferredPairingVal deferredKeys d0 d1 = 1 ∨
            Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out)
                (rightOf out) d0 d1 ρ ∧
              {ρ' |
                    Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys
                      (leftOf out) (rightOf out) d0 d1 ρ'}.card ≤
                1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound

/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_empty_program_digest_matches_rust_go' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_empty_program_digest_matches_rust_go
/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterProgram.encode_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterProgram.encode_injective
/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_outer_relation_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_outer_relation_sound
/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_folded_pairing_bad_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_folded_pairing_bad_card
/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_bad_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_bad_card
/-- info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_rejects_nonSubgroup' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_foldedPairingCheck_rejects_nonSubgroup
/--
info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound

-- 5. End-to-End BLS12-381 Pipeline Composition & Constructive Negative Controls
/--
info: @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_stageBindings_digest_injective : ∀ {d₁ d₂ : IxVM.Refinement.Digest}
  {friPub₁ friPub₂ : List Ix.Cert.Compression.Foreign.GoldilocksF}
  {kzgPub₁ kzgPub₂ : List Ix.Cert.Compression.Bls12381.Field.BLS12381Fr}
  {inp₁ inp₂ : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs},
  Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381StageBindings d₁ friPub₁ kzgPub₁ inp₁ →
    Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381StageBindings d₂ friPub₂ kzgPub₂ inp₂ →
      (∀ (i : Fin 8), inp₁.publics ↑i = inp₂.publics ↑i) → d₁ = d₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_stageBindings_digest_injective
/--
info: Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound : ∀
  (assumptions : Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381CryptoAssumptions)
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs}
  {PairingCheck : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs → Prop}
  (acc : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkOuterAccepted vk inp PairingCheck)
  (kzgBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (kzgLayout : Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelLayout)
  (kzgPub : List Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (wKzg : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  (Ix.Cert.Compression.Bls12381.RecursiveKzg.buildBls12381RecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg →
    ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
      (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
      (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
        ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
          (wFriFr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
          (Ix.Cert.Compression.Bls12381.Field.bls12381ForeignCompile
                  (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout)).Satisfies
              (Ix.Cert.Compression.Bls12381.Field.bls12381LiftPublicInputs friPub) wFriFr →
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
                                      ∀ (d : IxVM.Refinement.Digest),
                                        Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381StageBindings d friPub kzgPub
                                            inp →
                                          ∀ {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
                                            {result : Aiur.Value IxVM.F},
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
                                                                (Aiur.Circuit.RuleClaims
                                                                  (Aiur.Circuit.Message IxVM.F)))),
                                                          (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                                (Aiur.Circuit.Erasure.rawROM rom) root =
                                                              Except.ok () →
                                                            List.mapM
                                                                  (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom))
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
                                                                    Aiur.Circuit.RuleClaims
                                                                        (Aiur.Circuit.Message IxVM.F) →
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
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected),
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
                                                                        (Aiur.entryValues
                                                                          [IxVM.Refinement.digestValue d]) →
                                                                      Aiur.WireValue.decode specialized.program.enums
                                                                            output =
                                                                          some result →
                                                                        acc.outerProgram.encode ≠
                                                                              vk.expectedProgram.encode ∧
                                                                            Blake3.Pure.digest acc.outerProgram.encode =
                                                                              Blake3.Pure.digest
                                                                                vk.expectedProgram.encode ∨
                                                                          Ix.Cert.Compression.Bls12381.EndToEnd.bls12381CurveOk
                                                                              assumptions.frMod assumptions.fqMod
                                                                              assumptions.hasG1Cofactor
                                                                              assumptions.g1Cofactor ∧
                                                                            (∀ (i : Fin 8),
                                                                                inp.publics ↑i =
                                                                                  Ix.Cert.Compression.Bls12381.EndToEnd.digestWordBlsFr
                                                                                    d i) ∧
                                                                              (∃ out,
                                                                                  vk.expectedProgram.Satisfied inp out ∧
                                                                                    PairingCheck out) ∧
                                                                                Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelSatisfied
                                                                                    kzgBase kzgLayout kzgPub wKzg ∧
                                                                                  Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied
                                                                                      friBase friLayout friPub
                                                                                      (Ix.Cert.Compression.Bls12381.Field.bls12381ProjectGoldilocksWire
                                                                                        wFriFr) ∧
                                                                                    ∃ value heap calls,
                                                                                      Aiur.Generic.SourceSemantics.ObsFn
                                                                                          IxVM.source.world
                                                                                          IxVM.Refinement.verifyClaim
                                                                                          [IxVM.Refinement.digestValue
                                                                                              d]
                                                                                          [] value heap calls ∧
                                                                                        Aiur.Generic.SourceSemantics.CallsInROM
                                                                                            (compiled.traceROM rom)
                                                                                            calls ∧
                                                                                          P calls d
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound
/--
info: Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_folded_pairing_sound : ∀
  (assumptions : Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381CryptoAssumptions)
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs}
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (leftOf rightOf : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1)
  (ρ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (acc :
    Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out)
        (rightOf out) d0 d1 ρ)
  (kzgBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (kzgLayout : Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelLayout)
  (kzgPub : List Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (wKzg : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  (Ix.Cert.Compression.Bls12381.RecursiveKzg.buildBls12381RecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg →
    ∀ (friBase : Ix.Cert.Compression.Plonkish.Circuit Ix.Cert.Compression.Foreign.GoldilocksF)
      (friLayout : Ix.Cert.Compression.FriVerifier.FriVerifierLayout),
      (∀ s ∈ friLayout.merkleSteps, List.length s.2.1 = List.length s.2.2.1) →
        ∀ (friPub : List Ix.Cert.Compression.Foreign.GoldilocksF)
          (wFriFr : Ix.Cert.Compression.Plonkish.Wire → Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
          (Ix.Cert.Compression.Bls12381.Field.bls12381ForeignCompile
                  (Ix.Cert.Compression.FriVerifier.buildFriVerifierCircuit friBase friLayout)).Satisfies
              (Ix.Cert.Compression.Bls12381.Field.bls12381LiftPublicInputs friPub) wFriFr →
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
                                      ∀ (d : IxVM.Refinement.Digest),
                                        Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381StageBindings d friPub kzgPub
                                            inp →
                                          ∀ {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
                                            {result : Aiur.Value IxVM.F},
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
                                                                (Aiur.Circuit.RuleClaims
                                                                  (Aiur.Circuit.Message IxVM.F)))),
                                                          (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                                (Aiur.Circuit.Erasure.rawROM rom) root =
                                                              Except.ok () →
                                                            List.mapM
                                                                  (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom))
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
                                                                    Aiur.Circuit.RuleClaims
                                                                        (Aiur.Circuit.Message IxVM.F) →
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
                                                                          (Aiur.Optimized.Grouping.activeRules
                                                                            inspected),
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
                                                                        (Aiur.entryValues
                                                                          [IxVM.Refinement.digestValue d]) →
                                                                      Aiur.WireValue.decode specialized.program.enums
                                                                            output =
                                                                          some result →
                                                                        acc.outerProgram.encode ≠
                                                                              vk.expectedProgram.encode ∧
                                                                            Blake3.Pure.digest acc.outerProgram.encode =
                                                                              Blake3.Pure.digest
                                                                                vk.expectedProgram.encode ∨
                                                                          Ix.Cert.Compression.Bls12381.EndToEnd.bls12381CurveOk
                                                                              assumptions.frMod assumptions.fqMod
                                                                              assumptions.hasG1Cofactor
                                                                              assumptions.g1Cofactor ∧
                                                                            (∀ (i : Fin 8),
                                                                                inp.publics ↑i =
                                                                                  Ix.Cert.Compression.Bls12381.EndToEnd.digestWordBlsFr
                                                                                    d i) ∧
                                                                              (∃ out,
                                                                                  vk.expectedProgram.Satisfied inp out ∧
                                                                                    bp.AllInPrimeSubgroupG1 (leftOf out)
                                                                                        (rightOf out) d0 d1 ∧
                                                                                      (bp.outerPairingVal outerKeys
                                                                                              (leftOf out)
                                                                                              (rightOf out) =
                                                                                            1 ∧
                                                                                          bp.deferredPairingVal
                                                                                              deferredKeys d0 d1 =
                                                                                            1 ∨
                                                                                        Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck
                                                                                            bp outerKeys deferredKeys
                                                                                            (leftOf out) (rightOf out)
                                                                                            d0 d1 ρ ∧
                                                                                          {ρ' |
                                                                                                Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck
                                                                                                  bp outerKeys
                                                                                                  deferredKeys
                                                                                                  (leftOf out)
                                                                                                  (rightOf out) d0 d1
                                                                                                  ρ'}.card ≤
                                                                                            1)) ∧
                                                                                Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381FiveChannelSatisfied
                                                                                    kzgBase kzgLayout kzgPub wKzg ∧
                                                                                  Ix.Cert.Compression.FriVerifier.FriVerifierSatisfied
                                                                                      friBase friLayout friPub
                                                                                      (Ix.Cert.Compression.Bls12381.Field.bls12381ProjectGoldilocksWire
                                                                                        wFriFr) ∧
                                                                                    ∃ value heap calls,
                                                                                      Aiur.Generic.SourceSemantics.ObsFn
                                                                                          IxVM.source.world
                                                                                          IxVM.Refinement.verifyClaim
                                                                                          [IxVM.Refinement.digestValue
                                                                                              d]
                                                                                          [] value heap calls ∧
                                                                                        Aiur.Generic.SourceSemantics.CallsInROM
                                                                                            (compiled.traceROM rom)
                                                                                            calls ∧
                                                                                          P calls d
-/
#guard_msgs (whitespace := lax) in
set_option pp.deepTerms true in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_folded_pairing_sound
/--
info: Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_rejects_nonSubgroup_torsion_point : ∀
  (P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point) (z τ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionCoords.Canonical ∧
    Ix.Cert.Compression.Bls12381.CurveMsm.Bls12381OnCurve Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionCoords ∧
      Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint ≠ 0 ∧
        3 • Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint = 0 ∧
          ¬Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup
                Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint ∧
            ¬Ix.Cert.Compression.Bls12381.CurveMsm.EndoSubgroupChecked
                  Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint ∧
              ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck
                    Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint P z τ ∧
                ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck P
                    Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint z τ
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_rejects_nonSubgroup_torsion_point
/--
info: Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_bn254 : ∀ (hasCofactor : Bool) (cofactor : ℕ),
  ¬Ix.Cert.Compression.Bls12381.EndToEnd.bls12381CurveOk Ix.Cert.Compression.Foreign.bn254FrModulus
      Ix.Cert.Compression.NativeField.bn254FqModulus hasCofactor cofactor
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_bn254
/--
info: Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_missing_cofactor_check : ∀ (cofactor : ℕ),
  ¬Ix.Cert.Compression.Bls12381.EndToEnd.bls12381CurveOk Ix.Cert.Compression.Bls12381.Field.bls12381FrModulus
      Ix.Cert.Compression.Bls12381.Field.bls12381FqModulus false cofactor
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_missing_cofactor_check

/--
info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_stageBindings_digest_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_stageBindings_digest_injective
/--
info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound
/--
info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_folded_pairing_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_folded_pairing_sound
/--
info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_rejects_nonSubgroup_torsion_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_rejects_nonSubgroup_torsion_point
/-- info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_bn254' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_bn254
/-- info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_missing_cofactor_check' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_profile_rejects_missing_cofactor_check
