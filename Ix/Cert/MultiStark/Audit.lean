import Ix.Cert.MultiStark.EndToEnd
import Ix.Cert.MultiStark.Verifier

/-! # Workstream 1A-i Audit Surface (`Ix.Cert.MultiStark.Audit`)

Verifies that every headline theorem in the certified Multi-STARK / CertiFRI
stack depends ONLY on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`,
zero `bv_decide`, zero custom axioms).
-/

-- Gap 1a: Goldilocks field model & WellFormed
/--
info: Ix.Cert.MultiStark.goldilocksFieldModel : CertiFri.Exec.FieldModel CertiFri.P3.Goldilocks CertiFri.P3.GoldilocksExt3
  Ix.Cert.MultiStark.K
-/
#guard_msgs in #check @Ix.Cert.MultiStark.goldilocksFieldModel
/--
info: Ix.Cert.MultiStark.goldilocksWellFormed : ∀ (params : CertiFri.FriParams) (shape : CertiFri.Fri.ClaimShape),
  CertiFri.Fri.logMaxHeight params.logBlowup shape ≤ 32 →
    CertiFri.Exec.WellFormed Ix.Cert.MultiStark.goldilocksFieldModel params shape
-/
#guard_msgs in #check @Ix.Cert.MultiStark.goldilocksWellFormed
/-- info: 'Ix.Cert.MultiStark.goldilocksWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.goldilocksWellFormed

-- Gap 1b: BLAKE3 pure-specification parity
/--
info: Ix.Cert.MultiStark.blake3_eq_pure : ∀ (bytes : ByteArray),
  CertiFri.P3.blake3 bytes = { data := (Blake3.Pure.digest bytes.data.toList).toArray }
-/
#guard_msgs in #check @Ix.Cert.MultiStark.blake3_eq_pure
/--
info: Ix.Cert.MultiStark.hashPair_eq_pure : ∀ (a b : CertiFri.P3.Digest),
  (CertiFri.P3.Blake3.hashPair a b).toBytes =
    { data := (Blake3.Pure.digest (a.toBytes ++ b.toBytes).data.toList).toArray }
-/
#guard_msgs in #check @Ix.Cert.MultiStark.hashPair_eq_pure
/--
info: Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure : ∀ (row : Array CertiFri.P3.Goldilocks),
  (CertiFri.P3.baseHasher.hashRows row).toBytes =
    { data := (Blake3.Pure.digest (CertiFri.P3.Hashers.rowBytes row).data.toList).toArray }
-/
#guard_msgs in #check @Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure
/--
info: Ix.Cert.MultiStark.extHasher_hashRows_eq_pure : ∀ (row : Array CertiFri.P3.GoldilocksExt),
  (CertiFri.P3.extHasher.hashRows row).toBytes =
    { data := (Blake3.Pure.digest (CertiFri.P3.Hashers.extRowBytes row).data.toList).toArray }
-/
#guard_msgs in #check @Ix.Cert.MultiStark.extHasher_hashRows_eq_pure
/--
info: Ix.Cert.MultiStark.ext3Hasher_hashRows_eq_pure : ∀ (row : Array CertiFri.P3.GoldilocksExt3),
  (CertiFri.P3.ext3Hasher.hashRows row).toBytes =
    { data := (Blake3.Pure.digest (CertiFri.P3.Hashers.ext3RowBytes row).data.toList).toArray }
-/
#guard_msgs in #check @Ix.Cert.MultiStark.ext3Hasher_hashRows_eq_pure
/-- info: 'Ix.Cert.MultiStark.blake3_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.blake3_eq_pure
/-- info: 'Ix.Cert.MultiStark.hashPair_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.hashPair_eq_pure
/-- info: 'Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure
/-- info: 'Ix.Cert.MultiStark.extHasher_hashRows_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.extHasher_hashRows_eq_pure
/-- info: 'Ix.Cert.MultiStark.ext3Hasher_hashRows_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.ext3Hasher_hashRows_eq_pure

-- Gap 2: Shape-independent adaptive dynamic ROM & tightened round bounds
/--
info: @Ix.Cert.MultiStark.fractionLE_projectQueryIndex : ∀ {M h : ℕ},
  h ≤ M →
    ∀ {P : Fin (2 ^ h) → Prop} {ε : ℝ},
      CertiFri.Oracle.FractionLE P ε →
        CertiFri.Oracle.FractionLE (fun x => P (Ix.Cert.MultiStark.projectQueryIndex x)) ε
-/
#guard_msgs in #check @Ix.Cert.MultiStark.fractionLE_projectQueryIndex
/--
info: @Ix.Cert.MultiStark.settles_of_depends_on_digests : ∀ {Msg : Type} {Chal : ℕ → Type} {T D : Type}
  [inst : DecidableEq (CertiFri.Oracle.FSQuery Msg Chal (CertiFri.Oracle.HashQuery T D))] {Msg₂ : Type}
  (digestsOf : ℕ → Msg → List D) (r : ℕ)
  (interp : CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D) → ℕ → Msg → Msg₂),
  (∀ (l₁ l₂ : CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D)) (j : ℕ) (m : Msg),
      r ≤ j → interp l₁ j m = interp l₂ j m) →
    (∀ (l₁ l₂ : CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D)) (j : ℕ) (m : Msg),
        j < r →
          (∀ root ∈ digestsOf j m,
              ∀ (dims : Array CertiFri.Dimensions) (index : ℕ) (rows : Array (Array T)),
                CertiFri.Oracle.Opens l₁ root dims index rows ↔ CertiFri.Oracle.Opens l₂ root dims index rows) →
            interp l₁ j m = interp l₂ j m) →
      CertiFri.Oracle.Settles interp (CertiFri.Oracle.Hit digestsOf r)
-/
#guard_msgs in #check @Ix.Cert.MultiStark.settles_of_depends_on_digests
/--
info: @Ix.Cert.MultiStark.soundness_dynamic_rom : ∀ {Msg Msg₂ : Type} {Chal : ℕ → Type} {T D : Type}
  [inst : DecidableEq (CertiFri.Oracle.FSQuery Msg Chal (CertiFri.Oracle.HashQuery T D))]
  [inst_1 : (i : ℕ) → Fintype (Chal i)] [∀ (i : ℕ), Nonempty (Chal i)] [inst_3 : Fintype D] [Nonempty D] {α β : Type}
  {r M : ℕ} {digestsOf : ℕ → Msg → List D},
  (∀ (x : CertiFri.Oracle.FSQuery Msg Chal (CertiFri.Oracle.HashQuery T D)),
      (CertiFri.Oracle.chalDigests digestsOf r x).length ≤ M) →
    ∀ {doomed : (i : ℕ) → CertiFri.Oracle.Transcript Msg₂ Chal i → Prop}
      {interp : CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D) → ℕ → Msg → Msg₂} {ε : ℕ → ℝ}
      {εmax : ℝ},
      CertiFri.Oracle.RbrSound r doomed ε →
        (∀ i < r, ε i ≤ εmax) →
          0 ≤ εmax →
            doomed 0 CertiFri.Oracle.Transcript.nil →
              CertiFri.Oracle.Settles interp (CertiFri.Oracle.Hit digestsOf r) →
                ∀ {adv : CertiFri.Oracle.OracleComp (CertiFri.Oracle.MerkleAnswer Msg Chal T D) α} {Q : ℕ},
                  adv.QueryBound Q →
                    ∀ (msgs : α → ℕ → Msg)
                      {rest :
                        α × CertiFri.Oracle.Transcript Msg Chal r →
                          CertiFri.Oracle.OracleComp (CertiFri.Oracle.MerkleAnswer Msg Chal T D) β}
                      {R : ℕ},
                      (∀ (out : α × CertiFri.Oracle.Transcript Msg Chal r), (rest out).QueryBound R) →
                        ∀ {E : β → CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D) → Prop},
                          (∀ (out : α × CertiFri.Oracle.Transcript Msg Chal r)
                              (l : CertiFri.Oracle.Log (CertiFri.Oracle.FSAnswer Chal fun x => D)) (b : β)
                              (l' : CertiFri.Oracle.Log (CertiFri.Oracle.MerkleAnswer Msg Chal T D)),
                              (CertiFri.Oracle.fsExperiment r adv msgs).Outcome [] out l →
                                (rest out).Outcome l b l' →
                                  E b l' →
                                    ¬CertiFri.Oracle.HasBad (CertiFri.Oracle.Hit digestsOf r) l' →
                                      ¬doomed r (CertiFri.Oracle.Transcript.mapIdx (interp l') out.2)) →
                            CertiFri.Oracle.OracleComp.prob E ((CertiFri.Oracle.fsExperiment r adv msgs).bind rest) [] ≤
                              (↑Q + ↑r + ↑R) * εmax + ↑(max M 3 + 3) * (↑Q + ↑r + ↑R) ^ 2 / (4 * ↑(Fintype.card D))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.soundness_dynamic_rom
/--
info: Ix.Cert.MultiStark.fractionLE_zeta_in_domain_or_shift : ∀ (D : Finset Ix.Cert.MultiStark.K) {g : Ix.Cert.MultiStark.K},
  g ≠ 0 → CertiFri.Oracle.FractionLE (fun ζ => ζ ∈ D ∨ ζ * g ∈ D) (2 * ↑D.card / ↑(Fintype.card Ix.Cert.MultiStark.K))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.fractionLE_zeta_in_domain_or_shift
/--
info: Ix.Cert.MultiStark.fractionLE_zeta_ood : ∀ (D : Finset Ix.Cert.MultiStark.K) {g : Ix.Cert.MultiStark.K},
  g ≠ 0 →
    ∀ {P : Polynomial Ix.Cert.MultiStark.K} {d : ℕ},
      P ≠ 0 →
        P.natDegree ≤ d →
          CertiFri.Oracle.FractionLE (fun ζ => (ζ ∈ D ∨ ζ * g ∈ D) ∨ Polynomial.eval ζ P = 0)
            (↑(2 * D.card + d) / ↑(Fintype.card Ix.Cert.MultiStark.K))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.fractionLE_zeta_ood
/--
info: @Ix.Cert.MultiStark.fractionLE_logup_beta : ∀ {α : Type u_1} [DecidableEq α] {S : Finset α}
  {fp w : α → Ix.Cert.MultiStark.K} {m₀ : α},
  m₀ ∈ S →
    w m₀ ≠ 0 →
      (∀ m' ∈ S, m' ≠ m₀ → fp m' ≠ fp m₀) →
        CertiFri.Oracle.FractionLE (fun β => (∀ m ∈ S, β + fp m ≠ 0) ∧ ∑ m ∈ S, w m * (β + fp m)⁻¹ = 0)
          (↑(S.card - 1) / ↑(Fintype.card Ix.Cert.MultiStark.K))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.fractionLE_logup_beta
/--
info: @Ix.Cert.MultiStark.fractionLE_logup_pair : ∀ {α : Type u_1} [DecidableEq α] {S : Finset α}
  {args : α → List Ix.Cert.MultiStark.Fp} {w : α → Ix.Cert.MultiStark.K} {maxArity : ℕ} {m₀ : α},
  m₀ ∈ S →
    w m₀ ≠ 0 →
      (∀ m ∈ S, (args m).length ≤ maxArity) →
        (∀ m' ∈ S,
            m' ≠ m₀ → Ix.Cert.MultiStark.fingerprintPoly (args m') ≠ Ix.Cert.MultiStark.fingerprintPoly (args m₀)) →
          CertiFri.Oracle.FractionLE
            (fun p =>
              (∀ m ∈ S, p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m) ≠ 0) ∧
                ∑ m ∈ S, w m * (p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m))⁻¹ = 0)
            (↑((S.card - 1) * (maxArity + 1)) / ↑(Fintype.card Ix.Cert.MultiStark.K))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.fractionLE_logup_pair
/-- info: 'Ix.Cert.MultiStark.fractionLE_projectQueryIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_projectQueryIndex
/-- info: 'Ix.Cert.MultiStark.soundness_dynamic_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.soundness_dynamic_rom
/-- info: 'Ix.Cert.MultiStark.fractionLE_zeta_in_domain_or_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_zeta_in_domain_or_shift
/-- info: 'Ix.Cert.MultiStark.fractionLE_zeta_ood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_zeta_ood
/-- info: 'Ix.Cert.MultiStark.fractionLE_logup_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_logup_beta
/-- info: 'Ix.Cert.MultiStark.fractionLE_logup_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_logup_pair

-- Gap 3: Unconditional ROM soundness for Plonky3 pruned MMCS
/--
info: @Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding : ∀ {F EF D K : Type} [inst : CertiFri.FieldOps F]
  [inst_1 : CertiFri.FieldOps EF] [inst_2 : CertiFri.TwoAdicOps F] [inst_3 : CertiFri.ExtensionOps F EF]
  [inst_4 : Field K] [inst_5 : DecidableEq K] [inst_6 : DecidableEq D] [inst_7 : Inhabited D]
  (m : CertiFri.Exec.FieldModel F EF K) (params : CertiFri.FriParams) (shape : CertiFri.Fri.ClaimShape)
  (wf : CertiFri.Exec.WellFormed m params shape) [inst_8 : DecidableEq F] [inst_9 : DecidableEq EF]
  [inst_10 : Fintype K] [inst_11 : Fintype D],
  params.logFinalHeight ≤ CertiFri.Fri.logMaxHeight params.logBlowup shape →
    ∀ {δ : ℝ},
      0 ≤ δ →
        2 * δ + (1 / 2) ^ params.logBlowup ≤ 1 →
          ∀ {εmax : ℝ},
            ↑(CertiFri.Fri.claimRefs params.logBlowup shape).length *
                    ((1 + δ) * 2 ^ CertiFri.Fri.logMaxHeight params.logBlowup shape) /
                  ↑(Fintype.card K) ≤
                εmax →
              (1 + δ) * 2 ^ CertiFri.Fri.logMaxHeight params.logBlowup shape / ↑(Fintype.card K) /
                    2 ^ params.commitPowBits ≤
                  εmax →
                (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax →
                  ∀ {A : Type u_1} {adv : CertiFri.Oracle.OracleComp (CertiFri.Exec.OracleAnswer m params shape wf) A}
                    {Q : ℕ},
                    adv.QueryBound Q →
                      ∀ (attempt : A → Ix.Cert.MultiStark.PrunedAttempt F EF D),
                        CertiFri.Oracle.OracleComp.prob
                            (fun res l =>
                              (∃ f,
                                  (∀
                                      (x :
                                        CertiFri.Oracle.FSQuery (CertiFri.Exec.RawMsg F EF D)
                                          (CertiFri.PcsRbr.GrindChal (CertiFri.Exec.powBits params shape)
                                            (CertiFri.PcsRbr.Chal (CertiFri.Exec.modelParams m params shape wf).ldt
                                              (CertiFri.Exec.modelParams m params shape wf).queries))
                                          (CertiFri.Oracle.HashQuery K D))
                                      (y : CertiFri.Exec.OracleAnswer m params shape wf x),
                                      List.dlookup x l = some y → f x = y) ∧
                                    Ix.Cert.MultiStark.acceptsPruned m params shape wf f (attempt res.1) = true) ∧
                                CertiFri.PcsRbr.ClaimsFail (CertiFri.Exec.modelParams m params shape wf).ldt
                                  (CertiFri.Exec.modelParams m params shape wf).shift (1 - δ)
                                  ((CertiFri.Exec.modelParams m params shape wf).claims
                                    (CertiFri.Exec.view m params shape
                                      (CertiFri.Fri.firstMessage (attempt res.1).commitments (attempt res.1).points
                                        (attempt res.1).values))
                                    (CertiFri.Oracle.committedRow l)))
                            (Ix.Cert.MultiStark.experimentPruned m params shape wf adv attempt) [] ≤
                          (↑Q + (↑(CertiFri.Exec.modelParams m params shape wf).rounds + 2) +
                                2 * ↑(CertiFri.Exec.modelParams m params shape wf).verifierQueries) *
                              εmax +
                            ↑(max
                                      ((CertiFri.Exec.modelParams m params shape wf).batches +
                                        (CertiFri.Exec.modelParams m params shape wf).rounds)
                                      3 +
                                    3) *
                                (↑Q + (↑(CertiFri.Exec.modelParams m params shape wf).rounds + 2) +
                                    2 * ↑(CertiFri.Exec.modelParams m params shape wf).verifierQueries) ^
                                  2 /
                              (4 * ↑(Fintype.card D))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding
/--
info: Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness : ∀ (params : CertiFri.FriParams) (shape : CertiFri.Fri.ClaimShape)
  (hlog : CertiFri.Fri.logMaxHeight params.logBlowup shape ≤ 32),
  params.logFinalHeight ≤ CertiFri.Fri.logMaxHeight params.logBlowup shape →
    ∀ {δ : ℝ},
      0 ≤ δ →
        2 * δ + (1 / 2) ^ params.logBlowup ≤ 1 →
          ∀ {εmax : ℝ},
            ↑(CertiFri.Fri.claimRefs params.logBlowup shape).length *
                    ((1 + δ) * 2 ^ CertiFri.Fri.logMaxHeight params.logBlowup shape) /
                  ↑(Fintype.card Ix.Cert.MultiStark.K) ≤
                εmax →
              (1 + δ) * 2 ^ CertiFri.Fri.logMaxHeight params.logBlowup shape / ↑(Fintype.card Ix.Cert.MultiStark.K) /
                    2 ^ params.commitPowBits ≤
                  εmax →
                (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax →
                  ∀ {D : Type} [inst : DecidableEq D] [inst_1 : Inhabited D] [inst_2 : Fintype D] {A : Type u_1}
                    {adv :
                      CertiFri.Oracle.OracleComp
                        (CertiFri.Exec.OracleAnswer Ix.Cert.MultiStark.goldilocksFieldModel params shape ⋯) A}
                    {Q : ℕ},
                    adv.QueryBound Q →
                      ∀
                        (attempt :
                          A → Ix.Cert.MultiStark.PrunedAttempt CertiFri.P3.Goldilocks CertiFri.P3.GoldilocksExt3 D),
                        CertiFri.Oracle.OracleComp.prob
                            (fun res l =>
                              (∃ f,
                                  (∀
                                      (x :
                                        CertiFri.Oracle.FSQuery
                                          (CertiFri.Exec.RawMsg CertiFri.P3.Goldilocks CertiFri.P3.GoldilocksExt3 D)
                                          (CertiFri.PcsRbr.GrindChal (CertiFri.Exec.powBits params shape)
                                            (CertiFri.PcsRbr.Chal
                                              (CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params
                                                  shape ⋯).ldt
                                              (CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params
                                                  shape ⋯).queries))
                                          (CertiFri.Oracle.HashQuery Ix.Cert.MultiStark.K D))
                                      (y :
                                        CertiFri.Exec.OracleAnswer Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                          ⋯ x),
                                      List.dlookup x l = some y → f x = y) ∧
                                    Ix.Cert.MultiStark.acceptsPruned Ix.Cert.MultiStark.goldilocksFieldModel params
                                        shape ⋯ f (attempt res.1) =
                                      true) ∧
                                CertiFri.PcsRbr.ClaimsFail
                                  (CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape ⋯).ldt
                                  (CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                      ⋯).shift
                                  (1 - δ)
                                  ((CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                        ⋯).claims
                                    (CertiFri.Exec.view Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                      (CertiFri.Fri.firstMessage (attempt res.1).commitments (attempt res.1).points
                                        (attempt res.1).values))
                                    (CertiFri.Oracle.committedRow l)))
                            (Ix.Cert.MultiStark.experimentPruned Ix.Cert.MultiStark.goldilocksFieldModel params shape ⋯
                              adv attempt)
                            [] ≤
                          (↑Q +
                                  (↑(CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                          ⋯).rounds +
                                    2) +
                                2 *
                                  ↑(CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                        ⋯).verifierQueries) *
                              εmax +
                            ↑(max
                                      ((CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                            ⋯).batches +
                                        (CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                            ⋯).rounds)
                                      3 +
                                    3) *
                                (↑Q +
                                      (↑(CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                              ⋯).rounds +
                                        2) +
                                    2 *
                                      ↑(CertiFri.Exec.modelParams Ix.Cert.MultiStark.goldilocksFieldModel params shape
                                            ⋯).verifierQueries) ^
                                  2 /
                              (4 * ↑(Fintype.card D))
-/
#guard_msgs in #check @Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness
/--
info: @Ix.Cert.MultiStark.basePoly_of_eval_c1_c2_zero : ∀ {P : Polynomial Ix.Cert.MultiStark.K} {d : ℕ},
  P.degree < ↑(d + 1) →
    ∀ {B : Finset CertiFri.P3.GoldilocksField},
      d + 1 ≤ B.card →
        (∀ x ∈ B,
            (Polynomial.eval (CertiFri.P3.Fp3Model.embedHom x) P).c1 = 0 ∧
              (Polynomial.eval (CertiFri.P3.Fp3Model.embedHom x) P).c2 = 0) →
          Ix.Cert.MultiStark.polyC1 P = 0 ∧
            Ix.Cert.MultiStark.polyC2 P = 0 ∧
              P = Polynomial.map CertiFri.P3.Fp3Model.embedHom (Ix.Cert.MultiStark.polyC0 P)
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.basePoly_of_eval_c1_c2_zero
/-- info: 'Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.soundness_pruned_uniqueDecoding
/-- info: 'Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness

-- Gap 4a & 4b: Small-height off-domain decoding & AIR selectors / Horner batching
/--
info: @Ix.Cert.MultiStark.decodeMarginOff_blowup2_all_heights : ∀ {F : Type u_1} {D : Finset F} {ℓ : ℕ},
  D.card = 4 * 2 ^ ℓ → Ix.Cert.MultiStark.DecodeMarginOff D (2 ^ ℓ) (1 - 1 / 4)
-/
#guard_msgs in #check @Ix.Cert.MultiStark.decodeMarginOff_blowup2_all_heights
/--
info: @Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff : ∀ {F : Type u_1} [inst : Field F] {D : Finset F} {d : ℕ} {θ : ℝ},
  Ix.Cert.MultiStark.DecodeMarginOff D d θ →
    ∀ {m : ℕ} {claims : Fin m → CertiFri.Claim F},
      CertiFri.PcsRbr.ClaimsHoldOff D d θ claims →
        ∀ (k : Fin m),
          (claims k).z ∉ D →
            Polynomial.eval (claims k).z (Ix.Cert.MultiStark.decodeOff D d θ (claims k).f) = (claims k).y ∧
              (Ix.Cert.MultiStark.decodeOff D d θ (claims k).f).degree < ↑(d + 1)
-/
#guard_msgs in #check @Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff
/--
info: Ix.Cert.MultiStark.prob_zeta_in_domain_or_shift_le : ∀ (D : Finset Ix.Cert.MultiStark.K) {g : Ix.Cert.MultiStark.K},
  g ≠ 0 →
    ↑{z | z ∈ D ∨ z * g ∈ D}.card / ↑(Fintype.card Ix.Cert.MultiStark.K) ≤
      2 * ↑D.card / ↑(Fintype.card Ix.Cert.MultiStark.K)
-/
#guard_msgs in #check @Ix.Cert.MultiStark.prob_zeta_in_domain_or_shift_le
/--
info: @Ix.Cert.MultiStark.not_mem_coset_mul_of_mem_subgroup : ∀ {S : Subgroup Ix.Cert.MultiStark.Kˣ}
  {shift : Ix.Cert.MultiStark.Kˣ} {ζ : Ix.Cert.MultiStark.K} {g : Ix.Cert.MultiStark.Kˣ},
  g ∈ S → (∀ s ∈ S, ζ ≠ ↑(shift * s)) → ∀ s ∈ S, ζ * ↑g ≠ ↑(shift * s)
-/
#guard_msgs in #check @Ix.Cert.MultiStark.not_mem_coset_mul_of_mem_subgroup
/--
info: @Ix.Cert.MultiStark.eval_isFirstPoly_on_domain : ∀ {g : Ix.Cert.MultiStark.K} {ℓ : ℕ},
  IsPrimitiveRoot g (2 ^ ℓ) →
    ∀ {i : ℕ}, i < 2 ^ ℓ → Polynomial.eval (g ^ i) (Ix.Cert.MultiStark.isFirstPoly ℓ) = if i = 0 then 2 ^ ℓ else 0
-/
#guard_msgs in #check @Ix.Cert.MultiStark.eval_isFirstPoly_on_domain
/--
info: @Ix.Cert.MultiStark.eval_isLastPoly_on_domain : ∀ {g : Ix.Cert.MultiStark.K} {ℓ : ℕ},
  IsPrimitiveRoot g (2 ^ ℓ) →
    ∀ {i : ℕ},
      i < 2 ^ ℓ → Polynomial.eval (g ^ i) (Ix.Cert.MultiStark.isLastPoly ℓ g) = if i = 2 ^ ℓ - 1 then 2 ^ ℓ * g else 0
-/
#guard_msgs in #check @Ix.Cert.MultiStark.eval_isLastPoly_on_domain
/--
info: @Ix.Cert.MultiStark.card_horner_bad_le : ∀ {cs : List Ix.Cert.MultiStark.K},
  (∃ c ∈ cs, c ≠ 0) → {α | Ix.Cert.MultiStark.hornerFold α cs = 0}.card ≤ cs.length - 1
-/
#guard_msgs in #check @Ix.Cert.MultiStark.card_horner_bad_le
/-- info: 'Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.eval_decodeOff_of_claimsHoldOff
/-- info: 'Ix.Cert.MultiStark.prob_zeta_in_domain_or_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.prob_zeta_in_domain_or_shift_le
/-- info: 'Ix.Cert.MultiStark.card_horner_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.card_horner_bad_le

-- Gap 5: Linear LogUp soundness, sharded MEMSEG -> WidthROM.Valid, Plan.checkMemo, and IxVM CircuitSound
/--
info: @Ix.Cert.MultiStark.card_logup_beta_bad_le : ∀ {α : Type u_1} [DecidableEq α] {S : Finset α}
  {fp w : α → Ix.Cert.MultiStark.K} {m₀ : α},
  m₀ ∈ S →
    w m₀ ≠ 0 →
      (∀ m' ∈ S, m' ≠ m₀ → fp m' ≠ fp m₀) →
        {β | (∀ m ∈ S, β + fp m ≠ 0) ∧ ∑ m ∈ S, w m * (β + fp m)⁻¹ = 0}.card ≤ S.card - 1
-/
#guard_msgs in #check @Ix.Cert.MultiStark.card_logup_beta_bad_le
/--
info: @Ix.Cert.MultiStark.card_logup_pair_bad_le : ∀ {α : Type u_1} [DecidableEq α] {S : Finset α}
  {args : α → List Ix.Cert.MultiStark.Fp} {w : α → Ix.Cert.MultiStark.K} {maxArity : ℕ} {m₀ : α},
  m₀ ∈ S →
    w m₀ ≠ 0 →
      (∀ m ∈ S, (args m).length ≤ maxArity) →
        (∀ m' ∈ S,
            m' ≠ m₀ → Ix.Cert.MultiStark.fingerprintPoly (args m') ≠ Ix.Cert.MultiStark.fingerprintPoly (args m₀)) →
          {p |
                (∀ m ∈ S, p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m) ≠ 0) ∧
                  ∑ m ∈ S, w m * (p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m))⁻¹ = 0}.card ≤
            (S.card - 1) * (maxArity + 1) * Fintype.card Ix.Cert.MultiStark.K
-/
#guard_msgs in #check @Ix.Cert.MultiStark.card_logup_pair_bad_le
/--
info: @Ix.Cert.MultiStark.memseg_balance_implies_unique : ∀ {ivls : List (ℕ × ℕ)},
  Ix.Cert.MultiStark.DisjointIntervals ivls →
    ∀ {m : Ix.Cert.MultiStark.Fp → ℕ},
      ∑ x, m x + 1 < CertiFri.P3.Goldilocks.order →
        (∀ (x : Ix.Cert.MultiStark.Fp), ↑(m x) - ↑(m (x - 1)) + Ix.Cert.MultiStark.memsegBoundary ivls x = 0) →
          ∀ (x : Ix.Cert.MultiStark.Fp), m x = Ix.Cert.MultiStark.intervalCover ivls (ZMod.val x) ∧ m x ≤ 1
-/
#guard_msgs in #check @Ix.Cert.MultiStark.memseg_balance_implies_unique
/--
info: @Ix.Cert.MultiStark.plan_checkMemo_of_field_balance : ∀ {source : Aiur.Circuit.System Ix.Cert.MultiStark.Fp}
  {id : String → Except String ℕ} (plan : Aiur.Optimized.Grouping.Plan source id)
  (rom : Aiur.WireROM Ix.Cert.MultiStark.Fp) (root : Aiur.Circuit.Message Ix.Cert.MultiStark.Fp)
  (rows : List (Aiur.Circuit.Row Ix.Cert.MultiStark.Fp))
  (inspected : List (Option (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp)))),
  source.checkContext rom root = Except.ok () →
    List.mapM (plan.inspectRow rom) rows = Except.ok inspected →
      (Aiur.Circuit.Balance.required (fun c => decide (source.MapClaim c)) root
              (Aiur.Optimized.Grouping.activeRules inspected)).length <
          CertiFri.P3.Goldilocks.order →
        ∀ (provWeight : Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp) → Ix.Cert.MultiStark.Fp),
          (∀
              claim ∈
                Aiur.Circuit.Balance.required (fun c => decide (source.MapClaim c)) root
                  (Aiur.Optimized.Grouping.activeRules inspected),
              (List.map provWeight
                    (List.filter (fun r => decide (r.1 = claim)) (Aiur.Optimized.Grouping.activeRules inspected))).sum =
                ↑(List.countP (fun x => decide (x = claim))
                    (Aiur.Circuit.Balance.required (fun c => decide (source.MapClaim c)) root
                      (Aiur.Optimized.Grouping.activeRules inspected)))) →
            ∃ wrows, wrows.length = rows.length ∧ plan.checkMemo rom root wrows = Except.ok ()
-/
#guard_msgs in #check @Ix.Cert.MultiStark.plan_checkMemo_of_field_balance
/--
info: @Ix.Cert.MultiStark.prepared_eval_of_extracted_trace : ∀ {program : Aiur.Modules.Program Ix.Cert.MultiStark.Fp}
  (prepared : Aiur.Modules.Prepared program) (compiled : Aiur.Optimized.ModulesArtifact prepared)
  (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {cfg : Aiur.Optimized.Depth.Config},
  Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg →
    cfg.bits ≤ 24 →
      ∀ {id : String → Except String ℕ}
        (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
        plan.WellFormedActivation →
          ∀ {external : String} {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances},
            prepared.find? external = some entry →
              ∀ {rom : Aiur.WidthROM Ix.Cert.MultiStark.Fp} (ivlsOf : ℕ → List (ℕ × ℕ)),
                (∀ (w : ℕ), Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w)) →
                  (∀ (w : ℕ),
                      ∑ x, (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length + 1 <
                        CertiFri.P3.Goldilocks.order) →
                    (∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
                        ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                              ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1)) rom.entries).length +
                            Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                          0) →
                      ∀ {args : List (Aiur.SourceValue Ix.Cert.MultiStark.Fp)}
                        {result : Aiur.Value Ix.Cert.MultiStark.Fp}
                        {wires : List (Aiur.WireValue Ix.Cert.MultiStark.Fp)}
                        {output : Aiur.WireValue Ix.Cert.MultiStark.Fp},
                        Aiur.Circuit.Erasure.Signed compiled.circuit.system
                            { channel := entry.resolved.name, args := wires, result := output } →
                          ∀ {root : Aiur.Circuit.Message Ix.Cert.MultiStark.Fp},
                            Aiur.Optimized.Depth.erase cfg root =
                                Aiur.Circuit.Erasure.message compiled.circuit.system
                                  { channel := entry.resolved.name, args := wires, result := output } →
                              root.channel ∉ cfg.names →
                                ∀ (rows : List (Aiur.Circuit.Row Ix.Cert.MultiStark.Fp)),
                                  rows.length ≤ 2 ^ 39 →
                                    ∀
                                      (inspected :
                                        List
                                          (Option
                                            (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp)))),
                                      (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                            (Aiur.Circuit.Erasure.rawROM rom) root =
                                          Except.ok () →
                                        List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) rows =
                                            Except.ok inspected →
                                          (Aiur.Circuit.Balance.required
                                                  (fun c =>
                                                    decide
                                                      ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
                                                  root (Aiur.Optimized.Grouping.activeRules inspected)).length <
                                              CertiFri.P3.Goldilocks.order →
                                            ∀
                                              (provWeight :
                                                Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp) →
                                                  Ix.Cert.MultiStark.Fp),
                                              (∀
                                                  claim ∈
                                                    Aiur.Circuit.Balance.required
                                                      (fun c =>
                                                        decide
                                                          ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim
                                                            c))
                                                      root (Aiur.Optimized.Grouping.activeRules inspected),
                                                  (List.map provWeight
                                                        (List.filter (fun r => decide (r.1 = claim))
                                                          (Aiur.Optimized.Grouping.activeRules inspected))).sum =
                                                    ↑(List.countP (fun x => decide (x = claim))
                                                        (Aiur.Circuit.Balance.required
                                                          (fun c =>
                                                            decide
                                                              ((Aiur.Optimized.Depth.system cfg
                                                                    physical.system).MapClaim
                                                                c))
                                                          root (Aiur.Optimized.Grouping.activeRules inspected)))) →
                                                Aiur.DecodesValues compiled.specialized.program.enums wires
                                                    (Aiur.entryValues args) →
                                                  Aiur.WireValue.decode compiled.specialized.program.enums output =
                                                      some result →
                                                    ∃ value heap,
                                                      prepared.EvalFn external args value heap ∧
                                                        Aiur.Represents
                                                          (Aiur.WireROM.decode compiled.specialized.program.enums
                                                            (Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom))
                                                          heap value result
-/
#guard_msgs in #check @Ix.Cert.MultiStark.prepared_eval_of_extracted_trace
/--
info: @Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace : ∀
  {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.CircuitSound P →
    ∀ {id : String → Except String ℕ} {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
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
                          ∑ x, (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length + 1 <
                            CertiFri.P3.Goldilocks.order) →
                        (∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
                            ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                                  ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1)) rom.entries).length +
                                Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                              0) →
                          ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)}
                            {output : Aiur.WireValue IxVM.F} {result : Aiur.Value IxVM.F},
                            Aiur.Circuit.Erasure.Signed compiled.system
                                { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
                              ∀ {root : Aiur.Circuit.Message IxVM.F},
                                Aiur.Optimized.Depth.erase cfg root =
                                    Aiur.Circuit.Erasure.message compiled.system
                                      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
                                  root.channel ∉ cfg.names →
                                    ∀ (rows : List (Aiur.Circuit.Row IxVM.F)),
                                      rows.length ≤ 2 ^ 39 →
                                        ∀
                                          (inspected :
                                            List (Option (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F)))),
                                          (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                (Aiur.Circuit.Erasure.rawROM rom) root =
                                              Except.ok () →
                                            List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) rows =
                                                Except.ok inspected →
                                              (Aiur.Circuit.Balance.required
                                                      (fun c =>
                                                        decide
                                                          ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim
                                                            c))
                                                      root (Aiur.Optimized.Grouping.activeRules inspected)).length <
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
                                                          root (Aiur.Optimized.Grouping.activeRules inspected),
                                                      (List.map provWeight
                                                            (List.filter (fun r => decide (r.1 = claim))
                                                              (Aiur.Optimized.Grouping.activeRules inspected))).sum =
                                                        ↑(List.countP (fun x => decide (x = claim))
                                                            (Aiur.Circuit.Balance.required
                                                              (fun c =>
                                                                decide
                                                                  ((Aiur.Optimized.Depth.system cfg
                                                                        physical.system).MapClaim
                                                                    c))
                                                              root (Aiur.Optimized.Grouping.activeRules inspected)))) →
                                                    Aiur.DecodesValues specialized.program.enums wires
                                                        (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                                                      Aiur.WireValue.decode specialized.program.enums output =
                                                          some result →
                                                        ∃ value heap calls,
                                                          Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world
                                                              IxVM.Refinement.verifyClaim
                                                              [IxVM.Refinement.digestValue d] [] value heap calls ∧
                                                            Aiur.Generic.SourceSemantics.CallsInROM
                                                                (compiled.traceROM rom) calls ∧
                                                              P calls d
-/
#guard_msgs in #check @Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace
/-- info: 'Ix.Cert.MultiStark.card_logup_beta_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.card_logup_beta_bad_le
/-- info: 'Ix.Cert.MultiStark.card_logup_pair_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.card_logup_pair_bad_le
/-- info: 'Ix.Cert.MultiStark.memseg_balance_implies_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.memseg_balance_implies_unique
/-- info: 'Ix.Cert.MultiStark.plan_checkMemo_of_field_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.plan_checkMemo_of_field_balance
/-- info: 'Ix.Cert.MultiStark.prepared_eval_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.prepared_eval_of_extracted_trace
/-- info: 'Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace

-- Gap 5b: Complete LogUp zero-denominator bound, C6 vectorized ROM, & executable verifier surface
/--
info: @Ix.Cert.MultiStark.card_logup_pair_bad_or_zero_denom_le : ∀ {α : Type u_1} [DecidableEq α] {S S_all : Finset α}
  {args : α → List Ix.Cert.MultiStark.Fp} {w : α → Ix.Cert.MultiStark.K} {maxArity : ℕ} {m₀ : α},
  S ⊆ S_all →
    m₀ ∈ S →
      w m₀ ≠ 0 →
        (∀ m ∈ S, (args m).length ≤ maxArity) →
          (∀ m' ∈ S,
              m' ≠ m₀ → Ix.Cert.MultiStark.fingerprintPoly (args m') ≠ Ix.Cert.MultiStark.fingerprintPoly (args m₀)) →
            {p |
                  (∃ m ∈ S_all, p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m) = 0) ∨
                    ∑ m ∈ S, w m * (p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m))⁻¹ = 0}.card ≤
              ((S.card - 1) * (maxArity + 1) + S_all.card) * Fintype.card Ix.Cert.MultiStark.K
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.card_logup_pair_bad_or_zero_denom_le
/--
info: @Ix.Cert.MultiStark.fractionLE_logup_pair_or_zero_denom : ∀ {α : Type u_1} [DecidableEq α] {S S_all : Finset α}
  {args : α → List Ix.Cert.MultiStark.Fp} {w : α → Ix.Cert.MultiStark.K} {maxArity : ℕ} {m₀ : α},
  S ⊆ S_all →
    m₀ ∈ S →
      w m₀ ≠ 0 →
        (∀ m ∈ S, (args m).length ≤ maxArity) →
          (∀ m' ∈ S,
              m' ≠ m₀ → Ix.Cert.MultiStark.fingerprintPoly (args m') ≠ Ix.Cert.MultiStark.fingerprintPoly (args m₀)) →
            CertiFri.Oracle.FractionLE
              (fun p =>
                (∃ m ∈ S_all, p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m) = 0) ∨
                  ∑ m ∈ S, w m * (p.1 + Ix.Cert.MultiStark.fingerprintEval p.2 (args m))⁻¹ = 0)
              (↑((S.card - 1) * (maxArity + 1) + S_all.card) / ↑(Fintype.card Ix.Cert.MultiStark.K))
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.fractionLE_logup_pair_or_zero_denom
/--
info: Ix.Cert.MultiStark.vectorized_rom_widthROM_valid : ∀ (rom : Aiur.WidthROM Ix.Cert.MultiStark.Fp)
  (ivlsOf : ℕ → List (ℕ × ℕ)),
  (∀ (w : ℕ), Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w)) →
    (∀ (w : ℕ),
        ∑ x, (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length + 1 <
          CertiFri.P3.Goldilocks.order) →
      (∀ (w : ℕ),
          (∀ (x : Ix.Cert.MultiStark.Fp),
              ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                    ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1)) rom.entries).length +
                  Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                0) ∨
            ∃ K rows,
              1 < K ∧
                (∀ r ∈ rows, Aiur.MultiStarkSpec.KLaneRomRowValid w K r) ∧
                  List.filter (fun e => decide (e.2.length = w)) rom.entries =
                      Aiur.MultiStarkSpec.vecTraceEntries w K rows ∧
                    ∀ (x : Ix.Cert.MultiStark.Fp),
                      (List.map (fun r => Aiur.MultiStarkSpec.vecRowMemsegDelta w K r x) rows).sum +
                          Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                        0) →
        rom.Valid
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.vectorized_rom_widthROM_valid
/-- info: Ix.Cert.MultiStark.checkParams : Ix.Cert.MultiStark.StarkParams → Bool -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.checkParams
/--
info: @Ix.Cert.MultiStark.validatePreamble : (sys : Ix.Cert.MultiStark.StarkSystem) →
  Ix.Cert.MultiStark.BatchProof → optParam ℕ (32 - sys.params.logBlowup) → Bool
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.validatePreamble
/--
info: @Ix.Cert.MultiStark.verifyBatch : (sys : Ix.Cert.MultiStark.StarkSystem) →
  Ix.Cert.MultiStark.BatchProof → optParam ℕ (32 - sys.params.logBlowup) → Option (Array (Array Ix.Cert.MultiStark.F))
-/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.verifyBatch
/-- info: @Ix.Cert.MultiStark.verifyBatchBytes : ByteArray → ByteArray → ByteArray → optParam (Option ℕ) none → Bool -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.MultiStark.verifyBatchBytes
/-- info: 'Ix.Cert.MultiStark.card_logup_pair_bad_or_zero_denom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.card_logup_pair_bad_or_zero_denom_le
/-- info: 'Ix.Cert.MultiStark.fractionLE_logup_pair_or_zero_denom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.fractionLE_logup_pair_or_zero_denom
/-- info: 'Ix.Cert.MultiStark.vectorized_rom_widthROM_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.vectorized_rom_widthROM_valid
/-- info: 'Ix.Cert.MultiStark.validatePreamble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.validatePreamble
/-- info: 'Ix.Cert.MultiStark.verifyBatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.verifyBatch
/-- info: 'Ix.Cert.MultiStark.verifyBatchBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Cert.MultiStark.verifyBatchBytes
