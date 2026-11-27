import Ix.Cert.MultiStarkRefinement.EndToEnd
import Ix.Cert.MultiStarkRefinement.MutationControl

/-! # Recursive Verifier Refinement Audit Surface (`Ix.Cert.MultiStarkRefinement.Audit`)

Verifies that every headline theorem in `Ix.Cert.MultiStarkRefinement` (pinning and refining
`MultiStark.recursionProgram` onto `Ix.Cert.MultiStark.verifyBatch` and `EndToEnd`, plus
mutation negative controls) depends ONLY on standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero `bv_decide`).
-/

-- 1. Deployed MultiStark.recursionProgram AST pinning & BLAKE3 digest injectivity
/--
info: Ix.Cert.MultiStarkRefinement.recursionSource_core_functions_present : (Ix.Cert.MultiStarkRefinement.recursionModuleNames.all
      fun m => (MultiStark.recursionSource.findModule? m).isSome) =
    true ∧
  (Ix.Cert.MultiStarkRefinement.recursionCoreFunctions.all fun p =>
      Ix.Cert.MultiStarkRefinement.hasModuleFunction MultiStark.recursionSource p.1 p.2) =
    true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursionSource_core_functions_present

/--
info: Ix.Cert.MultiStarkRefinement.recursionSource_ast_pinned : Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
    MultiStark.recursionSource =
  true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursionSource_ast_pinned

/--
info: Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned : Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
    MultiStark.recursionProgram =
  true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned

/--
info: @Ix.Cert.MultiStarkRefinement.packDigest8_inj : ∀ {a b : Address},
  a.hash.size = 32 →
    b.hash.size = 32 → Ix.Cert.MultiStarkRefinement.packDigest8 a = Ix.Cert.MultiStarkRefinement.packDigest8 b → a = b
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.packDigest8_inj

/-- info: 'Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursionProgram_ast_pinned

/--
info: Ix.Cert.MultiStarkRefinement.recursionSource_ood_loop_binds_fixed_heights : Ix.Cert.MultiStarkRefinement.OodLoopBindsFixedHeights
    MultiStark.recursionSource =
  true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursionSource_ood_loop_binds_fixed_heights
/-- info: 'Ix.Cert.MultiStarkRefinement.recursionSource_ood_loop_binds_fixed_heights' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursionSource_ood_loop_binds_fixed_heights
/-- info: 'Ix.Cert.MultiStarkRefinement.packDigest8_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.packDigest8_inj

-- 2. Goldilocks field & extension bridge
/--
info: Ix.Cert.MultiStarkRefinement.glLtPModel_eq_one_iff : ∀ (b : Fin 8 → UInt8),
  Ix.Cert.MultiStarkRefinement.glLtPModel b = 1 ↔
    Ix.Cert.MultiStarkRefinement.leBytes8Nat b < CertiFri.P3.Goldilocks.order
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.glLtPModel_eq_one_iff

/--
info: @Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique : ∀ {v : Ix.Cert.MultiStark.Fp} {b₁ b₂ : Fin 8 → UInt8},
  Ix.Cert.MultiStarkRefinement.glValModel b₁ = v →
    Ix.Cert.MultiStarkRefinement.glLtPModel b₁ = 1 →
      Ix.Cert.MultiStarkRefinement.glValModel b₂ = v → Ix.Cert.MultiStarkRefinement.glLtPModel b₂ = 1 → b₁ = b₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique

/--
info: @Ix.Cert.MultiStarkRefinement.gl_inverse_spec : ∀ {x iv : Ix.Cert.MultiStark.Fp},
  x * (x * iv - 1) = 0 → iv * (x * iv - 1) = 0 → iv = x⁻¹
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.gl_inverse_spec

/--
info: @Ix.Cert.MultiStarkRefinement.eg_inverse_spec : ∀ {a : Ix.Cert.MultiStark.K} {ninv : Ix.Cert.MultiStark.Fp},
  a.norm * (a.norm * ninv - 1) = 0 →
    ninv * (a.norm * ninv - 1) = 0 →
      { c0 := a.adjugate.c0 * ninv, c1 := a.adjugate.c1 * ninv, c2 := a.adjugate.c2 * ninv } = a⁻¹
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.eg_inverse_spec

/--
info: Ix.Cert.MultiStarkRefinement.ext_is_zero_iff : ∀ (e : Ix.Cert.MultiStark.EF),
  Ix.Cert.MultiStarkRefinement.isZeroFp (Ix.Cert.MultiStark.baseToFp e.c0) *
          Ix.Cert.MultiStarkRefinement.isZeroFp (Ix.Cert.MultiStark.baseToFp e.c1) *
        Ix.Cert.MultiStarkRefinement.isZeroFp (Ix.Cert.MultiStark.baseToFp e.c2) =
      1 ↔
    e = CertiFri.P3.GoldilocksExt3.zero
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.ext_is_zero_iff

/--
info: Ix.Cert.MultiStarkRefinement.triple_mul_refines : ∀ (a0 a1 a2 b0 b1 b2 : Ix.Cert.MultiStark.EF),
  match Ix.Cert.MultiStark.tripleMul a0 a1 a2 b0 b1 b2 with
  | (r0, r1, r2) =>
    Ix.Cert.MultiStark.extToModel r0 =
        Ix.Cert.MultiStark.extToModel a0 * Ix.Cert.MultiStark.extToModel b0 +
          Ix.Cert.MultiStark.extToModel a1 * Ix.Cert.MultiStark.extToModel b2 +
          Ix.Cert.MultiStark.extToModel a2 * Ix.Cert.MultiStark.extToModel b1 ∧
      Ix.Cert.MultiStark.extToModel r1 =
          Ix.Cert.MultiStark.extToModel a0 * Ix.Cert.MultiStark.extToModel b1 +
            Ix.Cert.MultiStark.extToModel a1 * Ix.Cert.MultiStark.extToModel b0 +
            Ix.Cert.MultiStark.extToModel a1 * Ix.Cert.MultiStark.extToModel b2 +
            Ix.Cert.MultiStark.extToModel a2 * Ix.Cert.MultiStark.extToModel b1 +
            Ix.Cert.MultiStark.extToModel a2 * Ix.Cert.MultiStark.extToModel b2 ∧
        Ix.Cert.MultiStark.extToModel r2 =
          Ix.Cert.MultiStark.extToModel a0 * Ix.Cert.MultiStark.extToModel b2 +
            Ix.Cert.MultiStark.extToModel a1 * Ix.Cert.MultiStark.extToModel b1 +
            Ix.Cert.MultiStark.extToModel a2 * Ix.Cert.MultiStark.extToModel b0 +
            Ix.Cert.MultiStark.extToModel a2 * Ix.Cert.MultiStark.extToModel b2
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.triple_mul_refines

/--
info: Ix.Cert.MultiStarkRefinement.two_adic_gen_refines : ∀ (b : Fin 33),
  Ix.Cert.MultiStarkRefinement.twoAdicGenModel ↑b =
    Ix.Cert.MultiStark.baseToFp (CertiFri.P3.Goldilocks.twoAdicGenerator ↑b)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.two_adic_gen_refines

/--
info: Ix.Cert.MultiStarkRefinement.quotient_degree_of_refines : ∀ (md : Fin 34),
  Ix.Cert.MultiStarkRefinement.quotientDegreeOfModel ↑md =
    { mainWidth := 0, preprocessedWidth := 0, preprocessedHeight := 0, maxConstraintDegree := ↑md, lookupGroupSize := 1,
        nodes := #[], zeros := #[], lookups := #[] }.quotientDegree
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.quotient_degree_of_refines

/--
info: @Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq : ∀ {x r : Fin 8 → UInt8},
  Ix.Cert.MultiStarkRefinement.glLtPModel x = 1 →
    Ix.Cert.MultiStarkRefinement.glValModel r = Ix.Cert.MultiStarkRefinement.glValModel x →
      Ix.Cert.MultiStarkRefinement.glLtPModel r = 1 → x = r
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq

/-- info: Ix.Cert.MultiStarkRefinement.goldilocks_inv_two_eq : 9223372034707292161 = 2⁻¹ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.goldilocks_inv_two_eq

/--
info: Ix.Cert.MultiStarkRefinement.eg_div_base_eq : ∀ (e : Ix.Cert.MultiStark.K) (s : Ix.Cert.MultiStark.Fp),
  e * { c0 := s, c1 := 0, c2 := 0 }⁻¹ = { c0 := e.c0 * s⁻¹, c1 := e.c1 * s⁻¹, c2 := e.c2 * s⁻¹ }
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.eg_div_base_eq

/--
info: Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail : ∀ (xs : List Ix.Cert.MultiStark.Fp)
  (zs : List Ix.Cert.MultiStark.K) (alpha acc ap : Ix.Cert.MultiStark.K),
  xs.length = zs.length →
    match Ix.Cert.MultiStarkRefinement.roFoldHorner xs zs alpha with
    | (s, pw) => Ix.Cert.MultiStarkRefinement.roFoldTail xs zs alpha acc ap = (acc + ap * s, ap * pw)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail

/--
info: Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes : ∀ (q0 q1 : Ix.Cert.MultiStark.K)
  (s0s s1s : List Ix.Cert.MultiStark.K),
  (List.map (fun x => q0 * x) s0s).sum + (List.map (fun x => q1 * x) s1s).sum = q0 * s0s.sum + q1 * s1s.sum
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes

/-- info: 'Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.gl_to_bytes_unique
/-- info: 'Ix.Cert.MultiStarkRefinement.eg_inverse_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.eg_inverse_spec
/-- info: 'Ix.Cert.MultiStarkRefinement.two_adic_gen_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.two_adic_gen_refines
/-- info: 'Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.rows_pop_canonical_eq
/-- info: 'Ix.Cert.MultiStarkRefinement.eg_div_base_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.eg_div_base_eq
/-- info: 'Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.roFoldHorner_refines_tail
/-- info: 'Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.bucket_finalize_distributes

-- 3. Wire deserialization, transcript, MMCS, preamble bounds, and verifyBatch refinement
/--
info: Ix.Cert.MultiStarkRefinement.lookup_groups_count_refines : ∀ (c : Ix.Cert.MultiStark.SysCircuit),
  Ix.Cert.MultiStarkRefinement.lookupGroupsCountModel c.lookups.size 0 (max 1 c.lookupGroupSize) = c.logupGroupCount
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.lookup_groups_count_refines

/--
info: @Ix.Cert.MultiStarkRefinement.wire_decoding_authentic_or_collision : ∀
  {calls : List (Aiur.Generic.SourceSemantics.Call Ix.Cert.MultiStark.Fp)}
  {vkBytes claimsBytes sbytes cbytes proofBytes : ByteArray} {sys : Ix.Cert.MultiStark.StarkSystem}
  {expectedClaims : Array (Array Ix.Cert.MultiStark.F)} {batch : Ix.Cert.MultiStark.BatchProof},
  Ix.Cert.MultiStarkRefinement.WireDecodingWitness calls
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure vkBytes))
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure claimsBytes)) sbytes cbytes proofBytes sys
      expectedClaims batch →
    Ix.Cert.MultiStarkRefinement.MultiStarkCollision [vkBytes, claimsBytes] calls ∨
      sbytes = vkBytes ∧
        cbytes = claimsBytes ∧
          Ix.Cert.MultiStark.StarkSystem.fromBytes vkBytes = Except.ok sys ∧
            Ix.Cert.MultiStark.decodeClaims claimsBytes = Except.ok expectedClaims ∧
              Ix.Cert.MultiStark.BatchProof.fromBytes proofBytes = Except.ok batch
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.wire_decoding_authentic_or_collision

/--
info: Ix.Cert.MultiStarkRefinement.ch_sample_field_accept_iff : ∀ (b : Fin 8 → UInt8),
  Ix.Cert.MultiStarkRefinement.glLtPModel b = 1 ↔
    (CertiFri.P3.Goldilocks.ofCanonical? (Ix.Cert.MultiStarkRefinement.bytes8ToUInt64 b)).isSome = true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.ch_sample_field_accept_iff

/--
info: @Ix.Cert.MultiStarkRefinement.assert_shard_count_ok_sound : ∀ {k : Ix.Cert.MultiStark.Fp} {b : Fin 8 → UInt8},
  Ix.Cert.MultiStarkRefinement.assertShardCountOkSpec k b →
    1 ≤ ZMod.val k ∧ ZMod.val k ≤ Ix.Cert.MultiStark.MAX_BATCH_SHARDS
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.assert_shard_count_ok_sound

/--
info: @Ix.Cert.MultiStarkRefinement.at_most_row_bound_sound : ∀ {n : Ix.Cert.MultiStark.Fp} {b : Fin 8 → UInt8},
  Ix.Cert.MultiStarkRefinement.atMostRowBoundSpec n b → ZMod.val n ≤ Ix.Cert.MultiStark.MAX_BATCH_ROWS
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.at_most_row_bound_sound

/--
info: Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_one_iff : ∀ (x y : Fin 8 → UInt8),
  Ix.Cert.MultiStarkRefinement.bytes8LeModel x y = 1 ↔
    Ix.Cert.MultiStarkRefinement.leBytes8Nat x ≤ Ix.Cert.MultiStarkRefinement.leBytes8Nat y
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_one_iff

/--
info: @Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint : ∀ {ms : List Ix.Cert.MultiStark.BatchMessage}
  {prevW prevB : ℕ},
  Ix.Cert.MultiStarkRefinement.ClosurePairsAccepted ms prevW prevB →
    ∀ (targetW : ℕ),
      Ix.Cert.MultiStark.DisjointIntervals (Ix.Cert.MultiStarkRefinement.extractWidthIntervals targetW ms)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint

/--
info: @Ix.Cert.MultiStarkRefinement.verifyShard_of_witness : ∀ {sys : Ix.Cert.MultiStark.StarkSystem}
  {header : Ix.Cert.MultiStark.ShardHeader} {shardIdx : ℕ} {proof : Ix.Cert.MultiStark.ShardProof}
  {batchState : CertiFri.P3.ChallengerState} {beta gamma residual : Ix.Cert.MultiStark.EF}
  (w : Ix.Cert.MultiStarkRefinement.ShardVerifyWitness sys header shardIdx proof batchState beta gamma residual),
  Ix.Cert.MultiStark.verifyShard sys header shardIdx proof batchState beta gamma = some residual
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.verifyShard_of_witness

/--
info: @Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness : ∀ {sys : Ix.Cert.MultiStark.StarkSystem}
  {batch : Ix.Cert.MultiStark.BatchProof} {maxLogDeg : ℕ} {expectedClaims : Array (Array Ix.Cert.MultiStark.F)}
  (w : Ix.Cert.MultiStarkRefinement.BatchVerifyWitness sys batch maxLogDeg expectedClaims),
  Ix.Cert.MultiStark.verifyBatch sys batch maxLogDeg = some expectedClaims
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness

/-- info: 'Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.closurePairsAccepted_disjoint
/-- info: 'Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.verifyBatch_of_witness

-- 4. End-to-End Observed Trace Bridge & Recursive Verifier Soundness
/--
info: @Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace : ∀ {program : Aiur.Modules.Program Ix.Cert.MultiStark.Fp}
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
                                                    ∃ value heap calls,
                                                      prepared.ObsFn external args value heap calls ∧
                                                        Aiur.Represents (compiled.traceROM rom) heap value result ∧
                                                          Aiur.Generic.SourceSemantics.CallsInROM
                                                            (compiled.traceROM rom) calls
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace

/--
info: @Ix.Cert.MultiStarkRefinement.recursion_obs_refines_verifyBatch : ∀
  {calls : List (Aiur.Generic.SourceSemantics.Call Ix.Cert.MultiStark.Fp)} {vkBytes claimsBytes : ByteArray}
  (href :
    Ix.Cert.MultiStarkRefinement.RecursionExecutionRefines calls
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure vkBytes))
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure claimsBytes))),
  Ix.Cert.MultiStarkRefinement.MultiStarkCollision [vkBytes, claimsBytes] calls ∨
    ∃ proofBytes sys expectedClaims batch,
      Ix.Cert.MultiStark.StarkSystem.fromBytes vkBytes = Except.ok sys ∧
        Ix.Cert.MultiStark.decodeClaims claimsBytes = Except.ok expectedClaims ∧
          Ix.Cert.MultiStark.BatchProof.fromBytes proofBytes = Except.ok batch ∧
            Ix.Cert.MultiStark.verifyBatch sys batch = some expectedClaims ∧
              Ix.Cert.MultiStark.verifyBatchBytes vkBytes claimsBytes proofBytes = true ∧
                ∀ (w : ℕ),
                  Ix.Cert.MultiStark.DisjointIntervals
                    (Ix.Cert.MultiStarkRefinement.extractWidthIntervals w batch.preamble.messages.toList)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursion_obs_refines_verifyBatch

/--
info: Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify : ∀
  (prepared : Aiur.Modules.Prepared MultiStark.recursionProgram),
  Ix.Cert.MultiStarkRefinement.RecursionSourceSound prepared →
    ∀ (compiled : Aiur.Optimized.ModulesArtifact prepared)
      (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {cfg : Aiur.Optimized.Depth.Config},
      Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg →
        cfg.bits ≤ 24 →
          ∀ {id : String → Except String ℕ}
            (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
            plan.WellFormedActivation →
              ∀ {entry : Aiur.Modules.Selection MultiStark.recursionProgram prepared.environment.assembly.instances},
                prepared.find? Ix.Cert.MultiStarkRefinement.verifyMultiStarkEntry = some entry →
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
                          ∀ (vkBytes claimsBytes : ByteArray)
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
                                                    (Aiur.Circuit.RuleClaims
                                                      (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp)))),
                                              (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                                    (Aiur.Circuit.Erasure.rawROM rom) root =
                                                  Except.ok () →
                                                List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) rows =
                                                    Except.ok inspected →
                                                  (Aiur.Circuit.Balance.required
                                                          (fun c =>
                                                            decide
                                                              ((Aiur.Optimized.Depth.system cfg
                                                                    physical.system).MapClaim
                                                                c))
                                                          root (Aiur.Optimized.Grouping.activeRules inspected)).length <
                                                      CertiFri.P3.Goldilocks.order →
                                                    ∀
                                                      (provWeight :
                                                        Aiur.Circuit.RuleClaims
                                                            (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp) →
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
                                                                  (Aiur.Optimized.Grouping.activeRules inspected)))) →
                                                        Aiur.DecodesValues compiled.specialized.program.enums wires
                                                            (Aiur.entryValues
                                                              [Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                  (Ix.Cert.MultiStarkRefinement.packDigest8
                                                                    (Address.blake3Pure vkBytes)),
                                                                Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                  (Ix.Cert.MultiStarkRefinement.packDigest8
                                                                    (Address.blake3Pure claimsBytes))]) →
                                                          Aiur.WireValue.decode compiled.specialized.program.enums
                                                                output =
                                                              some result →
                                                            Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
                                                                  MultiStark.recursionProgram =
                                                                true ∧
                                                              ∃ value heap calls,
                                                                prepared.ObsFn
                                                                    Ix.Cert.MultiStarkRefinement.verifyMultiStarkEntry
                                                                    [Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                        (Ix.Cert.MultiStarkRefinement.packDigest8
                                                                          (Address.blake3Pure vkBytes)),
                                                                      Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                        (Ix.Cert.MultiStarkRefinement.packDigest8
                                                                          (Address.blake3Pure claimsBytes))]
                                                                    value heap calls ∧
                                                                  Aiur.Represents (compiled.traceROM rom) heap value
                                                                      result ∧
                                                                    Aiur.Generic.SourceSemantics.CallsInROM
                                                                        (compiled.traceROM rom) calls ∧
                                                                      (Ix.Cert.MultiStarkRefinement.MultiStarkCollision
                                                                          [vkBytes, claimsBytes] calls ∨
                                                                        ∃ proofBytes sys expectedClaims batch,
                                                                          Ix.Cert.MultiStark.StarkSystem.fromBytes
                                                                                vkBytes =
                                                                              Except.ok sys ∧
                                                                            Ix.Cert.MultiStark.decodeClaims
                                                                                  claimsBytes =
                                                                                Except.ok expectedClaims ∧
                                                                              Ix.Cert.MultiStark.BatchProof.fromBytes
                                                                                    proofBytes =
                                                                                  Except.ok batch ∧
                                                                                Ix.Cert.MultiStark.verifyBatch sys
                                                                                      batch =
                                                                                    some expectedClaims ∧
                                                                                  Ix.Cert.MultiStark.verifyBatchBytes
                                                                                        vkBytes claimsBytes proofBytes =
                                                                                      true ∧
                                                                                    ∀ (w : ℕ),
                                                                                      Ix.Cert.MultiStark.DisjointIntervals
                                                                                        (Ix.Cert.MultiStarkRefinement.extractWidthIntervals
                                                                                          w
                                                                                          batch.preamble.messages.toList))
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify

/--
info: @Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound : ∀
  {callsOuter : List (Aiur.Generic.SourceSemantics.Call Ix.Cert.MultiStark.Fp)} {vkBytes claimsBytes : ByteArray}
  (hOuter :
    Ix.Cert.MultiStarkRefinement.RecursionExecutionRefines callsOuter
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure vkBytes))
      (Ix.Cert.MultiStarkRefinement.packDigest8 (Address.blake3Pure claimsBytes)))
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
                                                        Ix.Cert.MultiStarkRefinement.MultiStarkCollision
                                                            [vkBytes, claimsBytes] callsOuter ∨
                                                          (∃ proofBytes,
                                                              Ix.Cert.MultiStark.verifyBatchBytes vkBytes claimsBytes
                                                                  proofBytes =
                                                                true) ∧
                                                            ∃ value heap callsInner,
                                                              Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world
                                                                  IxVM.Refinement.verifyClaim
                                                                  [IxVM.Refinement.digestValue d] [] value heap
                                                                  callsInner ∧
                                                                Aiur.Generic.SourceSemantics.CallsInROM
                                                                    (compiled.traceROM rom) callsInner ∧
                                                                  P callsInner d
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound

/-- info: 'Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.prepared_obs_of_extracted_trace
/-- info: 'Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursionProgram_refines_multiStark_verify
/-- info: 'Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.recursive_step_to_ixvm_circuit_sound

-- 5. Mutation Negative Controls
/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin : Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
    Ix.Cert.MultiStarkRefinement.mutatedRecursionSourceNoExtIsZero =
  false
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin

/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_fixed_height_fails_pins : Ix.Cert.MultiStarkRefinement.OodLoopBindsFixedHeights
      Ix.Cert.MultiStarkRefinement.mutatedRecursionSourceNoFixedHeight =
    false ∧
  Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
      Ix.Cert.MultiStarkRefinement.mutatedRecursionSourceNoFixedHeight =
    false
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_fixed_height_fails_pins
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_fixed_height_fails_pins' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_fixed_height_fails_pins

/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_security_floor_fails_pin : Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
    Ix.Cert.MultiStarkRefinement.mutatedRecursionSourceNoSecurityFloor =
  false
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_security_floor_fails_pin
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_security_floor_fails_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_security_floor_fails_pin

/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_prep_commit_guard_fails_pin : Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
    Ix.Cert.MultiStarkRefinement.mutatedRecursionSourceNoPrepCommitGuard =
  false
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_prep_commit_guard_fails_pin
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_prep_commit_guard_fails_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_prep_commit_guard_fails_pin

/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound : ¬∀ (total : Ix.Cert.MultiStark.EF),
    Ix.Cert.MultiStarkRefinement.mutatedFinalCheck total = true →
      Ix.Cert.MultiStarkRefinement.certifiedFinalCheck total = true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound

/--
info: Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound : Ix.Cert.MultiStark.checkClosurePairs
      Ix.Cert.MultiStarkRefinement.overlappingMemsegMessages =
    false ∧
  ¬Ix.Cert.MultiStark.DisjointIntervals
      (Ix.Cert.MultiStarkRefinement.extractWidthIntervals 1
        Ix.Cert.MultiStarkRefinement.overlappingMemsegMessages.toList)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_fails_pin
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_ext_is_zero_unsound
/-- info: 'Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.mutated_drop_closure_pairs_unsound

-- 6. Strict nonzero-inverse guards, strict closure-pair inequality, and vectorized ROM lanes
/--
info: Ix.Cert.MultiStarkRefinement.goldilocksLibrary_nonzero_inverses_pinned : (Ix.Cert.MultiStarkRefinement.goldilocksCoreFunctions.all fun p =>
      Ix.Cert.MultiStarkRefinement.hasModuleFunction Aiur.Library.Field.Goldilocks.declarations p.1 p.2) =
    true ∧
  Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts Aiur.Library.Field.Goldilocks.declarations "Goldilocks"
      "gl_inv_nonzero" [] 1 =
    true ∧
  Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts Aiur.Library.Field.Goldilocks.declarations "Goldilocks"
      "eg_inv_nonzero" ["gl_inv_nonzero"] 0 =
    true ∧
  Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts Aiur.Library.Field.Goldilocks.declarations "Goldilocks"
      "eg_div_nonzero" ["eg_mul", "eg_inv_nonzero"] 0 =
    true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.goldilocksLibrary_nonzero_inverses_pinned
/--
info: @Ix.Cert.MultiStarkRefinement.gl_inv_nonzero_spec : ∀ {x iv : Ix.Cert.MultiStark.Fp}, x * iv = 1 → x ≠ 0 ∧ iv = x⁻¹
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.gl_inv_nonzero_spec
/--
info: @Ix.Cert.MultiStarkRefinement.eg_inv_nonzero_spec : ∀ {a : Ix.Cert.MultiStark.K} {ninv : Ix.Cert.MultiStark.Fp},
  a.norm * ninv = 1 →
    a ≠ 0 ∧ { c0 := a.adjugate.c0 * ninv, c1 := a.adjugate.c1 * ninv, c2 := a.adjugate.c2 * ninv } = a⁻¹
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.eg_inv_nonzero_spec
/--
info: @Ix.Cert.MultiStarkRefinement.eg_div_nonzero_spec : ∀ {a b : Ix.Cert.MultiStark.K} {ninv : Ix.Cert.MultiStark.Fp},
  b.norm * ninv = 1 →
    b ≠ 0 ∧ a * { c0 := b.adjugate.c0 * ninv, c1 := b.adjugate.c1 * ninv, c2 := b.adjugate.c2 * ninv } = a * b⁻¹
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.eg_div_nonzero_spec
/--
info: Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_zero_iff : ∀ (x y : Fin 8 → UInt8),
  Ix.Cert.MultiStarkRefinement.bytes8LeModel y x = 0 ↔
    Ix.Cert.MultiStarkRefinement.leBytes8Nat x < Ix.Cert.MultiStarkRefinement.leBytes8Nat y
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_zero_iff
/--
info: Ix.Cert.MultiStarkRefinement.rom_lanes_of_refines : ∀ (w : ℕ),
  Ix.Cert.MultiStarkRefinement.romLanesOfModel w = Ix.Cert.MultiStark.romLanes w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStarkRefinement.rom_lanes_of_refines
/-- info: 'Ix.Cert.MultiStarkRefinement.goldilocksLibrary_nonzero_inverses_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.goldilocksLibrary_nonzero_inverses_pinned
/-- info: 'Ix.Cert.MultiStarkRefinement.gl_inv_nonzero_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.gl_inv_nonzero_spec
/-- info: 'Ix.Cert.MultiStarkRefinement.eg_inv_nonzero_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.eg_inv_nonzero_spec
/-- info: 'Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.bytes8LeModel_eq_zero_iff
/-- info: 'Ix.Cert.MultiStarkRefinement.rom_lanes_of_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.MultiStarkRefinement.rom_lanes_of_refines
