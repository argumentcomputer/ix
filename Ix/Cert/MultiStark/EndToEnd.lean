import Ix.Cert.MultiStark.Blake3Parity
import Ix.Cert.MultiStark.DynamicRom
import Ix.Cert.MultiStark.PlanBridge
import Ix.IxVM.Refinement.Statement

/-! # Multi-STARK Formal Soundness Components & Trace-to-IxVM Bridge

Assembles the five independently proved formal soundness components of the Multi-STARK
certification stack alongside the Mathlib-free executable verifier
(`Ix.Cert.MultiStark.{Preamble, Verifier}`):

1. **Field Model & BLAKE3 Parity (`FieldModel`, `Blake3Parity`):** Concrete Goldilocks
   (`p = 2^64 - 2^32 + 1`) quadratic-extension `Exec.FieldModel`, `WellFormed`, and byte-for-byte
   parity of plain (unkeyed) `CertiFri.P3.Blake3` against `Blake3.Pure.hash` (not the keyed
   `derive_key` hashers every v6 verifier uses).
2. **Dynamic ROM (`DynamicRom`):** Shape-independent `DynChal`, exact uniform dynamic-height
   projection `fractionLE_projectQueryIndex`, dynamic Merkle `Settles`, adaptive batch ROM
   soundness `soundness_dynamic_rom`, and per-round `FractionLE` bounds (including
   `fractionLE_logup_pair_or_zero_denom` covering disabled/padding zero-denominator events).
3. **Pruned MMCS Soundness (`PrunedSoundness`):** Unconditional ROM unique-decoding soundness of
   Plonky3's pruned MMCS (`CertiFri.P3.prunedMmcs`) via `soundness_pruned_uniqueDecoding`
   and base-field polynomial descent `basePoly_of_eval_c1_c2_zero`.
4. **Small-Height Decoding & AIR Soundness (`SmallHeight`, `AirSoundness`):** Tight off-domain
   decoding at all trace heights including `ℓ = 0, 1` (`DecodeMarginOff`,
   `decodeMarginOff_blowup2_all_heights`), trace-domain selectors `isFirst`/`isLast`/`isTrans`,
   and Horner constraint batching `card_horner_bad_le`.
5. **LogUp & Plan Bridge (`LogUpSoundness`, `PlanBridge`):** Linear LogUp soundness including
   zero-denominator exclusion (`card_logup_pair_bad_or_zero_denom_le`), sharded `MEMSEG = 16`
   interval uniqueness → `Aiur.WidthROM.Valid` (including vectorized ROM
   `vectorized_rom_widthROM_valid`), field-level LogUp balance → integer
   `Aiur.Optimized.Grouping.Plan.checkMemo`, and composition with `IxVM.Refinement.CircuitSound`
   (`ixvm_circuit_sound_of_extracted_trace`).

## Current Scope & Remaining Inter-Stage Bridges
- **Horner-vs-tensor batching & shipped `v6` verifier gap:** `CertiFRI`'s proved
  `Fri.verify` soundness theorems (`goldilocks_pruned_fri_soundness`, `CertiFriProofs.Audit128`)
  cover Horner-batched, binary-folding FRI over a 64-byte `Digest64` type (or plain unkeyed
  BLAKE3 in the quadratic-extension model), whereas the shipped Protocol `v6` verifier uses
  multilinear tensor batching (`FriBatching::Tensor`), cubic extension `Fp^3`, and 32-byte
  `BLAKE3 derive_key` digests. No soundness theorem covers the shipped tensor-batched `v6`
  verifier.
- **Executable verifier ↔ ROM model gap:** No theorem here yet bridges the executable
  `Ix.Cert.MultiStark.{verifyBatch, verifyBatchBytes}` / `shardFriChallenges` BLAKE3 transcript
  (which omits observing `points`) to `goldilocks_pruned_fri_soundness` (which uses CertiFRI's
  standalone `freeChallenger` ROM) or to `soundness_dynamic_rom` (which is parameterized by an
  abstract `RbrSound` predicate not yet instantiated to the full multi-shard verifier).
- **Extracted-trace entry point:** `ixvm_circuit_sound_of_extracted_trace` starts from
  already-extracted trace hypotheses (`rom`, `rows`, `inspected`, `hbal`, `hmemseg`) rather
  than extracting those trace polynomials cryptographically from `verifyBatchBytes` acceptance.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping

/-- **End-to-End Multi-STARK → `IxVM.Refinement.CircuitSound` Composition:**

Given `IxVM.Refinement.CircuitSound P` (a hypothesis: the endpoint proves it only
for the nested two-run property of `CircuitComposed`, via
`IxVM.Refinement.Endpoint.circuitComposed`, not for `IxVMClaimSpecIn`, whose target
`VerifyClaimSoundIn` is unproved) and an extracted Multi-STARK
trace `(rom, rows)` satisfying:
- sharded `MEMSEG = 16` interval balance against sorted disjoint preamble intervals
  (proving `rom.Valid` via `memseg_balance_implies_unique`),
- per-row AIR polynomial satisfaction (`rows.mapM (plan.inspectRow _) = .ok inspected`), and
- Goldilocks field-level LogUp balance for `root` (proving `plan.checkMemo = .ok ()`
  via `plan_checkMemo_of_field_balance`),

we obtain an observed `IxVM::verify_claim` source derivation whose calls are carried
in `rom` and which satisfies the refinement property `P calls d`! -/
theorem ixvm_circuit_sound_of_extracted_trace
    {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop}
    (hcirc : IxVM.Refinement.CircuitSound P)
    {id : String → Except String ℕ}
    {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {rom : Aiur.WidthROM IxVM.F}
    (hrom_len : rom.entries.length ≤ 2 ^ 39)
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Fp, (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
        memsegBoundary (ivlsOf w) x = 0)
    (d : IxVM.Refinement.Digest)
    {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
    {result : Aiur.Value IxVM.F}
    (signed : Erasure.Signed compiled.system
      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    {root : Message IxVM.F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.system
        { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (outside : root.channel ∉ cfg.names)
    (rows : List (Row IxVM.F)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (RuleClaims (Message IxVM.F))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (activeRules inspected)).length < CertiFri.P3.Goldilocks.order)
    (provWeight : RuleClaims (Message IxVM.F) → Fp)
    (hbal : ∀ claim ∈ Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (activeRules inspected),
        (((activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
          ((((Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (activeRules inspected)).countP fun x => decide (x = claim)) : ℕ) : Fp))
    (arguments : Aiur.DecodesValues specialized.program.enums wires
      (Aiur.entryValues [IxVM.Refinement.digestValue d]))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap calls,
      Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
        [IxVM.Refinement.digestValue d] [] value heap calls ∧
      Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧
      P calls d := by
  have hvalid : rom.Valid := widthROM_valid_of_count_le_one rom fun w x =>
    (memseg_balance_implies_unique (hdisj w) (hrom_lt w) (hmemseg w) x).2
  obtain ⟨wrows, hlen, hchecked⟩ := plan_checkMemo_of_field_balance plan (Erasure.rawROM rom) root
    rows inspected hctx hinsp hdem_lt provWeight hbal
  exact hcirc compiled physical certified bits plan activated hvalid hrom_len d signed rooted
    outside (hlen ▸ hrows_len) hchecked arguments decoded

/-- **Goldilocks Pruned-MMCS Concrete FRI Soundness Instantiation (`Fp^3`):**
Instantiates `soundness_pruned_uniqueDecoding` at the concrete Goldilocks
cubic-extension `goldilocksFieldModel` (`p = 2^64 - 2^32 + 1`, `K = Fp[X]/(X^3 - X - 1)`),
eliminating all abstract field-model hypotheses. -/
theorem goldilocks_pruned_fri_soundness
    (params : CertiFri.FriParams) (shape : CertiFri.Fri.ClaimShape)
    (hlog : CertiFri.Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ CertiFri.Fri.logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((CertiFri.Fri.claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ CertiFri.Fri.logMaxHeight params.logBlowup shape) /
        Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ CertiFri.Fri.logMaxHeight params.logBlowup shape) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {D : Type} [DecidableEq D] [Inhabited D] [Fintype D]
    {A : Type*}
    {adv : CertiFri.Oracle.OracleComp
      (CertiFri.Exec.OracleAnswer (D := D) goldilocksFieldModel params shape
        (goldilocksWellFormed params shape hlog)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → PrunedAttempt CertiFri.P3.Goldilocks CertiFri.P3.GoldilocksExt3 D) :
    CertiFri.Oracle.OracleComp.prob (fun res l =>
        (∃ f : ∀ x, CertiFri.Exec.OracleAnswer (D := D) goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog) x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsPruned goldilocksFieldModel params shape
              (goldilocksWellFormed params shape hlog) f (attempt res.1) = true) ∧
        CertiFri.PcsRbr.ClaimsFail
          (CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).ldt
          (CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).shift (1 - δ)
          ((CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).claims
            (CertiFri.Exec.view goldilocksFieldModel params shape
              (CertiFri.Fri.firstMessage (attempt res.1).commitments
                (attempt res.1).points (attempt res.1).values))
            (CertiFri.Oracle.committedRow l)))
      (experimentPruned goldilocksFieldModel params shape
        (goldilocksWellFormed params shape hlog) adv attempt) [] ≤
      (Q + ((CertiFri.Exec.modelParams goldilocksFieldModel params shape
          (goldilocksWellFormed params shape hlog)).rounds + 2) +
          2 * (CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).verifierQueries) * εmax +
        ((max ((CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).batches +
            (CertiFri.Exec.modelParams goldilocksFieldModel params shape
              (goldilocksWellFormed params shape hlog)).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((CertiFri.Exec.modelParams goldilocksFieldModel params shape
            (goldilocksWellFormed params shape hlog)).rounds + 2) +
            2 * (CertiFri.Exec.modelParams goldilocksFieldModel params shape
              (goldilocksWellFormed params shape hlog)).verifierQueries) ^ 2 /
          (4 * Fintype.card D) :=
  soundness_pruned_uniqueDecoding goldilocksFieldModel params shape
    (goldilocksWellFormed params shape hlog) hheight hδ hrate hα hβ hq hadv attempt

end Ix.Cert.MultiStark
