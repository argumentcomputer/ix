import Ix.Cert.MultiStarkRefinement.AirLogUpPcs
import Ix.Cert.MultiStark.EndToEnd
import Aiur.Optimized.Observed

/-! # Formal Refinement Scaffold for `MultiStark.recursionProgram` (Workstream 1A-ii)

Composes the currently proved refinement components for `MultiStark.recursionProgram`:
1. `prepared_obs_of_extracted_trace`: lifts an already-extracted Multi-STARK trace `(rom, rows)`
   (sharded `MEMSEG = 16` interval balance + `Plan.inspectRow` + Goldilocks LogUp balance,
   `rows.length ≤ 2^39`) directly to an observed source derivation `prepared.ObsFn` whose
   calls are carried by `compiled.traceROM rom` (`CallsInROM`), via
   `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed`.
2. `recursion_obs_refines_verifyBatch`: refines a `RecursionExecutionRefines` witness for
   `MultiStark::verify_multi_stark_proof` onto `Ix.Cert.MultiStark.{verifyBatch, verifyBatchBytes}`
   up to a concrete BLAKE3 collision exhibited in `calls`.
3. `recursionProgram_refines_multiStark_verify`: conditional circuit-to-verifier headline for
   `MultiStark.recursionProgram` (`RecursionVerifierAstPinned MultiStark.recursionProgram = true`),
   **parameterized by the uninstantiated inter-stage hypothesis `RecursionSourceSound prepared`**.
4. `recursive_step_to_ixvm_circuit_sound`: bundles an outer `RecursionExecutionRefines` witness
   with an independently supplied inner extracted IxVM trace to yield `IxVM.Refinement.CircuitSound P`.

## Current Scope & Remaining Inter-Stage Bridges
- **`RecursionSourceSound prepared` is NOT yet instantiated** for `MultiStark.recursionProgram`:
  proving that every `prepared.ObsFn verifyMultiStarkEntry` execution of the deployed Aiur source
  actually constructs `WireDecodingWitness` and `BatchVerifyWitness` (source-to-witness
  extraction) remains open.
- **`RecursionVerifierAstPinned`** checks required callee presence and minimum `assert_eq!` counts
  in five functions (`verify_multi_stark_proof`, `verify_batch`, `verify_shard`, `rows_pop`,
  `finalize_buckets`); it is a structural regression pin, not a semantic equivalence check.
- **`prepared_obs_of_extracted_trace` and `recursive_step_to_ixvm_circuit_sound`** start from
  already-extracted trace hypotheses (`rom`, `rows`, `inspected`, `hbal`, `hmemseg`), and in
  `recursive_step_to_ixvm_circuit_sound` the inner extracted IxVM trace is supplied separately
  rather than extracted cryptographically from the outer `verifyBatchBytes` acceptance.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping
open CertiFri CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. Observed Trace Bridge for Any Goldilocks `Aiur.Modules.Program` -/

/-- **Observed Extracted-Trace → `Modules.Prepared.ObsFn` Bridge (Goldilocks):**
Upgrades `Ix.Cert.MultiStark.prepared_eval_of_extracted_trace` to the observed headline
(`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed`), yielding
`prepared.ObsFn external args value heap calls`, `Represents`, and `CallsInROM`.
Applies uniformly to `MultiStark.recursionProgram` and `MultiStark.aggregateProgram`. -/
theorem prepared_obs_of_extracted_trace
    {program : Aiur.Modules.Program Fp}
    (prepared : Aiur.Modules.Prepared program)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Depth.Certified cfg physical.system) (bits : cfg.bits ≤ 24)
    {id : String → Except String ℕ}
    (plan : Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : Aiur.WidthROM Fp}
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Fp, (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
        memsegBoundary (ivlsOf w) x = 0)
    {args : List (Aiur.SourceValue Fp)} {result : Aiur.Value Fp}
    {wires : List (Aiur.WireValue Fp)} {output : Aiur.WireValue Fp}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message Fp}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (rows : List (Row Fp)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (RuleClaims (Message Fp))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (activeRules inspected)).length < CertiFri.P3.Goldilocks.order)
    (provWeight : RuleClaims (Message Fp) → Fp)
    (hbal : ∀ claim ∈ Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (activeRules inspected),
        (((activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
          ((((Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (activeRules inspected)).countP fun x => decide (x = claim)) : ℕ) : Fp))
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Aiur.Represents (compiled.traceROM rom) heap value result ∧
      Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls := by
  have hvalid : rom.Valid := widthROM_valid_of_count_le_one rom fun w x =>
    (memseg_balance_implies_unique (hdisj w) (hrom_lt w) (hmemseg w) x).2
  obtain ⟨wrows, hlen, hchecked⟩ := plan_checkMemo_of_field_balance plan (Erasure.rawROM rom) root
    rows inspected hctx hinsp hdem_lt provWeight hbal
  exact prepared.depth_grouped_activated_heap_sound_goldilocks_observed compiled physical certified
    bits plan activated selected hvalid signed rooted outside (hlen ▸ hrows_len) hchecked
    arguments decoded

/-! ## 2. Source-Level Refinement of `MultiStark::verify_multi_stark_proof` -/

/-- The source-level refinement relation for an observed execution of
`MultiStark::verify_multi_stark_proof(systemDigest, claimsDigest)`:
the observed run's BLAKE3 calls and verifier checks decode `(sbytes, cbytes, proofBytes)` into
`(sys, expectedClaims, batch)` satisfying `WireDecodingWitness` and `BatchVerifyWitness`
at default `maxLogDeg = 32 - sys.params.logBlowup`. -/
structure RecursionExecutionRefines
    (calls : List (Aiur.Generic.SourceSemantics.Call Fp))
    (systemDigest claimsDigest : Fin 8 → Fp) where
  sbytes : ByteArray
  cbytes : ByteArray
  proofBytes : ByteArray
  sys : StarkSystem
  expectedClaims : Array (Array F)
  batch : BatchProof
  wire : WireDecodingWitness calls systemDigest claimsDigest
    sbytes cbytes proofBytes sys expectedClaims batch
  verify : BatchVerifyWitness sys batch (32 - sys.params.logBlowup) expectedClaims

/-- Source-level soundness contract for a prepared `MultiStark.recursionProgram`:
every observed execution of `MultiStark::verify_multi_stark_proof` on `(sysDig, clDig)`
admits a `RecursionExecutionRefines` witness. -/
def RecursionSourceSound (prepared : Aiur.Modules.Prepared MultiStark.recursionProgram) : Prop :=
  ∀ (sysDig clDig : Fin 8 → Fp) (value : Aiur.SourceValue Fp) (heap : Aiur.Heap Fp)
    (calls : List (Aiur.Generic.SourceSemantics.Call Fp)),
    prepared.ObsFn verifyMultiStarkEntry [digest8SourceValue sysDig, digest8SourceValue clDig]
      value heap calls →
    Nonempty (RecursionExecutionRefines calls sysDig clDig)

/-- **Core Refinement Theorem (`recursion_obs_refines_verifyBatch`):**
Given `RecursionExecutionRefines calls (packDigest8 (blake3Pure vkBytes)) (packDigest8 (blake3Pure claimsBytes))`:
EITHER the recursive verifier run hashed a concrete BLAKE3 collision against `[vkBytes, claimsBytes]`,
OR there exist decoded `(sys, expectedClaims, batch, proofBytes)` such that:
1. `StarkSystem.fromBytes vkBytes = .ok sys`, `decodeClaims claimsBytes = .ok expectedClaims`,
   `BatchProof.fromBytes proofBytes = .ok batch`,
2. `Ix.Cert.MultiStark.verifyBatch sys batch = some expectedClaims`,
3. `Ix.Cert.MultiStark.verifyBatchBytes vkBytes claimsBytes proofBytes = true`, and
4. For every width `w`, the batch preamble's `MEMSEG` messages induce `DisjointIntervals`. -/
theorem recursion_obs_refines_verifyBatch
    {calls : List (Aiur.Generic.SourceSemantics.Call Fp)}
    {vkBytes claimsBytes : ByteArray}
    (href : RecursionExecutionRefines calls
      (packDigest8 (Address.blake3Pure vkBytes))
      (packDigest8 (Address.blake3Pure claimsBytes))) :
    MultiStarkCollision [vkBytes, claimsBytes] calls ∨
      ∃ (proofBytes : ByteArray) (sys : StarkSystem) (expectedClaims : Array (Array F))
        (batch : BatchProof),
        StarkSystem.fromBytes vkBytes = .ok sys ∧
        decodeClaims claimsBytes = .ok expectedClaims ∧
        BatchProof.fromBytes proofBytes = .ok batch ∧
        verifyBatch sys batch = some expectedClaims ∧
        verifyBatchBytes vkBytes claimsBytes proofBytes = true ∧
        (∀ w, DisjointIntervals (extractWidthIntervals w batch.preamble.messages.toList)) := by
  rcases wire_decoding_authentic_or_collision href.wire with hcol | ⟨_, _, hsys, hcl, hbat⟩
  · exact Or.inl hcol
  · have hvb : verifyBatch href.sys href.batch (32 - href.sys.params.logBlowup) =
        some href.expectedClaims :=
      verifyBatch_of_witness href.verify
    have hvbb : verifyBatchBytes vkBytes claimsBytes href.proofBytes = true := by
      unfold verifyBatchBytes verifyBatchBytesWithFloor
      rw [hsys, hcl, hbat]
      have hvb' : verifyBatchWithFloor href.sys href.batch (32 - href.sys.params.logBlowup) false false =
          some href.expectedClaims := hvb
      simp only [Option.getD_none, hvb', beq_self_eq_true]
    exact Or.inr ⟨href.proofBytes, href.sys, href.expectedClaims, href.batch,
      hsys, hcl, hbat, hvb, hvbb,
      fun w => closurePairsAccepted_disjoint href.verify.closure_ok w⟩

/-! ## 3. Full Circuit-to-Verifier Headline for `MultiStark.recursionProgram` -/

/-- **Workstream 1A-ii Conditional Headline (`recursionProgram_refines_multiStark_verify`):**
For the deployed recursive verifier `MultiStark.recursionProgram`
(`RecursionVerifierAstPinned MultiStark.recursionProgram = true`), any already-extracted Multi-STARK
trace `(rom, rows)` (`rows.length ≤ 2^39`) of `MultiStark::verify_multi_stark_proof` on public
digests `(packDigest8 (blake3Pure vkBytes), packDigest8 (blake3Pure claimsBytes))` yields an
observed source derivation whose calls are carried by `compiled.traceROM rom`, and under the
(not yet instantiated) source-level hypothesis `RecursionSourceSound prepared`, EITHER exhibits a
concrete BLAKE3 collision in `calls` OR certifies
`Ix.Cert.MultiStark.verifyBatchBytes vkBytes claimsBytes proofBytes = true` (with
`verifyBatch sys batch = some expectedClaims` and per-width `DisjointIntervals`). -/
theorem recursionProgram_refines_multiStark_verify
    (prepared : Aiur.Modules.Prepared MultiStark.recursionProgram)
    (hsound : RecursionSourceSound prepared)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Depth.Certified cfg physical.system) (bits : cfg.bits ≤ 24)
    {id : String → Except String ℕ}
    (plan : Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {entry : Aiur.Modules.Selection MultiStark.recursionProgram
      prepared.environment.assembly.instances}
    (selected : prepared.find? verifyMultiStarkEntry = some entry)
    {rom : Aiur.WidthROM Fp}
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Fp, (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Fp)) +
        memsegBoundary (ivlsOf w) x = 0)
    (vkBytes claimsBytes : ByteArray)
    {result : Aiur.Value Fp}
    {wires : List (Aiur.WireValue Fp)} {output : Aiur.WireValue Fp}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message Fp}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (rows : List (Row Fp)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (RuleClaims (Message Fp))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (activeRules inspected)).length < CertiFri.P3.Goldilocks.order)
    (provWeight : RuleClaims (Message Fp) → Fp)
    (hbal : ∀ claim ∈ Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (activeRules inspected),
        (((activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
          ((((Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (activeRules inspected)).countP fun x => decide (x = claim)) : ℕ) : Fp))
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires
      (Aiur.entryValues
        [digest8SourceValue (packDigest8 (Address.blake3Pure vkBytes)),
         digest8SourceValue (packDigest8 (Address.blake3Pure claimsBytes))]))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    RecursionVerifierAstPinned MultiStark.recursionProgram = true ∧
    ∃ value heap calls,
      prepared.ObsFn verifyMultiStarkEntry
        [digest8SourceValue (packDigest8 (Address.blake3Pure vkBytes)),
         digest8SourceValue (packDigest8 (Address.blake3Pure claimsBytes))]
        value heap calls ∧
      Aiur.Represents (compiled.traceROM rom) heap value result ∧
      Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧
      (MultiStarkCollision [vkBytes, claimsBytes] calls ∨
        ∃ (proofBytes : ByteArray) (sys : StarkSystem) (expectedClaims : Array (Array F))
          (batch : BatchProof),
          StarkSystem.fromBytes vkBytes = .ok sys ∧
          decodeClaims claimsBytes = .ok expectedClaims ∧
          BatchProof.fromBytes proofBytes = .ok batch ∧
          verifyBatch sys batch = some expectedClaims ∧
          verifyBatchBytes vkBytes claimsBytes proofBytes = true ∧
          (∀ w, DisjointIntervals (extractWidthIntervals w batch.preamble.messages.toList))) := by
  refine ⟨recursionProgram_ast_pinned, ?_⟩
  obtain ⟨value, heap, calls, hobs, hrep, hcalls⟩ :=
    prepared_obs_of_extracted_trace prepared compiled physical certified bits plan activated
      selected ivlsOf hdisj hrom_lt hmemseg signed rooted outside rows hrows_len inspected
      hctx hinsp hdem_lt provWeight hbal arguments decoded
  exact ⟨value, heap, calls, hobs, hrep, hcalls,
    (hsound _ _ value heap calls hobs).elim recursion_obs_refines_verifyBatch⟩

/-- **Recursive Multi-STARK Verification + Inner Extracted Trace → `IxVM.Refinement.CircuitSound`:**
Bundles `recursion_obs_refines_verifyBatch` (outer `RecursionExecutionRefines` witness) with
`Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace` (an independently supplied inner
extracted IxVM trace): when `hOuter` holds AND the supplied inner trace satisfies sharded
`MEMSEG` + `Plan.inspectRow` + LogUp balance, we obtain both the outer `verifyBatchBytes`
certificate (up to BLAKE3 collision) AND the inner observed `IxVM::verify_claim` derivation
satisfying `P callsInner d`. (Cryptographic extraction of the inner trace from the outer
`verifyBatchBytes` acceptance is not yet bridged here.) -/
theorem recursive_step_to_ixvm_circuit_sound
    -- Outer recursive Multi-STARK verifier
    {callsOuter : List (Aiur.Generic.SourceSemantics.Call Fp)}
    {vkBytes claimsBytes : ByteArray}
    (hOuter : RecursionExecutionRefines callsOuter
      (packDigest8 (Address.blake3Pure vkBytes))
      (packDigest8 (Address.blake3Pure claimsBytes)))
    -- Inner IxVM CircuitSound & extracted inner trace
    {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop}
    (hcirc : IxVM.Refinement.CircuitSound P)
    {id : String → Except String ℕ}
    {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Depth.Certified cfg physical.system)
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
    MultiStarkCollision [vkBytes, claimsBytes] callsOuter ∨
      ((∃ proofBytes, verifyBatchBytes vkBytes claimsBytes proofBytes = true) ∧
       ∃ value heap callsInner,
         Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
           [IxVM.Refinement.digestValue d] [] value heap callsInner ∧
         Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) callsInner ∧
         P callsInner d) := by
  rcases recursion_obs_refines_verifyBatch hOuter with hcol | ⟨pb, _, _, _, _, _, _, _, hvbb, _⟩
  · exact Or.inl hcol
  · refine Or.inr ⟨⟨pb, hvbb⟩, ?_⟩
    exact ixvm_circuit_sound_of_extracted_trace hcirc compiled physical certified bits plan
      activated hrom_len ivlsOf hdisj hrom_lt hmemseg d signed rooted outside rows hrows_len
      inspected hctx hinsp hdem_lt provWeight hbal arguments decoded

end Ix.Cert.MultiStarkRefinement
