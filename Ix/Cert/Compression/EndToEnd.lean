import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.RecursiveKzg
import Ix.Cert.Compression.FriVerifier

/-! # Proof-Compression Certification Composition Scaffold

Bundles the four independently proved stage theorems of the BN254 proof-compression
stack into a single theorem signature:

1. **Stage 5 (Gnark Outer-IR):** `OuterRelation.gnark_outer_relation_sound` reduces a
   `GnarkOuterAccepted` witness against `vk` (`vk.programDigest = outerProg.digest`) to either
   a BLAKE3 collision or `vk.expectedProgram.Satisfied inp out ∧ PairingCheck out`.
2. **Stage 4–3 (Final & First Recursive KZG over `BN254Fr`):**
   `RecursiveKzg.recursiveKzgCircuit_sound` reduces a Plonkish witness `hKzg` satisfying
   `buildRecursiveKzgCircuit` to `FiveChannelSatisfied` over `BN254Fr`.
   (The standalone algebraic KZG theorems `RecursiveKzg.kzg_pairing_sound_at_bn254G1` and
   `RecursiveKzg.kzg_batched_horner_bad_card` are proved in `RecursiveKzg.lean` and not yet
   wired into this composition theorem.)
3. **Stage 2 (BN254 Foreign-Field Compiler → Goldilocks Plonkish FRI Verifier):**
   `FriVerifier.foreign_friVerifier_sound` (`Foreign.foreign_compile_sound_lifted` composed
   with `FriVerifier.friVerifierCircuit_sound`) lifts a BN254 Plonkish witness `hFri` satisfying
   `Foreign.foreignCompile (buildFriVerifierCircuit base layout)` on `liftPublicInputs pub`
   down to `FriVerifierSatisfied base layout pub (projectGoldilocksWire w_fr)` in Goldilocks.
4. **Stage 1 (Multi-STARK → `IxVM.Refinement.CircuitSound`):**
   `Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace` bridges an already-extracted
   Multi-STARK trace (`MEMSEG` + `Plan.inspectRow` + Goldilocks LogUp balance) to
   `IxVM.Refinement.CircuitSound P` (a hypothesis; the endpoint proves it only for the nested
   two-run property of `CircuitComposed`, via `IxVM.Refinement.Endpoint.circuitComposed`).

## Current Scope & Remaining Inter-Stage Bridges
This module is a **stage-isolated composition scaffold**, NOT yet an end-to-end cryptographic
reduction from an on-chain Gnark proof to `IxVM`:
- **Unchained stage hypotheses:** `compression_pipeline_sound` and
  `compression_pipeline_folded_pairing_sound` take four independent stage witnesses
  (`acc : GnarkOuterAccepted ...`, `hKzg`, `hFri`, and the extracted Multi-STARK trace
  `(rom, rows, inspected, hbal, hmemseg)`) with no cross-stage wiring constraining one stage's
  public inputs/outputs to extract or imply the next stage's witness.
- **Abstract Gnark acceptance (`GnarkOuterAccepted`):** `GnarkOuterAccepted` directly carries
  `programSat : outerProgram.Satisfied inp outputs` and `pairingHolds : PairingCheck outputs`
  as structure fields; Groth16/PLONK knowledge soundness and linkage to `tools/gnark/circuit.go`
  are not yet formalized here.
- **Foreign-field circuit model:** `hFri` targets the idealized unoptimized
  `Foreign.foreignCompile` model rather than the production Halo2/BN254 constraint system.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.Compression

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeCurveMsm
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.RecursiveKzg
open Ix.Cert.Compression.FriVerifier

/-- **Stage-Isolated Proof-Compression Composition Scaffold (`compression_pipeline_sound`):**

Bundles four independently supplied stage hypotheses into a single conjunction:
- Gnark Outer-IR witness (`acc : GnarkOuterAccepted`, assuming `programSat` and `pairingHolds`,
  yielding `vk.expectedProgram.Satisfied` up to BLAKE3 collision),
- Recursive KZG verifier satisfaction (`hKzg`, yielding `FiveChannelSatisfied` over `BN254Fr`),
- Unoptimized foreign-compiled BN254 → Goldilocks FRI verifier witness (`hFri`, yielding
  `FriVerifierSatisfied` over `GoldilocksF`),
- Already-extracted Multi-STARK trace (`rom`, `rows`, `inspected`, `hbal`, `hmemseg`) →
  `IxVM.Refinement.CircuitSound P`.

Note: the four stage witnesses are NOT yet chained to one another (inter-stage public-input
binding and cryptographic SNARK/KZG/FRI extractors remain to be bridged). -/
theorem compression_pipeline_sound
    {vk : GnarkVerifyingKey} {inp : OuterInputs} {PairingCheck : OuterOutputs → Prop}
    (acc : GnarkOuterAccepted vk inp PairingCheck)
    (kzgBase : Circuit BN254Fr) (kzgLayout : FiveChannelLayout)
    (kzgPub : List BN254Fr) (wKzg : Wire → BN254Fr)
    (hKzg : (buildRecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg)
    (friBase : Circuit GoldilocksF) (friLayout : FriVerifierLayout)
    (hMerkleLen : ∀ s ∈ friLayout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (friPub : List GoldilocksF) (wFriFr : Wire → BN254Fr)
    (hFri : (foreignCompile (buildFriVerifierCircuit friBase friLayout)).Satisfies
      (liftPublicInputs friPub) wFriFr)
    {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop}
    (hcirc : IxVM.Refinement.CircuitSound P)
    {id : String → Except String ℕ}
    {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {rom : Aiur.WidthROM IxVM.F}
    (hrom_len : rom.entries.length ≤ 2 ^ 39)
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Ix.Cert.MultiStark.Fp,
        (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Ix.Cert.MultiStark.Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Ix.Cert.MultiStark.Fp)) +
        Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x = 0)
    (d : IxVM.Refinement.Digest)
    {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
    {result : Aiur.Value IxVM.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.system
      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    {root : Aiur.Circuit.Message IxVM.F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.system
        { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (outside : root.channel ∉ cfg.names)
    (rows : List (Aiur.Circuit.Row IxVM.F)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Aiur.Circuit.Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (Aiur.Optimized.Grouping.activeRules inspected)).length <
        CertiFri.P3.Goldilocks.order)
    (provWeight : Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F) → Ix.Cert.MultiStark.Fp)
    (hbal : ∀ claim ∈ Aiur.Circuit.Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (Aiur.Optimized.Grouping.activeRules inspected),
        (((Aiur.Optimized.Grouping.activeRules inspected).filter fun r =>
          decide (r.1 = claim)).map provWeight).sum =
          ((((Aiur.Circuit.Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (Aiur.Optimized.Grouping.activeRules inspected)).countP fun x =>
              decide (x = claim)) : ℕ) : Ix.Cert.MultiStark.Fp))
    (arguments : Aiur.DecodesValues specialized.program.enums wires
      (Aiur.entryValues [IxVM.Refinement.digestValue d]))
    (decoded : output.decode specialized.program.enums = some result) :
    (acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode) ∨
    ((∃ out, vk.expectedProgram.Satisfied inp out ∧ PairingCheck out) ∧
     FiveChannelSatisfied kzgBase kzgLayout kzgPub wKzg ∧
     FriVerifierSatisfied friBase friLayout friPub (projectGoldilocksWire wFriFr) ∧
     ∃ value heap calls,
       Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
         [IxVM.Refinement.digestValue d] [] value heap calls ∧
       Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧
       P calls d) := by
  have hOuter := gnark_outer_relation_sound acc
  rcases hOuter with hCol | hSatOuter
  · exact Or.inl hCol
  · refine Or.inr ⟨hSatOuter, ?_, ?_, ?_⟩
    · exact recursiveKzgCircuit_sound kzgBase kzgLayout kzgPub wKzg hKzg
    · exact foreign_friVerifier_sound friBase friLayout hMerkleLen friPub wFriFr hFri
    · exact Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace hcirc compiled physical
        certified bits plan activated hrom_len ivlsOf hdisj hrom_lt hmemseg d signed rooted
        outside rows hrows_len inspected hctx hinsp hdem_lt provWeight hbal arguments decoded

/-- **Folded-Pairing Composition Scaffold (`compression_pipeline_folded_pairing_sound`):**
Specializes `compression_pipeline_sound` to `FoldedPairingCheck` (the folded BN254 pairing
relation modeling `tools/gnark/circuit.go`), yielding that either an `"ix/outer-ir/v1"` BLAKE3
collision occurred, OR all four independently supplied stages hold with either both individual
outer and deferred BN254 pairing checks valid (`outer = 1 ∧ deferred = 1`) or `ρ` hitting the
bad folding challenge set of size `≤ 1` out of `bn254FrModulus`. As in
`compression_pipeline_sound`, inter-stage extraction and witness chaining remain to be bridged. -/
theorem compression_pipeline_folded_pairing_sound
    {vk : GnarkVerifyingKey} {inp : OuterInputs}
    (bp : BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BN254Fr)
    (acc : GnarkOuterAccepted vk inp
      (fun out => FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ))
    (kzgBase : Circuit BN254Fr) (kzgLayout : FiveChannelLayout)
    (kzgPub : List BN254Fr) (wKzg : Wire → BN254Fr)
    (hKzg : (buildRecursiveKzgCircuit kzgBase kzgLayout).Satisfies kzgPub wKzg)
    (friBase : Circuit GoldilocksF) (friLayout : FriVerifierLayout)
    (hMerkleLen : ∀ s ∈ friLayout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (friPub : List GoldilocksF) (wFriFr : Wire → BN254Fr)
    (hFri : (foreignCompile (buildFriVerifierCircuit friBase friLayout)).Satisfies
      (liftPublicInputs friPub) wFriFr)
    {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop}
    (hcirc : IxVM.Refinement.CircuitSound P)
    {id : String → Except String ℕ}
    {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg)
    (bits : cfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {rom : Aiur.WidthROM IxVM.F}
    (hrom_len : rom.entries.length ≤ 2 ^ 39)
    (ivlsOf : ℕ → List (ℕ × ℕ))
    (hdisj : ∀ w, Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w))
    (hrom_lt : ∀ w,
      (∑ x : Ix.Cert.MultiStark.Fp,
        (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length) + 1 <
        CertiFri.P3.Goldilocks.order)
    (hmemseg : ∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
      (((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x)).length : Ix.Cert.MultiStark.Fp) -
        ((rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = x - 1)).length : Ix.Cert.MultiStark.Fp)) +
        Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x = 0)
    (d : IxVM.Refinement.Digest)
    {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
    {result : Aiur.Value IxVM.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.system
      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    {root : Aiur.Circuit.Message IxVM.F}
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Aiur.Circuit.Erasure.message compiled.system
        { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (outside : root.channel ∉ cfg.names)
    (rows : List (Aiur.Circuit.Row IxVM.F)) (hrows_len : rows.length ≤ 2 ^ 39)
    (inspected : List (Option (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F))))
    (hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) = .ok inspected)
    (hdem_lt : (Aiur.Circuit.Balance.required
        (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
        root (Aiur.Optimized.Grouping.activeRules inspected)).length <
        CertiFri.P3.Goldilocks.order)
    (provWeight : Aiur.Circuit.RuleClaims (Aiur.Circuit.Message IxVM.F) → Ix.Cert.MultiStark.Fp)
    (hbal : ∀ claim ∈ Aiur.Circuit.Balance.required
          (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
          root (Aiur.Optimized.Grouping.activeRules inspected),
        (((Aiur.Optimized.Grouping.activeRules inspected).filter fun r =>
          decide (r.1 = claim)).map provWeight).sum =
          ((((Aiur.Circuit.Balance.required
            (fun c => decide ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
            root (Aiur.Optimized.Grouping.activeRules inspected)).countP fun x =>
              decide (x = claim)) : ℕ) : Ix.Cert.MultiStark.Fp))
    (arguments : Aiur.DecodesValues specialized.program.enums wires
      (Aiur.entryValues [IxVM.Refinement.digestValue d]))
    (decoded : output.decode specialized.program.enums = some result) :
    (acc.outerProgram.encode ≠ vk.expectedProgram.encode ∧
      Blake3.Pure.digest acc.outerProgram.encode = Blake3.Pure.digest vk.expectedProgram.encode) ∨
    ((∃ out, vk.expectedProgram.Satisfied inp out ∧
        ((bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1 ∧
          bp.deferredPairingVal deferredKeys d0 d1 = 1) ∨
         (FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ ∧
          (Finset.univ.filter fun ρ' : BN254Fr =>
            FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ').card ≤ 1))) ∧
     FiveChannelSatisfied kzgBase kzgLayout kzgPub wKzg ∧
     FriVerifierSatisfied friBase friLayout friPub (projectGoldilocksWire wFriFr) ∧
     ∃ value heap calls,
       Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
         [IxVM.Refinement.digestValue d] [] value heap calls ∧
       Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧
       P calls d) := by
  rcases gnark_folded_pairing_sound bp outerKeys deferredKeys leftOf rightOf d0 d1 ρ acc with hCol | hFold
  · exact Or.inl hCol
  · refine Or.inr ⟨hFold, ?_, ?_, ?_⟩
    · exact recursiveKzgCircuit_sound kzgBase kzgLayout kzgPub wKzg hKzg
    · exact foreign_friVerifier_sound friBase friLayout hMerkleLen friPub wFriFr hFri
    · exact Ix.Cert.MultiStark.ixvm_circuit_sound_of_extracted_trace hcirc compiled physical
        certified bits plan activated hrom_len ivlsOf hdisj hrom_lt hmemseg d signed rooted
        outside rows hrows_len inspected hctx hinsp hdem_lt provWeight hbal arguments decoded

end Ix.Cert.Compression
