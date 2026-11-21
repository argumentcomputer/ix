import Ix.Cert.Aggr.ConditionalShard
import Ix.Cert.Aggr.Shapes
import Ix.Cert.MultiStarkRefinement.EndToEnd
import Ix.Cert.MultiStark.EndToEnd

/-! # End-to-End Aggregated Root Soundness (`Ix.Cert.Aggr.EndToEnd`, Workstreams `1B` + `5A`/`5B`)

Composes the complete certification stack from an accepted outer `MultiStark.aggregateProgram`
trace (`MultiStark::ix_aggr`) spanning ALL 19 aggregation shapes (`0..18`) down to:
- Pinned deployed Aiur programs (`MultiStark.recursionProgram` and `MultiStark.aggregateProgram`),
- Observed trace extraction (`prepared_obs_of_extracted_trace` via
  `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed`),
- Recursive `MultiStark.recursionProgram` verification (`recursion_obs_refines_verifyBatch`),
- Multi-node ROM tree error union bound (`tree_rom_error_bound`),
- Inductive 19-shape soundness (`Aggr.aggrDerivation19_checkEnv_sound`, `catalog_sound`,
  `dynamicLink_sound`),
- Tier 1 & Tier 2 dynamic linking (`Ix.DynamicLink.Soundness`),
- Conditional shards `CheckEnv(S, A)` with `A7` axiom merging and Shape 18 eval discharge, and
- Unconditional set-theoretic models via frozen `IxVM.Consistency.ComposedSpec` (`CircuitComposed`).

Also includes three constructive negative controls verifying rejection of:
1. Weak Shape 17 security envelopes (`< 220` conjectured security bits),
2. `A7` dropped user axioms during pair/discharge merge, and
3. Shape 18 premature full discharge (`10 → 3` / `11 → 4`) with an undischarged `EvalAssumption`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

universe u

namespace Ix.Cert.Aggr

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping
open CertiFri CertiFri.P3
open Ix.Cert.MultiStark
open Ix.Cert.MultiStarkRefinement
open Ix.DynamicLink
open IxVM.Consistency IxVM.Refinement
open _root_.Aggr

/-! ## 1. General Headline Theorem: `aggregated_root_sound` (All 19 Shapes `0..18`) -/

/-- **Main Headline Theorem (`aggregated_root_sound`):**
Given:
1. An extracted outer Multi-STARK trace `(rom, rows)` (`rows.length ≤ 2^39`) of the pinned
   deployed `MultiStark.aggregateProgram` at entry `MultiStark::ix_aggr`, satisfying sharded
   `MEMSEG = 16` interval balance, `Plan.inspectRow`, and Goldilocks field-level LogUp balance;
2. An accepted 19-shape aggregation proof tree `t : AcceptedAggrTree sem batchClaim rootStmt`
   whose `M = t.verificationCount` recursive Multi-STARK child verifications have per-node
   ROM failure probabilities `nodeProbs` each bounded by `ε`;

Then:
- Both deployed Aiur programs (`MultiStark.recursionProgram` and `MultiStark.aggregateProgram`)
  satisfy their kernel-checked AST pins;
- The outer trace yields an observed `MultiStark::ix_aggr` derivation whose calls are carried
  by `compiled.traceROM rom`;
- The cumulative ROM error bound across all `M` recursive verifications satisfies
  `nodeProbs.sum ≤ (t.verificationCount : ℝ) * ε`;
- The root statement satisfies `AggrNodeHolds sem rootStmt` (via `AggrDerivation19` across
  all 19 shapes `0..18`); and
- EITHER some recursive child verification hashed a concrete BLAKE3 collision (`t.HasTreeCollision`),
  OR every recursive child verification in `t` passes the certified out-of-circuit verifier
  `Ix.Cert.MultiStark.verifyBatchBytes = true`! -/
theorem aggregated_root_sound
    -- Outer `MultiStark.aggregateProgram` trace extraction
    (prepared : Aiur.Modules.Prepared MultiStark.aggregateProgram)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Depth.Certified cfg physical.system) (bits : cfg.bits ≤ 24)
    {id : String → Except String ℕ}
    (plan : Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {entry : Aiur.Modules.Selection MultiStark.aggregateProgram
      prepared.environment.assembly.instances}
    (selected : prepared.find? ixAggrEntry = some entry)
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
    (allowedDig outClaimDig : Fin 8 → Fp)
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
      (Aiur.entryValues [digest8SourceValue allowedDig, digest8SourceValue outClaimDig]))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    -- 19-shape recursive aggregation tree & ROM error union bound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {rootStmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement}
    (t : AcceptedAggrTree sem batchClaim rootStmt)
    (nodeProbs : List ℝ) {ε : ℝ}
    (hLenProbs : nodeProbs.length = t.verificationCount)
    (hNodeBound : ∀ p ∈ nodeProbs, p ≤ ε) :
    RecursionVerifierAstPinned MultiStark.recursionProgram = true ∧
    AggregateProgramAstPinned MultiStark.aggregateProgram = true ∧
    (∃ value heap calls,
      prepared.ObsFn ixAggrEntry
        [digest8SourceValue allowedDig, digest8SourceValue outClaimDig] value heap calls ∧
      Aiur.Represents (compiled.traceROM rom) heap value result ∧
      Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls) ∧
    nodeProbs.sum ≤ (t.verificationCount : ℝ) * ε ∧
    AggrNodeHolds sem rootStmt ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  have hObs := prepared_obs_of_extracted_trace prepared compiled physical certified bits plan
    activated selected ivlsOf hdisj hrom_lt hmemseg signed rooted outside rows hrows_len
    inspected hctx hinsp hdem_lt provWeight hbal arguments decoded
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  have hErr : nodeProbs.sum ≤ (t.verificationCount : ℝ) * ε := by
    rw [← hLenProbs]
    exact tree_rom_error_bound nodeProbs hNodeBound
  exact ⟨recursionProgram_ast_pinned, aggregateProgram_ast_pinned, hObs, hErr,
    aggrDerivation19_invariant hDeriv, hChildOk⟩

/-! ## 2. Specialized Corollaries: `CheckEnv`, Zero-Axiom `SetTheory` Model, `Catalog`, `DynamicLink` -/

/-- **Unconditional (or Axiom-Explicit `Ax`) `CheckEnv` Root Soundness (`aggregated_root_checkEnv_sound`):**
For any accepted 19-shape aggregation tree whose root is an assumption-free, eval-free,
binding-discharged `CheckEnv` (`validator ∈ {3, 5}`, `A = ∅`, `EvalA = ∅`, explicit axioms `Ax`),
every subject `x ∈ S` satisfies `Valid mode.bindingOf Ax x`, and either a concrete BLAKE3
collision occurred or every recursive child proof passed `verifyBatchBytes = true`! -/
theorem aggregated_root_checkEnv_sound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {Valid : Address → (Address → Prop) → Address → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) x →
      (∀ y, sem.Dep x y → Valid b Ax y) → Valid b Ax x)
    {mode : ValidatorMode Address} {S Ax : Address → Prop}
    (hDis : mode.isBindingDischarged = true)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv mode S (fun _ => False) Ax (fun _ => False))) :
    (∀ x, S x → Valid mode.bindingOf Ax x) ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  exact ⟨aggrDerivation19_checkEnv_sound hWf hStep hDis hDeriv, hChildOk⟩

/-- **Zero-Axiom Set-Theoretic Model Corollary (`aggregated_root_checkEnv_no_axioms_model`):**
When an accepted 19-shape aggregation tree closes to an unconditional `CheckEnv` root with
`Ax = ∅`, `A = ∅`, `EvalA = ∅`, and `validator = 3` (or `5`), and its unconditional subjects
are witnessed by frozen `IxVM.Consistency.ComposedSpec` (paired with its verified binding),
then in every set theory `W`, EITHER a BLAKE3 collision occurred OR the claimed environment
is consistent with a model `Ix.Kernel.Model W (claimedEnv env)` and no claimed constant has
type `False`! -/
theorem aggregated_root_checkEnv_no_axioms_model (W : Type u) [Ix.Kernel.SetTheory W]
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {mode : ValidatorMode Address} {S : Address → Prop}
    (hDis : mode.isBindingDischarged = true)
    {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {dA dB : IxVM.Refinement.Digest}
    (hComp : ComposedSpec.{u} callsA callsB dA dB)
    {bytesB : ByteArray} {spec : Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec mode.bindingOf))
    (hdB : packDigest (Address.blake3Pure bytesB) = dB)
    {bytesA : ByteArray} {cA : Ix.Claim}
    (hdeA : Ix.Claim.de bytesA = .ok cA)
    (hdA : packDigest (Address.blake3Pure bytesA) = dA)
    (hsc : InScopeTyping cA)
    {ctx : Ix.ClaimContext} (hctx : cA.context? = some ctx) (hba : ctx.binding = mode.bindingOf)
    {V : View} {seeds : List Address} (hseeds : ClaimSeeds cA V seeds)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv mode S (fun _ => False) (fun _ => False) (fun _ => False))) :
    (∀ x, S x → sem.Checked mode.bindingOf (fun _ => False) (fun _ => False) x) ∧
    (∀ x y, S x → sem.Dep x y → S y) ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) ∧
    (V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun tRole R _ => SeedsNotFalse callsA tRole R seeds) callsB mode.bindingOf) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  obtain ⟨hChk, hCl⟩ := aggrDerivation19_invariant hDeriv
  have hCond : mode.bindingCond sem.BindingValid := by
    cases mode <;> simp [ValidatorMode.isBindingDischarged, ValidatorMode.bindingCond] at hDis ⊢
  have hMod := composedModelConclusion_of_composedSpec hComp hdeB hdB hdeA hdA hsc hctx hba hseeds
  exact ⟨hChk hCond, fun x y hx hDep => (hCl x y hx hDep).elim id False.elim,
    hChildOk, composedModelConclusion_no_false W hMod⟩

/-- **`Catalog` Root Soundness (`aggregated_root_catalog_sound`, Shape `16`):**
Every member `(b, S, Ax)` of an accepted `Catalog` root satisfies `Valid b Ax x` for all
subjects `x ∈ S`. -/
theorem aggregated_root_catalog_sound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {Valid : Address → (Address → Prop) → Address → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) x →
      (∀ y, sem.Dep x y → Valid b Ax y) → Valid b Ax x)
    {members : (Address × (Address → Prop) × (Address → Prop)) → Prop}
    (t : AcceptedAggrTree sem batchClaim (.catalogStmt members)) :
    (∀ b S Ax, members (b, S, Ax) → ∀ x, S x → Valid b Ax x) ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  exact ⟨aggrDerivation19_catalog_sound hWf hStep hDeriv, hChildOk⟩

/-- **Tier 1 `DynamicLink` Root Soundness & Reification (`aggregated_root_dynamicLink_sound`, Shape `17`):**
For an accepted Shape 17 `DynamicLinkStatement` root whose `DynamicLinkValid` certifies external
trace acceptance under `accepts`, combining with an IxVM-verified soundness bridge `EvalSound`
reifies directly to the target Lean proposition `R x y`! -/
theorem aggregated_root_dynamicLink_sound
    {α β : Type} {accepts : TraceRelation}
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {s : DynamicLinkStatement}
    (hDLTrace : sem.DynamicLinkValid s →
      accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim)
    {encode : α → β → Array UInt64} {R : α → β → Prop} {x : α} {y : β}
    (hEnc : encode x y = s.expectedMultiStarkClaim)
    (hBridge : EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode R)
    (t : AcceptedAggrTree sem batchClaim (.dynamicLinkStmt s)) :
    R x y ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  have hDL : sem.DynamicLinkValid s := aggrDerivation19_dynamicLink_sound hDeriv
  exact ⟨reify_accepted_eval_trace (hDLTrace hDL) hEnc hBridge, hChildOk⟩

/-! ## 3. Constructive Negative Controls (Shape 17 Envelope, `A7` Axioms, Shape 18 Discharge) -/

/-- Weak external STARK parameters (`1 * 50 + 10 = 60 < 220` conjectured bits). -/
def weakExternalStarkParams : StarkParams :=
  { logBlowup := 1
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 50
    commitPowBits := 0
    queryPowBits := 10 }

/-- **Negative Control 1 (Shape 17 Security Envelope):**
An external accelerator VK with `< 220` conjectured security bits is rejected by
`SecurityEnvelopeOk` (and by `Aiur.meetsSecurityFloor`). -/
theorem negative_control_weak_security_envelope :
    ¬ SecurityEnvelopeOk weakExternalStarkParams := by
  intro h
  have hsec := h.2.2.2.2.2.2.2.2
  unfold weakExternalStarkParams Aiur.minConjecturedSecurityBits at hsec
  dsimp only at hsec
  omega

/-- **Negative Control 2 (`A7` Axiom Merge):**
Dropping a user axiom `a₀` present in the left child violates `Aggr.AxiomMergeRel`. -/
theorem negative_control_a7_dropped_axiom (a₀ : Address) :
    ¬ AxiomMergeRel (fun a => a = a₀) (fun _ => False) (fun _ => False) := by
  intro h
  exact (h a₀).mpr (.inl rfl)

/-- **Negative Control 3 (Shape 18 Eval Discharge):**
Transitioning to `EvalAfter = ∅` (`10 → 3` / `11 → 4`) when a second distinct `EvalAssumption`
leaf `e₁ ≠ e₀` remains in `EvalBefore` violates `Aggr.EvalRemoveRel`. -/
theorem negative_control_shape18_undischarged_eval {e₀ e₁ : EvalAssumption} (hne : e₁ ≠ e₀) :
    ¬ EvalRemoveRel (fun e => e = e₀ ∨ e = e₁) (fun _ => False) e₀ := by
  intro hRem
  exact hne (evalRemoveRel_rejects_undischarged hRem (.inr rfl))

end Ix.Cert.Aggr
