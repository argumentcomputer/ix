import Ix.Cert.Aggr.ConditionalShard
import Ix.Cert.Aggr.Shapes
import Ix.Cert.MultiStarkRefinement.EndToEnd
import Ix.Cert.MultiStark.EndToEnd

/-! # Stage-Isolated Aggregated Root Soundness (`Ix.Cert.Aggr.EndToEnd`, Workstreams `1B` + `5A`/`5B`)

Composes the stage-isolated certification stack from an accepted outer `MultiStark.aggregateProgram`
trace (`MultiStark::ix_aggr`) spanning ALL 19 aggregation shapes (`0..18`) together with an
explicit `AcceptedAggrTree` witness tree down to:
- Pinned deployed Aiur programs (`MultiStark.recursionProgram` and `MultiStark.aggregateProgram`),
- Observed trace extraction (`prepared_obs_of_extracted_trace` via
  `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed`),
- Recursive `MultiStark.recursionProgram` verification (`recursion_obs_refines_verifyBatch`),
- Multi-node ROM tree error union bound (`tree_rom_error_bound`),
- Inductive 19-shape soundness (`Aggr.aggrDerivation19_checkEnv_sound`,
  `aggrDerivation19_linked_checkEnv_sound`, `catalog_sound`, `dynamicLink_sound`),
- Tier 1 & Tier 2 dynamic linking (`Ix.DynamicLink.Soundness`): Mode 2 (`@Eq` `Claim.check`)
  discharges unconditionally (`10 → 3` / `11 → 4`, zero external circuits), whereas Mode 3a
  (`DynamicLinkStatement`) explicitly records every `LinkedCircuitEntry` into validators `12`/`13`
  (never erasing into validators `3`/`4`),
- Conditional shards `CheckEnv(S, A)` with `A7` axiom merging and Shape 18 eval discharge, and
- Unconditional set-theoretic models via frozen `IxVM.Consistency.ComposedSpec` (`CircuitComposed`).

**Scope Honesty Note:** `aggregated_root_sound` is a **stage-isolated** composition theorem:
`t : AcceptedAggrTree` and `nodeProbs` are passed as explicit witnesses alongside the extracted
`prepared.ObsFn ixAggrEntry` derivation; mechanical extraction of `AcceptedAggrTree` from
`ObsFn ixAggrEntry` and linking `nodeProbs` to FRI soundness remain tracked follow-up bridges.

Also includes five constructive negative controls verifying rejection of:
1. Weak Shape 17 security envelopes (`< 220` conjectured security bits),
2. Deceptive high-blowup Shape 17 envelopes (`(4, 55, 0)` — 220 conjectured yet 50.2-bit UD),
3. `A7` dropped user axioms during pair/discharge merge,
4. Shape 18 premature full discharge (`10 → 3` / `11 → 4`) with an undischarged `EvalAssumption`,
5. Shape 18 Mode 3a erasure of `LinkedCircuitEntry` or emission of validator `3`/`4`.

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

/-! ## 1. Stage-Isolated Headline Theorem: `aggregated_root_sound` (All 19 Shapes `0..18`) -/

/-- **Stage-Isolated Headline Theorem (`aggregated_root_sound`):**
Given:
1. An extracted outer Multi-STARK trace `(rom, rows)` (`rows.length ≤ 2^39`) of the pinned
   deployed `MultiStark.aggregateProgram` at entry `MultiStark::ix_aggr`, satisfying sharded
   `MEMSEG = 16` interval balance, `Plan.inspectRow`, and Goldilocks field-level LogUp balance;
2. A stage-isolated 19-shape aggregation proof tree `t : AcceptedAggrTree sem batchClaim rootStmt`
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
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
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
    -- Stage-isolated 19-shape recursive aggregation tree & ROM error union bound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {rootStmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
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

/-! ## 2. Specialized Corollaries: `CheckEnv`, `LinkedCheckEnv`, Zero-Axiom `SetTheory` Model, `Catalog`, `DynamicLink` -/

/-- **Unconditional (or Axiom-Explicit `Ax`) Unlinked `CheckEnv` Root Soundness (`aggregated_root_checkEnv_sound`):**
For any accepted 19-shape aggregation tree whose root is an assumption-free, eval-free,
unlinked, binding-discharged `CheckEnv` (`validator ∈ {3, 5}`, `A = ∅`, `EvalA = ∅`, `Linked = ∅`,
explicit axioms `Ax`):
1. every subject `x ∈ S` satisfies `Valid mode.bindingOf Ax x`,
2. **zero** Shape 18 Mode 3a external dynamic-circuit discharges occurred (`t.dynamicLinkDischarges = 0`), and
3. either a concrete BLAKE3 collision occurred or every recursive child proof passed `verifyBatchBytes = true`! -/
theorem aggregated_root_checkEnv_sound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {Valid : Address → (Address → Prop) → Address → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) (fun _ => False) x →
      (∀ y, sem.Dep x y → Valid b Ax y) → Valid b Ax x)
    {mode : ValidatorMode Address} {S Ax : Address → Prop}
    (hDis : mode.isBindingDischarged = true)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False))) :
    (∀ x, S x → Valid mode.bindingOf Ax x) ∧
    t.dynamicLinkDischarges = 0 ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  have hUnl : mode.isLinked = false := by
    cases mode <;> simp [ValidatorMode.isBindingDischarged, ValidatorMode.isLinked] at hDis ⊢
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  exact ⟨aggrDerivation19_checkEnv_sound hWf hStep hDis hDeriv,
    acceptedAggrTree_unlinked_zero_dynamicLinkDischarges hUnl t, hChildOk⟩

/-- **Mode 3a Linked `CheckEnv` Root Soundness (`aggregated_root_linked_checkEnv_sound`):**
For an accepted 19-shape aggregation tree closing to validator `12` (`.linked b`) with `A = ∅`,
`EvalA = ∅`, explicit axioms `Ax`, and explicit `Linked` circuit set, every subject `x ∈ S`
satisfies `Valid b Ax Linked x` relative to the committed `Linked` circuits (for `ClaimPolicy`
allowlisting). -/
theorem aggregated_root_linked_checkEnv_sound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {Valid : Address → (Address → Prop) → (LinkedCircuitEntry → Prop) → Address → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax Linked x, sem.Checked b Ax (fun _ => False) Linked x →
      (∀ y, sem.Dep x y → Valid b Ax Linked y) → Valid b Ax Linked x)
    {b : Address} {S Ax : Address → Prop} {Linked : LinkedCircuitEntry → Prop}
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv (.linked b) S (fun _ => False) Ax (fun _ => False) Linked)) :
    (∀ x, S x → Valid b Ax Linked x) ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  exact ⟨aggrDerivation19_linked_checkEnv_sound hWf hStep hDeriv, hChildOk⟩

/-- **Zero-Axiom Zero-Link Set-Theoretic Model Corollary (`aggregated_root_checkEnv_no_axioms_model`):**
When an accepted 19-shape aggregation tree closes to an unconditional, unlinked `CheckEnv` root
with `Ax = ∅`, `A = ∅`, `EvalA = ∅`, `Linked = ∅`, and `validator = 3` (`.validated b` — a concrete
role binding `b`, excluding validator-5 literal classes which have no `.binding` claim), and its
subject set `S` is linked (`hS : ∀ x, S x ↔ x ∈ seeds`) to the `ClaimSeeds` of an in-scope claim
`cA` witnessed by frozen `IxVM.Consistency.ComposedSpec` paired with its verified binding proof
`.binding spec b`, then in every set theory `W`, `t.dynamicLinkDischarges = 0`, and EITHER a
BLAKE3 collision occurred OR the claimed environment is consistent with a model
`Ix.Kernel.Model W (claimedEnv env)` and no subject `x` with `S x` has type `False`!

**Scope note:** This is a stage-isolated composition connecting `t : AcceptedAggrTree` and
`hComp : ComposedSpec` through shared validated role binding `b`, `hba : ctx.binding = b`, and
exact subject-seed correspondence `hS : ∀ x, S x ↔ x ∈ seeds`. -/
theorem aggregated_root_checkEnv_no_axioms_model (W : Type u) [Ix.Kernel.SetTheory W]
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {b : Address} {S : Address → Prop}
    {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {dA dB : IxVM.Refinement.Digest}
    (hComp : ComposedSpec.{u} callsA callsB dA dB)
    {bytesB : ByteArray} {spec : Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec b))
    (hdB : packDigest (Address.blake3Pure bytesB) = dB)
    {bytesA : ByteArray} {cA : Ix.Claim}
    (hdeA : Ix.Claim.de bytesA = .ok cA)
    (hdA : packDigest (Address.blake3Pure bytesA) = dA)
    (hsc : InScopeTyping cA)
    {ctx : Ix.ClaimContext} (hctx : cA.context? = some ctx) (hba : ctx.binding = b)
    {V : View} {seeds : List Address} (hseeds : ClaimSeeds cA V seeds)
    (hS : ∀ x, S x ↔ x ∈ seeds)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv (.validated b) S (fun _ => False) (fun _ => False) (fun _ => False) (fun _ => False))) :
    (∀ x, S x → sem.Checked b (fun _ => False) (fun _ => False) (fun _ => False) x) ∧
    (∀ x y, S x → sem.Dep x y → S y) ∧
    (∀ x, S x ↔ x ∈ seeds) ∧
    t.dynamicLinkDischarges = 0 ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) ∧
    (V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun tRole R _ => SeedsNotFalse callsA tRole R seeds) callsB b) := by
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  obtain ⟨hChk, hCl, _⟩ := aggrDerivation19_invariant hDeriv
  have hMod := composedModelConclusion_of_composedSpec hComp hdeB hdB hdeA hdA hsc hctx hba hseeds
  exact ⟨hChk trivial, fun x y hx hDep => (hCl x y hx hDep).elim id False.elim,
    hS, acceptedAggrTree_unlinked_zero_dynamicLinkDischarges rfl t,
    hChildOk, composedModelConclusion_no_false W hMod⟩

/-- **`Catalog` Root Soundness (`aggregated_root_catalog_sound`, Shape `16`):**
Every member `(b, S, Ax)` of an accepted `Catalog` root satisfies `Valid b Ax x` for all
subjects `x ∈ S` (with `Linked = ∅`). -/
theorem aggregated_root_catalog_sound
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {Valid : Address → (Address → Prop) → Address → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) (fun _ => False) x →
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
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
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

/-! ## 3. Constructive Negative Controls (Shape 17 Envelope, `A7` Axioms, Shape 18 Mode 2 & Mode 3a) -/

/-- Weak external STARK parameters (`1 * 50 + 10 = 60 < 220` conjectured bits). -/
def weakExternalStarkParams : StarkParams :=
  { logBlowup := 1
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 50
    commitPowBits := 0
    queryPowBits := 10 }

/-- Deceptive high-blowup parameters `(logBlowup = 4, numQueries = 55, queryPow = 0)`:
meets the `4 * 55 + 0 = 220` conjectured ethSTARK floor yet yields only `50.2` bits provable UD! -/
def deceptiveHighBlowupParams : StarkParams :=
  { logBlowup := 4
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 55
    commitPowBits := 0
    queryPowBits := 0 }

/-- **Negative Control 1 (Shape 17 Security Envelope — Conjectured Floor):**
An external accelerator VK with `< 220` conjectured security bits is rejected by
`SecurityEnvelopeOk` (and by `Aiur.meetsSecurityFloor`). -/
theorem negative_control_weak_security_envelope :
    ¬ SecurityEnvelopeOk weakExternalStarkParams := by
  intro h
  have hsec := h.2.2.2.2.2.2.2.2.1
  unfold weakExternalStarkParams Aiur.minConjecturedSecurityBits at hsec
  dsimp only at hsec
  omega

/-- **Negative Control 2 (Shape 17 Security Envelope — Provable UD Floor):**
The deceptive `(4, 55, 0)` config passes `220` conjectured bits yet has only `50.2` bits provable
unique-decoding query soundness (`912 * 55 = 50160 < 80000`) and is REJECTED by `SecurityEnvelopeOk`! -/
theorem negative_control_deceptive_high_blowup_envelope :
    ¬ SecurityEnvelopeOk deceptiveHighBlowupParams := by
  intro h
  have hud := h.2.2.2.2.2.2.2.2.2.1
  unfold deceptiveHighBlowupParams minProvableUdMillibits udQueryMillibits udMillibitsPerQuery at hud
  simp at hud

/-- **Negative Control 3 (`A7` Axiom Merge):**
Dropping a user axiom `a₀` present in the left child violates `Aggr.AxiomMergeRel`. -/
theorem negative_control_a7_dropped_axiom (a₀ : Address) :
    ¬ AxiomMergeRel (fun a => a = a₀) (fun _ => False) (fun _ => False) := by
  intro h
  exact (h a₀).mpr (.inl rfl)

/-- **Negative Control 4 (Shape 18 Eval Discharge):**
Transitioning to `EvalAfter = ∅` (`10 → 3` / `11 → 4`) when a second distinct `EvalAssumption`
leaf `e₁ ≠ e₀` remains in `EvalBefore` violates `Aggr.EvalRemoveRel`. -/
theorem negative_control_shape18_undischarged_eval {e₀ e₁ : EvalAssumption} (hne : e₁ ≠ e₀) :
    ¬ EvalRemoveRel (fun e => e = e₀ ∨ e = e₁) (fun _ => False) e₀ := by
  intro hRem
  exact hne (evalRemoveRel_rejects_undischarged hRem (.inr rfl))

/-- **Negative Control 5 (Shape 18 Mode 3a — No Erasure / No Validator `3`/`4` Emission):**
Recording a `LinkedCircuitEntry` in Mode 3a can NEVER satisfy `LinkedMergeRel` with an empty
`LinkedAfter = ∅`, and `ValidatorMode.toLinkedMode` NEVER produces validator `3` or `4` (always
emitting a linked validator `12`/`13`). -/
theorem negative_control_mode3a_cannot_erase_linked
    (LinkedBefore : LinkedCircuitEntry → Prop) (entry : LinkedCircuitEntry) :
    (¬ LinkedMergeRel LinkedBefore entry (fun _ => False)) ∧
    (∀ (m out : ValidatorMode Address),
      m.toLinkedMode = some out →
      out.isLinked = true ∧ out.validatorCode ≠ 3 ∧ out.validatorCode ≠ 4) :=
  ⟨linkedMergeRel_rejects_erasure, fun _ _ h =>
    let ⟨h1, h2, h3, _, _⟩ := validatorMode_toLinkedMode_props h
    ⟨h1, h2, h3⟩⟩

end Ix.Cert.Aggr
