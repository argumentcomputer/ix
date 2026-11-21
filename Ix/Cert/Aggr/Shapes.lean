import MultiStark.Program
import Ix.Cert.MultiStarkRefinement.EndToEnd
import Ix.Aggr.Verification
import Ix.Aiur.Parameters
import Ix.DynamicLink.Soundness

/-! # 19-Shape Aggregation Program Pin, Telescoping, Security Envelope, & Tree Refinement (`Ix.Cert.Aggr.Shapes`)

Covers Workstreams `1B` and `5A`/`5B` + `A7`:
1. **Kernel-Checked Pin of `MultiStark.aggregateSource` & `MultiStark.aggregateProgram`:**
   Proves by kernel reduction (`decide`) that `MultiStark::ix_aggr` dispatches on the exact
   19 shape codes `[0, 1, ..., 18]` to all 11 handlers (`aggr_wrap`, `aggr_pair`,
   `aggr_pair_structural`, `aggr_range_leaf`, `aggr_range_join`, `aggr_range_root`,
   `aggr_discharge_binding`, `aggr_cross_binding`, `aggr_catalog_join`, `aggr_dynamic_link`,
   `aggr_discharge_eval`), and that `Aggregation` defines all `A7` / Shape 17 / Shape 18 helpers.
2. **Concrete Goldilocks-Extension Range Telescoping (`aggr_range_telescoping`):**
   Instantiates `Aggr.ResidualMonoid` over `K = Fp[u]/(u^2 - 7)` (`Ix.Cert.MultiStark.K`) and
   proves that recursive binary folding of Shapes `10 → 11 → 12` computes the exact global sum
   over `[0, k)`.
3. **Uniform Security Envelope Refinement (`securityEnvelopeOk_iff`):**
   Refines `Aggregation::aggr_assert_security_envelope` (Shape 17) onto
   `Ix.Cert.MultiStark.checkParams p = true ∧ Ix.Aiur.meetsSecurityFloor ... = true`.
4. **Real-Valued Multi-Node ROM Tree Error Union Bound (`tree_rom_error_bound`):**
   Bounds the cumulative soundness failure probability across an `M`-node aggregation tree
   by `(M : ℝ) * ε_node`.
5. **19-Shape Recursive Aggregation Tree Refinement (`acceptedAggrTree_refines_derivation19`):**
   Inductively refines an `AcceptedAggrTree` across ALL 19 shapes (`0..18`) — composing
   `Ix.Cert.MultiStarkRefinement.recursion_obs_refines_verifyBatch` at every recursive child
   verification step — into `Aggr.AggrDerivation19` (up to a concrete BLAKE3 collision).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.Aggr

open Aiur Aiur.Generic Aiur.Modules
open CertiFri CertiFri.P3
open Ix.Cert.MultiStark
open Ix.Cert.MultiStarkRefinement
open Ix.DynamicLink
open _root_.Aggr

/-! ## 1. Kernel-Checked AST Pin of `MultiStark.aggregateSource` & `MultiStark.aggregateProgram` -/

/-- Entry point name of the aggregator Aiur program. -/
def ixAggrEntry : String := "MultiStark::ix_aggr"

/-- All 11 shape dispatch handlers invoked by `MultiStark::ix_aggr` across shapes `0..18`. -/
def ixAggrRequiredCalls : List String :=
  [ "StarkIO::read_byte_stream"
  , "Blake3::hash"
  , "Blake3::pack_digest"
  , "Aggregation::aggr_wrap"
  , "Aggregation::aggr_pair"
  , "Aggregation::aggr_pair_structural"
  , "Aggregation::aggr_range_leaf"
  , "Aggregation::aggr_range_join"
  , "Aggregation::aggr_range_root"
  , "Aggregation::aggr_discharge_binding"
  , "Aggregation::aggr_cross_binding"
  , "Aggregation::aggr_catalog_join"
  , "Aggregation::aggr_dynamic_link"
  , "Aggregation::aggr_discharge_eval"
  ]

/-- Required `Aggregation` helper functions covering all 19 shapes, `A7`, Shape 17, and Shape 18. -/
def aggregationCoreFunctions : List String :=
  [ "aggr_wrap"
  , "aggr_pair"
  , "aggr_pair_structural"
  , "aggr_range_leaf"
  , "aggr_range_join"
  , "aggr_range_root"
  , "aggr_discharge_binding"
  , "aggr_cross_binding"
  , "aggr_catalog_join"
  , "aggr_assert_same_context_base"
  , "aggr_assert_axioms_merge"
  , "aggr_assert_security_envelope"
  , "aggr_parse_dynamic_link"
  , "aggr_verify_bridge_cert"
  , "aggr_dynamic_link"
  , "aggr_parse_eval_assumption"
  , "aggr_parse_eval_assumed"
  , "aggr_parse_eval_discharge_out"
  , "aggr_extract_removed_leaf"
  , "aggr_assert_packed_addr_u64s"
  , "aggr_verify_eq_check_record"
  , "aggr_discharge_eval"
  ]

/-- Kernel-checked pin: `MultiStark::ix_aggr` in `MultiStark.aggregateSource` dispatches on the
exact 19 literal shape codes `[0, 1, ..., 18]` matching `AggrShape.all.map AggrShape.code`. -/
theorem aggregateSource_exact_19_shape_arms :
    (match findModuleFunction? MultiStark.aggregateSource "MultiStark" "ix_aggr" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = List.range 19 := by
  decide

/-- Kernel-checked pin: all 22 core aggregation & `A7`/Shape 17/Shape 18 helpers are defined
in `MultiStark.aggregateSource`'s `Aggregation` module. -/
theorem aggregateSource_core_helpers_present :
    aggregationCoreFunctions.all
      (fun fnName => hasModuleFunction MultiStark.aggregateSource "Aggregation" fnName) = true := by
  decide

/-- AST pin predicate on any MultiStark aggregator program: pins `MultiStark::ix_aggr`,
`Aggregation::aggr_dynamic_link` (Shape 17), `Aggregation::aggr_discharge_eval` (Shape 18),
and the shared `StarkVerifier::verify_batch` + `verify_shard` checks. -/
def AggregateProgramAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "MultiStark" "ix_aggr" ixAggrRequiredCalls 3 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_dynamic_link"
    ["aggr_assert_security_envelope", "aggr_verify_child", "aggr_parse_dynamic_link",
     "aggr_verify_bridge_cert"] 1 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_discharge_eval"
    ["aggr_parse_eval_assumed", "aggr_parse_eval_discharge_out", "aggr_extract_removed_leaf",
     "aggr_parse_eval_assumption", "aggr_assert_axioms_merge", "aggr_verify_eq_check_record",
     "aggr_assert_packed_addr_u64s"] 2 &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 5 &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_shard" verifyShardRequiredCalls 15

/-- Kernel-checked AST pin of the deployed `MultiStark.aggregateSource`. -/
theorem aggregateSource_ast_pinned :
    AggregateProgramAstPinned MultiStark.aggregateSource = true := by
  decide

/-- None of `MultiStark`, `Aggregation`, or `StarkVerifier` appear in the library prefix. -/
theorem libraries_disjoint_aggregate :
    let libPrefix : Modules.Program Fp :=
      (Aiur.Library.Blake3.Goldilocks.program.append
        (Aiur.Library.Option.declarations.toField Fp)).append
        Aiur.Library.Field.Goldilocks.program
    libPrefix.findModule? "MultiStark" = none ∧
    libPrefix.findModule? "Aggregation" = none ∧
    libPrefix.findModule? "StarkVerifier" = none := by
  have hb1 : Aiur.Library.Blake3.Goldilocks.program.findModule? "MultiStark" = none := rfl
  have hb2 : Aiur.Library.Blake3.Goldilocks.program.findModule? "Aggregation" = none := rfl
  have hb3 : Aiur.Library.Blake3.Goldilocks.program.findModule? "StarkVerifier" = none := rfl
  have ho : Aiur.Library.Option.declarations.findModule? "MultiStark" = none ∧
      Aiur.Library.Option.declarations.findModule? "Aggregation" = none ∧
      Aiur.Library.Option.declarations.findModule? "StarkVerifier" = none := by
    decide
  have hf : Aiur.Library.Field.Goldilocks.declarations.findModule? "MultiStark" = none ∧
      Aiur.Library.Field.Goldilocks.declarations.findModule? "Aggregation" = none ∧
      Aiur.Library.Field.Goldilocks.declarations.findModule? "StarkVerifier" = none := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · apply findModule?_append_none
    · exact findModule?_append_none _ _ _ hb1 (findModule?_map_none _ _ _ ho.1)
    · exact findModule?_map_none _ _ _ hf.1
  · apply findModule?_append_none
    · exact findModule?_append_none _ _ _ hb2 (findModule?_map_none _ _ _ ho.2.1)
    · exact findModule?_map_none _ _ _ hf.2.1
  · apply findModule?_append_none
    · exact findModule?_append_none _ _ _ hb3 (findModule?_map_none _ _ _ ho.2.2)
    · exact findModule?_map_none _ _ _ hf.2.2

/-- Kernel-checked AST pin lifted to the deployed Goldilocks `MultiStark.aggregateProgram`. -/
theorem aggregateProgram_ast_pinned :
    AggregateProgramAstPinned MultiStark.aggregateProgram = true := by
  have hdisj := libraries_disjoint_aggregate
  unfold MultiStark.aggregateProgram MultiStark.withLibraries AggregateProgramAstPinned
  unfold fnHasCallsAndAsserts
  rw [findModuleFunction?_append_right _ _ "MultiStark" _ hdisj.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2.2]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2.2]
  have hsrc := aggregateSource_ast_pinned
  unfold AggregateProgramAstPinned fnHasCallsAndAsserts at hsrc
  have h1 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "MultiStark" "ix_aggr" ixAggrRequiredCalls 3
  have h2 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_dynamic_link"
    ["aggr_assert_security_envelope", "aggr_verify_child", "aggr_parse_dynamic_link",
     "aggr_verify_bridge_cert"] 1
  have h3 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_discharge_eval"
    ["aggr_parse_eval_assumed", "aggr_parse_eval_discharge_out", "aggr_extract_removed_leaf",
     "aggr_parse_eval_assumption", "aggr_assert_axioms_merge", "aggr_verify_eq_check_record",
     "aggr_assert_packed_addr_u64s"] 2
  have h4 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 5
  have h5 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "StarkVerifier" "verify_shard" verifyShardRequiredCalls 15
  unfold fnHasCallsAndAsserts at h1 h2 h3 h4 h5
  unfold Modules.Program.toField
  rw [h1, h2, h3, h4, h5]
  exact hsrc

/-! ## 2. Concrete Goldilocks-Extension Range Telescoping (Shapes `10–12`) -/

/-- Additive `ResidualMonoid` over the quadratic Goldilocks extension field `K = Fp[u]/(u^2 - 7)`. -/
def kResidualMonoid : _root_.Aggr.ResidualMonoid K where
  zero := 0
  add := (· + ·)
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero

/-- **Telescoping Identity in `K = Fp[u]/(u^2 - 7)` (Shapes `10–12`):**
Combining adjacent shard ranges `[lo, mid)` and `[mid, hi)` by `Goldilocks::eg_add` produces
the exact partial sum `rangeSum kResidualMonoid f lo hi`. -/
theorem aggr_range_telescoping (f : Nat → K) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    rangeSum kResidualMonoid f lo mid + rangeSum kResidualMonoid f mid hi =
      rangeSum kResidualMonoid f lo hi :=
  rangeSum_append kResidualMonoid f h1 h2

/-! ## 3. Shape 17 Uniform Security Envelope Refinement (`aggr_assert_security_envelope`) -/

/-- Exact arithmetic predicate enforced by `Aggregation::aggr_assert_security_envelope`
(`Aggregation.lean:1243-1263`):
- Fixed structural parameters: `capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`,
- Blowup range: `1 ≤ logBlowup ≤ 4`,
- Positive queries: `1 ≤ numQueries`,
- Proof-of-work ceiling: `commitPowBits ≤ 32`, `queryPowBits ≤ 32`,
- Conjectured ethSTARK security floor: `logBlowup * numQueries + queryPowBits ≥ 220`. -/
def SecurityEnvelopeOk (p : StarkParams) : Prop :=
  p.capHeight = 0 ∧
  p.logFinalPolyLen = 0 ∧
  p.maxLogArity = 1 ∧
  1 ≤ p.logBlowup ∧ p.logBlowup ≤ 4 ∧
  1 ≤ p.numQueries ∧
  p.commitPowBits ≤ Aiur.maxProofOfWorkBits ∧
  p.queryPowBits ≤ Aiur.maxProofOfWorkBits ∧
  Aiur.minConjecturedSecurityBits ≤ p.logBlowup * p.numQueries + p.queryPowBits

/-- Convert `StarkParams` to `(Aiur.CommitmentParameters, Aiur.FriParameters)`. -/
def toAiurParams (p : StarkParams) : Aiur.CommitmentParameters × Aiur.FriParameters :=
  (⟨p.logBlowup, p.capHeight⟩,
   ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩)

/-- **Uniform Security Envelope Equivalence (`securityEnvelopeOk_iff`):**
`SecurityEnvelopeOk p` holds iff BOTH `Ix.Cert.MultiStark.checkParams p = true` AND
`Aiur.meetsSecurityFloor (toAiurParams p).1 (toAiurParams p).2 = true`! -/
theorem securityEnvelopeOk_iff (p : StarkParams) :
    SecurityEnvelopeOk p ↔
      Ix.Cert.MultiStark.checkParams p = true ∧
      Aiur.meetsSecurityFloor (toAiurParams p).1 (toAiurParams p).2 = true := by
  unfold SecurityEnvelopeOk Ix.Cert.MultiStark.checkParams Aiur.meetsSecurityFloor
    Aiur.conjecturedSecurityBits toAiurParams Aiur.maxProofOfWorkBits Aiur.minConjecturedSecurityBits
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, hsec⟩
    exact ⟨⟨⟨⟨⟨hc, hfl⟩, hma⟩, hlb1⟩, hnq⟩,
      ⟨⟨⟨⟨⟨hlb1, hlb4⟩, by omega⟩, hcp⟩, hqp⟩, hsec⟩⟩
  · rintro ⟨⟨⟨⟨⟨hc, hfl⟩, hma⟩, hlb1⟩, hnq⟩, ⟨⟨⟨⟨⟨_, hlb4⟩, _⟩, hcp⟩, hqp⟩, hsec⟩⟩
    exact ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, hsec⟩

/-! ## 4. Real-Valued Multi-Node ROM Tree Soundness Union Bound -/

/-- **Union Bound over an `M`-Node Aggregation Tree (`tree_rom_error_bound`):**
Given a finite list of `M` recursive verification nodes whose individual ROM soundness failure
probabilities `p_i` each satisfy `p_i ≤ ε` (with `0 ≤ ε`), the union bound `∑_{i} p_i` is at
most `(M : ℝ) * ε`! -/
theorem tree_rom_error_bound (probs : List ℝ) {ε : ℝ} (hbound : ∀ p ∈ probs, p ≤ ε) :
    probs.sum ≤ (probs.length : ℝ) * ε := by
  induction probs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hp : p ≤ ε := hbound p (by simp)
    have hps : ps.sum ≤ (ps.length : ℝ) * ε := ih (fun q hq => hbound q (by simp [hq]))
    linarith

/-- Compositional form of the ROM union bound when merging two subtrees of sizes `M₁, M₂`
under a new aggregation node: `(M₁ + M₂ + 1 : ℝ) * ε = M₁ * ε + M₂ * ε + ε`. -/
theorem tree_rom_error_merge (M₁ M₂ : Nat) (ε : ℝ) :
    ((M₁ + M₂ + 1 : Nat) : ℝ) * ε = (M₁ : ℝ) * ε + (M₂ : ℝ) * ε + ε := by
  push_cast
  ring

/-! ## 5. 19-Shape Recursive Aggregation Proof Tree (`AcceptedAggrTree`) → `AggrDerivation19` -/

/-- A verified child Multi-STARK proof check executed inside an `ix_aggr` node
(calling `StarkVerifier::verify_batch_at` inside `Aggregation::aggr_verify_child`). -/
structure VerifiedChildProof where
  vkBytes : ByteArray
  claimsBytes : ByteArray
  calls : List (Aiur.Generic.SourceSemantics.Call Fp)
  refines : RecursionExecutionRefines calls
    (packDigest8 (Address.blake3Pure vkBytes))
    (packDigest8 (Address.blake3Pure claimsBytes))

/-- Complete inductive witness tree of an accepted `MultiStark::ix_aggr` execution spanning
ALL 19 aggregation shapes (`0..18`), recording:
- every verified child Multi-STARK proof (`VerifiedChildProof`),
- `A7` axiom-set merge relations (`AxiomMergeRel`),
- Shape `17` uniform security envelope (`SecurityEnvelopeOk`) + verified external proof +
  optional verified bridge cert,
- Shape `18` `EvalRemoveRel` + verified discharger (`Claim.eval` / `Claim.check` / Shape `17`). -/
inductive AcceptedAggrTree
    (sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement)
    (batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop) :
    AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement → Type where
  /-- Base IxVM leaf (`Check` / `CheckEnv`) verified by an outer Multi-STARK proof. -/
  | leaf {mode S A Ax EvalA} :
      VerifiedChildProof →
      LeafValid19 sem mode S A Ax EvalA →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA)
  /-- Base IxVM `binding` claim establishing `BindingValid b`. -/
  | bindingLeaf {b : Address} :
      VerifiedChildProof →
      sem.BindingValid b →
      AcceptedAggrTree sem batchClaim (.bindingStmt b)
  /-- Base IxVM `Claim.eval` or `Claim.check` discharging an `EvalAssumption` leaf `e`. -/
  | evalDischargerLeaf {b : Address} {Ax : Address → Prop} {e : EvalAssumption} :
      VerifiedChildProof →
      sem.EvalValid b Ax e →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt b Ax e)
  /-- Shapes `0–1` (`aggr_wrap`): wraps an IxVM or `ix_aggr` child proof. -/
  | wrap {stmt} :
      (isAggrChild : Bool) →
      VerifiedChildProof →
      AcceptedAggrTree sem batchClaim stmt →
      AcceptedAggrTree sem batchClaim stmt
  /-- Shapes `2–5` (`aggr_pair`): flat canonical pair fold with cross-discharge + `A7` axiom merge. -/
  | pairFlat {mode SL AL AxL SR AR AxR Sout Aout AxOut} :
      (leftIsAggr rightIsAggr : Bool) →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False)) →
      JoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False))
  /-- Shapes `6–9` (`aggr_pair_structural`): structural Merkle pair fold + `A7` axiom merge. -/
  | pairStructural {mode SL AL AxL SR AR AxR Sout Aout AxOut} :
      (leftIsAggr rightIsAggr : Bool) →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False)) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False))
  /-- Shape `10` (`aggr_range_leaf`): verifies shards `[lo, hi)` of `batchId`. -/
  | rangeLeaf {batchId lo hi : Nat} :
      lo ≤ hi →
      AcceptedAggrTree sem batchClaim
        (.rangeStmt batchId lo hi (rangeSum sem.residualMonoid (sem.shardResidual batchId) lo hi))
  /-- Shape `11` (`aggr_range_join`): adds residuals of adjacent shard ranges `[lo, mid)` and `[mid, hi)`. -/
  | rangeJoin {batchId lo mid hi : Nat} {rL rR : K} :
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.rangeStmt batchId lo mid rL) →
      AcceptedAggrTree sem batchClaim (.rangeStmt batchId mid hi rR) →
      AcceptedAggrTree sem batchClaim
        (.rangeStmt batchId lo hi (sem.residualMonoid.add rL rR))
  /-- Shape `12` (`aggr_range_root`): closes `[0, shardCount batchId)` with global LogUp vanishing. -/
  | rangeRoot {batchId : Nat} {r : K} {mode S A Ax EvalA} :
      VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.rangeStmt batchId 0 (sem.shardCount batchId) r) →
      sem.residualMonoid.add (sem.messagesAcc batchId) r = sem.residualMonoid.zero →
      batchClaim batchId mode S A Ax EvalA →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA)
  /-- Shapes `13–14` (`aggr_discharge_binding`): discharges assumed binding (`validator 4 → 3`). -/
  | dischargeBinding {b S A Ax} :
      (isAggrChild : Bool) →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv (.assumedBinding b) S A Ax (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.bindingStmt b) →
      AcceptedAggrTree sem batchClaim (.checkEnv (.validated b) S A Ax (fun _ => False))
  /-- Shape `15` (`aggr_cross_binding`): cross-binding structural join under 13-role class `k`
  (`validator ∈ {3, 5} → 5`) + `A7` axiom merge. -/
  | crossBinding {modeL modeR : ValidatorMode Address} {k : Address}
      {SL AL AxL SR AR AxR Sout Aout AxOut} :
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv modeL SL AL AxL (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv modeR SR AR AxR (fun _ => False)) →
      modeL.isBindingDischarged = true →
      modeR.isBindingDischarged = true →
      (modeL = .literalClass k ∨ sem.LiteralClassOf modeL.bindingOf k) →
      (modeR = .literalClass k ∨ sem.LiteralClassOf modeR.bindingOf k) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv (.literalClass k) Sout Aout AxOut (fun _ => False))
  /-- Shape `16` (`aggr_catalog_join`): catalog union of unconditional `CheckEnv`/`Catalog` children. -/
  | catalogJoin {membersL membersR membersOut : (Address × (Address → Prop) × (Address → Prop)) → Prop}
      {stmtL stmtR : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement} :
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim stmtL →
      AcceptedAggrTree sem batchClaim stmtR →
      ((∃ mode S Ax, stmtL = .checkEnv mode S (fun _ => False) Ax (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersL m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtL = .catalogStmt membersL) →
      ((∃ mode S Ax, stmtR = .checkEnv mode S (fun _ => False) Ax (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersR m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtR = .catalogStmt membersR) →
      (∀ m, membersOut m ↔ membersL m ∨ membersR m) →
      AcceptedAggrTree sem batchClaim (.catalogStmt membersOut)
  /-- Shape `17` (`aggr_dynamic_link`, `0xE8 0x0D`): verifies external Multi-STARK proof under
  `SecurityEnvelopeOk` (and optional bridge cert proof on slot 1). -/
  | dynamicLink {stmt : DynamicLinkStatement} :
      (extProof : VerifiedChildProof) →
      (extSys : StarkSystem) →
      StarkSystem.fromBytes extProof.vkBytes = .ok extSys →
      SecurityEnvelopeOk extSys.params →
      Address.blake3Pure extProof.vkBytes = stmt.circuit.vkDigest →
      (bridgeCert? : Option VerifiedChildProof) →
      (stmt.bridge?.isSome → bridgeCert?.isSome) →
      sem.DynamicLinkValid stmt →
      AcceptedAggrTree sem batchClaim (.dynamicLinkStmt stmt)
  /-- Lifting a bridged Shape 17 `DynamicLinkStatement` into a Shape 18 eval discharger. -/
  | dynamicLinkDischarger {stmt : DynamicLinkStatement} {b : Address} {e : EvalAssumption} :
      AcceptedAggrTree sem batchClaim (.dynamicLinkStmt stmt) →
      (sem.DynamicLinkValid stmt → sem.EvalValid b (fun _ => False) e) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt b (fun _ => False) e)
  /-- Shape `18` partial step (`aggr_discharge_eval`): discharges one `EvalAssumption` leaf `e₀`,
  keeping remaining `EvalAfter` under validator `10`/`11` with `A7` axiom merge. -/
  | dischargeEvalStep {mode : ValidatorMode Address} {S A Ax₀ Ax₁ AxOut EvalBefore EvalAfter e₀} :
      VerifiedChildProof → VerifiedChildProof →
      mode.dischargeAllEvals.isSome = true →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore EvalAfter e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A AxOut EvalAfter)
  /-- Shape `18` final step (`aggr_discharge_eval`): discharges the final `EvalAssumption` leaf `e₀`,
  transitioning validator `10 → 3` or `11 → 4` with `EvalA = ∅` and `A7` axiom merge. -/
  | dischargeEvalAll {mode outMode : ValidatorMode Address} {S A Ax₀ Ax₁ AxOut EvalBefore e₀} :
      VerifiedChildProof → VerifiedChildProof →
      mode.dischargeAllEvals = some outMode →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv outMode S A AxOut (fun _ => False))

/-- Collect every `VerifiedChildProof` executed across an entire `AcceptedAggrTree`. -/
def AcceptedAggrTree.childProofs
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement} :
    AcceptedAggrTree sem batchClaim stmt → List VerifiedChildProof
  | .leaf vp _ => [vp]
  | .bindingLeaf vp _ => [vp]
  | .evalDischargerLeaf vp _ => [vp]
  | .wrap _ vp t => vp :: t.childProofs
  | .pairFlat _ _ vpL vpR tL tR _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .pairStructural _ _ vpL vpR tL tR _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .rangeLeaf _ => []
  | .rangeJoin vpL vpR tL tR => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .rangeRoot vp t _ _ => vp :: t.childProofs
  | .dischargeBinding _ vpC vpB tC tB => vpC :: vpB :: tC.childProofs ++ tB.childProofs
  | .crossBinding vpL vpR tL tR _ _ _ _ _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .catalogJoin vpL vpR tL tR _ _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .dynamicLink extP _ _ _ _ bridge? _ _ =>
      match bridge? with
      | some bp => [extP, bp]
      | none => [extP]
  | .dynamicLinkDischarger t _ => t.childProofs
  | .dischargeEvalStep vpC vpD _ tC tD _ _ => vpC :: vpD :: tC.childProofs ++ tD.childProofs
  | .dischargeEvalAll vpC vpD _ tC tD _ _ => vpC :: vpD :: tC.childProofs ++ tD.childProofs

/-- Total number of recursive Multi-STARK proof verifications inside an `AcceptedAggrTree`. -/
def AcceptedAggrTree.verificationCount
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement}
    (t : AcceptedAggrTree sem batchClaim stmt) : Nat :=
  t.childProofs.length

/-- Whether ANY recursive Multi-STARK child verification in `t` exhibited a concrete BLAKE3
collision against its anchored `(vkBytes, claimsBytes)`. -/
def AcceptedAggrTree.HasTreeCollision
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement}
    (t : AcceptedAggrTree sem batchClaim stmt) : Prop :=
  ∃ vp ∈ t.childProofs, MultiStarkCollision [vp.vkBytes, vp.claimsBytes] vp.calls

/-- **19-Shape Recursive Aggregation Tree Refinement (`acceptedAggrTree_refines_derivation19`):**
For ANY accepted aggregation tree `t` across all 19 shapes (`0..18`):
1. Every node's statement refines cleanly into `Aggr.AggrDerivation19 sem batchClaim stmt`, AND
2. EITHER some child verification in `t` hashed a concrete BLAKE3 collision (`t.HasTreeCollision`),
   OR EVERY child verification `vp ∈ t.childProofs` is accepted by the certified out-of-circuit
   Multi-STARK verifier `Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true`! -/
theorem acceptedAggrTree_refines_derivation19
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement}
    (t : AcceptedAggrTree sem batchClaim stmt) :
    AggrDerivation19 sem batchClaim stmt ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  constructor
  · induction t with
    | leaf _ hL => exact .leaf hL
    | bindingLeaf _ hB => exact .bindingLeaf hB
    | evalDischargerLeaf _ hE => exact .evalDischargerLeaf hE
    | wrap _ _ _ ih => exact .wrap ih
    | pairFlat _ _ _ _ _ _ hJ hA ihL ihR => exact .pairFlat ihL ihR hJ hA
    | pairStructural _ _ _ _ _ _ hJ hA ihL ihR => exact .pairStructural ihL ihR hJ hA
    | rangeLeaf hle => exact .rangeLeaf hle
    | rangeJoin _ _ _ _ ihL ihR => exact .rangeJoin ihL ihR
    | rangeRoot _ _ hZ hC ih => exact .rangeRoot ih hZ hC
    | dischargeBinding _ _ _ _ _ ihC ihB => exact .dischargeBinding ihC ihB
    | crossBinding _ _ _ _ hDL hDR hCL hCR hJ hA ihL ihR =>
        exact .crossBinding ihL ihR hDL hDR hCL hCR hJ hA
    | catalogJoin _ _ _ _ hSL hSR hU ihL ihR => exact .catalogJoin ihL ihR hSL hSR hU
    | dynamicLink _ _ _ _ _ _ _ hDL => exact .dynamicLink hDL
    | dynamicLinkDischarger _ hLift ih => exact .dynamicLinkDischarger ih hLift
    | dischargeEvalStep _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalStep hM ihC ihD hR hA
    | dischargeEvalAll _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalAll hM ihC ihD hR hA
  · by_cases hCol : t.HasTreeCollision
    · exact Or.inl hCol
    · refine Or.inr fun vp hvp => ?_
      rcases recursion_obs_refines_verifyBatch vp.refines with hvpCol | ⟨pb, _, _, _, _, _, _, _, hvbb, _⟩
      · exact absurd ⟨vp, hvp, hvpCol⟩ hCol
      · exact ⟨pb, hvbb⟩

end Ix.Cert.Aggr
