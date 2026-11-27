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
  , "aggr_assert_codec_arity"
  , "aggr_verify_bridge_cert"
  , "aggr_dynamic_link"
  , "aggr_parse_eval_assumption"
  , "aggr_put_u64"
  , "aggr_linked_entry_addr"
  , "aggr_assert_linked_merge"
  , "aggr_parse_eval_assumed"
  , "aggr_parse_eval_discharge_out"
  , "aggr_extract_removed_leaf"
  , "aggr_assert_packed_addr_u64s"
  , "aggr_verify_eq_check_record"
  , "aggr_discharge_eval"
  ]

mutual
/-- Collect all numeric literal values appearing anywhere inside an Aiur `Generic.Expr Nat`. -/
def exprLiterals : Generic.Expr Nat → List Nat
  | .literal n => [n]
  | .var _ | .global _ _ => []
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => exprListLiterals xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _
  | .project x _ | .store x | .load x | .hint _ x _ | .neg x | .control _ x =>
      exprLiterals x
  | .letValue _ v b | .binary _ v b => exprLiterals v ++ exprLiterals b
  | .call _ _ args => exprListLiterals args
  | .matchValue s arms => exprLiterals s ++ exprArmsLiterals arms

def exprListLiterals : List (Generic.Expr Nat) → List Nat
  | [] => []
  | x :: xs => exprLiterals x ++ exprListLiterals xs

def exprArmsLiterals : List (Generic.Pattern Nat × Generic.Expr Nat) → List Nat
  | [] => []
  | (pat, e) :: arms =>
      (match pat with | .literal n => [n] | _ => []) ++ exprLiterals e ++ exprArmsLiterals arms
end

/-- Required literal constants inside `Aggregation::aggr_assert_security_envelope`, pinning
the fixed structural parameters (`0`, `1`), blowup bounds (`1..4`, `< 5`), PoW cap (`< 33`),
conjectured floor (`219` / `220`), UD millibit table (`415`, `678`, `830`, `912`),
provable UD floor (`79999` / `80000`), and finite-`m` Johnson 128-bit floor (`500`, `45`, `127999`). -/
def securityEnvelopeRequiredLiterals : List Nat :=
  [0, 1, 5, 33, 219, 415, 678, 830, 912, 79999, 500, 45, 127999]

/-- Kernel-checked pin: `MultiStark::ix_aggr` in `MultiStark.aggregateSource` dispatches on the
exact 19 literal shape codes `[0, 1, ..., 18]` matching `AggrShape.all.map AggrShape.code`. -/
theorem aggregateSource_exact_19_shape_arms :
    (match findModuleFunction? MultiStark.aggregateSource "MultiStark" "ix_aggr" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = List.range 19 := by
  decide

/-- Kernel-checked pin: `Aggregation::aggr_discharge_eval` dispatches on the exact two
discharger tag arms `[228, 232]` (Mode 2 `@Eq` `Claim.check` and Mode 3a `DynamicLinkStatement`),
strictly excluding Mode 1 (`tag == 227`, `Claim.eval`). -/
theorem aggregateSource_discharge_eval_exact_arms :
    (match findModuleFunction? MultiStark.aggregateSource "Aggregation" "aggr_discharge_eval" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = [228, 232] := by
  decide

/-- Kernel-checked pin: `Aggregation::aggr_verify_bridge_cert` dispatches on the exact two
unconditional certificate tag arms `[228, 229]` (`Check` and `CheckEnv`, validator `3`). -/
theorem aggregateSource_bridge_cert_exact_arms :
    (match findModuleFunction? MultiStark.aggregateSource "Aggregation" "aggr_verify_bridge_cert" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = [228, 229] := by
  decide

/-- Kernel-checked pin: `Aggregation::aggr_parse_eval_assumed` admits only validators
`[10, 11, 12, 13]` (never validators `3`, `4`, or `5`). -/
theorem aggregateSource_eval_assumed_exact_arms :
    (match findModuleFunction? MultiStark.aggregateSource "Aggregation" "aggr_parse_eval_assumed" with
     | some fdecl => exprMatchLitArms fdecl.body
     | none => []) = [10, 11, 12, 13] := by
  decide

/-- Kernel-checked pin: dead `Aggregation::aggr_parse_eval` is absent from `MultiStark.aggregateSource`. -/
theorem aggregateSource_parse_eval_absent :
    hasModuleFunction MultiStark.aggregateSource "Aggregation" "aggr_parse_eval" = false := by
  decide

/-- Kernel-checked pin: `Aggregation::aggr_assert_security_envelope` retains all required
structural, conjectured-security, and per-`log_blowup` UD floor literal constants. -/
theorem aggregateSource_security_envelope_literals_pinned :
    (match findModuleFunction? MultiStark.aggregateSource "Aggregation" "aggr_assert_security_envelope" with
     | some fdecl =>
         let lits := exprLiterals fdecl.body
         securityEnvelopeRequiredLiterals.all (fun n => lits.contains n)
     | none => false) = true := by
  decide

/-- Kernel-checked pin: all 26 core aggregation & `A7`/Shape 17/Shape 18 helpers are defined
in `MultiStark.aggregateSource`'s `Aggregation` module. -/
theorem aggregateSource_core_helpers_present :
    aggregationCoreFunctions.all
      (fun fnName => hasModuleFunction MultiStark.aggregateSource "Aggregation" fnName) = true := by
  decide

/-- Pinned BLAKE3 program digest of the deployed `MultiStark.aggregateProgram`
(`MultiStark.aggregateDigest`, hashing `reprStr MultiStark.aggregateProgram`).
Any edit to any module in `MultiStark.aggregateSource` changes this digest and forces an
explicit audit review. -/
def pinnedAggregateDigest : String :=
  "f4c4bfbfe9244c4ffa798e82c25b5a71b2e211eae20db7f0350aa92b53d3de68"

theorem aggregateDigest_eq : MultiStark.aggregateDigest = pinnedAggregateDigest := rfl

private theorem hasModuleFunction_map {α β : Type} (f : α → β) (prog : Modules.Program α)
    (modName fnName : String) :
    hasModuleFunction (prog.map f) modName fnName = hasModuleFunction prog modName fnName := by
  unfold hasModuleFunction
  rw [findModuleFunction?_map]
  cases findModuleFunction? prog modName fnName <;> rfl

/-- AST pin predicate on any MultiStark aggregator program: pins `MultiStark::ix_aggr`,
`Aggregation::aggr_parse_range` (`gl_lt_p`), `Aggregation::aggr_range_root` (`assert_closure_widths_ok`),
`Aggregation::aggr_assert_security_envelope`, `Aggregation::aggr_assert_codec_arity`,
`Aggregation::aggr_verify_bridge_cert`, `Aggregation::aggr_dynamic_link` (Shape 17),
`Aggregation::aggr_parse_eval_discharge_out`, `Aggregation::aggr_discharge_eval` (Shape 18,
including Mode 3a `aggr_linked_entry_addr` and `aggr_assert_linked_merge`), absence of
`Aggregation::aggr_parse_eval`, and the shared `StarkVerifier::verify_batch` + `verify_shard` checks. -/
def AggregateProgramAstPinned {α : Type} (prog : Modules.Program α) : Bool :=
  fnHasCallsAndAsserts prog "MultiStark" "ix_aggr" ixAggrRequiredCalls 3 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_parse_range"
    ["Goldilocks::gl_lt_p"] 6 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_range_root"
    ["StarkVerifier::assert_shard_count_ok", "StarkVerifier::assert_batch_bounds",
     "StarkVerifier::assert_closure_pairs", "StarkVerifier::assert_closure_widths_ok",
     "StarkVerifier::ext_is_zero"] 10 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_assert_security_envelope"
    ["UInt32::less_than_fields"] 11 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_assert_codec_arity"
    ["UInt64::eq", "Lists::length"] 4 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_verify_bridge_cert"
    ["aggr_parse_check", "aggr_parse_check_env", "Bytes::address_eq", "aggr_opt_address_eq"] 14 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_dynamic_link"
    ["aggr_assert_security_envelope", "aggr_verify_child", "aggr_parse_dynamic_link",
     "aggr_assert_codec_arity", "aggr_verify_bridge_cert"] 3 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_parse_eval_discharge_out"
    ["Fields::is_zero"] 4 &&
  fnHasCallsAndAsserts prog "Aggregation" "aggr_discharge_eval"
    ["aggr_parse_eval_assumed", "aggr_parse_eval_discharge_out", "aggr_extract_removed_leaf",
     "aggr_parse_eval_assumption", "aggr_assert_axioms_merge", "aggr_verify_eq_check_record",
     "aggr_assert_packed_addr_u64s", "aggr_linked_entry_addr", "aggr_assert_linked_merge"] 18 &&
  !hasModuleFunction prog "Aggregation" "aggr_parse_eval" &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 6 &&
  fnHasCallsAndAsserts prog "StarkVerifier" "verify_shard" verifyShardRequiredCalls 27

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
  unfold fnHasCallsAndAsserts hasModuleFunction
  rw [findModuleFunction?_append_right _ _ "MultiStark" _ hdisj.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "Aggregation" _ hdisj.2.1]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2.2]
  rw [findModuleFunction?_append_right _ _ "StarkVerifier" _ hdisj.2.2]
  have hsrc := aggregateSource_ast_pinned
  unfold AggregateProgramAstPinned fnHasCallsAndAsserts hasModuleFunction at hsrc
  have h1 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "MultiStark" "ix_aggr" ixAggrRequiredCalls 3
  have h2 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_parse_range" ["Goldilocks::gl_lt_p"] 6
  have h3 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_range_root"
    ["StarkVerifier::assert_shard_count_ok", "StarkVerifier::assert_batch_bounds",
     "StarkVerifier::assert_closure_pairs", "StarkVerifier::assert_closure_widths_ok",
     "StarkVerifier::ext_is_zero"] 10
  have h4 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_assert_security_envelope" ["UInt32::less_than_fields"] 11
  have h5 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_assert_codec_arity" ["UInt64::eq", "Lists::length"] 4
  have h6 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_verify_bridge_cert"
    ["aggr_parse_check", "aggr_parse_check_env", "Bytes::address_eq", "aggr_opt_address_eq"] 14
  have h7 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_dynamic_link"
    ["aggr_assert_security_envelope", "aggr_verify_child", "aggr_parse_dynamic_link",
     "aggr_assert_codec_arity", "aggr_verify_bridge_cert"] 3
  have h8 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_parse_eval_discharge_out" ["Fields::is_zero"] 4
  have h9 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_discharge_eval"
    ["aggr_parse_eval_assumed", "aggr_parse_eval_discharge_out", "aggr_extract_removed_leaf",
     "aggr_parse_eval_assumption", "aggr_assert_axioms_merge", "aggr_verify_eq_check_record",
     "aggr_assert_packed_addr_u64s", "aggr_linked_entry_addr", "aggr_assert_linked_merge"] 18
  have h10 := hasModuleFunction_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "Aggregation" "aggr_parse_eval"
  have h11 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "StarkVerifier" "verify_batch" verifyBatchRequiredCalls 6
  have h12 := fnHasCallsAndAsserts_map (Nat.cast : Nat → Fp) MultiStark.aggregateSource
    "StarkVerifier" "verify_shard" verifyShardRequiredCalls 17
  unfold fnHasCallsAndAsserts at h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12
  unfold hasModuleFunction at h10
  unfold Modules.Program.toField
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
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

/-- Conservative integer millibits per FRI query under unique decoding:
`floor(-1000 * log2((1 + 2^(-logBlowup)) / 2))` for `logBlowup ∈ {1, 2, 3, 4}`.
Matches `Aggregation::aggr_assert_security_envelope` identically. -/
def udMillibitsPerQuery : Nat → Nat
  | 1 => 415
  | 2 => 678
  | 3 => 830
  | 4 => 912
  | _ => 0

/-- Provable unique-decoding query soundness floor enforced by Shape 17:
`80.000` bits (`80000` millibits), blocking weak high-blowup configs such as
`(logBlowup = 4, numQueries = 55, queryPow = 0)` (`50.2` bits UD despite `220` conjectured). -/
def minProvableUdMillibits : Nat := 80000

/-- Conservative provable unique-decoding query soundness in millibits:
`udMillibitsPerQuery logBlowup * numQueries + 1000 * queryPowBits`. -/
def udQueryMillibits (logBlowup numQueries queryPowBits : Nat) : Nat :=
  udMillibitsPerQuery logBlowup * numQueries + 1000 * queryPowBits

/-- Finite-`m` (`m = 16`, slack 45 millibits/query) Johnson query soundness floor enforced by
Protocol `v6` (`Fp^3`) Shape 17: `128.000` bits (`128000` millibits). -/
def minJohnson128Millibits : Nat := 128000

/-- Finite-`m` (`m = 16`) Johnson query soundness in millibits:
`(500 * logBlowup - 45) * numQueries + 1000 * queryPowBits`. -/
def johnsonQueryMillibits (logBlowup numQueries queryPowBits : Nat) : Nat :=
  (500 * logBlowup - 45) * numQueries + 1000 * queryPowBits

/-- Exact arithmetic predicate enforced by `Aggregation::aggr_assert_security_envelope`
(`Aggregation.lean`, Protocol `v6` `Fp^3`):
- Fixed structural parameters: `capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`,
- Blowup range: `1 ≤ logBlowup ≤ 4`,
- Positive queries: `1 ≤ numQueries`,
- Proof-of-work ceiling: `commitPowBits ≤ 32`, `queryPowBits ≤ 32`,
- Conjectured ethSTARK security floor: `logBlowup * numQueries + queryPowBits ≥ 220`,
- Explicit per-`logBlowup` provable UD query soundness floor:
  `udQueryMillibits logBlowup numQueries queryPowBits ≥ 80000` (≥ 80 bits UD),
- Explicit finite-`m` (`m = 16`) Johnson query soundness floor:
  `johnsonQueryMillibits logBlowup numQueries queryPowBits ≥ 128000` (≥ 128 bits Johnson). -/
def SecurityEnvelopeOk (p : StarkParams) : Prop :=
  p.capHeight = 0 ∧
  p.logFinalPolyLen = 0 ∧
  p.maxLogArity = 1 ∧
  1 ≤ p.logBlowup ∧ p.logBlowup ≤ 4 ∧
  1 ≤ p.numQueries ∧
  p.commitPowBits ≤ Aiur.maxProofOfWorkBits ∧
  p.queryPowBits ≤ Aiur.maxProofOfWorkBits ∧
  Aiur.minConjecturedSecurityBits ≤ p.logBlowup * p.numQueries + p.queryPowBits ∧
  minProvableUdMillibits ≤ udQueryMillibits p.logBlowup p.numQueries p.queryPowBits ∧
  minJohnson128Millibits ≤ johnsonQueryMillibits p.logBlowup p.numQueries p.queryPowBits

/-- Convert `StarkParams` to `(Aiur.CommitmentParameters, Aiur.FriParameters)`. -/
def toAiurParams (p : StarkParams) : Aiur.CommitmentParameters × Aiur.FriParameters :=
  (⟨p.logBlowup, p.capHeight⟩,
   ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩)

/-- **Uniform Security Envelope Equivalence (`securityEnvelopeOk_iff`):**
`SecurityEnvelopeOk p` holds iff `Ix.Cert.MultiStark.checkParams p = true`,
`Aiur.meetsSecurityFloor (toAiurParams p).1 (toAiurParams p).2 = true`, AND
provable unique-decoding (80-bit) + finite-`m` Johnson (128-bit) query floors hold! -/
theorem securityEnvelopeOk_iff (p : StarkParams) :
    SecurityEnvelopeOk p ↔
      Ix.Cert.MultiStark.checkParams p = true ∧
      Aiur.meetsSecurityFloor (toAiurParams p).1 (toAiurParams p).2 = true ∧
      minProvableUdMillibits ≤ udQueryMillibits p.logBlowup p.numQueries p.queryPowBits ∧
      minJohnson128Millibits ≤ johnsonQueryMillibits p.logBlowup p.numQueries p.queryPowBits := by
  unfold SecurityEnvelopeOk Ix.Cert.MultiStark.checkParams Ix.Cert.MultiStark.checkParamsWithFloor
    Ix.Cert.MultiStark.checkParamsStructural Aiur.meetsSecurityFloor Aiur.conjecturedSecurityBits
    toAiurParams Aiur.maxProofOfWorkBits Aiur.minConjecturedSecurityBits Aiur.minProvableUdBits
    Aiur.minJohnsonBits Aiur.johnsonMillibits Aiur.johnsonSlackMillibitsPerQuery
    Aiur.provableUdMillibits minProvableUdMillibits udQueryMillibits
    minJohnson128Millibits johnsonQueryMillibits
  simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, hsec, hud, hj⟩
    have hlbCases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by
      omega
    have hmq : (match Aiur.minQueriesForLogBlowup p.logBlowup with
        | some minQ => decide (minQ ≤ p.numQueries) | none => false) = true := by
      rcases hlbCases with hlb | hlb | hlb | hlb <;>
        (rw [hlb] at hsec hud hj ⊢;
         simp [udMillibitsPerQuery, Aiur.minQueriesForLogBlowup] at hud hj ⊢; omega)
    have hud' : (match Option.map (fun rate => p.numQueries * rate + p.queryPowBits * 1000)
        (Aiur.udMillibitsPerQuery p.logBlowup) with
        | some udMb => decide (80 * 1000 ≤ udMb) | none => false) = true := by
      rcases hlbCases with hlb | hlb | hlb | hlb <;>
        (rw [hlb] at hud ⊢; simp [udMillibitsPerQuery, Aiur.udMillibitsPerQuery] at hud ⊢; omega)
    have hj' : 128 * 1000 ≤ (p.logBlowup * 500 - 45) * p.numQueries + p.queryPowBits * 1000 := by
      rcases hlbCases with hlb | hlb | hlb | hlb <;>
        (rw [hlb] at hj ⊢; omega)
    exact ⟨hc, hfl, hma, hlb1, hnq,
      hc, hfl, hma, hlb1, hlb4, by omega, hcp, hqp, hmq, hsec, hud', hj',
      hc, hfl, hma, hlb1, hlb4, by omega, hcp, hqp, hmq, hsec, hud', hj',
      hud, hj⟩
  · rintro ⟨hc, hfl, hma, hlb1, hnq,
      _, _, _, _, hlb4, _, hcp, hqp, _, hsec, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _,
      hud, hj⟩
    exact ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, hsec, hud, hj⟩

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

/-! ## 5. Stage-Isolated 19-Shape Recursive Aggregation Proof Tree (`AcceptedAggrTree`) → `AggrDerivation19`

**Scope Note:** `AcceptedAggrTree` is a **stage-isolated** inductive witness tree modeling
the 19 shapes of `MultiStark::ix_aggr` together with `VerifiedChildProof` child verifications;
mechanical extraction of an `AcceptedAggrTree` from `prepared.ObsFn ixAggrEntry` is tracked
separately. Within this stage-isolated model:
- Mode 2 (`dischargeEvalStep`, `dischargeEvalAll`, `dischargeEvalLinkedFinal`) discharges an
  `EvalAssumption` leaf via a kernel `@Eq` `Claim.check`, transitioning `10 → 14` / `11 → 15`
  ONLY when `EvalA = ∅` AND `Linked = ∅`.
- Mode 3a (`dischargeEvalViaDynamicLink`) discharges an `EvalAssumption` leaf via a Shape 17
  `DynamicLinkStatement` ONLY by recording its `LinkedCircuitEntry` in `LinkedAfter` under
  validators `12`/`13` (NEVER erasing into validators `3`/`4`).
- `acceptedAggrTree_unlinked_zero_dynamicLinkDischarges` proves unconditionally that ANY
  accepted tree whose root is a non-linked claim (`validator ∈ {3, 4, 5, 10, 11}`) contains
  **zero** Mode 3a dynamic-link discharge steps! -/

/-- A verified child Multi-STARK proof check executed inside an `ix_aggr` node
(calling `StarkVerifier::verify_batch_at` inside `Aggregation::aggr_verify_child`). -/
structure VerifiedChildProof where
  vkBytes : ByteArray
  claimsBytes : ByteArray
  calls : List (Aiur.Generic.SourceSemantics.Call Fp)
  refines : RecursionExecutionRefines calls
    (packDigest8 (Address.blake3Pure vkBytes))
    (packDigest8 (Address.blake3Pure claimsBytes))

/-- Stage-isolated inductive witness tree of an accepted `MultiStark::ix_aggr` execution spanning
ALL 19 aggregation shapes (`0..18`), recording:
- every verified child Multi-STARK proof (`VerifiedChildProof`),
- `A7` axiom-set merge relations (`AxiomMergeRel`),
- Shape `17` uniform security envelope (`SecurityEnvelopeOk`) + verified external proof +
  optional verified bridge cert,
- Shape `18` Mode 2 (`EvalRemoveRel` + verified `@Eq` `Claim.check`) and Mode 3a
  (`EvalRemoveRel` + verified Shape `17` `DynamicLinkStatement` + `LinkedMergeRel` into
  validators `12`/`13`). -/
inductive AcceptedAggrTree
    (sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry)
    (batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop) :
    AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry → Type where
  /-- Base IxVM leaf (`Check` / `CheckEnv`, `Linked = ∅`) verified by an outer Multi-STARK proof. -/
  | leaf {mode S A Ax EvalA} :
      VerifiedChildProof →
      LeafValid19 sem mode S A Ax EvalA →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  /-- Base IxVM `binding` claim establishing `BindingValid b`. -/
  | bindingLeaf {b : Address} :
      VerifiedChildProof →
      sem.BindingValid b →
      AcceptedAggrTree sem batchClaim (.bindingStmt b)
  /-- Base IxVM Mode 2 `@Eq` `Claim.check` discharging an `EvalAssumption` leaf `e`. -/
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
      mode.isLinked = false →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      JoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shapes `6–9` (`aggr_pair_structural`): structural Merkle pair fold + `A7` axiom merge. -/
  | pairStructural {mode SL AL AxL SR AR AxR Sout Aout AxOut} :
      (leftIsAggr rightIsAggr : Bool) →
      mode.isLinked = false →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shape `10` (`aggr_range_leaf`): verifies the `hi - lo` shard proofs covering `[lo, hi)` of
  `batchId`, each witnessed by a `VerifiedChildProof`. -/
  | rangeLeaf {batchId lo hi : Nat} :
      (shardProofs : List VerifiedChildProof) →
      lo ≤ hi →
      shardProofs.length = hi - lo →
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
      mode.isLinked = false →
      VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.rangeStmt batchId 0 (sem.shardCount batchId) r) →
      sem.residualMonoid.add (sem.messagesAcc batchId) r = sem.residualMonoid.zero →
      batchClaim batchId mode S A Ax EvalA →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  /-- Shapes `13–14` (`aggr_discharge_binding`): discharges assumed binding (`validator 4 → 3`). -/
  | dischargeBinding {b S A Ax} :
      (isAggrChild : Bool) →
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv (.assumedBinding b) S A Ax (fun _ => False) (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.bindingStmt b) →
      AcceptedAggrTree sem batchClaim (.checkEnv (.validated b) S A Ax (fun _ => False) (fun _ => False))
  /-- Shape `15` (`aggr_cross_binding`): cross-binding structural join under 13-role class `k`
  (`validator ∈ {3, 5} → 5`) + `A7` axiom merge. -/
  | crossBinding {modeL modeR : ValidatorMode Address} {k : Address}
      {SL AL AxL SR AR AxR Sout Aout AxOut} :
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim (.checkEnv modeL SL AL AxL (fun _ => False) (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.checkEnv modeR SR AR AxR (fun _ => False) (fun _ => False)) →
      modeL.isBindingDischarged = true →
      modeR.isBindingDischarged = true →
      (modeL = .literalClass k ∨ sem.LiteralClassOf modeL.bindingOf k) →
      (modeR = .literalClass k ∨ sem.LiteralClassOf modeR.bindingOf k) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv (.literalClass k) Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shape `16` (`aggr_catalog_join`): catalog union of unconditional, unlinked `CheckEnv`/`Catalog` children. -/
  | catalogJoin {membersL membersR membersOut : (Address × (Address → Prop) × (Address → Prop)) → Prop}
      {stmtL stmtR : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry} :
      VerifiedChildProof → VerifiedChildProof →
      AcceptedAggrTree sem batchClaim stmtL →
      AcceptedAggrTree sem batchClaim stmtR →
      ((∃ mode S Ax, stmtL = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersL m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtL = .catalogStmt membersL) →
      ((∃ mode S Ax, stmtR = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersR m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtR = .catalogStmt membersR) →
      (∀ m, membersOut m ↔ membersL m ∨ membersR m) →
      AcceptedAggrTree sem batchClaim (.catalogStmt membersOut)
  /-- Shape `17` (`aggr_dynamic_link`, `0xE8 0x0D`): verifies external Multi-STARK proof under
  `SecurityEnvelopeOk` (and optional bridge cert proof on slot 1 binding `(spec, binding)`). -/
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
  /-- Shape `18` Mode 2 partial step (`aggr_discharge_eval`): discharges one `EvalAssumption` leaf
  `e₀` via an `@Eq` `Claim.check`, preserving `mode ∈ {10, 11, 12, 13}` and `Linked`, with `A7` merge. -/
  | dischargeEvalStep {mode : ValidatorMode Address} {S A Ax₀ Ax₁ AxOut EvalBefore EvalAfter Linked e₀} :
      VerifiedChildProof → VerifiedChildProof →
      mode.canDischargeEval = true →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore EvalAfter e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A AxOut EvalAfter Linked)
  /-- Shape `18` Mode 2 final unlinked step (`aggr_discharge_eval`): discharges the final
  `EvalAssumption` leaf `e₀` via an `@Eq` `Claim.check` when `Linked = ∅`, transitioning
  validator `10 → 14` or `11 → 15` with `EvalA = ∅`, `Linked = ∅`, and `A7` axiom merge. -/
  | dischargeEvalAll {mode outMode : ValidatorMode Address} {S A Ax₀ Ax₁ AxOut EvalBefore e₀} :
      VerifiedChildProof → VerifiedChildProof →
      mode.dischargeAllEvals = some outMode →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore (fun _ => False)) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv outMode S A AxOut (fun _ => False) (fun _ => False))
  /-- Shape `18` Mode 2 final linked step (`aggr_discharge_eval`): discharges the final
  `EvalAssumption` leaf `e₀` via an `@Eq` `Claim.check` on an already-linked claim (`12`/`13`),
  staying in linked mode `12`/`13` with `Linked` preserved (NEVER `3`/`4`). -/
  | dischargeEvalLinkedFinal {mode : ValidatorMode Address} {S A Ax₀ Ax₁ AxOut EvalBefore Linked e₀} :
      VerifiedChildProof → VerifiedChildProof →
      mode.isLinked = true →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      AcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A AxOut (fun _ => False) Linked)
  /-- Shape `18` Mode 3a (`aggr_discharge_eval`, tag `232`): discharges `e₀` via a Shape `17`
  `DynamicLinkStatement`, ALWAYS transitioning to linked mode (`10 → 12`, `11 → 13`, `12 → 12`,
  `13 → 13`) and recording `entry : LinkedCircuitEntry` into `LinkedAfter` via `LinkedMergeRel`. -/
  | dischargeEvalViaDynamicLink {mode outMode : ValidatorMode Address}
      {S A Ax EvalBefore EvalAfter LinkedBefore LinkedAfter stmt e₀ entry} :
      VerifiedChildProof → VerifiedChildProof →
      mode.toLinkedMode = some outMode →
      AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalBefore LinkedBefore) →
      AcceptedAggrTree sem batchClaim (.dynamicLinkStmt stmt) →
      EvalRemoveRel EvalBefore EvalAfter e₀ →
      sem.LinkedRecords stmt mode.bindingOf e₀ entry →
      LinkedMergeRel LinkedBefore entry LinkedAfter →
      AcceptedAggrTree sem batchClaim (.checkEnv outMode S A Ax EvalAfter LinkedAfter)

/-- Collect every `VerifiedChildProof` executed across an entire `AcceptedAggrTree`. -/
def AcceptedAggrTree.childProofs
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry} :
    AcceptedAggrTree sem batchClaim stmt → List VerifiedChildProof
  | .leaf vp _ => [vp]
  | .bindingLeaf vp _ => [vp]
  | .evalDischargerLeaf vp _ => [vp]
  | .wrap _ vp t => vp :: t.childProofs
  | .pairFlat _ _ _ vpL vpR tL tR _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .pairStructural _ _ _ vpL vpR tL tR _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .rangeLeaf shardProofs _ _ => shardProofs
  | .rangeJoin vpL vpR tL tR => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .rangeRoot _ vp t _ _ => vp :: t.childProofs
  | .dischargeBinding _ vpC vpB tC tB => vpC :: vpB :: tC.childProofs ++ tB.childProofs
  | .crossBinding vpL vpR tL tR _ _ _ _ _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .catalogJoin vpL vpR tL tR _ _ _ => vpL :: vpR :: tL.childProofs ++ tR.childProofs
  | .dynamicLink extP _ _ _ _ bridge? _ _ =>
      match bridge? with
      | some bp => [extP, bp]
      | none => [extP]
  | .dischargeEvalStep vpC vpD _ tC tD _ _ => vpC :: vpD :: tC.childProofs ++ tD.childProofs
  | .dischargeEvalAll vpC vpD _ tC tD _ _ => vpC :: vpD :: tC.childProofs ++ tD.childProofs
  | .dischargeEvalLinkedFinal vpC vpD _ tC tD _ _ => vpC :: vpD :: tC.childProofs ++ tD.childProofs
  | .dischargeEvalViaDynamicLink vpC vpDL _ tC tDL _ _ _ => vpC :: vpDL :: tC.childProofs ++ tDL.childProofs

/-- Count of Shape 18 Mode 3a (`DynamicLinkStatement`) external-circuit discharge steps
occurring anywhere in an `AcceptedAggrTree`. -/
def AcceptedAggrTree.dynamicLinkDischarges
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry} :
    AcceptedAggrTree sem batchClaim stmt → Nat
  | .leaf _ _ => 0
  | .bindingLeaf _ _ => 0
  | .evalDischargerLeaf _ _ => 0
  | .wrap _ _ t => t.dynamicLinkDischarges
  | .pairFlat _ _ _ _ _ tL tR _ _ => tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .pairStructural _ _ _ _ _ tL tR _ _ => tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .rangeLeaf _ _ _ => 0
  | .rangeJoin _ _ tL tR => tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .rangeRoot _ _ t _ _ => t.dynamicLinkDischarges
  | .dischargeBinding _ _ _ tC tB => tC.dynamicLinkDischarges + tB.dynamicLinkDischarges
  | .crossBinding _ _ tL tR _ _ _ _ _ _ => tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .catalogJoin _ _ tL tR _ _ _ => tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .dynamicLink _ _ _ _ _ _ _ _ => 0
  | .dischargeEvalStep _ _ _ tC tD _ _ => tC.dynamicLinkDischarges + tD.dynamicLinkDischarges
  | .dischargeEvalAll _ _ _ tC tD _ _ => tC.dynamicLinkDischarges + tD.dynamicLinkDischarges
  | .dischargeEvalLinkedFinal _ _ _ tC tD _ _ => tC.dynamicLinkDischarges + tD.dynamicLinkDischarges
  | .dischargeEvalViaDynamicLink _ _ _ tC tDL _ _ _ =>
      1 + tC.dynamicLinkDischarges + tDL.dynamicLinkDischarges

private def stmtIsUnlinked :
    AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry → Prop
  | .checkEnv mode _ _ _ _ _ => mode.isLinked = false
  | .rangeStmt _ _ _ _ => True
  | .bindingStmt _ => True
  | .catalogStmt _ => True
  | .dynamicLinkStmt _ => True
  | .evalDischargerStmt _ _ _ => True

private theorem isLinked_false_of_isBindingDischarged {mode : ValidatorMode Address}
    (h : mode.isBindingDischarged = true) : mode.isLinked = false := by
  cases mode <;> simp [ValidatorMode.isBindingDischarged, ValidatorMode.isLinked] at h ⊢

private theorem acceptedAggrTree_stmtIsUnlinked_zero
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim stmt)
    (hunl : stmtIsUnlinked stmt) :
    t.dynamicLinkDischarges = 0 := by
  induction t with
  | leaf _ _ => rfl
  | bindingLeaf _ _ => rfl
  | evalDischargerLeaf _ _ => rfl
  | wrap _ _ _ ih => exact ih hunl
  | pairFlat _ _ hUnl _ _ _ _ _ _ ihL ihR =>
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihL hUnl, ihR hUnl]
  | pairStructural _ _ hUnl _ _ _ _ _ _ ihL ihR =>
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihL hUnl, ihR hUnl]
  | rangeLeaf _ _ _ => rfl
  | rangeJoin _ _ _ _ ihL ihR =>
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihL trivial, ihR trivial]
  | rangeRoot _ _ _ _ _ ih => exact ih trivial
  | dischargeBinding _ _ _ _ _ ihC ihB =>
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihC rfl, ihB trivial]
  | crossBinding _ _ _ _ hDisL hDisR _ _ _ _ ihL ihR =>
    simp [AcceptedAggrTree.dynamicLinkDischarges,
      ihL (isLinked_false_of_isBindingDischarged hDisL),
      ihR (isLinked_false_of_isBindingDischarged hDisR)]
  | catalogJoin _ _ _ _ hSL hSR _ ihL ihR =>
    simp only [AcceptedAggrTree.dynamicLinkDischarges]
    rw [ihL (by
      rcases hSL with ⟨mode, _, _, hEq, hDis, _⟩ | hEq
      · rw [hEq]; exact isLinked_false_of_isBindingDischarged hDis
      · rw [hEq]; trivial),
      ihR (by
      rcases hSR with ⟨mode, _, _, hEq, hDis, _⟩ | hEq
      · rw [hEq]; exact isLinked_false_of_isBindingDischarged hDis
      · rw [hEq]; trivial)]
  | dynamicLink _ _ _ _ _ _ _ _ => rfl
  | dischargeEvalStep _ _ _ _ _ _ _ ihC ihD =>
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihC hunl, ihD trivial]
  | dischargeEvalAll _ _ hTrans _ _ _ _ ihC ihD =>
    have hUnl := (validatorMode_dischargeAllEvals_unlinked hTrans).1
    simp [AcceptedAggrTree.dynamicLinkDischarges, ihC hUnl, ihD trivial]
  | dischargeEvalLinkedFinal _ _ hLnk _ _ _ _ _ _ =>
    simp [stmtIsUnlinked, hLnk] at hunl
  | dischargeEvalViaDynamicLink _ _ hToLnk _ _ _ _ _ _ _ =>
    have hLnk := (validatorMode_toLinkedMode_props hToLnk).1
    simp [stmtIsUnlinked, hLnk] at hunl

/-- **Zero External-Circuit Guarantee for Unlinked Validator Outputs (`acceptedAggrTree_unlinked_zero_dynamicLinkDischarges`):**
Any accepted 19-shape aggregation tree whose root is an unlinked `.checkEnv` claim
(`mode.isLinked = false`, in particular ANY validator `3`, `4`, or `5` claim!) performed
**zero** Shape 18 Mode 3a external dynamic-circuit discharges (`t.dynamicLinkDischarges = 0`). -/
theorem acceptedAggrTree_unlinked_zero_dynamicLinkDischarges
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {mode : ValidatorMode Address} {S A Ax : Address → Prop}
    {EvalA : EvalAssumption → Prop} {Linked : LinkedCircuitEntry → Prop}
    (hUnl : mode.isLinked = false)
    (t : AcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA Linked)) :
    t.dynamicLinkDischarges = 0 :=
  acceptedAggrTree_stmtIsUnlinked_zero t hUnl

/-- Total number of recursive Multi-STARK proof verifications inside an `AcceptedAggrTree`. -/
def AcceptedAggrTree.verificationCount
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim stmt) : Nat :=
  t.childProofs.length

/-- Shape 10 range leaves expose every shard proof they verify in `childProofs`. -/
theorem rangeLeaf_childProofs
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {batchId lo hi : Nat} (shardProofs : List VerifiedChildProof)
    (hle : lo ≤ hi) (hlen : shardProofs.length = hi - lo) :
    (AcceptedAggrTree.rangeLeaf (sem := sem) (batchClaim := batchClaim)
      (batchId := batchId) (lo := lo) (hi := hi) shardProofs hle hlen).childProofs = shardProofs :=
  rfl

/-- Shape 10 range leaves contribute `hi - lo` verifications to `verificationCount`. -/
theorem rangeLeaf_verificationCount
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {batchId lo hi : Nat} (shardProofs : List VerifiedChildProof)
    (hle : lo ≤ hi) (hlen : shardProofs.length = hi - lo) :
    (AcceptedAggrTree.rangeLeaf (sem := sem) (batchClaim := batchClaim)
      (batchId := batchId) (lo := lo) (hi := hi) shardProofs hle hlen).verificationCount =
      hi - lo :=
  hlen

/-- Whether ANY recursive Multi-STARK child verification in `t` exhibited a concrete BLAKE3
collision against its anchored `(vkBytes, claimsBytes)`. -/
def AcceptedAggrTree.HasTreeCollision
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    (t : AcceptedAggrTree sem batchClaim stmt) : Prop :=
  ∃ vp ∈ t.childProofs, MultiStarkCollision [vp.vkBytes, vp.claimsBytes] vp.calls

/-- **Stage-Isolated 19-Shape Recursive Aggregation Tree Refinement (`acceptedAggrTree_refines_derivation19`):**
For ANY accepted aggregation tree `t` across all 19 shapes (`0..18`):
1. Every node's statement refines cleanly into `Aggr.AggrDerivation19 sem batchClaim stmt`, AND
2. EITHER some child verification in `t` hashed a concrete BLAKE3 collision (`t.HasTreeCollision`),
   OR EVERY child verification `vp ∈ t.childProofs` is accepted by the certified out-of-circuit
   Multi-STARK verifier `Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true`! -/
theorem acceptedAggrTree_refines_derivation19
    {sem : AggrSemantics Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
    {batchClaim : Nat → ValidatorMode Address → (Address → Prop) → (Address → Prop) →
      (Address → Prop) → (EvalAssumption → Prop) → Prop}
    {stmt : AggrNodeStmt Address Address EvalAssumption Address K DynamicLinkStatement LinkedCircuitEntry}
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
    | pairFlat _ _ hUnl _ _ _ _ hJ hA ihL ihR => exact .pairFlat hUnl ihL ihR hJ hA
    | pairStructural _ _ hUnl _ _ _ _ hJ hA ihL ihR => exact .pairStructural hUnl ihL ihR hJ hA
    | rangeLeaf _ hle _ => exact .rangeLeaf hle
    | rangeJoin _ _ _ _ ihL ihR => exact .rangeJoin ihL ihR
    | rangeRoot hUnl _ _ hZ hC ih => exact .rangeRoot hUnl ih hZ hC
    | dischargeBinding _ _ _ _ _ ihC ihB => exact .dischargeBinding ihC ihB
    | crossBinding _ _ _ _ hDL hDR hCL hCR hJ hA ihL ihR =>
        exact .crossBinding ihL ihR hDL hDR hCL hCR hJ hA
    | catalogJoin _ _ _ _ hSL hSR hU ihL ihR => exact .catalogJoin ihL ihR hSL hSR hU
    | dynamicLink _ _ _ _ _ _ _ hDL => exact .dynamicLink hDL
    | dischargeEvalStep _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalStep hM ihC ihD hR hA
    | dischargeEvalAll _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalAll hM ihC ihD hR hA
    | dischargeEvalLinkedFinal _ _ hLnk _ _ hR hA ihC ihD =>
        exact .dischargeEvalLinkedFinal hLnk ihC ihD hR hA
    | dischargeEvalViaDynamicLink _ _ hToLnk _ _ hR hRec hMerge ihC ihDL =>
        exact .dischargeEvalViaDynamicLink hToLnk ihC ihDL hR hRec hMerge
  · by_cases hCol : t.HasTreeCollision
    · exact Or.inl hCol
    · refine Or.inr fun vp hvp => ?_
      rcases recursion_obs_refines_verifyBatch vp.refines with hvpCol | ⟨pb, _, _, _, _, _, _, _, hvbb, _⟩
      · exact absurd ⟨vp, hvp, hvpCol⟩ hCol
      · exact ⟨pb, hvbb⟩

end Ix.Cert.Aggr
