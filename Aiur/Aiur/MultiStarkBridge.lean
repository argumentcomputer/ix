import Aiur.MultiStarkSpec
import Aiur.Tiling.Grouped
import Aiur.Tiling.Enables
import Aiur.Optimized.Depth.Grouped
import Aiur.Optimized.Depth.StructuralEndToEnd
import Mathlib.Algebra.Polynomial.Roots

/-!
# Formal Multi-STARK AIR Lowering Bridge to Grouping Plan & Memo Verification

This module proves the end-to-end soundness bridge from the deployed Multi-STARK
lowering (`Aiur.MultiStarkSpec.lowerFullSystem`) and the fast boolean-enable
verifier (`Aiur.Tiling.Bridge.checkChipEnables`) to
`Aiur.Optimized.Grouping.Plan.inspectRow`, `Aiur.Optimized.Grouping.Plan.checkMemo`,
`Aiur.Optimized.Physical.Prepared.checkDepthPlan_sound`, and
`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`.

## Main Components

1. **Lowered Multi-STARK Trace Semantics (`CircuitTrace`, `CircuitAirSatisfied`,
   `circuitRowLedger`, `circuitLedger`):**
   Evaluates every compiled and retuned circuit emitted by `lowerFullSystem`
   (after constant folding, zero elimination, deduplication, and
   `lookup_groups::retune` permutation/chunking) and proves exact invariance of
   both row constraints and row ledgers under `compileCircuit` and `retune`.

2. **Stage-2 Grouped Rational LogUp Bridge (`CircuitStage2Satisfied`,
   `batch_stage2_logup_eq_trimmed_sum`, `trimmed_ledger_zero_of_stage2_logup`,
   `card_stage2_logup_bad_beta_le`):**
   Connects the degree-3 chained stage-2 accumulator constraints on retuned
   lookup chunks (`MultiStarkSpec.CircuitLogUpSatisfied`) to the trimmed
   multiset balance `Finsupp.mapDomain Tiling.trimZeros (...) = 0` via Horner
   fingerprints and partial-fraction non-vanishing.

3. **Enable Booleanity & Unit-Weight Pulls (`checkEnables_implies_unit_weight`):**
   Connects `Aiur.Tiling.Bridge.checkChipEnables` on all chips of a grouping plan
   to every lowered function circuit emitted by `lowerFullSystem` (both single
   chips and grouped layouts, including compacted slots), proving that every
   padding row has zero receive multiplicity and zero row ledger, and every
   non-receive lookup has `{0, 1}`-valued multiplicity.

4. **Scalar & Vectorized ROM Extraction and Validity (`extractWidthROM`,
   `extractWidthROM_valid_unsegmented`, `extractWidthROM_valid_segmented_zmod`):**
   Handles both scalar (`K = 1`) and `K`-lane vectorized ROM circuits emitted by
   `lowerRomCircuitsWithLayout`, proving ROM ledger support and `WidthROM.Valid`
   in both standalone (`segmented = false`) and sharded/batched (`segmented = true`,
   via `MEMSEG` interval balance) modes.

5. **Row-to-Plan & Memo-Checker Bridge (`LoweredSystemSatisfied`,
   `lowerFullSystem_row_implies_inspectRow`,
   `lowerFullSystem_satisfied_implies_checkMemo`):**
   Proves that any trace family satisfying `LoweredSystemSatisfied` over
   `lowerFullSystem` reconstructs weighted rows accepted by
   `plan.checkMemo (Erasure.rawROM rom) root wrows = .ok ()`, using only the
   physical lookup budget (`< bound`) and `checkChipEnables`.

6. **End-to-End Composition with `Physical.Prepared.checkDepthPlan_sound`:**
   Composes `lowerFullSystem_satisfied_implies_checkMemo` directly with
   `Physical.Prepared.checkDepthPlan_sound` and
   `Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks` (both
   standalone and segmented modes, as well as starting from stage-2 grouped
   LogUp accumulator constraints).

Zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`.
-/

namespace Aiur.MultiStarkBridge

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping
open Aiur.MultiStarkSpec
open Aiur.Tiling (Ledger SmallCast smallCast_zmod trimZeros trimZeros_inj_of_length trimZeros_head)
open Aiur.Tiling.Bridge (Boolean checkChipEnables boolean_of_checkChipEnables encode encodeRom Shaped)
open Aiur.Tiling.Grouped (allChips circuitNames group_row group_inspect group_virtual
  instLedger lowerGroup memberInst project trimZeros_eq_iff)

/-! ## 1. Lowered Multi-STARK Trace Semantics & `compileCircuit`/`retune` Invariance -/

section TraceSemantics

/-- Main and preprocessed trace matrices of a single lowered Multi-STARK circuit. -/
structure CircuitTrace (F : Type) where
  height : Nat
  mainRow : Nat → Nat → F
  prepRow : Nat → Nat → F

/-- Next-row accessor on a trace domain (wrapping cyclically at the last row). -/
def CircuitTrace.nextRow (tr : CircuitTrace F) (r : Nat) : Nat → F :=
  if r + 1 < tr.height then tr.mainRow (r + 1) else tr.mainRow 0

/-- Evaluate an `AirExpr F` at row `r` of a `CircuitTrace F`. -/
def CircuitTrace.evalExpr [Ring F] (tr : CircuitTrace F) (r : Nat) (e : AirExpr F) : F :=
  e.eval (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
    (if r = 0 then 1 else 0)
    (if r + 1 = tr.height then 1 else 0)
    (if r + 1 < tr.height then 1 else 0)

/-- Row-wise AIR polynomial constraint satisfaction for a compiled circuit. -/
def CircuitRowSatisfied [Ring F] (c : CompiledCircuit F) (tr : CircuitTrace F) (r : Nat) : Prop :=
  ∀ e ∈ c.constraints, tr.evalExpr r e = 0

/-- Trace-wide AIR polynomial constraint satisfaction for a compiled circuit. -/
def CircuitAirSatisfied [Ring F] (c : CompiledCircuit F) (tr : CircuitTrace F) : Prop :=
  ∀ r < tr.height, CircuitRowSatisfied c tr r

/-- Compile and retune a single `CircuitInput F`, matching `lowerFullSystem`. -/
def compileRetune [Ring F] [DecidableEq F] (logBlowup extDegree : Nat)
    (inp : CircuitInput F) : CompiledCircuit F :=
  retune (compileCircuit inp extDegree) (2 ^ logBlowup) extDegree

theorem lowerFullSystem_eq_map [Field F] [DecidableEq F] {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat)
    (logBlowup : Nat) (segmented : Bool) (extDegree : Nat := goldilocksExtDegree)
    (romLayout : RomLayout := .vectorized) :
    lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout =
      (lowerPlanFunctionsOrdered callableId plan ++
        lowerFixedTables (F := F) fixedMaps logBlowup ++
        lowerRomCircuitsWithLayout (F := F) romWidths segmented romLayout).map
          (compileRetune logBlowup extDegree) := rfl

theorem evalExpr_fold [Ring F] [DecidableEq F] (tr : CircuitTrace F) (r : Nat) (e : AirExpr F) :
    tr.evalExpr r e.fold = tr.evalExpr r e :=
  AirExpr.eval_fold _ _ _ _ _ _ e

theorem evalExpr_lowerPoly [Field F] (tr : CircuitTrace F) (r : Nat) (p : Circuit.ArithExpr F) :
    tr.evalExpr r (lowerPoly p) = p.denote (tr.mainRow r) :=
  eval_lowerPoly _ _ _ _ _ _ p

private theorem airExpr_bne_const_zero_of_ne [Ring F] [DecidableEq F]
    {e : AirExpr F} (hz : e ≠ .const 0) : (e != .const 0) = true := by
  cases e with
  | const c =>
      have hc : c ≠ 0 := fun h => hz (by rw [h])
      change (!(c == (0 : F))) = true
      simp [hc]
  | main _ | mainNext _ | preprocessed _ | isFirstRow | isLastRow | isTransition
  | add _ _ | sub _ _ | mul _ _ | neg _ => rfl

/-- AIR satisfaction of a compiled and retuned circuit is equivalent to every
constraint of the uncompiled `CircuitInput` vanishing on the row. -/
theorem circuitRowSatisfied_retune_compile_iff [Ring F] [DecidableEq F]
    (inp : CircuitInput F) (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    CircuitRowSatisfied (compileRetune logBlowup extDegree inp) tr r ↔
      ∀ e ∈ inp.constraints, tr.evalExpr r e = 0 := by
  have hcons : (compileRetune logBlowup extDegree inp).constraints =
      ((inp.constraints.map AirExpr.fold).filter fun e => e != .const 0).dedup := by
    unfold compileRetune
    rw [(retune_lookups_perm (compileCircuit inp extDegree) (2 ^ logBlowup) extDegree).2.2.2]
    rfl
  constructor
  · intro hsat e he
    by_cases hz : e.fold = .const 0
    · rw [← evalExpr_fold tr r e, hz]; rfl
    · have hmem : e.fold ∈ (compileRetune logBlowup extDegree inp).constraints := by
        rw [hcons, List.mem_dedup, List.mem_filter]
        exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩, airExpr_bne_const_zero_of_ne hz⟩
      rw [← evalExpr_fold tr r e]
      exact hsat _ hmem
  · intro hsat e he
    rw [hcons, List.mem_dedup, List.mem_filter] at he
    obtain ⟨hmap, _⟩ := he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp hmap
    rw [evalExpr_fold]
    exact hsat e0 he0

/-- Single `AirLookup` evaluated into a `Ledger F` entry at row `r`. -/
noncomputable def airLookupLedger [Field F] (tr : CircuitTrace F) (r : Nat)
    (l : AirLookup F) : Ledger F :=
  Finsupp.single (l.args.map (tr.evalExpr r)) (tr.evalExpr r l.multiplicity)

/-- Row LogUp ledger of a `CompiledCircuit F`. -/
noncomputable def circuitRowLedger [Field F] (c : CompiledCircuit F)
    (tr : CircuitTrace F) (r : Nat) : Ledger F :=
  (c.lookups.map (airLookupLedger tr r)).sum

/-- Total LogUp ledger of a `CompiledCircuit F` summed over all rows `0 .. tr.height - 1`. -/
noncomputable def circuitLedger [Field F] (c : CompiledCircuit F)
    (tr : CircuitTrace F) : Ledger F :=
  ((List.range tr.height).map (circuitRowLedger c tr)).sum

/-- Compilation and `lookup_groups::retune` preserve the exact per-row LogUp ledger. -/
theorem circuitRowLedger_retune_compile_eq [Field F] [DecidableEq F]
    (inp : CircuitInput F) (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    circuitRowLedger (compileRetune logBlowup extDegree inp) tr r =
      (inp.lookups.map (airLookupLedger tr r)).sum := by
  unfold circuitRowLedger compileRetune
  have hperm : (retune (compileCircuit inp extDegree) (2 ^ logBlowup) extDegree).lookups.Perm
      inp.lookups := by
    simpa [compileCircuit] using
      (retune_lookups_perm (compileCircuit inp extDegree) (2 ^ logBlowup) extDegree).1
  exact (hperm.map (airLookupLedger tr r)).sum_eq

/-- Compilation and `lookup_groups::retune` preserve the exact circuit-level LogUp ledger. -/
theorem circuitLedger_retune_compile_eq [Field F] [DecidableEq F]
    (inp : CircuitInput F) (logBlowup extDegree : Nat) (tr : CircuitTrace F) :
    circuitLedger (compileRetune logBlowup extDegree inp) tr =
      ((List.range tr.height).map fun r => (inp.lookups.map (airLookupLedger tr r)).sum).sum := by
  unfold circuitLedger
  congr 1
  apply List.map_congr_left
  intro r _
  exact circuitRowLedger_retune_compile_eq inp logBlowup extDegree tr r

/-- Helper: splitting `List.Forall₂` across an append of the left list. -/
theorem forall₂_append_left_split {α β : Type*} {R : α → β → Prop} :
    ∀ {xs ys : List α} {zs : List β}, List.Forall₂ R (xs ++ ys) zs →
      List.Forall₂ R xs (zs.take xs.length) ∧ List.Forall₂ R ys (zs.drop xs.length)
  | [], ys, zs, h => by simpa using h
  | x :: xs, ys, [], h => by cases h
  | x :: xs, ys, z :: zs, h => by
      obtain ⟨hxz, hrest⟩ := List.forall₂_cons.mp h
      obtain ⟨h1, h2⟩ := forall₂_append_left_split hrest
      exact ⟨List.Forall₂.cons hxz h1, h2⟩

/-- Helper: splitting `List.zipWith` across an append of the left list. -/
theorem zipWith_append_left_split {α β γ : Type*} (f : α → β → γ) :
    ∀ {xs ys : List α} {zs : List β}, zs.length = (xs ++ ys).length →
      List.zipWith f (xs ++ ys) zs =
        List.zipWith f xs (zs.take xs.length) ++ List.zipWith f ys (zs.drop xs.length)
  | [], ys, zs, _ => by simp
  | x :: xs, ys, [], hlen => by simp at hlen
  | x :: xs, ys, z :: zs, hlen => by
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons,
        List.take_succ_cons, List.drop_succ_cons]
      congr 1
      exact zipWith_append_left_split f (by simp only [List.length_cons, List.length_append] at hlen ⊢; omega)

/-- Total lookup budget matching `check_system_shape` (`1 + ∑ H_i * lookups_i`). -/
def systemLookupBudget (circuits : List (CompiledCircuit F)) (traces : List (CircuitTrace F)) : Nat :=
  1 + (List.zipWith (fun c tr => tr.height * c.lookups.length) circuits traces).sum

/-- Total physical function rows summed across function traces. -/
def totalRows (traces : List (CircuitTrace F)) : Nat :=
  (traces.map CircuitTrace.height).sum

end TraceSemantics

/-! ## 2. Stage-2 Grouped Rational LogUp → Trimmed Multiset Ledger Bridge -/

section Stage2LogUpBridge

variable {F K : Type} [Field F] [DecidableEq F] [Field K]

theorem trimZeros_idemp : ∀ (args : List F), trimZeros (trimZeros args) = trimZeros args
  | [] => rfl
  | a :: rest => by
      simp only [trimZeros]
      split_ifs with h
      · rfl
      · simp [trimZeros, trimZeros_idemp rest, h]

/-- Multi-STARK's Horner fingerprint ignores trailing zeros (`trimZeros`). -/
theorem fingerprint_trimZeros (embed : F →+* K) (β γ : K) (args : List F) :
    fingerprint β γ (args.map embed) = fingerprint β γ ((trimZeros args).map embed) := by
  apply fingerprint_eq_of_word_eq
  intro j
  have hget : args.getD j 0 = (trimZeros args).getD j 0 :=
    trimZeros_eq_iff.mp (trimZeros_idemp args).symm j
  have hmap : ∀ (xs : List F), (xs.map embed)[j]?.getD 0 = embed (xs.getD j 0) := by
    intro xs
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases xs[j]? with
    | none => simp [map_zero]
    | some v => rfl
  rw [hmap args, hmap (trimZeros args), hget]

/-- Evaluating a `Ledger F` against the rational LogUp kernel `(k, w) ↦ embed w / fp(k)`. -/
def ledgerLogUpSum (embed : F →+* K) (β γ : K) (L : Ledger F) : K :=
  L.sum fun k w => embed w * (fingerprint β γ (k.map embed))⁻¹

omit [DecidableEq F] in
theorem ledgerLogUpSum_zero (embed : F →+* K) (β γ : K) :
    ledgerLogUpSum embed β γ (0 : Ledger F) = 0 := by
  simp [ledgerLogUpSum]

omit [DecidableEq F] in
theorem ledgerLogUpSum_single (embed : F →+* K) (β γ : K) (t : List F) (w : F) :
    ledgerLogUpSum embed β γ (Finsupp.single t w) =
      embed w * (fingerprint β γ (t.map embed))⁻¹ := by
  unfold ledgerLogUpSum
  rw [Finsupp.sum_single_index (by simp [map_zero])]

omit [DecidableEq F] in
theorem ledgerLogUpSum_add (embed : F →+* K) (β γ : K) (L₁ L₂ : Ledger F) :
    ledgerLogUpSum embed β γ (L₁ + L₂) =
      ledgerLogUpSum embed β γ L₁ + ledgerLogUpSum embed β γ L₂ := by
  unfold ledgerLogUpSum
  exact Finsupp.sum_add_index' (fun _ => by simp [map_zero])
    (fun _ a b => by rw [map_add, add_mul])

omit [DecidableEq F] in
theorem ledgerLogUpSum_list_sum (embed : F →+* K) (β γ : K) :
    ∀ Ls : List (Ledger F),
      ledgerLogUpSum embed β γ Ls.sum = (Ls.map (ledgerLogUpSum embed β γ)).sum
  | [] => by simp [ledgerLogUpSum_zero]
  | L :: Ls => by
      simp only [List.sum_cons, List.map_cons, ledgerLogUpSum_add, ledgerLogUpSum_list_sum]

theorem ledgerLogUpSum_mapDomain_trimZeros (embed : F →+* K) (β γ : K) (L : Ledger F) :
    ledgerLogUpSum embed β γ (Finsupp.mapDomain trimZeros L) =
      ledgerLogUpSum embed β γ L := by
  unfold ledgerLogUpSum
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp [map_zero])
    (fun _ a b => by rw [map_add, add_mul])]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [← fingerprint_trimZeros]

omit [DecidableEq F] in
/-- Per-row ungrouped LogUp rational sum equals `ledgerLogUpSum` of `circuitRowLedger`. -/
theorem row_ungroupedLogUpSum_eq_ledger (embed : F →+* K) (β γ : K)
    (c : CompiledCircuit F) (tr : CircuitTrace F) (r : Nat) :
    ungroupedLogUpSum (c.lookups.map fun l =>
      evalLookup embed β γ (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
        (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
        (if r + 1 < tr.height then 1 else 0) l) =
      ledgerLogUpSum embed β γ (circuitRowLedger c tr r) := by
  unfold ungroupedLogUpSum circuitRowLedger
  rw [ledgerLogUpSum_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, airLookupLedger, ledgerLogUpSum_single, evalLookup,
    CircuitTrace.evalExpr, List.map_map]
  rfl

/-- Stage-2 grouped LogUp accumulator satisfaction for one circuit (handling both
inactive `height = 0` circuits and active `height > 0` circuits). -/
def CircuitStage2Satisfied (embed : F →+* K) (β γ : K)
    (c : CompiledCircuit F) (tr : CircuitTrace F)
    (acc : Nat → Nat → K) (accInitial accFinal : K) : Prop :=
  (tr.height = 0 ∧ accFinal = accInitial) ∨
  (CircuitLogUpSatisfied tr.height
      (fun r => chunkList c.lookupGroupSize
        (c.lookups.map fun l =>
          evalLookup embed β γ (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
            (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
            (if r + 1 < tr.height then 1 else 0) l))
      acc accInitial accFinal ∧
    ∀ r < tr.height, ∀ l ∈ c.lookups,
      (evalLookup embed β γ (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
        (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
        (if r + 1 < tr.height then 1 else 0) l).2 ≠ 0)

omit [DecidableEq F] in
/-- Per-circuit stage-2 accumulator delta equals `ledgerLogUpSum` of `circuitLedger`. -/
theorem circuitStage2_delta_eq_ledger (embed : F →+* K) (β γ : K)
    (c : CompiledCircuit F) (tr : CircuitTrace F)
    (acc : Nat → Nat → K) (accInitial accFinal : K)
    (hsat : CircuitStage2Satisfied embed β γ c tr acc accInitial accFinal) :
    accFinal - accInitial = ledgerLogUpSum embed β γ (circuitLedger c tr) := by
  rcases hsat with ⟨h0, heq⟩ | ⟨hlogup, hne⟩
  · simp [h0, heq, circuitLedger, ledgerLogUpSum_zero]
  · have hneChunks : ∀ r < tr.height,
        ∀ ch ∈ chunkList c.lookupGroupSize (c.lookups.map fun l =>
          evalLookup embed β γ (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
            (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
            (if r + 1 < tr.height then 1 else 0) l),
        ∀ t ∈ ch, t.2 ≠ 0 := by
      intro r hr ch hch t ht
      have hflat : t ∈ (chunkList c.lookupGroupSize _).flatten := List.mem_flatten.mpr ⟨ch, hch, ht⟩
      rw [chunkList_flatten] at hflat
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hflat
      exact hne r hr l hl
    rw [circuitLogUp_telescopes hlogup hneChunks]
    unfold circuitLedger
    rw [ledgerLogUpSum_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    rw [chunkList_flatten]
    exact row_ungroupedLogUpSum_eq_ledger embed β γ c tr r

/-- **Batch-wide Stage-2 Grouped LogUp → Trimmed Ledger Rational Identity:**
If every circuit in a lowered system satisfies `CircuitStage2Satisfied` and the
global accumulator deltas close against the public root claim and boundary
ledger, then the trimmed system ledger's rational sum vanishes identically. -/
theorem batch_stage2_logup_eq_trimmed_sum (embed : F →+* K) (β γ : K)
    (circuits : List (CompiledCircuit F)) (traces : List (CircuitTrace F))
    (acc : Nat → Nat → Nat → K) (accInitial accFinal : Nat → K)
    (rootTuple : List F) (boundaryLedger : Ledger F)
    (hlen : traces.length = circuits.length)
    (hsat : ∀ (i : Nat) (hi : i < circuits.length),
      CircuitStage2Satisfied embed β γ circuits[i] (traces[i]'(hlen ▸ hi))
        (acc i) (accInitial i) (accFinal i))
    (hclose :
      ((List.range circuits.length).map fun i => accFinal i - accInitial i).sum +
        (fingerprint β γ (rootTuple.map embed))⁻¹ +
        ledgerLogUpSum embed β γ boundaryLedger = 0) :
    ledgerLogUpSum embed β γ
      (Finsupp.mapDomain trimZeros
        ((List.zipWith circuitLedger circuits traces).sum +
          Finsupp.single rootTuple 1 + boundaryLedger)) = 0 := by
  rw [ledgerLogUpSum_mapDomain_trimZeros, ledgerLogUpSum_add, ledgerLogUpSum_add,
    ledgerLogUpSum_single, map_one, one_mul, ledgerLogUpSum_list_sum]
  have hzip :
      ((List.zipWith circuitLedger circuits traces).map (ledgerLogUpSum embed β γ)) =
      ((List.range circuits.length).map fun i => accFinal i - accInitial i) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi1 hi2
      have hi : i < circuits.length := by simpa using hi2
      simp only [List.getElem_map, List.getElem_zipWith, List.getElem_range]
      exact (circuitStage2_delta_eq_ledger embed β γ circuits[i] (traces[i]'(hlen ▸ hi))
        (acc i) (accInitial i) (accFinal i) (hsat i hi)).symm
  rw [hzip]
  exact hclose

/-- Horner RLC polynomial evaluation without the `β` shift: `∑ args[k] * γ^k`. -/
def rlcEval (γ : K) (args : List K) : K :=
  args.foldr (fun a acc => acc * γ + a) 0

theorem fingerprint_eq_add_rlc (β γ : K) (args : List K) :
    fingerprint β γ args = β + rlcEval γ args := by
  unfold fingerprint rlcEval
  ring

/-- Cleared-denominator LogUp polynomial in `β` over a finite support `S`. -/
noncomputable def logupClearedPoly {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) : _root_.Polynomial K :=
  ∑ m ∈ S, _root_.Polynomial.C (w m) *
    ∏ m' ∈ S.erase m, (_root_.Polynomial.X + _root_.Polynomial.C (fp m'))

theorem eval_logupClearedPoly_at_neg_fp {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) {m₀ : α} (hm₀ : m₀ ∈ S) :
    (logupClearedPoly S fp w).eval (-fp m₀) =
      w m₀ * ∏ m' ∈ S.erase m₀, (-fp m₀ + fp m') := by
  unfold logupClearedPoly
  rw [_root_.Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single m₀]
  · simp [_root_.Polynomial.eval_prod]
  · intro m _ hne
    simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_prod]
    have hm₀_in : m₀ ∈ S.erase m := Finset.mem_erase.mpr ⟨hne.symm, hm₀⟩
    have hprod0 : (∏ x ∈ S.erase m,
        (_root_.Polynomial.X + _root_.Polynomial.C (fp x)).eval (-fp m₀)) = 0 := by
      apply Finset.prod_eq_zero hm₀_in
      simp
    rw [hprod0, mul_zero]
  · intro hnot; exact absurd hm₀ hnot

theorem natDegree_logupClearedPoly_le {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) :
    (logupClearedPoly S fp w).natDegree ≤ S.card - 1 := by
  unfold logupClearedPoly
  refine (_root_.Polynomial.natDegree_sum_le S _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun m hm => ?_⟩
  refine (_root_.Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (_root_.Polynomial.natDegree_prod_le _ _).trans ?_
  have hsum : ∑ m' ∈ S.erase m, (_root_.Polynomial.X + _root_.Polynomial.C (fp m')).natDegree ≤
      (S.erase m).card := by
    calc ∑ m' ∈ S.erase m, (_root_.Polynomial.X + _root_.Polynomial.C (fp m')).natDegree
        ≤ ∑ _m' ∈ S.erase m, 1 := Finset.sum_le_sum
            (f := fun m' => (_root_.Polynomial.X + _root_.Polynomial.C (fp m')).natDegree)
            (g := fun _ => 1) fun m' _ => by rw [_root_.Polynomial.natDegree_X_add_C]
      _ = (S.erase m).card := by simp
  rwa [Finset.card_erase_of_mem hm] at hsum

theorem logupClearedPoly_ne_zero {α : Type*} [DecidableEq α] {S : Finset α}
    {fp : α → K} {w : α → K}
    {m₀ : α} (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0)
    (hsep : ∀ m' ∈ S, m' ≠ m₀ → fp m' ≠ fp m₀) :
    logupClearedPoly S fp w ≠ 0 := by
  intro h0
  have hev := congrArg (fun p : _root_.Polynomial K => p.eval (-fp m₀)) h0
  rw [_root_.Polynomial.eval_zero, eval_logupClearedPoly_at_neg_fp S fp w hm₀] at hev
  have hprod_ne : (∏ m' ∈ S.erase m₀, (-fp m₀ + fp m')) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m' hm'
    obtain ⟨hne, hm'S⟩ := Finset.mem_erase.mp hm'
    intro hsum
    have hfp : fp m' = fp m₀ := by
      have := eq_neg_of_add_eq_zero_left hsum
      simpa using this.symm
    exact hsep m' hm'S hne hfp
  exact mul_ne_zero hw hprod_ne hev

theorem eval_logupClearedPoly_eq_mul_sum {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) (β : K) (hden : ∀ m ∈ S, β + fp m ≠ 0) :
    (logupClearedPoly S fp w).eval β =
      (∏ m ∈ S, (β + fp m)) * (∑ m ∈ S, w m * (β + fp m)⁻¹) := by
  unfold logupClearedPoly
  rw [_root_.Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_prod,
    _root_.Polynomial.eval_add, _root_.Polynomial.eval_X]
  have hsplit : (∏ x ∈ S, (β + fp x)) = (β + fp m) * (∏ x ∈ S.erase m, (β + fp x)) :=
    (Finset.mul_prod_erase S (fun x => β + fp x) hm).symm
  rw [hsplit]
  have hd : β + fp m ≠ 0 := hden m hm
  field_simp [hd]

/-- **Generic LogUp Partial-Fraction Soundness (`trimmed_ledger_zero_of_logup_sum`):**
If a ledger `L : Ledger F` satisfies `ledgerLogUpSum embed β γ L = 0` with nonzero
denominators, and `β` is not a root of the cleared-denominator polynomial whenever
`logupClearedPoly ≠ 0` (and `γ` separates distinct tuples in `L.support`), then `L = 0`. -/
theorem trimmed_ledger_zero_of_logup_sum (embed : F →+* K) (β γ : K) (L : Ledger F)
    (hden : ∀ k ∈ L.support, fingerprint β γ (k.map embed) ≠ 0)
    (hsep : ∀ k ∈ L.support, ∀ k' ∈ L.support, k' ≠ k →
      rlcEval γ (k'.map embed) ≠ rlcEval γ (k.map embed))
    (hnonroot :
      let Q := logupClearedPoly L.support (fun k => rlcEval γ (k.map embed)) (fun k => embed (L k))
      Q ≠ 0 → Q.eval β ≠ 0)
    (hzero : ledgerLogUpSum embed β γ L = 0) : L = 0 := by
  by_contra hne
  have hsupp : L.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨k₀, hk₀⟩ := hsupp
  have hw0 : embed (L k₀) ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hk₀ (embed.injective (by simpa [map_zero] using hz))
  set Q := logupClearedPoly L.support (fun k => rlcEval γ (k.map embed)) (fun k => embed (L k))
  have hQne : Q ≠ 0 := logupClearedPoly_ne_zero hk₀ hw0 (fun k' hk' hneq => hsep k₀ hk₀ k' hk' hneq)
  have hden' : ∀ k ∈ L.support, β + rlcEval γ (k.map embed) ≠ 0 := fun k hk => by
    rw [← fingerprint_eq_add_rlc]
    exact hden k hk
  have heval : Q.eval β = 0 := by
    rw [eval_logupClearedPoly_eq_mul_sum L.support _ _ β hden']
    have hsum0 : (∑ k ∈ L.support, embed (L k) * (β + rlcEval γ (k.map embed))⁻¹) = 0 := by
      unfold ledgerLogUpSum Finsupp.sum at hzero
      simpa only [fingerprint_eq_add_rlc] using hzero
    rw [hsum0, mul_zero]
  exact hnonroot hQne heval

/-- **Finite-Field Schwartz-Zippel Bound for Stage-2 LogUp (`β` bad-challenge count):**
If `L ≠ 0` and `γ` separates some unbalanced entry `k₀ ∈ L.support` from all other
entries in `L.support`, then at most `L.support.card - 1` challenges `β ∈ K` can
make `ledgerLogUpSum embed β γ L = 0` with nonzero denominators. -/
theorem card_stage2_logup_bad_beta_le [Fintype K] [DecidableEq K] (embed : F →+* K) (γ : K)
    (L : Ledger F) {k₀ : List F} (hk₀ : k₀ ∈ L.support)
    (hsep : ∀ k' ∈ L.support, k' ≠ k₀ → rlcEval γ (k'.map embed) ≠ rlcEval γ (k₀.map embed)) :
    (Finset.univ.filter fun β : K =>
      (∀ k ∈ L.support, fingerprint β γ (k.map embed) ≠ 0) ∧
      ledgerLogUpSum embed β γ L = 0).card ≤ L.support.card - 1 := by
  have hw0 : embed (L k₀) ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hk₀ (embed.injective (by simpa [map_zero] using hz))
  set Q := logupClearedPoly L.support (fun k => rlcEval γ (k.map embed)) (fun k => embed (L k))
  have hQne : Q ≠ 0 := logupClearedPoly_ne_zero hk₀ hw0 hsep
  have hsub : (Finset.univ.filter fun β : K =>
      (∀ k ∈ L.support, fingerprint β γ (k.map embed) ≠ 0) ∧
      ledgerLogUpSum embed β γ L = 0) ⊆ Q.roots.toFinset := by
    intro β hβ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
    rw [Multiset.mem_toFinset, _root_.Polynomial.mem_roots hQne, _root_.Polynomial.IsRoot.def]
    have hden' : ∀ k ∈ L.support, β + rlcEval γ (k.map embed) ≠ 0 := fun k hk => by
      rw [← fingerprint_eq_add_rlc]
      exact hβ.1 k hk
    rw [eval_logupClearedPoly_eq_mul_sum L.support _ _ β hden']
    have hsum0 : (∑ k ∈ L.support, embed (L k) * (β + rlcEval γ (k.map embed))⁻¹) = 0 := by
      have h2 := hβ.2
      unfold ledgerLogUpSum Finsupp.sum at h2
      simpa only [fingerprint_eq_add_rlc] using h2
    rw [hsum0, mul_zero]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((_root_.Polynomial.card_roots' Q).trans
      (natDegree_logupClearedPoly_le L.support _ _)))

end Stage2LogUpBridge

/-! ## 3. Exact Lowering Correspondence (`lowerSingleChip`, `lowerGroupLayout`, `lowerFixedTables`) -/

section LoweringCorrespondence

variable {F : Type} [Field F] [DecidableEq F]

/-- `lowerSingleChip` constraints (after `compileCircuit` + `retune`) hold on row `r`
iff `Aiur.Tiling.Bridge.lower` holds on `tr.mainRow r`. -/
theorem lowerSingleChip_rowSatisfied_iff (callableId : String → Nat)
    (c : Chip F) (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    CircuitRowSatisfied
        (compileRetune logBlowup extDegree (lowerSingleChip callableId (Activation.compile c) c.numVars))
        tr r ↔
      (Aiur.Tiling.Bridge.lower callableId c).Holds (tr.mainRow r) := by
  rw [circuitRowSatisfied_retune_compile_iff]
  unfold lowerSingleChip Aiur.Tiling.Bridge.lower Tiling.Circuit.Holds Scalar.Circuit.Satisfies
  have hnumVars : (Activation.compile c).numVars = c.numVars + 1 := rfl
  constructor
  · intro h p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hmem : lowerPoly p ∈ (Activation.compile c).constraints.map lowerPoly ++
          [AirExpr.mul (.sub (.const (1 : F)) (.main c.numVars)) (.main (Activation.compile c).numVars)] :=
        List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
      simpa only [evalExpr_lowerPoly] using h _ hmem
    · simp only [List.mem_singleton] at hp
      subst hp
      have hmem : AirExpr.mul (.sub (.const (1 : F)) (.main c.numVars))
          (.main (Activation.compile c).numVars) ∈
          (Activation.compile c).constraints.map lowerPoly ++
            [AirExpr.mul (.sub (.const (1 : F)) (.main c.numVars))
              (.main (Activation.compile c).numVars)] :=
        List.mem_append_right _ (List.mem_singleton_self _)
      simpa only [CircuitTrace.evalExpr, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, hnumVars]
        using h _ hmem
  · intro h e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      rw [evalExpr_lowerPoly]
      exact h p (List.mem_append_left _ hp)
    · simp only [List.mem_singleton] at he
      subst he
      have hpad := h (.mul (.sub (.const 1) (.var c.numVars)) (.var (c.numVars + 1)))
        (List.mem_append_right _ (List.mem_singleton_self _))
      simpa only [CircuitTrace.evalExpr, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, hnumVars]
        using hpad

/-- `lowerSingleChip` row ledger (after `compileCircuit` + `retune`) equals
`Aiur.Tiling.Bridge.lower`'s `rowLedger`. -/
theorem lowerSingleChip_rowLedger_eq (callableId : String → Nat)
    (c : Chip F) (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    circuitRowLedger
        (compileRetune logBlowup extDegree (lowerSingleChip callableId (Activation.compile c) c.numVars))
        tr r =
      (Aiur.Tiling.Bridge.lower callableId c).rowLedger (tr.mainRow r) := by
  rw [circuitRowLedger_retune_compile_eq]
  unfold lowerSingleChip Aiur.Tiling.Bridge.lower Tiling.Circuit.rowLedger
  have hnumVars : (Activation.compile c).numVars = c.numVars + 1 := rfl
  simp only [List.cons_append, List.map_cons, List.sum_cons, List.map_append, List.sum_append]
  congr 1
  · -- receive lookup
    simp only [airLookupLedger, AirLookup.pull, Tiling.Lookup.entry, Tiling.Lookup.tuple,
      Aiur.Tiling.Bridge.receiveLookup, CircuitTrace.evalExpr, AirExpr.eval,
      Scalar.Circuit.ArithExpr.denote, hnumVars, zero_sub]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_map,
      callTag, Aiur.Tiling.Bridge.CALL, List.nil_append]
    congr 2
    congr 1
    apply List.map_congr_left
    intro p _
    exact eval_lowerPoly _ _ _ _ _ _ p
  · congr 1
    · -- send lookups
      rw [List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro s _
      simp only [Function.comp_apply, airLookupLedger, AirLookup.push, Tiling.Lookup.entry,
        Tiling.Lookup.tuple, Aiur.Tiling.Bridge.sendLookup, evalExpr_lowerPoly]
      congr 1
      simp only [List.map_append, List.map_cons, List.map_map,
        CircuitTrace.evalExpr, AirExpr.eval, Scalar.Circuit.ArithExpr.denote,
        callTag, Aiur.Tiling.Bridge.CALL, List.nil_append]
      congr 2
      congr 1
      apply List.map_congr_left
      intro p _
      exact eval_lowerPoly _ _ _ _ _ _ p
    · -- ROM lookups
      rw [List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro m _
      simp only [Function.comp_apply, lowerRomAccess, airLookupLedger, AirLookup.push,
        Tiling.Lookup.entry, Tiling.Lookup.tuple, Aiur.Tiling.Bridge.memoryLookup,
        evalExpr_lowerPoly]
      congr 1
      simp only [List.map_cons, List.map_map,
        CircuitTrace.evalExpr, AirExpr.eval, Scalar.Circuit.ArithExpr.denote,
        romTag, Aiur.Tiling.Bridge.ROM, eval_lowerPoly, List.cons_append, List.nil_append]
      congr 3
      apply List.map_congr_left
      intro p _
      exact eval_lowerPoly _ _ _ _ _ _ p

/-- `lowerGroupLayout` constraints (after `compileCircuit` + `retune`) hold on row `r`
iff `Aiur.Tiling.Grouped.lowerGroup` holds on `tr.mainRow r`. -/
theorem lowerGroupLayout_rowSatisfied_iff (g : Grouping.Layout F)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    CircuitRowSatisfied (compileRetune logBlowup extDegree (lowerGroupLayout g)) tr r ↔
      (lowerGroup g).Holds (tr.mainRow r) := by
  rw [circuitRowSatisfied_retune_compile_iff]
  unfold lowerGroupLayout lowerGroup Tiling.Circuit.Holds Scalar.Circuit.Satisfies
  constructor
  · intro h p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hmem : lowerPoly p ∈ g.constraints.map lowerPoly ++
          [AirExpr.mul (.sub (.const (1 : F)) (lowerPoly g.activation)) (.main g.width)] :=
        List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
      simpa only [evalExpr_lowerPoly] using h _ hmem
    · simp only [List.mem_singleton] at hp
      subst hp
      have hmem : AirExpr.mul (.sub (.const (1 : F)) (lowerPoly g.activation)) (.main g.width) ∈
          g.constraints.map lowerPoly ++
            [AirExpr.mul (.sub (.const (1 : F)) (lowerPoly g.activation)) (.main g.width)] :=
        List.mem_append_right _ (List.mem_singleton_self _)
      simpa only [CircuitTrace.evalExpr, AirExpr.eval, eval_lowerPoly,
        Scalar.Circuit.ArithExpr.denote] using h _ hmem
  · intro h e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      rw [evalExpr_lowerPoly]
      exact h p (List.mem_append_left _ hp)
    · simp only [List.mem_singleton] at he
      subst he
      have hpad := h (.mul (.sub (.const 1) g.activation) (.var g.width))
        (List.mem_append_right _ (List.mem_singleton_self _))
      simpa only [CircuitTrace.evalExpr, AirExpr.eval, eval_lowerPoly,
        Scalar.Circuit.ArithExpr.denote] using hpad

/-- `lowerGroupLayout` row ledger (after `compileCircuit` + `retune`) equals
`Aiur.Tiling.Grouped.lowerGroup`'s `rowLedger`. -/
theorem lowerGroupLayout_rowLedger_eq (g : Grouping.Layout F)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat) :
    circuitRowLedger (compileRetune logBlowup extDegree (lowerGroupLayout g)) tr r =
      (lowerGroup g).rowLedger (tr.mainRow r) := by
  rw [circuitRowLedger_retune_compile_eq]
  unfold lowerGroupLayout lowerGroup Tiling.Circuit.rowLedger
  simp only [List.map_cons, List.sum_cons]
  congr 1
  · simp only [airLookupLedger, AirLookup.pull, Tiling.Lookup.entry, Tiling.Lookup.tuple,
      CircuitTrace.evalExpr, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, zero_sub]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact eval_lowerPoly _ _ _ _ _ _ p
  · rw [List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, airLookupLedger, AirLookup.push, Tiling.Lookup.entry,
      Tiling.Lookup.tuple, evalExpr_lowerPoly]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact eval_lowerPoly _ _ _ _ _ _ p

/-- Every function circuit emitted by `lowerPlanFunctionsOrdered` is either an
activated single chip `c ∈ plan.singles` or a packed group `p ∈ plan.groups`. -/
theorem mem_lowerPlanFunctionsOrdered {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    {inp : CircuitInput F} (hmem : inp ∈ lowerPlanFunctionsOrdered callableId plan) :
    (∃ c ∈ plan.singles, inp = lowerSingleChip callableId (Activation.compile c) c.numVars) ∨
    (∃ p ∈ plan.groups, inp = lowerGroupLayout p.checked.layout) := by
  unfold lowerPlanFunctionsOrdered at hmem
  let P : CircuitInput F → Prop := fun x =>
    (∃ c ∈ plan.singles, x = lowerSingleChip callableId (Activation.compile c) c.numVars) ∨
    (∃ p ∈ plan.groups, x = lowerGroupLayout p.checked.layout)
  suffices ∀ (chips : List (Chip F)) (acc : List String × List (CircuitInput F)),
      (∀ c ∈ chips, c ∈ source.chips) →
      (∀ x ∈ acc.2, P x) →
      ∀ x ∈ (chips.foldl (fun (acc : List String × List (CircuitInput F)) (chip : Chip F) =>
        let (emittedGroups, out) := acc
        match plan.groups.find? fun p => p.checked.layout.members.any (·.name == chip.name) with
        | some p =>
            let gname := p.checked.layout.name
            if emittedGroups.contains gname then (emittedGroups, out)
            else (gname :: emittedGroups, out ++ [lowerGroupLayout p.checked.layout])
        | none =>
            (emittedGroups, out ++ [lowerSingleChip callableId (Activation.compile chip) chip.numVars]))
        acc).2, P x from
    this source.chips ([], []) (fun _ h => h) (fun _ h => by cases h) inp hmem
  intro chips
  induction chips with
  | nil => intro acc _ hacc; exact hacc
  | cons chip rest ih =>
      intro acc hchips hacc
      simp only [List.foldl_cons]
      apply ih _ (fun c hc => hchips c (List.mem_cons_of_mem _ hc))
      intro x hx
      cases hfind : plan.groups.find? fun p => p.checked.layout.members.any (·.name == chip.name) with
      | some p =>
          simp only [hfind] at hx
          have hp : p ∈ plan.groups := List.mem_of_find?_eq_some hfind
          split_ifs at hx
          · exact hacc x hx
          · rcases List.mem_append.mp hx with hx' | hx'
            · exact hacc x hx'
            · simp only [List.mem_singleton] at hx'
              exact Or.inr ⟨p, hp, hx'⟩
      | none =>
          simp only [hfind] at hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hacc x hx'
          · simp only [List.mem_singleton] at hx'
            have hchipSrc : chip ∈ source.chips := hchips chip List.mem_cons_self
            have hnotGrp : ¬∃ p ∈ plan.groups, chip ∈ p.sources := by
              rintro ⟨p, hp, hmemP⟩
              rw [← p.checked.certificate.sources_eq] at hmemP
              obtain ⟨m, hm, hmEq⟩ := List.mem_map.mp hmemP
              have hname : m.name = chip.name := by
                rw [p.checked.certificate.names m hm, hmEq]
              have hany : p.checked.layout.members.any (·.name == chip.name) = true :=
                List.any_eq_true.mpr ⟨m, hm, beq_iff_eq.mpr hname⟩
              have hnone := List.find?_eq_none.mp hfind p hp
              exact hnone hany
            have hsingle : chip ∈ plan.singles :=
              (plan.certificate.2.2 chip hchipSrc).resolve_right hnotGrp
            exact Or.inl ⟨chip, hsingle, hx'⟩

/-- Empty fixed tables (`preprocessed.height = 0`) constrain every multiplicity column
to `0`, so their row ledger vanishes identically under AIR satisfaction. -/
theorem lowerFixedTables_empty_ledger_zero (maps : List FixedMapMeta) (logBlowup extDegree : Nat)
    {inp : CircuitInput F} (hinp : inp ∈ lowerFixedTables (F := F) maps logBlowup)
    (hempty : inp.preprocessed.height = 0)
    (tr : CircuitTrace F)
    (hsat : CircuitAirSatisfied (compileRetune logBlowup extDegree inp) tr) :
    circuitLedger (compileRetune logBlowup extDegree inp) tr = 0 := by
  unfold lowerFixedTables at hinp
  obtain ⟨⟨inputName, realHeight, groupMaps⟩, _, rfl⟩ := List.mem_map.mp hinp
  dsimp only at hempty ⊢
  have hzeroH : nextPow2 realHeight = 0 := by
    by_cases hz : nextPow2 realHeight = 0
    · exact hz
    · have hne : (nextPow2 realHeight == 0) = false := beq_false_of_ne hz
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hempty
      exact hempty
  have hbeq : (nextPow2 realHeight == 0) = true := beq_iff_eq.mpr hzeroH
  -- Show every lookup in the fold has its multiplicity column constrained to 0.
  let step : (Nat × List (Nat × Nat × Nat) × List (AirLookup F) × List (AirExpr F)) →
      (FixedMapMeta × Nat) →
      (Nat × List (Nat × Nat × Nat) × List (AirLookup F) × List (AirExpr F)) :=
    fun (width, cols, lookups, constraints) (m, colIdx) =>
      let (width1, cols1, inOff) :=
        match cols.find? (fun (tid, _, _) => tid == m.inputTableId) with
        | some (_, start, _) => (width, cols, start)
        | none => (width + m.inputWidth, cols ++ [(m.inputTableId, width, m.inputWidth)], width)
      let (width2, cols2, outOff) :=
        match cols1.find? (fun (tid, _, _) => tid == m.outputTableId) with
        | some (_, start, _) => (width1, cols1, start)
        | none => (width1 + m.outputWidth, cols1 ++ [(m.outputTableId, width1, m.outputWidth)], width1)
      let prefixArgs : List (AirExpr F) :=
        [.const (callTag : F), .const (m.callableId : F)]
      let (args, constraints') :=
        if (nextPow2 realHeight == 0) = true then
          (prefixArgs ++ List.replicate (m.inputWidth + m.outputWidth) (.const (0 : F)),
            constraints ++ [.main colIdx])
        else
          let inArgs := (List.range m.inputWidth).map fun k => AirExpr.preprocessed (inOff + k)
          let outArgs := (List.range m.outputWidth).map fun k => AirExpr.preprocessed (outOff + k)
          (prefixArgs ++ inArgs ++ outArgs, constraints)
      (width2, cols2, lookups ++ [AirLookup.pull (.main colIdx) args], constraints')
  have hinv : ∀ (xs : List (FixedMapMeta × Nat))
      (acc : Nat × List (Nat × Nat × Nat) × List (AirLookup F) × List (AirExpr F)),
      (∀ l ∈ acc.2.2.1, ∃ col, l.multiplicity = .neg (.main col) ∧ AirExpr.main col ∈ acc.2.2.2) →
      ∀ l ∈ (xs.foldl step acc).2.2.1,
        ∃ col, l.multiplicity = .neg (.main col) ∧ AirExpr.main col ∈ (xs.foldl step acc).2.2.2 := by
    intro xs
    induction xs with
    | nil => intro acc hacc; exact hacc
    | cons x rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        rcases acc with ⟨w, cols, ls, cs⟩
        rcases x with ⟨m, colIdx⟩
        intro l hl
        simp only [step, hbeq, ↓reduceIte] at hl ⊢
        rcases List.mem_append.mp hl with hl' | hl'
        · obtain ⟨col, hmul, hmemC⟩ := hacc l hl'
          exact ⟨col, hmul, List.mem_append_left _ hmemC⟩
        · simp only [List.mem_singleton] at hl'
          subst hl'
          exact ⟨colIdx, rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩
  have hlookups := hinv groupMaps.zipIdx (1, [], [], []) (fun _ h => by cases h)
  rw [circuitLedger_retune_compile_eq]
  apply List.sum_eq_zero
  intro L hL
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hL
  have hrLt : r < tr.height := List.mem_range.mp hr
  have hrowSat := (circuitRowSatisfied_retune_compile_iff _ logBlowup extDegree tr r).mp (hsat r hrLt)
  apply List.sum_eq_zero
  intro L' hL'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hL'
  obtain ⟨col, hmul, hmemC⟩ := hlookups l hl
  have hcol0 : tr.mainRow r col = 0 := by
    simpa [CircuitTrace.evalExpr, AirExpr.eval] using hrowSat (.main col) hmemC
  simp [airLookupLedger, hmul, CircuitTrace.evalExpr, AirExpr.eval, hcol0]

/-- Trusted preprocessed fixed-table validity: for every non-empty lowered fixed-table
circuit (`preprocessed.height > 0`), every lookup tuple evaluated on the verifier's
preprocessed rows lies in `source.mapClaims.map (encode callableId)`. -/
def FixedTablesValid (source : Circuit.System F) (callableId : String → Nat)
    (tblInputs : List (CircuitInput F)) (tblTraces : List (CircuitTrace F)) : Prop :=
  List.Forall₂ (fun inp tr =>
    0 < inp.preprocessed.height →
      ∀ r < tr.height, ∀ l ∈ inp.lookups,
        l.args.map (tr.evalExpr r) ∈ source.mapClaims.map (encode callableId))
    tblInputs tblTraces

/-- Every nonzero entry of the combined fixed-table ledger lies in the system's
encoded map claims (`source.mapClaims.map (encode callableId)`). -/
theorem fixedTables_ledger_support {source : Circuit.System F} (callableId : String → Nat)
    (fixedMaps : List FixedMapMeta) (logBlowup extDegree : Nat)
    (tblTraces : List (CircuitTrace F))
    (hsat : List.Forall₂ CircuitAirSatisfied
      ((lowerFixedTables (F := F) fixedMaps logBlowup).map (compileRetune logBlowup extDegree))
      tblTraces)
    (hvalid : FixedTablesValid source callableId
      (lowerFixedTables (F := F) fixedMaps logBlowup) tblTraces) :
    ∀ t, (List.zipWith circuitLedger
      ((lowerFixedTables (F := F) fixedMaps logBlowup).map (compileRetune logBlowup extDegree))
      tblTraces).sum t ≠ 0 →
      t ∈ source.mapClaims.map (encode callableId) := by
  have hstep : ∀ (inps : List (CircuitInput F)) (trs : List (CircuitTrace F)),
      (∀ inp ∈ inps, inp ∈ lowerFixedTables (F := F) fixedMaps logBlowup) →
      List.Forall₂ CircuitAirSatisfied (inps.map (compileRetune logBlowup extDegree)) trs →
      FixedTablesValid source callableId inps trs →
      ∀ t, (List.zipWith circuitLedger (inps.map (compileRetune logBlowup extDegree)) trs).sum t ≠ 0 →
        t ∈ source.mapClaims.map (encode callableId) := by
    intro inps trs hinps hsat' hval'
    induction inps generalizing trs with
    | nil =>
        cases trs with
        | nil => intro t ht; simp at ht
        | cons _ _ => cases hsat'
    | cons inp rest ih =>
        cases trs with
        | nil => cases hsat'
        | cons tr trs' =>
            simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, Finsupp.add_apply]
            have ⟨hsatH, hsatT⟩ := List.forall₂_cons.mp hsat'
            have ⟨hvalH, hvalT⟩ := List.forall₂_cons.mp hval'
            intro t ht
            by_cases hhead : circuitLedger (compileRetune logBlowup extDegree inp) tr t = 0
            · rw [hhead, zero_add] at ht
              exact ih trs' (fun x hx => hinps x (List.mem_cons_of_mem _ hx)) hsatT hvalT t ht
            · by_cases hempty : inp.preprocessed.height = 0
              · have hz := lowerFixedTables_empty_ledger_zero fixedMaps logBlowup extDegree
                  (hinps inp List.mem_cons_self) hempty tr hsatH
                rw [hz] at hhead
                exact absurd rfl hhead
              · have hpos : 0 < inp.preprocessed.height := Nat.pos_of_ne_zero hempty
                rw [circuitLedger_retune_compile_eq] at hhead
                simp only [Tiling.System.ledger_list_sum, List.map_map] at hhead
                obtain ⟨v, hv, hne⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum hhead
                obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
                simp only [Function.comp_apply, Tiling.System.ledger_list_sum, List.map_map] at hne
                obtain ⟨v', hv', hne'⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum hne
                obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv'
                simp only [Function.comp_apply, airLookupLedger, Finsupp.single_apply] at hne'
                split at hne'
                · rename_i heq
                  subst heq
                  exact hvalH hpos r (List.mem_range.mp hr) l hl
                · exact absurd rfl hne'
  exact hstep _ tblTraces (fun _ h => h) hsat hvalid

end LoweringCorrespondence

/-! ## 4. Enable Booleanity & Unit-Weight Pulls (`checkEnables_implies_unit_weight`) -/

section EnableBooleanity

variable {F : Type} [Field F] [DecidableEq F]

/-- Every non-receive lookup of a lowered single chip has `{0, 1}`-valued multiplicity
under `checkChipEnables`, and every padding row is completely silent. -/
theorem checkChipEnables_single_unit_weight (callableId : String → Nat)
    (c : Chip F) (hok : checkChipEnables c = true)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat)
    (hsat : CircuitRowSatisfied
      (compileRetune logBlowup extDegree (lowerSingleChip callableId (Activation.compile c) c.numVars))
      tr r) :
    let w := tr.mainRow r
    let cc := compileRetune logBlowup extDegree (lowerSingleChip callableId (Activation.compile c) c.numVars)
    (w c.numVars = 0 ∨ w c.numVars = 1) ∧
    (w c.numVars = 0 → w (c.numVars + 1) = 0 ∧ circuitRowLedger cc tr r = 0) ∧
    (∀ s ∈ (Activation.compile c).sends, s.enable.denote w = 0 ∨ s.enable.denote w = 1) ∧
    (∀ m ∈ (Activation.compile c).memory, m.enable.denote w = 0 ∨ m.enable.denote w = 1) ∧
    (∀ l ∈ cc.lookups,
      l.multiplicity = .neg (.main (c.numVars + 1)) ∨
        tr.evalExpr r l.multiplicity = 0 ∨ tr.evalExpr r l.multiplicity = 1) := by
  have hholds := (lowerSingleChip_rowSatisfied_iff callableId c logBlowup extDegree tr r).mp hsat
  have hactSat : Scalar.Circuit.Satisfies (Activation.compile c).constraints (tr.mainRow r) :=
    fun p hp => hholds p (List.mem_append_left _ hp)
  have hpad : (1 - tr.mainRow r c.numVars) * tr.mainRow r (c.numVars + 1) = 0 := by
    simpa [Scalar.Circuit.ArithExpr.denote] using
      hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hsel : tr.mainRow r c.numVars = 0 ∨ tr.mainRow r c.numVars = 1 := by
    have h := hactSat (Activation.boolean c.numVars) (by simp [Activation.compile])
    simpa [Activation.boolean, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] using h
  have hbool : Boolean c (tr.mainRow r) := boolean_of_checkChipEnables hok hactSat
  have hperm : (compileRetune logBlowup extDegree
      (lowerSingleChip callableId (Activation.compile c) c.numVars)).lookups.Perm
      (lowerSingleChip callableId (Activation.compile c) c.numVars).lookups := by
    unfold compileRetune
    simpa [compileCircuit] using (retune_lookups_perm
      (compileCircuit (lowerSingleChip callableId (Activation.compile c) c.numVars) extDegree)
      (2 ^ logBlowup) extDegree).1
  refine ⟨hsel, ?_, hbool.1, hbool.2, ?_⟩
  · intro hoff
    have hmult0 : tr.mainRow r (c.numVars + 1) = 0 := by
      rw [hoff, sub_zero, one_mul] at hpad
      exact hpad
    refine ⟨hmult0, ?_⟩
    rw [lowerSingleChip_rowLedger_eq, Aiur.Tiling.Grouped.lower_instLedger]
    simp only [instLedger, hmult0, neg_zero, Finsupp.single_zero, zero_add]
    have hs0 : ((Activation.compile c).sends.map fun s =>
        Finsupp.single (encode callableId (s.message (tr.mainRow r)))
          (s.enable.denote (tr.mainRow r))).sum = 0 := by
      apply List.sum_eq_zero
      intro L hL
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hL
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      have hguard : (Activation.send c.numVars s0).enable ∈ Activation.guards c :=
        List.mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩))
      have hsil := hactSat (Activation.silent c.numVars (Activation.send c.numVars s0).enable)
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hguard, rfl⟩)))
      simp only [Activation.silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote,
        hoff, sub_zero, one_mul] at hsil
      simp [hsil]
    have hm0 : ((Activation.compile c).memory.map fun m =>
        Finsupp.single (encodeRom (m.address.denote (tr.mainRow r),
          m.value.map (Circuit.ArithExpr.denote (tr.mainRow r))))
          (m.enable.denote (tr.mainRow r))).sum = 0 := by
      apply List.sum_eq_zero
      intro L hL
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hL
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      have hguard : (Activation.memory c.numVars m0).enable ∈ Activation.guards c :=
        List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨m0, hm0, rfl⟩))
      have hsil := hactSat (Activation.silent c.numVars (Activation.memory c.numVars m0).enable)
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hguard, rfl⟩)))
      simp only [Activation.silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote,
        hoff, sub_zero, one_mul] at hsil
      simp [hsil]
    rw [hs0, hm0, add_zero]
  · intro l hl
    have hl' := hperm.subset hl
    unfold lowerSingleChip at hl'
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hl'
    rcases hl' with rfl | ⟨s, hs, rfl⟩ | ⟨m, hm, rfl⟩
    · exact Or.inl rfl
    · right
      simpa [AirLookup.push, evalExpr_lowerPoly] using hbool.1 s hs
    · right
      simpa [lowerRomAccess, AirLookup.push, evalExpr_lowerPoly] using hbool.2 m hm

/-- Every non-receive lookup (shared send slot) of a lowered grouped layout has
`{0, 1}`-valued multiplicity under `checkChipEnables` on the group's members, and
every padding row is completely silent. -/
theorem checkChipEnables_group_unit_weight {id : String → Except String Nat}
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (p : Grouping.Packed F id) (hok : ∀ c ∈ p.sources, checkChipEnables c = true)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F) (r : Nat)
    (hsat : CircuitRowSatisfied
      (compileRetune logBlowup extDegree (lowerGroupLayout p.checked.layout)) tr r) :
    let g := p.checked.layout
    let w := tr.mainRow r
    let cc := compileRetune logBlowup extDegree (lowerGroupLayout g)
    (g.activation.denote w = 0 ∨ g.activation.denote w = 1) ∧
    (g.activation.denote w = 0 → w g.width = 0 ∧ circuitRowLedger cc tr r = 0) ∧
    (∀ s ∈ g.sends, s.enable.denote w = 0 ∨ s.enable.denote w = 1) ∧
    (∀ l ∈ cc.lookups,
      l.multiplicity = .neg (.main g.width) ∨
        tr.evalExpr r l.multiplicity = 0 ∨ tr.evalExpr r l.multiplicity = 1) := by
  set g := p.checked.layout
  set w := tr.mainRow r
  have hholds := (lowerGroupLayout_rowSatisfied_iff g logBlowup extDegree tr r).mp hsat
  have hvalid : Scalar.Circuit.Satisfies g.constraints w :=
    fun q hq => hholds q (List.mem_append_left _ hq)
  have hpad : (1 - g.activation.denote w) * w g.width = 0 := by
    simpa [Scalar.Circuit.ArithExpr.denote] using
      hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hactBool : g.activation.denote w = 0 ∨ g.activation.denote w = 1 := by
    have h := Grouping.exclusive_sum (g.exclusive p.checked.certificate.shapes w hvalid)
    simpa [Grouping.Layout.activation, Grouping.sum_denote, Function.comp_def,
      Scalar.Circuit.ArithExpr.denote] using h
  have hslotBool : ∀ s ∈ g.sends, s.enable.denote w = 0 ∨ s.enable.denote w = 1 := by
    intro s hs
    obtain ⟨si, hsi, rfl⟩ := List.getElem_of_mem hs
    have hslotEq : g.slot si = g.sends[si] := by simp [Grouping.Layout.slot, hsi]
    rw [← hslotEq]
    rcases hactBool with hoff | hon
    · left
      have hp := (p.checked.padding_sound w hvalid hoff).2.2 si
      simp only [Grouping.bucketOf] at hp
      exact hp.1
    · obtain ⟨m, hm, hsel, _⟩ := g.select p.checked.certificate.shapes w hvalid hon
      obtain ⟨_, provided, required, hmsgs, hsame⟩ :=
        Aiur.Tiling.Grouped.packet_active p.checked m hm w hvalid hon hsel
      have hmsat := Aiur.Tiling.Grouped.member_sat p.checked hm hvalid hsel
      have hmIn : m.origin ∈ p.sources := Aiur.Tiling.Grouped.origin_mem p.checked hm
      have hboolM : Boolean m.origin (project m w) :=
        boolean_of_checkChipEnables (hok m.origin hmIn) hmsat
      have hselProj : project m w m.origin.numVars = 1 := by
        rw [Aiur.Tiling.Grouped.project_selector p.checked hm]; exact hsel
      obtain ⟨_, hreqs⟩ := Aiur.Tiling.Grouped.messages_ok callableId idOk hmsgs
      have hreqBool : ∀ k : Nat,
          (Grouping.lookupAt required k).enable.denote (project m w) = 0 ∨
          (Grouping.lookupAt required k).enable.denote (project m w) = 1 := by
        intro k
        unfold Grouping.lookupAt
        cases hget : required[k]? with
        | none => left; rfl
        | some lk =>
            simp only [Option.getD_some]
            have hlkMem : lk ∈ required := List.mem_of_getElem? hget
            have hpair : (lk.enable, lk.args) ∈ required.map fun l => (l.enable, l.args) :=
              List.mem_map.mpr ⟨lk, hlkMem, rfl⟩
            rw [hreqs] at hpair
            rcases List.mem_append.mp hpair with hsMem | hmMem
            · obtain ⟨send0, hsend0, hEq⟩ := List.mem_map.mp hsMem
              have hEqEn : lk.enable = send0.enable := (Prod.mk.inj hEq).1.symm
              rw [hEqEn]
              have := hboolM.1 (Activation.send m.origin.numVars send0)
                (List.mem_map.mpr ⟨send0, hsend0, rfl⟩)
              simpa [Activation.send, Activation.polynomial_active _ _ _ hselProj] using this
            · obtain ⟨mem0, hmem0, hEq⟩ := List.mem_map.mp hmMem
              have hEqEn : lk.enable = mem0.enable := (Prod.mk.inj hEq).1.symm
              rw [hEqEn]
              have := hboolM.2 (Activation.memory m.origin.numVars mem0)
                (List.mem_map.mpr ⟨mem0, hmem0, rfl⟩)
              simpa [Activation.memory, Activation.polynomial_active _ _ _ hselProj] using this
      have hsl := hsame.2.2 si
      dsimp only at hsl
      cases hB : Grouping.bucketOf m.slotMap required.length si with
      | nil =>
          rw [hB] at hsl
          exact Or.inl hsl.1
      | cons k1 rest =>
          cases rest with
          | nil =>
              rw [hB] at hsl
              rw [hsl.1]
              exact hreqBool k1
          | cons k2 tail =>
              rw [hB] at hsl
              rcases hsl with ⟨h0, _, _⟩ | ⟨_, _, _, _, h1, _⟩
              · exact Or.inl h0
              · exact Or.inr h1
  have hperm : (compileRetune logBlowup extDegree (lowerGroupLayout g)).lookups.Perm
      (lowerGroupLayout g).lookups := by
    unfold compileRetune
    simpa [compileCircuit] using (retune_lookups_perm
      (compileCircuit (lowerGroupLayout g) extDegree) (2 ^ logBlowup) extDegree).1
  refine ⟨hactBool, ?_, hslotBool, ?_⟩
  · intro hoff
    have hmult0 : w g.width = 0 := by
      rw [hoff, sub_zero, one_mul] at hpad
      exact hpad
    refine ⟨hmult0, ?_⟩
    rw [lowerGroupLayout_rowLedger_eq, Aiur.Tiling.Grouped.lowerGroup_rowLedger]
    apply Aiur.Tiling.Grouped.pairsLedger_zero
    intro i
    cases i with
    | zero =>
        simp only [Aiur.Tiling.Grouped.groupPairs, List.getD_cons_zero]
        show -(w g.width) = 0
        rw [hmult0, neg_zero]
    | succ i =>
        simp only [Aiur.Tiling.Grouped.groupPairs, List.getD_cons_succ]
        rw [Aiur.Tiling.Grouped.getD_map_default _ _ ⟨.const 0, []⟩ i
          (by simp [Scalar.Circuit.ArithExpr.denote])]
        have hp := (p.checked.padding_sound w hvalid hoff).2.2 i
        simp only [Grouping.bucketOf] at hp
        simpa [Grouping.Layout.slot, Scalar.Circuit.ArithExpr.denote] using hp.1
  · intro l hl
    have hl' := hperm.subset hl
    unfold lowerGroupLayout at hl'
    simp only [List.mem_cons, List.mem_map] at hl'
    rcases hl' with rfl | ⟨s, hs, rfl⟩
    · exact Or.inl rfl
    · right
      simpa [AirLookup.push, evalExpr_lowerPoly] using hslotBool s hs

/-- **Headline Enable Booleanity & Unit-Weight Pulls Theorem (`checkEnables_implies_unit_weight`):**
Under `checkChipEnables` on all chips of `plan`, for every function circuit emitted
by `lowerFullSystem` (`lowerPlanFunctionsOrdered`) and every trace row satisfying
its compiled and retuned AIR constraints:
1. Every lookup in the retuned circuit is either the circuit's unique receive pull
   (negated multiplicity column at `cc.mainWidth - 1`) or a unit-weight `{0, 1}` push;
2. Whenever the row's activation selector vanishes (padding row), the receive
   multiplicity is `0` and the entire row LogUp ledger is identically `0`. -/
theorem checkEnables_implies_unit_weight {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (plan : Grouping.Plan source id)
    (henables : ∀ c ∈ allChips plan, checkChipEnables c = true)
    (logBlowup extDegree : Nat)
    {inp : CircuitInput F} (hinp : inp ∈ lowerPlanFunctionsOrdered callableId plan)
    (tr : CircuitTrace F) (r : Nat)
    (hsat : CircuitRowSatisfied (compileRetune logBlowup extDegree inp) tr r) :
    let cc := compileRetune logBlowup extDegree inp
    (∀ l ∈ cc.lookups,
      l.multiplicity = .neg (.main (cc.mainWidth - 1)) ∨
        tr.evalExpr r l.multiplicity = 0 ∨ tr.evalExpr r l.multiplicity = 1) ∧
    ((∃ c ∈ plan.singles, inp = lowerSingleChip callableId (Activation.compile c) c.numVars ∧
        (tr.mainRow r c.numVars = 0 ∨ tr.mainRow r c.numVars = 1) ∧
        (tr.mainRow r c.numVars = 0 →
          tr.mainRow r (c.numVars + 1) = 0 ∧ circuitRowLedger cc tr r = 0)) ∨
     (∃ p ∈ plan.groups, inp = lowerGroupLayout p.checked.layout ∧
        (p.checked.layout.activation.denote (tr.mainRow r) = 0 ∨
          p.checked.layout.activation.denote (tr.mainRow r) = 1) ∧
        (p.checked.layout.activation.denote (tr.mainRow r) = 0 →
          tr.mainRow r p.checked.layout.width = 0 ∧ circuitRowLedger cc tr r = 0))) := by
  rcases mem_lowerPlanFunctionsOrdered callableId plan hinp with ⟨c, hc, rfl⟩ | ⟨p, hp, rfl⟩
  · have hok : checkChipEnables c = true := henables c (List.mem_append_left _ hc)
    obtain ⟨hsel, hpad, _, _, hlook⟩ :=
      checkChipEnables_single_unit_weight callableId c hok logBlowup extDegree tr r hsat
    have hwidth : (compileRetune logBlowup extDegree
        (lowerSingleChip callableId (Activation.compile c) c.numVars)).mainWidth = c.numVars + 2 := by
      unfold compileRetune
      rw [(retune_lookups_perm _ _ _).2.1]
      rfl
    refine ⟨?_, Or.inl ⟨c, hc, rfl, hsel, hpad⟩⟩
    intro l hl
    simpa [hwidth] using hlook l hl
  · have hok : ∀ c ∈ p.sources, checkChipEnables c = true := fun c hc =>
      henables c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))
    obtain ⟨hact, hpad, _, hlook⟩ :=
      checkChipEnables_group_unit_weight callableId idOk p hok logBlowup extDegree tr r hsat
    have hwidth : (compileRetune logBlowup extDegree
        (lowerGroupLayout p.checked.layout)).mainWidth = p.checked.layout.width + 1 := by
      unfold compileRetune
      rw [(retune_lookups_perm _ _ _).2.1]
      rfl
    refine ⟨?_, Or.inr ⟨p, hp, rfl, hact, hpad⟩⟩
    intro l hl
    simpa [hwidth] using hlook l hl

end EnableBooleanity

/-! ## 5. Scalar & Vectorized ROM Extraction, Support, and `WidthROM.Valid` -/

section RomSoundness

variable {F : Type} [Field F] [DecidableEq F]

/-- Lane count per physical row for a given `RomLayout` and payload width `w`. -/
def romLayoutLanes (layout : RomLayout) (w : Nat) : Nat :=
  match layout with
  | .scalar => 1
  | .vectorized => romLanes w

theorem romLayoutLanes_pos (layout : RomLayout) (w : Nat) : 0 < romLayoutLanes layout w := by
  cases layout with
  | scalar => exact Nat.one_pos
  | vectorized => exact romLanes_pos w

omit [DecidableEq F] in
theorem lowerRomCircuitsWithLayout_eq (widths : List Nat) (segmented : Bool) (layout : RomLayout) :
    lowerRomCircuitsWithLayout (F := F) widths segmented layout =
      widths.map fun w => lowerKLaneRomCircuit w (romLayoutLanes layout w) segmented := by
  cases layout <;> rfl

/-- Extract the active `(address, payload)` entry (if any) from one scalar `<ROM:w>` row. -/
def scalarRomRowEntries (w : Nat) (row : Nat → F) : List (F × List F) :=
  if row 1 = 1 then
    [(row 2, (List.range w).map fun k => row (3 + k))]
  else []

/-- Extract all active `(address, payload)` entries from a scalar `<ROM:w>` trace. -/
def scalarRomTraceEntries (w : Nat) (tr : CircuitTrace F) : List (F × List F) :=
  ((List.range tr.height).map tr.mainRow).flatMap (scalarRomRowEntries w)

/-- Unified entry extraction for a `K`-lane `<ROM:w>` circuit (scalar when `K ≤ 1`,
vectorized active prefix when `1 < K`). -/
def klaneRomEntries (w K : Nat) (tr : CircuitTrace F) : List (F × List F) :=
  if K ≤ 1 then scalarRomTraceEntries w tr
  else vecTraceEntries w K ((List.range tr.height).map tr.mainRow)

/-- Extract active `(address, payload)` entries for width `w` under `layout`. -/
def extractRomEntries (w : Nat) (layout : RomLayout) (tr : CircuitTrace F) : List (F × List F) :=
  klaneRomEntries w (romLayoutLanes layout w) tr

/-- Reconstruct the full `WidthROM F` from the ROM circuit traces of `lowerFullSystem`. -/
def extractWidthROM (romWidths : List Nat) (layout : RomLayout)
    (romTraces : List (CircuitTrace F)) : WidthROM F :=
  ⟨(List.zipWith (fun w tr => extractRomEntries w layout tr) romWidths romTraces).flatten⟩

theorem scalarRomRowEntries_payload_length (w : Nat) (row : Nat → F)
    {e : F × List F} (he : e ∈ scalarRomRowEntries w row) : e.2.length = w := by
  unfold scalarRomRowEntries at he
  split_ifs at he with h
  · simp only [List.mem_singleton] at he
    subst he
    simp
  · cases he

theorem klaneRomEntries_payload_length (w K : Nat) (tr : CircuitTrace F)
    {e : F × List F} (he : e ∈ klaneRomEntries w K tr) : e.2.length = w := by
  unfold klaneRomEntries at he
  split_ifs at he with hK
  · unfold scalarRomTraceEntries at he
    obtain ⟨row, _, hrow⟩ := List.mem_flatMap.mp he
    exact scalarRomRowEntries_payload_length w row hrow
  · unfold vecTraceEntries at he
    obtain ⟨row, _, hrow⟩ := List.mem_flatMap.mp he
    unfold vecRowEntries at hrow
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hrow
    simp [vecPayload]

/-- Extract scalar `<ROM:w>` row and transition equations from `CircuitAirSatisfied`. -/
theorem scalarRom_air_extract (w : Nat) (segmented : Bool) (logBlowup extDegree : Nat)
    (tr : CircuitTrace F)
    (hsat : CircuitAirSatisfied
      (compileRetune logBlowup extDegree (lowerScalarRomCircuit w segmented)) tr) :
    (∀ r < tr.height, tr.mainRow r 1 = 0 ∨ tr.mainRow r 1 = 1) ∧
    (∀ r < tr.height, tr.mainRow r 1 = 0 → tr.mainRow r 0 = 0) ∧
    (∀ r, r + 1 < tr.height → tr.mainRow (r + 1) 1 = 1 →
      tr.mainRow r 1 = 1 ∧ tr.mainRow (r + 1) 2 = tr.mainRow r 2 + 1) ∧
    (segmented = false → 0 < tr.height → tr.mainRow 0 2 = 0) := by
  have hbase : ∀ r < tr.height, ∀ e ∈
      ([AirExpr.mul (.main 1) (.sub (.main 1) (.const (1 : F))),
        .mul (.main 0) (.sub (.const (1 : F)) (.main 1)),
        .mul (.mul .isTransition (.mainNext 1)) (.sub (.main 1) (.const (1 : F))),
        .mul (.mul .isTransition (.mainNext 1)) (.sub (.sub (.mainNext 2) (.main 2)) (.const (1 : F)))] :
        List (AirExpr F)),
      tr.evalExpr r e = 0 := by
    intro r hr e he
    apply (circuitRowSatisfied_retune_compile_iff _ logBlowup extDegree tr r).mp (hsat r hr)
    unfold lowerScalarRomCircuit
    cases segmented
    · exact List.mem_append_left _ he
    · exact he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    have h := hbase r hr (.mul (.main 1) (.sub (.main 1) (.const (1 : F)))) (by simp)
    simp only [CircuitTrace.evalExpr, AirExpr.eval] at h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · intro r hr h0
    have h := hbase r hr (.mul (.main 0) (.sub (.const (1 : F)) (.main 1))) (by simp)
    simp only [CircuitTrace.evalExpr, AirExpr.eval, h0, sub_zero, mul_one] at h
    exact h
  · intro r hr1 hact1
    have hr : r < tr.height := by omega
    have h1 := hbase r hr
      (.mul (.mul .isTransition (.mainNext 1)) (.sub (.main 1) (.const (1 : F)))) (by simp)
    have h2 := hbase r hr
      (.mul (.mul .isTransition (.mainNext 1)) (.sub (.sub (.mainNext 2) (.main 2)) (.const (1 : F))))
      (by simp)
    simp only [CircuitTrace.evalExpr, AirExpr.eval, CircuitTrace.nextRow, hr1, ↓reduceIte,
      one_mul, hact1] at h1 h2
    exact ⟨sub_eq_zero.mp h1, by linear_combination h2⟩
  · intro hseg h0
    subst hseg
    have hmem : AirExpr.mul .isFirstRow (.main (F := F) 2) ∈
        (lowerScalarRomCircuit w false).constraints := by
      simp [lowerScalarRomCircuit]
    have h := (circuitRowSatisfied_retune_compile_iff _ logBlowup extDegree tr 0).mp (hsat 0 h0) _ hmem
    simpa [CircuitTrace.evalExpr, AirExpr.eval] using h

/-- `CircuitAirSatisfied` on `lowerKLaneRomCircuit w K segmented` (`1 < K`) implies
`MultiStarkSpec.KLaneRomTraceValid w K segmented ((List.range tr.height).map tr.mainRow)`. -/
theorem klaneRomTraceValid_of_air {w K : Nat} (hK : 1 < K) (segmented : Bool)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F)
    (hsat : CircuitAirSatisfied
      (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w K segmented)) tr) :
    KLaneRomTraceValid w K segmented ((List.range tr.height).map tr.mainRow) := by
  intro t ht
  dsimp only
  intro c hc
  have ht' : t < tr.height := by simpa using ht
  have hrow := (circuitRowSatisfied_retune_compile_iff _ logBlowup extDegree tr t).mp (hsat t ht')
  have hc0 := hrow c hc
  have hcur : ((List.range tr.height).map tr.mainRow)[t] = tr.mainRow t := by simp
  have hnotle : ¬(K ≤ 1) := by omega
  by_cases ht1 : t + 1 < tr.height
  · have hnxt : (if h : t + 1 < ((List.range tr.height).map tr.mainRow).length
        then ((List.range tr.height).map tr.mainRow)[t + 1] else fun _ => 0) = tr.nextRow t := by
      simp [CircuitTrace.nextRow, ht1]
    have hlen : ((List.range tr.height).map tr.mainRow).length = tr.height := by simp
    have hnoPrep : ∀ e ∈ (lowerKLaneRomCircuit w K segmented).constraints,
        ∀ (a b p₁ p₂ : Nat → F) (f l trs : F),
          e.eval a b p₁ f l trs = e.eval a b p₂ f l trs := by
      intro e he a b p₁ p₂ f l trs
      unfold lowerKLaneRomCircuit at he
      simp only [hnotle, ↓reduceIte] at he
      have hbase : ∀ x ∈
          ((List.range K).flatMap fun lane =>
            [AirExpr.mul (.main (vecActiveCol w lane)) (.sub (.main (vecActiveCol w lane)) (.const (1 : F))),
             .mul (.main (vecCountCol w lane)) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))]) ++
          ((List.range (K - 1)).map fun lane =>
            .mul (.main (vecActiveCol w (lane + 1))) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))) ++
          [.mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
                (.sub (.main (vecActiveCol w (K - 1))) (.const (1 : F))),
           .mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
                (.sub (.sub (.mainNext 0) (.main 0)) (.const (K : F)))],
          x.eval a b p₁ f l trs = x.eval a b p₂ f l trs := by
        intro x hx
        simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with ((⟨lane, _, rfl | rfl⟩ | ⟨lane, _, rfl⟩) | (rfl | rfl)) <;>
          simp [AirExpr.eval]
      cases segmented
      · rcases List.mem_append.mp he with h | h
        · exact hbase e h
        · simp only [List.mem_singleton] at h; subst h; simp [AirExpr.eval]
      · exact hbase e he
    rw [hcur, hnxt, hlen]
    rw [hnoPrep c hc _ _ _ (tr.prepRow t)]
    simpa [CircuitTrace.evalExpr, ht1] using hc0
  · have hlen : ((List.range tr.height).map tr.mainRow).length = tr.height := by simp
    rw [hcur]
    simp only [hlen, ht1, ↓reduceDIte, ↓reduceIte]
    unfold lowerKLaneRomCircuit at hc
    simp only [hnotle, ↓reduceIte] at hc
    have hbase : ∀ x ∈
        ((List.range K).flatMap fun lane =>
          [AirExpr.mul (.main (vecActiveCol w lane)) (.sub (.main (vecActiveCol w lane)) (.const (1 : F))),
           .mul (.main (vecCountCol w lane)) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))]) ++
        ((List.range (K - 1)).map fun lane =>
          .mul (.main (vecActiveCol w (lane + 1))) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))) ++
        [.mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
              (.sub (.main (vecActiveCol w (K - 1))) (.const (1 : F))),
         .mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
              (.sub (.sub (.mainNext 0) (.main 0)) (.const (K : F)))],
        x.eval (tr.mainRow t) (tr.nextRow t) (tr.prepRow t)
          (if t = 0 then 1 else 0) (if t + 1 = tr.height then 1 else 0) 0 = 0 →
        x.eval (tr.mainRow t) (fun _ => 0) (fun _ => 0)
          (if t = 0 then 1 else 0) (if t + 1 = tr.height then 1 else 0) 0 = 0 := by
      intro x hx h0
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((⟨lane, _, rfl | rfl⟩ | ⟨lane, _, rfl⟩) | (rfl | rfl))
      · simpa [AirExpr.eval] using h0
      · simpa [AirExpr.eval] using h0
      · simpa [AirExpr.eval] using h0
      · simp [AirExpr.eval]
      · simp [AirExpr.eval]
    have hc0' : c.eval (tr.mainRow t) (tr.nextRow t) (tr.prepRow t)
        (if t = 0 then 1 else 0) (if t + 1 = tr.height then 1 else 0) 0 = 0 := by
      simpa [CircuitTrace.evalExpr, ht1] using hc0
    cases segmented
    · rcases List.mem_append.mp hc with h | h
      · exact hbase c h hc0'
      · simp only [List.mem_singleton] at h; subst h; simpa [AirExpr.eval] using hc0'
    · exact hbase c hc hc0'

/-- **ROM Circuit Ledger Support:** every nonzero tuple in a compiled/retuned `<ROM:w>`
circuit ledger is either an encoded `ROM` entry in `klaneRomEntries w K tr` or (when
`segmented = true`) a `MEMSEG` boundary tuple `[memsegTag, w, addr]`. -/
theorem klaneRom_circuitLedger_support (w K : Nat) (segmented : Bool)
    (logBlowup extDegree : Nat) (tr : CircuitTrace F)
    (hsat : CircuitAirSatisfied
      (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w K segmented)) tr) :
    ∀ t, circuitLedger (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w K segmented)) tr t ≠ 0 →
      (∃ e ∈ klaneRomEntries w K tr, t = encodeRom (e.1, Erasure.pack e.2)) ∨
      (segmented = true ∧ t.head? = some (memsegTag : F) ∧ t.tail.head? = some (w : F) ∧ t.length = 3) := by
  intro t ht
  rw [circuitLedger_retune_compile_eq] at ht
  simp only [Tiling.System.ledger_list_sum, List.map_map] at ht
  obtain ⟨v, hv, hne⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  have hrLt : r < tr.height := List.mem_range.mp hr
  simp only [Function.comp_apply, Tiling.System.ledger_list_sum, List.map_map] at hne
  obtain ⟨v', hv', hne'⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum hne
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv'
  simp only [Function.comp_apply, airLookupLedger, Finsupp.single_apply] at hne'
  split at hne'
  · rename_i htEq
    by_cases hK : K ≤ 1
    · -- Scalar ROM case
      have hcirc : lowerKLaneRomCircuit (F := F) w K segmented = lowerScalarRomCircuit w segmented := by
        unfold lowerKLaneRomCircuit; simp [hK]
      rw [hcirc] at hl hsat
      obtain ⟨h01, hcnt0, _, _⟩ := scalarRom_air_extract w segmented logBlowup extDegree tr hsat
      unfold lowerScalarRomCircuit at hl
      cases segmented with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hl
          subst hl
          have hmultNe : tr.mainRow r 0 ≠ 0 := by
            intro h0
            apply hne'
            simp [AirLookup.pull, CircuitTrace.evalExpr, AirExpr.eval, h0]
          have hact1 : tr.mainRow r 1 = 1 := by
            rcases h01 r hrLt with h0 | h1
            · exact absurd (hcnt0 r hrLt h0) hmultNe
            · exact h1
          left
          refine ⟨(tr.mainRow r 2, (List.range w).map fun k => tr.mainRow r (3 + k)), ?_, ?_⟩
          · unfold klaneRomEntries
            simp only [hK, ↓reduceIte, scalarRomTraceEntries, List.mem_flatMap, List.mem_map,
              List.mem_range]
            exact ⟨tr.mainRow r, ⟨r, hrLt, rfl⟩, by simp [scalarRomRowEntries, hact1]⟩
          · rw [← htEq]
            simp [AirLookup.pull, encodeRom, Erasure.pack, romTag, Aiur.Tiling.Bridge.ROM,
              CircuitTrace.evalExpr, AirExpr.eval, List.map_map, Function.comp_def]
      | true =>
          simp only [↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl | rfl
          · have hmultNe : tr.mainRow r 0 ≠ 0 := by
              intro h0
              apply hne'
              simp [AirLookup.pull, CircuitTrace.evalExpr, AirExpr.eval, h0]
            have hact1 : tr.mainRow r 1 = 1 := by
              rcases h01 r hrLt with h0 | h1
              · exact absurd (hcnt0 r hrLt h0) hmultNe
              · exact h1
            left
            refine ⟨(tr.mainRow r 2, (List.range w).map fun k => tr.mainRow r (3 + k)), ?_, ?_⟩
            · unfold klaneRomEntries
              simp only [hK, ↓reduceIte, scalarRomTraceEntries, List.mem_flatMap, List.mem_map,
                List.mem_range]
              exact ⟨tr.mainRow r, ⟨r, hrLt, rfl⟩, by simp [scalarRomRowEntries, hact1]⟩
            · rw [← htEq]
              simp [AirLookup.pull, encodeRom, Erasure.pack, romTag, Aiur.Tiling.Bridge.ROM,
                CircuitTrace.evalExpr, AirExpr.eval, List.map_map, Function.comp_def]
          · right
            rw [← htEq]
            simp [AirLookup.push, CircuitTrace.evalExpr, AirExpr.eval]
          · right
            rw [← htEq]
            simp [AirLookup.pull, CircuitTrace.evalExpr, AirExpr.eval]
    · -- Vectorized `1 < K` ROM case
      have hKgt : 1 < K := by omega
      have hvalid := klaneRomTraceValid_of_air hKgt segmented logBlowup extDegree tr hsat
      obtain ⟨hrows, _, _⟩ := hvalid.extract hKgt
      have hrowR : KLaneRomRowValid w K (tr.mainRow r) := by
        have h := hrows r (by simpa using hrLt)
        simpa [List.getElem_map, List.getElem_range] using h
      obtain ⟨hmK, _, _, hoff, _, _, _⟩ := vecRow_prefix_of_valid hKgt hrowR
      unfold lowerKLaneRomCircuit at hl
      simp only [hK, ↓reduceIte] at hl
      have hromCase : ∀ lane < K,
          l = AirLookup.pull (.main (vecCountCol w lane))
            ([.const (romTag : F), .const (w : F),
              if lane == 0 then .main 0 else .add (.main 0) (.const (lane : F))] ++
              (List.range w).map fun k => AirExpr.main (vecPayloadCol w lane k)) →
          ∃ e ∈ klaneRomEntries w K tr, t = encodeRom (e.1, Erasure.pack e.2) := by
        intro lane hlane hlEq
        subst hlEq
        have hcntNe : vecCount w (tr.mainRow r) lane ≠ 0 := by
          intro h0
          apply hne'
          simp [AirLookup.pull, CircuitTrace.evalExpr, AirExpr.eval, show tr.mainRow r (vecCountCol w lane) = 0 from h0]
        have hlaneLt : lane < vecRowActiveCount w K (tr.mainRow r) := by
          by_contra hge
          have hc0 := (hoff lane (Nat.not_lt.mp hge) hlane).2
          exact hcntNe hc0
        refine ⟨(vecBaseAddr (tr.mainRow r) + (lane : F), vecPayload w (tr.mainRow r) lane), ?_, ?_⟩
        · unfold klaneRomEntries
          simp only [hK, ↓reduceIte, vecTraceEntries, List.mem_flatMap, List.mem_map, List.mem_range]
          exact ⟨tr.mainRow r, ⟨r, hrLt, rfl⟩, by
            unfold vecRowEntries
            exact List.mem_map.mpr ⟨lane, List.mem_range.mpr hlaneLt, rfl⟩⟩
        · rw [← htEq]
          have haddr :
              AirExpr.eval (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
                (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
                (if r + 1 < tr.height then 1 else 0)
                (if lane = 0 then AirExpr.main (F := F) 0
                 else AirExpr.add (.main 0) (.const (lane : F))) =
              vecBaseAddr (tr.mainRow r) + (lane : F) := by
            cases lane with
            | zero => simp [AirExpr.eval, vecBaseAddr]
            | succ l' => simp [AirExpr.eval, vecBaseAddr]
          simp [AirLookup.pull, encodeRom, Erasure.pack, romTag, Aiur.Tiling.Bridge.ROM,
            CircuitTrace.evalExpr, AirExpr.eval, vecPayload, List.map_map, Function.comp_def,
            haddr]
      cases segmented with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_range] at hl
          obtain ⟨lane, hlane, rfl⟩ := hl
          exact Or.inl (hromCase lane hlane rfl)
      | true =>
          simp only [↓reduceIte, List.mem_append, List.mem_map, List.mem_range,
            List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with ⟨lane, hlane, rfl⟩ | rfl | rfl
          · exact Or.inl (hromCase lane hlane rfl)
          · right
            rw [← htEq]
            simp [AirLookup.push, CircuitTrace.evalExpr, AirExpr.eval]
          · right
            rw [← htEq]
            simp [AirLookup.pull, CircuitTrace.evalExpr, AirExpr.eval]
  · exact absurd rfl hne'

/-- **Unsegmented ROM Validity (`extractWidthROM_valid_unsegmented`):**
When `segmented = false`, `romWidths.Nodup`, `SmallCast F bound`, and every ROM
circuit satisfies its lowered AIR constraints with `layout.lanes w * tr.height ≤ bound`,
the extracted `WidthROM F` is automatically `Valid` (uniquely addressed per width). -/
theorem extractWidthROM_valid_unsegmented {bound : Nat} (small : SmallCast F bound)
    (romWidths : List Nat) (hnd : romWidths.Nodup) (layout : RomLayout)
    (logBlowup extDegree : Nat) (romTraces : List (CircuitTrace F))
    (hsat : List.Forall₂ CircuitAirSatisfied
      ((lowerRomCircuitsWithLayout (F := F) romWidths false layout).map
        (compileRetune logBlowup extDegree))
      romTraces)
    (hcap : List.Forall₂ (fun w tr => romLayoutLanes layout w * tr.height ≤ bound) romWidths romTraces) :
    (extractWidthROM romWidths layout romTraces).Valid := by
  have hlen : romTraces.length = romWidths.length := hcap.length_eq.symm
  -- Helper: within one width `w`, all extracted entries have distinct addresses.
  have hsingleValid : ∀ (i : Nat) (hi : i < romWidths.length),
      ∀ a ∈ extractRomEntries romWidths[i] layout (romTraces[i]'(hlen ▸ hi)),
      ∀ b ∈ extractRomEntries romWidths[i] layout (romTraces[i]'(hlen ▸ hi)),
        a.1 = b.1 → a.2 = b.2 := by
    intro i hi a ha b hb haddrEq
    set w := romWidths[i]
    set tr := romTraces[i]'(hlen ▸ hi)
    have hsatI : CircuitAirSatisfied
        (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w (romLayoutLanes layout w) false)) tr := by
      have := List.forall₂_iff_get.mp hsat
      have hget := this.2 i (by simp [lowerRomCircuitsWithLayout_eq, hi]) (by simp [hlen, hi])
      simpa [lowerRomCircuitsWithLayout_eq, w, tr] using hget
    have hcapI : romLayoutLanes layout w * tr.height ≤ bound :=
      (List.forall₂_iff_get.mp hcap).2 i hi (by simp [hlen, hi])
    unfold extractRomEntries klaneRomEntries at ha hb
    by_cases hK : romLayoutLanes layout w ≤ 1
    · simp only [hK, ↓reduceIte] at ha hb
      have hcirc : lowerKLaneRomCircuit (F := F) w (romLayoutLanes layout w) false =
          lowerScalarRomCircuit w false := by
        unfold lowerKLaneRomCircuit; simp [hK]
      rw [hcirc] at hsatI
      obtain ⟨h01, _, htrans, hfirst⟩ :=
        scalarRom_air_extract w false logBlowup extDegree tr hsatI
      have hK1 : romLayoutLanes layout w = 1 := by have := romLayoutLanes_pos layout w; omega
      have hHle : tr.height ≤ bound := by simpa [hK1] using hcapI
      -- Show every active row `r` has all prior rows active and `addr r = (r : F)`.
      have hactAddr : ∀ r < tr.height, tr.mainRow r 1 = 1 → tr.mainRow r 2 = (r : F) := by
        intro r
        induction r with
        | zero =>
            intro hr _
            simpa using hfirst rfl hr
        | succ r ih =>
            intro hr1 hact1
            obtain ⟨hprev, hstep⟩ := htrans r hr1 hact1
            rw [hstep, ih (by omega) hprev]
            push_cast; ring
      unfold scalarRomTraceEntries at ha hb
      obtain ⟨rowA, hrowA, haIn⟩ := List.mem_flatMap.mp ha
      obtain ⟨rA, hrA, rfl⟩ := List.mem_map.mp hrowA
      have hrALt : rA < tr.height := List.mem_range.mp hrA
      obtain ⟨rowB, hrowB, hbIn⟩ := List.mem_flatMap.mp hb
      obtain ⟨rB, hrB, rfl⟩ := List.mem_map.mp hrowB
      have hrBLt : rB < tr.height := List.mem_range.mp hrB
      unfold scalarRomRowEntries at haIn hbIn
      split_ifs at haIn with hactA
      · split_ifs at hbIn with hactB
        · simp only [List.mem_singleton] at haIn hbIn
          subst haIn; subst hbIn
          dsimp only at haddrEq
          rw [hactAddr rA hrALt hactA, hactAddr rB hrBLt hactB] at haddrEq
          have hrEq : rA = rB := small.inj (by omega) (by omega) haddrEq
          subst hrEq; rfl
        · cases hbIn
      · cases haIn
    · simp only [hK, ↓reduceIte] at ha hb
      have hKgt : 1 < romLayoutLanes layout w := by omega
      have hvalid := klaneRomTraceValid_of_air hKgt false logBlowup extDegree tr hsatI
      obtain ⟨activeRows, haLe, hon, hfull, hoff, hfirst⟩ :=
        vectorizedRom_rows_contiguous hKgt hvalid
      have hrowsLen : ((List.range tr.height).map tr.mainRow).length = tr.height := by simp
      rw [hrowsLen] at haLe
      unfold vecTraceEntries at ha hb
      obtain ⟨rowA, hrowA, haIn⟩ := List.mem_flatMap.mp ha
      obtain ⟨rA, hrA, rfl⟩ := List.mem_map.mp hrowA
      have hrALt : rA < tr.height := List.mem_range.mp hrA
      obtain ⟨rowB, hrowB, hbIn⟩ := List.mem_flatMap.mp hb
      obtain ⟨rB, hrB, rfl⟩ := List.mem_map.mp hrowB
      have hrBLt : rB < tr.height := List.mem_range.mp hrB
      unfold vecRowEntries at haIn hbIn
      obtain ⟨lA, hlA, rfl⟩ := List.mem_map.mp haIn
      obtain ⟨lB, hlB, rfl⟩ := List.mem_map.mp hbIn
      have hlALt : lA < vecRowActiveCount w (romLayoutLanes layout w) (tr.mainRow rA) := List.mem_range.mp hlA
      have hlBLt : lB < vecRowActiveCount w (romLayoutLanes layout w) (tr.mainRow rB) := List.mem_range.mp hlB
      have hrAAct : rA < activeRows := by
        by_contra hge
        have hm0 := (hoff rA (Nat.not_lt.mp hge) (by simpa using hrALt)).2
        simp only [List.getElem_map, List.getElem_range] at hm0
        omega
      have hrBAct : rB < activeRows := by
        by_contra hge
        have hm0 := (hoff rB (Nat.not_lt.mp hge) (by simpa using hrBLt)).2
        simp only [List.getElem_map, List.getElem_range] at hm0
        omega
      have h0Pos : 0 < activeRows := by omega
      have hbase0 : vecBaseAddr (tr.mainRow 0) = 0 := by
        have := hfirst rfl h0Pos (by simpa using Nat.lt_of_lt_of_le h0Pos haLe)
        simpa using this
      have hbaseA : vecBaseAddr (tr.mainRow rA) = ((romLayoutLanes layout w * rA : Nat) : F) := by
        have := (hon rA hrAAct).2
        simpa [hbase0] using this
      have hbaseB : vecBaseAddr (tr.mainRow rB) = ((romLayoutLanes layout w * rB : Nat) : F) := by
        have := (hon rB hrBAct).2
        simpa [hbase0] using this
      obtain ⟨hrowsValid, _, _⟩ := hvalid.extract hKgt
      have hrowValidA : KLaneRomRowValid w (romLayoutLanes layout w) (tr.mainRow rA) := by
        have h := hrowsValid rA (by simpa using hrALt)
        simpa [List.getElem_map, List.getElem_range] using h
      have hrowValidB : KLaneRomRowValid w (romLayoutLanes layout w) (tr.mainRow rB) := by
        have h := hrowsValid rB (by simpa using hrBLt)
        simpa [List.getElem_map, List.getElem_range] using h
      have hlAK : lA < romLayoutLanes layout w :=
        lt_of_lt_of_le hlALt (vecRow_prefix_of_valid hKgt hrowValidA).1
      have hlBK : lB < romLayoutLanes layout w :=
        lt_of_lt_of_le hlBLt (vecRow_prefix_of_valid hKgt hrowValidB).1
      dsimp only at haddrEq
      rw [hbaseA, hbaseB] at haddrEq
      have hcastEq : ((romLayoutLanes layout w * rA + lA : Nat) : F) =
          ((romLayoutLanes layout w * rB + lB : Nat) : F) := by
        rw [Nat.cast_add, Nat.cast_add]; exact haddrEq
      have hltA : romLayoutLanes layout w * rA + lA < bound := by
        have h1 : romLayoutLanes layout w * (rA + 1) ≤ romLayoutLanes layout w * tr.height :=
          Nat.mul_le_mul_left _ hrALt
        have h2 : romLayoutLanes layout w * (rA + 1) =
            romLayoutLanes layout w * rA + romLayoutLanes layout w := by ring
        omega
      have hltB : romLayoutLanes layout w * rB + lB < bound := by
        have h1 : romLayoutLanes layout w * (rB + 1) ≤ romLayoutLanes layout w * tr.height :=
          Nat.mul_le_mul_left _ hrBLt
        have h2 : romLayoutLanes layout w * (rB + 1) =
            romLayoutLanes layout w * rB + romLayoutLanes layout w := by ring
        omega
      have hnatEq : romLayoutLanes layout w * rA + lA = romLayoutLanes layout w * rB + lB :=
        small.inj hltA hltB hcastEq
      have hposK : 0 < romLayoutLanes layout w := romLayoutLanes_pos layout w
      have hrEq : rA = rB := by
        have := congrArg (· / romLayoutLanes layout w) hnatEq
        rw [Nat.mul_add_div hposK, Nat.mul_add_div hposK,
          Nat.div_eq_of_lt hlAK, Nat.div_eq_of_lt hlBK, Nat.add_zero, Nat.add_zero] at this
        exact this
      subst hrEq
      have hlEq : lA = lB := by omega
      subst hlEq; rfl
  -- Combine across distinct widths using `romWidths.Nodup` and payload length = width.
  intro a ha b hb haddrEq hlenEq
  unfold extractWidthROM at ha hb
  obtain ⟨xsA, hxsA, haIn⟩ := List.mem_flatten.mp ha
  obtain ⟨xsB, hxsB, hbIn⟩ := List.mem_flatten.mp hb
  obtain ⟨iA, hiA, hxsAEq⟩ := List.mem_iff_getElem.mp hxsA
  obtain ⟨iB, hiB, hxsBEq⟩ := List.mem_iff_getElem.mp hxsB
  have hiALt : iA < romWidths.length := by simp [List.length_zipWith, hlen] at hiA; exact hiA
  have hiBLt : iB < romWidths.length := by simp [List.length_zipWith, hlen] at hiB; exact hiB
  rw [List.getElem_zipWith] at hxsAEq hxsBEq
  subst hxsAEq; subst hxsBEq
  have hlenA : a.2.length = romWidths[iA] := klaneRomEntries_payload_length _ _ _ haIn
  have hlenB : b.2.length = romWidths[iB] := klaneRomEntries_payload_length _ _ _ hbIn
  have hwEq : romWidths[iA] = romWidths[iB] := hlenA.symm.trans (hlenEq.trans hlenB)
  have hiEq : iA = iB := congrArg Fin.val
    ((List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨iA, hiALt⟩) (a₂ := ⟨iB, hiBLt⟩) hwEq)
  subst hiEq
  exact hsingleValid iA hiALt a haIn b hbIn haddrEq

/-! ### Segmented `MEMSEG` Interval Balance → `WidthROM.Valid` over `ZMod p` -/

/-- Sorted disjoint half-open intervals `[a_j, b_j) ⊆ [0, p)`. -/
def DisjointIntervalsP (p : Nat) (ivls : List (Nat × Nat)) : Prop :=
  (∀ iv ∈ ivls, iv.1 ≤ iv.2 ∧ iv.2 < p) ∧
  (∀ i (hi : i + 1 < ivls.length), ivls[i].2 ≤ ivls[i + 1].1)

/-- Interval coverage count at `x : Nat`. -/
def intervalCoverP (ivls : List (Nat × Nat)) (x : Nat) : Nat :=
  (ivls.filter fun iv => decide (iv.1 ≤ x ∧ x < iv.2)).length

theorem intervalCoverP_le_one {p : Nat} {ivls : List (Nat × Nat)}
    (hd : DisjointIntervalsP p ivls) (x : Nat) :
    intervalCoverP ivls x ≤ 1 := by
  unfold intervalCoverP
  have hmono : ∀ i j (hi : i < ivls.length) (hj : j < ivls.length), i < j →
      ivls[i].2 ≤ ivls[j].1 := by
    intro i j hi hj hlt
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases heq : i = j
        · subst heq; exact hd.2 i hj
        · have hprev := ih (by omega) (by omega)
          have hstep := hd.2 j hj
          have hle := (hd.1 ivls[j] (List.getElem_mem (by omega))).1
          omega
  by_contra hgt
  have h2 : 2 ≤ (ivls.filter fun iv => decide (iv.1 ≤ x ∧ x < iv.2)).length := by omega
  have hpair : ∀ (l : List (Nat × Nat)) (q : Nat × Nat → Bool),
      2 ≤ (l.filter q).length →
      ∃ (i j : Nat) (hi : i < l.length) (hj : j < l.length),
        i < j ∧ q l[i] = true ∧ q l[j] = true := by
    intro l q
    induction l with
    | nil => simp
    | cons a as ih =>
        intro hlen
        cases hpa : q a with
        | false =>
            simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hlen
            obtain ⟨i, j, hi, hj, hlt, hpi, hpj⟩ := ih hlen
            exact ⟨i + 1, j + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hj,
              Nat.succ_lt_succ hlt, hpi, hpj⟩
        | true =>
            simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons] at hlen
            have hne : as.filter q ≠ [] := List.ne_nil_of_length_pos (by omega)
            obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hne
            obtain ⟨hb_mem, hpb⟩ := List.mem_filter.mp hb
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb_mem
            exact ⟨0, j + 1, Nat.zero_lt_succ _, Nat.succ_lt_succ hj, Nat.zero_lt_succ _, hpa, hpb⟩
  obtain ⟨i, j, hi, hj, hlt, hpi, hpj⟩ := hpair ivls _ h2
  simp only [decide_eq_true_eq] at hpi hpj
  have := hmono i j hi hj hlt
  omega

theorem intervalCoverP_last {p : Nat} {ivls : List (Nat × Nat)}
    (hd : DisjointIntervalsP p ivls) :
    intervalCoverP ivls (p - 1) = 0 := by
  unfold intervalCoverP
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro iv hiv
  have hlt := (hd.1 iv hiv).2
  simp only [decide_eq_true_eq, not_and, not_lt]
  intro _; omega

/-- Preamble `MEMSEG` boundary contribution at address `x` in `ZMod p`. -/
def memsegBoundaryZ (p : Nat) (ivls : List (Nat × Nat)) (x : ZMod p) : ZMod p :=
  (ivls.map fun iv =>
    (if x = (iv.2 : ZMod p) then (1 : ZMod p) else 0) -
    (if x = (iv.1 : ZMod p) then (1 : ZMod p) else 0)).sum

/-- Preamble `MEMSEG` closure ledger across all ROM widths: for each width `w`
and each interval `[a, b) ∈ ivlsOf w`, pulls `[memsegTag, w, a]` and pushes `[memsegTag, w, b]`. -/
noncomputable def memsegPreambleLedger {G : Type} [Field G]
    (romWidths : List Nat) (ivlsOf : Nat → List (Nat × Nat)) : Ledger G :=
  (romWidths.map fun w =>
    ((ivlsOf w).map fun iv =>
      Finsupp.single [(memsegTag : G), (w : G), (iv.2 : G)] 1 +
      Finsupp.single [(memsegTag : G), (w : G), (iv.1 : G)] (-1)).sum).sum

theorem memsegPreambleLedger_head {G : Type} [Field G] [DecidableEq G]
    (romWidths : List Nat) (ivlsOf : Nat → List (Nat × Nat)) :
    ∀ t, memsegPreambleLedger (G := G) romWidths ivlsOf t ≠ 0 →
      t.head? = some (memsegTag : G) := by
  intro t ht
  unfold memsegPreambleLedger at ht
  simp only [Tiling.System.ledger_list_sum, List.map_map] at ht
  obtain ⟨v, hv, hne⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum ht
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  simp only [Function.comp_apply, Tiling.System.ledger_list_sum, List.map_map] at hne
  obtain ⟨v', hv', hne'⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum hne
  obtain ⟨iv, _, rfl⟩ := List.mem_map.mp hv'
  simp only [Function.comp_apply, Finsupp.add_apply, Finsupp.single_apply] at hne'
  by_cases h1 : [(memsegTag : G), (w : G), (iv.2 : G)] = t
  · rw [← h1]; rfl
  · by_cases h2 : [(memsegTag : G), (w : G), (iv.1 : G)] = t
    · rw [← h2]; rfl
    · exfalso; apply hne'
      simp [h1, h2]

private theorem single_interval_diff_zmod {p : Nat} [Fact (Nat.Prime p)]
    {a b : Nat} (hab : a ≤ b) (hb : b < p) (x : ZMod p) :
    ((if a ≤ x.val ∧ x.val < b then (1 : Nat) else 0 : Nat) : ZMod p) -
    ((if a ≤ (x - 1).val ∧ (x - 1).val < b then (1 : Nat) else 0 : Nat) : ZMod p) =
      (if x = (a : ZMod p) then (1 : ZMod p) else 0) -
      (if x = (b : ZMod p) then (1 : ZMod p) else 0) := by
  have hpPos : 0 < p := (Fact.out : Nat.Prime p).pos
  have : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  have hxv : x.val < p := ZMod.val_lt x
  have ha_eq : (x = (a : ZMod p)) ↔ x.val = a := by
    constructor
    · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, ZMod.natCast_zmod_val]
  have hb_eq : (x = (b : ZMod p)) ↔ x.val = b := by
    constructor
    · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, ZMod.natCast_zmod_val]
  by_cases hx0 : x.val = 0
  · have hx_zero : x = 0 := by rw [← ZMod.natCast_zmod_val x, hx0]; simp
    have hprev : (x - 1).val = p - 1 := by
      rw [hx_zero, zero_sub]
      have : (-1 : ZMod p) = ((p - 1 : Nat) : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [hprev, hx0, ha_eq, hb_eq]
    split_ifs <;> try (exfalso; omega)
    all_goals (push_cast; ring)
  · have hprev : (x - 1).val = x.val - 1 := by
      have hx1 : x = ((x.val - 1 : Nat) : ZMod p) + 1 := by
        have hnat : x.val = (x.val - 1) + 1 := by omega
        calc x = (x.val : ZMod p) := (ZMod.natCast_zmod_val x).symm
          _ = (((x.val - 1) + 1 : Nat) : ZMod p) := by rw [← hnat]
          _ = ((x.val - 1 : Nat) : ZMod p) + 1 := by push_cast; rfl
      have hsub : x - 1 = ((x.val - 1 : Nat) : ZMod p) := sub_eq_of_eq_add hx1
      rw [hsub, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [hprev, ha_eq, hb_eq]
    split_ifs <;> try (exfalso; omega)
    all_goals (push_cast; ring)

theorem intervalCoverP_diff_eq_neg_memsegBoundaryZ {p : Nat} [Fact (Nat.Prime p)]
    {ivls : List (Nat × Nat)} (hd : DisjointIntervalsP p ivls) (x : ZMod p) :
    ((intervalCoverP ivls x.val : Nat) : ZMod p) -
    ((intervalCoverP ivls (x - 1).val : Nat) : ZMod p) =
      -memsegBoundaryZ p ivls x := by
  induction ivls with
  | nil => simp [intervalCoverP, memsegBoundaryZ]
  | cons iv rest ih =>
      have hrest : DisjointIntervalsP p rest :=
        ⟨fun a ha => hd.1 a (List.mem_cons_of_mem _ ha), fun i hi => hd.2 (i + 1) (by simp; omega)⟩
      have hiv := hd.1 iv (List.mem_cons_self ..)
      have h1 := single_interval_diff_zmod hiv.1 hiv.2 x
      have hstep := ih hrest
      have hcov : ∀ y : Nat, ((intervalCoverP (iv :: rest) y : Nat) : ZMod p) =
          ((if iv.1 ≤ y ∧ y < iv.2 then (1 : Nat) else 0 : Nat) : ZMod p) +
          ((intervalCoverP rest y : Nat) : ZMod p) := by
        intro y
        unfold intervalCoverP
        by_cases hy : iv.1 ≤ y ∧ y < iv.2 <;> simp [hy, Nat.cast_add, add_comm]
      rw [hcov x.val, hcov (x - 1).val]
      unfold memsegBoundaryZ at hstep ⊢
      simp only [List.map_cons, List.sum_cons]
      linear_combination h1 + hstep

/-- **Sharded `MEMSEG` Interval Uniqueness over any prime field `ZMod p`:**
if per-address active ROM counts `m : ZMod p → Nat` satisfy `∑ x, m x + 1 < p` and
`((m x : ZMod p) - (m (x - 1) : ZMod p)) + memsegBoundaryZ p ivls x = 0`,
then `m x = intervalCoverP ivls x.val ≤ 1` for every `x : ZMod p`. -/
theorem memseg_balance_implies_unique_zmod {p : Nat} [Fact (Nat.Prime p)]
    {ivls : List (Nat × Nat)} (hd : DisjointIntervalsP p ivls)
    {m : ZMod p → Nat} (hsum : (∑ x : ZMod p, m x) + 1 < p)
    (hbal : ∀ x : ZMod p, ((m x : ZMod p) - (m (x - 1) : ZMod p)) + memsegBoundaryZ p ivls x = 0) :
    ∀ x : ZMod p, m x = intervalCoverP ivls x.val ∧ m x ≤ 1 := by
  have hpPos : 0 < p := (Fact.out : Nat.Prime p).pos
  have : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  have hconst_step : ∀ x : ZMod p,
      (m x : ZMod p) - (intervalCoverP ivls x.val : ZMod p) =
        (m (x - 1) : ZMod p) - (intervalCoverP ivls (x - 1).val : ZMod p) := by
    intro x
    have hb := hbal x
    have hd' := intervalCoverP_diff_eq_neg_memsegBoundaryZ hd x
    linear_combination hb - hd'
  have hconst : ∀ n : Nat,
      (m (n : ZMod p) : ZMod p) - (intervalCoverP ivls (n : ZMod p).val : ZMod p) =
        (m 0 : ZMod p) - (intervalCoverP ivls (0 : ZMod p).val : ZMod p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := hconst_step ((n + 1 : Nat) : ZMod p)
        have hsub : ((n + 1 : Nat) : ZMod p) - 1 = (n : ZMod p) := by push_cast; ring
        rw [hsub] at hstep
        exact hstep.trans ih
  have hconst_all : ∀ x y : ZMod p,
      (m x : ZMod p) - (intervalCoverP ivls x.val : ZMod p) =
        (m y : ZMod p) - (intervalCoverP ivls y.val : ZMod p) := by
    intro x y
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, hconst x.val, hconst y.val]
  -- Pick `y₀` with `m y₀ = 0` by pigeonhole (`∑ m < p = |ZMod p|`).
  have hex0 : ∃ y₀ : ZMod p, m y₀ = 0 := by
    by_contra hall
    push Not at hall
    have hge : p ≤ ∑ x : ZMod p, m x := by
      calc p = Fintype.card (ZMod p) := (ZMod.card p).symm
        _ = ∑ _x : ZMod p, 1 := by simp
        _ ≤ ∑ x : ZMod p, m x := Finset.sum_le_sum fun x _ => Nat.pos_of_ne_zero (hall x)
    omega
  obtain ⟨y₀, hy₀⟩ := hex0
  set c : ZMod p := (m (p - 1 : Nat) : ZMod p)
  have hlastVal : ((p - 1 : Nat) : ZMod p).val = p - 1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hcovLast : intervalCoverP ivls ((p - 1 : Nat) : ZMod p).val = 0 := by
    rw [hlastVal]; exact intervalCoverP_last hd
  have heqC : ∀ x : ZMod p, (m x : ZMod p) - (intervalCoverP ivls x.val : ZMod p) = c := by
    intro x
    rw [hconst_all x ((p - 1 : Nat) : ZMod p), hcovLast, Nat.cast_zero, sub_zero]
  have hc0 : c = 0 := by
    have h1 := heqC y₀
    rw [hy₀, Nat.cast_zero, zero_sub] at h1
    have hcovLe : intervalCoverP ivls y₀.val ≤ 1 := intervalCoverP_le_one hd y₀.val
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcovLe with h0 | h1'
    · rw [h0, Nat.cast_zero, neg_zero] at h1; exact h1.symm
    · -- If `c = -1`, then `m((p - 1 : Nat)) = p - 1`, contradicting `∑ m + 1 < p`!
      rw [h1', Nat.cast_one] at h1
      have hlastM : (m ((p - 1 : Nat) : ZMod p) : ZMod p) = -1 := h1.symm
      have hmLe : m ((p - 1 : Nat) : ZMod p) ≤ ∑ x : ZMod p, m x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have hcast0 : ((m ((p - 1 : Nat) : ZMod p) + 1 : Nat) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hlastM, neg_add_cancel]
      have hdvd : p ∣ m ((p - 1 : Nat) : ZMod p) + 1 := (ZMod.natCast_eq_zero_iff _ p).mp hcast0
      have hge := Nat.le_of_dvd (Nat.succ_pos _) hdvd
      omega
  intro x
  have hx := heqC x
  rw [hc0, sub_eq_zero] at hx
  have hcovLe := intervalCoverP_le_one hd x.val
  have hmLe : m x ≤ ∑ y : ZMod p, m y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hcastEq : m x = intervalCoverP ivls x.val := by
    have h1 : (m x : ZMod p).val = (intervalCoverP ivls x.val : ZMod p).val := congrArg ZMod.val hx
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    exact h1
  exact ⟨hcastEq, hcastEq ▸ hcovLe⟩

/-- Row-level trimmed `MEMSEG` delta of a `K`-lane ROM circuit (`segmented = true`)
at `k = trimZeros [memsegTag, w, x]`. -/
theorem klaneRom_memseg_trim_apply {bound : Nat} (small : SmallCast F bound) (htags : 16 < bound)
    (w K : Nat) (logBlowup extDegree : Nat) (tr : CircuitTrace F)
    (hsat : CircuitAirSatisfied
      (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w K true)) tr)
    (x : F) :
    Finsupp.mapDomain trimZeros
      (circuitLedger (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w K true)) tr)
      (trimZeros [(memsegTag : F), (w : F), x]) =
    (((klaneRomEntries w K tr).filter fun e => decide (e.1 = x)).length : F) -
    (((klaneRomEntries w K tr).filter fun e => decide (e.1 = x - 1)).length : F) := by
  have hmemNe0 : (memsegTag : F) ≠ 0 := by
    intro h; have := small memsegTag htags h; simp [memsegTag] at this
  have hromNeMem : (romTag : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := romTag) (b := memsegTag) (by simp [romTag]; omega) htags h
    simp [romTag, memsegTag] at this
  have hromDisj : ∀ (u : List F), u.head? = some (romTag : F) →
      trimZeros u ≠ trimZeros [(memsegTag : F), (w : F), x] := by
    intro u hu heq
    have hh := trimZeros_head heq.symm (by simp) hmemNe0
    rw [hu, Option.some.injEq] at hh
    exact hromNeMem hh
  have h3iff : ∀ a : F,
      trimZeros [(memsegTag : F), (w : F), a] = trimZeros [(memsegTag : F), (w : F), x] ↔ a = x := by
    intro a
    constructor
    · intro h
      have heq := trimZeros_inj_of_length (by simp) h
      simp only [List.cons.injEq] at heq
      exact heq.2.2.1
    · intro h; subst h; rfl
  rw [circuitLedger_retune_compile_eq, Aiur.Tiling.Grouped.mapDomain_list_sum]
  simp only [Tiling.System.ledger_list_sum, List.map_map, Function.comp_def]
  by_cases hK : K ≤ 1
  · have hcirc : lowerKLaneRomCircuit (F := F) w K true = lowerScalarRomCircuit w true := by
      unfold lowerKLaneRomCircuit; simp [hK]
    rw [hcirc] at hsat ⊢
    obtain ⟨h01, _, _, _⟩ := scalarRom_air_extract w true logBlowup extDegree tr hsat
    have hrowEq : ∀ r ∈ List.range tr.height,
        Finsupp.mapDomain trimZeros (((lowerScalarRomCircuit (F := F) w true).lookups.map
          (airLookupLedger tr r)).sum) (trimZeros [(memsegTag : F), (w : F), x]) =
        (((scalarRomRowEntries w (tr.mainRow r)).filter fun e => decide (e.1 = x)).length : F) -
        (((scalarRomRowEntries w (tr.mainRow r)).filter fun e => decide (e.1 = x - 1)).length : F) := by
      intro r hr
      have hrLt : r < tr.height := List.mem_range.mp hr
      unfold lowerScalarRomCircuit
      simp only [↓reduceIte, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Finsupp.mapDomain_add, Finsupp.add_apply,
        airLookupLedger, AirLookup.pull, AirLookup.push, Finsupp.mapDomain_single,
        Finsupp.single_apply, CircuitTrace.evalExpr, AirExpr.eval, List.map_map,
        Function.comp_def, h3iff]
      have hrom0 : trimZeros ((romTag : F) :: (w : F) :: tr.mainRow r 2 ::
          (List.range w).map (fun k => tr.mainRow r (3 + k))) ≠
          trimZeros [(memsegTag : F), (w : F), x] :=
        hromDisj _ rfl
      simp only [hrom0, ↓reduceIte, zero_add]
      have hadd1 : (tr.mainRow r 2 + 1 = x) ↔ (tr.mainRow r 2 = x - 1) := by
        constructor <;> intro h <;> linear_combination h
      rcases h01 r hrLt with h0 | h1
      · simp only [h0, scalarRomRowEntries, zero_ne_one, ↓reduceIte, List.filter_nil,
          List.length_nil, Nat.cast_zero, sub_self, neg_zero, ite_self, add_zero]
      · simp only [h1, scalarRomRowEntries, ↓reduceIte, hadd1, List.filter_cons, List.filter_nil,
          decide_eq_true_eq]
        have hif : ∀ (P Q : Prop) [Decidable P] [Decidable Q] (a : F × List F),
            ((if P then (1 : F) else 0) + if Q then (-1 : F) else 0) =
            ((if P then [a] else []).length : F) - ((if Q then [a] else []).length : F) := by
          intro P Q _ _ a
          by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
        exact hif (tr.mainRow r 2 = x) (tr.mainRow r 2 = x - 1) _
    rw [List.map_congr_left hrowEq]
    unfold klaneRomEntries
    simp only [hK, ↓reduceIte, scalarRomTraceEntries]
    -- Sum of differences = difference of flatMap filter lengths
    have hsumSub : ∀ (xs : List Nat) (f g : Nat → F),
        (xs.map fun r => f r - g r).sum = (xs.map f).sum - (xs.map g).sum := by
      intro xs f g
      induction xs with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    have hlenFlat : ∀ (rs : List (Nat → F)) (p : (F × List F) → Bool),
        ((rs.flatMap (scalarRomRowEntries w)).filter p).length =
          (rs.map fun row => ((scalarRomRowEntries w row).filter p).length).sum := by
      intro rs p
      induction rs with
      | nil => rfl
      | cons r rs ih => simp [List.flatMap_cons, List.filter_append, ih]
    rw [hsumSub, hlenFlat, hlenFlat, Nat.cast_list_sum, Nat.cast_list_sum,
      List.map_map, List.map_map, List.map_map, List.map_map]
    rfl
  · have hKgt : 1 < K := by omega
    have hvalid := klaneRomTraceValid_of_air hKgt true logBlowup extDegree tr hsat
    obtain ⟨hrows, _, _⟩ := hvalid.extract hKgt
    have hrowEq : ∀ r ∈ List.range tr.height,
        Finsupp.mapDomain trimZeros (((lowerKLaneRomCircuit (F := F) w K true).lookups.map
          (airLookupLedger tr r)).sum) (trimZeros [(memsegTag : F), (w : F), x]) =
        vecRowMemsegDelta w K (tr.mainRow r) x := by
      intro r hr
      have hrLt : r < tr.height := List.mem_range.mp hr
      unfold lowerKLaneRomCircuit
      simp only [hK, ↓reduceIte, List.map_append, List.sum_append, Finsupp.mapDomain_add,
        Finsupp.add_apply]
      have hromZero :
          Finsupp.mapDomain trimZeros
            ((((List.range K).map fun lane =>
              AirLookup.pull (.main (vecCountCol w lane))
                ([.const (romTag : F), .const (w : F),
                  if lane == 0 then .main 0 else .add (.main 0) (.const (lane : F))] ++
                  (List.range w).map fun k => AirExpr.main (vecPayloadCol w lane k))).map
              (airLookupLedger tr r)).sum)
            (trimZeros [(memsegTag : F), (w : F), x]) = 0 := by
        rw [Aiur.Tiling.Grouped.mapDomain_list_sum]
        simp only [Tiling.System.ledger_list_sum, List.map_map]
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨lane, _, rfl⟩ := List.mem_map.mp hv
        simp only [Function.comp_apply, airLookupLedger, AirLookup.pull, Finsupp.mapDomain_single,
          Finsupp.single_apply, CircuitTrace.evalExpr, AirExpr.eval, List.map_append,
          List.map_cons, List.map_nil]
        exact ite_eq_right_iff.mpr fun h => absurd h (hromDisj _ rfl)
      rw [hromZero, zero_add]
      have hsumActive :
          ((List.range (K - 1)).foldl
            (fun acc i => AirExpr.add acc (.main (vecActiveCol w (i + 1))))
            (.main (vecActiveCol w 0))).eval (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
              (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
              (if r + 1 < tr.height then 1 else 0) =
          ((List.range K).map fun l => vecActive w (tr.mainRow r) l).sum := by
        have hgo : ∀ k,
            ((List.range k).foldl
              (fun acc i => AirExpr.add acc (.main (vecActiveCol w (i + 1))))
              (.main (vecActiveCol w 0))).eval (tr.mainRow r) (tr.nextRow r) (tr.prepRow r)
                (if r = 0 then 1 else 0) (if r + 1 = tr.height then 1 else 0)
                (if r + 1 < tr.height then 1 else 0) =
            ((List.range (k + 1)).map fun l => vecActive w (tr.mainRow r) l).sum := by
          intro k
          induction k with
          | zero => simp [AirExpr.eval, vecActive]
          | succ k ih =>
              rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                AirExpr.eval, ih]
              conv_rhs => rw [List.range_succ]
              simp [AirExpr.eval, vecActive]
        have := hgo (K - 1)
        rwa [show K - 1 + 1 = K by omega] at this
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Finsupp.mapDomain_add, Finsupp.add_apply, airLookupLedger, AirLookup.push, AirLookup.pull,
        Finsupp.mapDomain_single, Finsupp.single_apply, CircuitTrace.evalExpr, AirExpr.eval,
        hsumActive, h3iff]
      unfold vecRowMemsegDelta vecBaseAddr vecActive
      dsimp only
      by_cases h1 : tr.mainRow r 0 = x <;>
        by_cases h2 : tr.mainRow r 0 + ((List.range K).map fun l => tr.mainRow r (vecActiveCol w l)).sum = x <;>
        simp [h1, h2]
      all_goals
        by_cases h3 : ((List.range K).map fun l => tr.mainRow r (vecActiveCol w l)).sum = 0 <;>
          simp [h3]
    rw [List.map_congr_left hrowEq]
    have htrEq : ((List.range tr.height).map fun r => vecRowMemsegDelta w K (tr.mainRow r) x).sum =
        (((List.range tr.height).map tr.mainRow).map fun row => vecRowMemsegDelta w K row x).sum := by
      rw [List.map_map]; rfl
    rw [htrEq]
    unfold klaneRomEntries
    simp only [hK, ↓reduceIte]
    exact vecTrace_memseg_delta_eq_scalar hKgt
      (fun row hrow => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
        have h := hrows r (by simpa using List.mem_range.mp hr)
        simpa [List.getElem_map, List.getElem_range] using h) x

/-- Any `K`-lane ROM circuit for width `w' ≠ w` (both `< bound`) contributes `0`
to the trimmed `MEMSEG` channel at width `w`. -/
theorem klaneRom_memseg_trim_other_width {bound : Nat} (small : SmallCast F bound)
    (htags : 16 < bound) {w w' K' : Nat} (hw : w < bound) (hw' : w' < bound) (hne : w' ≠ w)
    (logBlowup extDegree : Nat) (tr' : CircuitTrace F)
    (hsat : CircuitAirSatisfied
      (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w' K' true)) tr')
    (x : F) :
    Finsupp.mapDomain trimZeros
      (circuitLedger (compileRetune logBlowup extDegree (lowerKLaneRomCircuit w' K' true)) tr')
      (trimZeros [(memsegTag : F), (w : F), x]) = 0 := by
  by_contra hnz
  obtain ⟨u, hu, heq⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hnz
  have hmemNe0 : (memsegTag : F) ≠ 0 := by
    intro h; have := small memsegTag htags h; simp [memsegTag] at this
  have hromNeMem : (romTag : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := romTag) (b := memsegTag) (by simp [romTag]; omega) htags h
    simp [romTag, memsegTag] at this
  rcases klaneRom_circuitLedger_support w' K' true logBlowup extDegree tr' hsat u hu with
    ⟨e, _, rfl⟩ | ⟨_, _, htail, hlen3⟩
  · have hh := trimZeros_head heq.symm (by simp) hmemNe0
    simp [encodeRom, Aiur.Tiling.Bridge.ROM] at hh
    exact hromNeMem hh
  · have hEq3 := trimZeros_inj_of_length (by simp [hlen3]) heq
    have hidx1 := congrArg (fun l => l.tail.head?) hEq3
    rw [htail] at hidx1
    simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hidx1
    exact hne (small.inj hw' hw hidx1)

end RomSoundness

/-! ## 6. `LoweredSystemSatisfied`, Row-to-Plan Bridge & End-to-End Composition -/

section PlanBridge

variable {F : Type} [Field F] [DecidableEq F]

/-- Trace slice corresponding to `lowerPlanFunctionsOrdered callableId plan`. -/
def fnTracesOf {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (traces : List (CircuitTrace F)) : List (CircuitTrace F) :=
  traces.take (lowerPlanFunctionsOrdered callableId plan).length

/-- Trace slice corresponding to `lowerFixedTables fixedMaps logBlowup`. -/
def tblTracesOf {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (logBlowup : Nat)
    (traces : List (CircuitTrace F)) : List (CircuitTrace F) :=
  (traces.drop (lowerPlanFunctionsOrdered callableId plan).length).take
    (lowerFixedTables (F := F) fixedMaps logBlowup).length

/-- Trace slice corresponding to `lowerRomCircuitsWithLayout romWidths segmented romLayout`. -/
def romTracesOf {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (logBlowup : Nat)
    (traces : List (CircuitTrace F)) : List (CircuitTrace F) :=
  traces.drop ((lowerPlanFunctionsOrdered callableId plan).length +
    (lowerFixedTables (F := F) fixedMaps logBlowup).length)

/-- **Exact AIR + LogUp Trace Satisfaction Predicate (`LoweredSystemSatisfied`)**
for a complete system produced by `Aiur.MultiStarkSpec.lowerFullSystem`:
1. Every row of every compiled and retuned circuit (functions, fixed tables, and
   scalar/vectorized ROMs) satisfies all its lowered polynomial constraints;
2. Every non-empty fixed table has trusted preprocessed rows matching
   `source.mapClaims.map (encode callableId)` (empty tables are forced silent by AIR);
3. Every chip of `plan` (singles and group members) passes `checkChipEnables`;
4. Any external boundary ledger (empty when `segmented = false`, or `MEMSEG`
   preamble intervals when `segmented = true`) is supported strictly on `memsegTag`;
5. The global trimmed LogUp multiset balance across all circuits of
   `lowerFullSystem`, the public root claim, and `boundaryLedger` vanishes. -/
structure LoweredSystemSatisfied {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat)
    (logBlowup : Nat) (segmented : Bool) (extDegree : Nat) (romLayout : RomLayout)
    (root : Circuit.Message F) (boundaryLedger : Ledger F)
    (traces : List (CircuitTrace F)) : Prop where
  airOk : List.Forall₂ CircuitAirSatisfied
    (lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout)
    traces
  fixedValid : FixedTablesValid source callableId
    (lowerFixedTables (F := F) fixedMaps logBlowup)
    (tblTracesOf callableId plan fixedMaps logBlowup traces)
  enablesOk : ∀ c ∈ allChips plan, checkChipEnables c = true
  boundaryOk : ∀ t, boundaryLedger t ≠ 0 → t.head? = some (memsegTag : F)
  logupBalanced :
    Finsupp.mapDomain trimZeros
      ((List.zipWith circuitLedger
          (lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout)
          traces).sum +
        Finsupp.single (encode callableId root) 1 +
        boundaryLedger) = 0

/-- Split `LoweredSystemSatisfied` into its function, fixed-table, and ROM slices. -/
theorem LoweredSystemSatisfied.split {source : Circuit.System F} {id : String → Except String Nat}
    {callableId : String → Nat} {plan : Grouping.Plan source id}
    {fixedMaps : List FixedMapMeta} {romWidths : List Nat}
    {logBlowup : Nat} {segmented : Bool} {extDegree : Nat} {romLayout : RomLayout}
    {root : Circuit.Message F} {boundaryLedger : Ledger F}
    {traces : List (CircuitTrace F)}
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup segmented
      extDegree romLayout root boundaryLedger traces) :
    let fnCs := (lowerPlanFunctionsOrdered callableId plan).map (compileRetune logBlowup extDegree)
    let tblCs := (lowerFixedTables (F := F) fixedMaps logBlowup).map (compileRetune logBlowup extDegree)
    let romCs := (lowerRomCircuitsWithLayout (F := F) romWidths segmented romLayout).map
      (compileRetune logBlowup extDegree)
    let fnTrs := fnTracesOf callableId plan traces
    let tblTrs := tblTracesOf callableId plan fixedMaps logBlowup traces
    let romTrs := romTracesOf callableId plan fixedMaps logBlowup traces
    List.Forall₂ CircuitAirSatisfied fnCs fnTrs ∧
    List.Forall₂ CircuitAirSatisfied tblCs tblTrs ∧
    List.Forall₂ CircuitAirSatisfied romCs romTrs ∧
    (List.zipWith circuitLedger
        (lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout)
        traces).sum =
      (List.zipWith circuitLedger fnCs fnTrs).sum +
      (List.zipWith circuitLedger tblCs tblTrs).sum +
      (List.zipWith circuitLedger romCs romTrs).sum ∧
    systemLookupBudget fnCs fnTrs ≤
      systemLookupBudget
        (lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout)
        traces := by
  dsimp only
  set fnIn := lowerPlanFunctionsOrdered callableId plan
  set tblIn := lowerFixedTables (F := F) fixedMaps logBlowup
  set romIn := lowerRomCircuitsWithLayout (F := F) romWidths segmented romLayout
  set cr := compileRetune (F := F) logBlowup extDegree
  have hfull :
      lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout =
      (fnIn.map cr ++ tblIn.map cr) ++ romIn.map cr := by
    rw [lowerFullSystem_eq_map callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout,
      List.map_append, List.map_append]
  have hair := hsat.airOk
  rw [hfull] at hair
  obtain ⟨hFT, hRom⟩ := forall₂_append_left_split hair
  obtain ⟨hFn, hTbl⟩ := forall₂_append_left_split hFT
  have hlenFn : (fnIn.map cr).length = fnIn.length := List.length_map _
  have hlenTbl : (tblIn.map cr).length = tblIn.length := List.length_map _
  have hlenFT : (fnIn.map cr ++ tblIn.map cr).length = fnIn.length + tblIn.length := by
    simp [hlenFn, hlenTbl]
  have hfnEq : (traces.take (fnIn.map cr ++ tblIn.map cr).length).take (fnIn.map cr).length =
      fnTracesOf callableId plan traces := by
    unfold fnTracesOf
    rw [List.take_take, hlenFT, hlenFn, Nat.min_eq_left (Nat.le_add_right _ _)]
  have htblEq : (traces.take (fnIn.map cr ++ tblIn.map cr).length).drop (fnIn.map cr).length =
      tblTracesOf callableId plan fixedMaps logBlowup traces := by
    unfold tblTracesOf
    rw [List.drop_take, hlenFT, hlenFn, Nat.add_sub_cancel_left]
  have hromEq : traces.drop (fnIn.map cr ++ tblIn.map cr).length =
      romTracesOf callableId plan fixedMaps logBlowup traces := by
    unfold romTracesOf
    rw [hlenFT]
  rw [hfnEq] at hFn
  rw [htblEq] at hTbl
  rw [hromEq] at hRom
  have hlenAll : traces.length = ((fnIn.map cr ++ tblIn.map cr) ++ romIn.map cr).length :=
    hair.length_eq.symm
  have hlenFT' : (traces.take (fnIn.map cr ++ tblIn.map cr).length).length =
      (fnIn.map cr ++ tblIn.map cr).length := by
    rw [List.length_take]
    rw [List.length_append] at hlenAll
    omega
  refine ⟨hFn, hTbl, hRom, ?_, ?_⟩
  · rw [hfull, zipWith_append_left_split circuitLedger hlenAll,
      zipWith_append_left_split circuitLedger hlenFT', hfnEq, htblEq, hromEq,
      List.sum_append, List.sum_append]
  · unfold systemLookupBudget
    rw [hfull, zipWith_append_left_split _ hlenAll, zipWith_append_left_split _ hlenFT',
      hfnEq, htblEq, hromEq, List.sum_append, List.sum_append]
    omega

/-! ### Row-to-Plan Bridge (`lowerFullSystem_row_implies_inspectRow`) -/

/-- **Row-to-Plan Bridge (`lowerFullSystem_row_implies_inspectRow`):**
For every function circuit `inp ∈ lowerPlanFunctionsOrdered callableId plan`
(compiled & retuned via `compileRetune`) and every trace row `r < tr.height`
satisfying its lowered AIR constraints (under `plan.WellFormedActivation` and
`(circuitNames plan).Nodup`):
- If `inp` is a single chip `c ∈ plan.singles`, then `tr.mainRow r c.numVars ∈ {0, 1}`,
  padding rows (`= 0`) force multiplicity `0` and pass `plan.inspectRow rom row = .ok none`
  unconditionally, and active rows (`= 1`) with valid memory lookups pass
  `plan.inspectRow rom row = .ok (some ((Activation.compile c).conclusion w, (Activation.compile c).requirements w))`.
- If `inp` is a grouped layout `p ∈ plan.groups`, then `g.activation.denote w ∈ {0, 1}`,
  padding rows (`= 0`) force multiplicity `0` and pass `plan.inspectRow rom row = .ok none`
  unconditionally, and active rows (`= 1`) select a unique member `m ∈ g.members`
  whose valid memory lookups yield
  `plan.inspectRow rom row = .ok (some ((Activation.compile m.origin).conclusion (project m w), (Activation.compile m.origin).requirements (project m w)))`. -/
theorem lowerFullSystem_row_implies_inspectRow {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (activated : plan.WellFormedActivation) (names : (circuitNames plan).Nodup)
    (rom : WireROM F) (logBlowup extDegree : Nat)
    {inp : CircuitInput F} (hinp : inp ∈ lowerPlanFunctionsOrdered callableId plan)
    (tr : CircuitTrace F) (r : Nat)
    (hsat : CircuitRowSatisfied (compileRetune logBlowup extDegree inp) tr r) :
    let w := tr.mainRow r
    (∃ c ∈ plan.singles, inp = lowerSingleChip callableId (Activation.compile c) c.numVars ∧
      let row := Row.ofAssignment c.name (c.numVars + 1) w
      (w c.numVars = 0 ∨ w c.numVars = 1) ∧
      (w c.numVars = 0 → w (c.numVars + 1) = 0 ∧ plan.inspectRow rom row = .ok none) ∧
      (w c.numVars = 1 →
        (∀ m ∈ (Activation.compile c).memory, MemoryLookup.Valid rom w m) →
        plan.inspectRow rom row =
          .ok (some ((Activation.compile c).conclusion w, (Activation.compile c).requirements w)))) ∨
    (∃ p ∈ plan.groups, inp = lowerGroupLayout p.checked.layout ∧
      let g := p.checked.layout
      let row := Row.ofAssignment g.name g.width w
      (g.activation.denote w = 0 ∨ g.activation.denote w = 1) ∧
      (g.activation.denote w = 0 → w g.width = 0 ∧ plan.inspectRow rom row = .ok none) ∧
      (g.activation.denote w = 1 →
        ∃ m ∈ g.members, w m.selector = 1 ∧
          ((∀ l ∈ (Activation.compile m.origin).memory, MemoryLookup.Valid rom (project m w) l) →
            plan.inspectRow rom row =
              .ok (some ((Activation.compile m.origin).conclusion (project m w),
                (Activation.compile m.origin).requirements (project m w)))))) := by
  dsimp only
  set w := tr.mainRow r
  rcases mem_lowerPlanFunctionsOrdered callableId plan hinp with ⟨c, hc, rfl⟩ | ⟨p, hp, rfl⟩
  · left
    refine ⟨c, hc, rfl, ?_, ?_, ?_⟩
    · have hholds := (lowerSingleChip_rowSatisfied_iff callableId c logBlowup extDegree tr r).mp hsat
      have hactSat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w :=
        fun q hq => hholds q (List.mem_append_left _ hq)
      have hb := hactSat (Activation.boolean c.numVars) (by simp [Activation.compile])
      simpa [Activation.boolean, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] using hb
    · intro hoff
      have hholds := (lowerSingleChip_rowSatisfied_iff callableId c logBlowup extDegree tr r).mp hsat
      have hactSat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w :=
        fun q hq => hholds q (List.mem_append_left _ hq)
      have hpad : (1 - w c.numVars) * w (c.numVars + 1) = 0 := by
        simpa [Scalar.Circuit.ArithExpr.denote] using
          hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hmult0 : w (c.numVars + 1) = 0 := by rw [hoff, sub_zero, one_mul] at hpad; exact hpad
      refine ⟨hmult0, ?_⟩
      obtain ⟨_, formedA⟩ := activated c hc
      have hmemVac : ∀ m ∈ (Activation.compile c).memory, MemoryLookup.Valid rom w m := by
        intro m hm henab
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
        have hguard : (Activation.memory c.numVars m0).enable ∈ Activation.guards c :=
          List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨m0, hm0, rfl⟩))
        have hsil := hactSat (Activation.silent c.numVars (Activation.memory c.numVars m0).enable)
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hguard, rfl⟩)))
        simp only [Activation.silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote,
          hoff, sub_zero, one_mul] at hsil
        exact absurd (hsil.symm.trans henab) zero_ne_one
      have hfinite := Chip.finiteAssignment formedA w rom
      have hvalidA : (Activation.compile c).ValidAssignment rom w := ⟨hactSat, hmemVac⟩
      have hcheck : (Activation.compile c).checkRow rom (Row.ofAssignment c.name (c.numVars + 1) w) =
          .ok ((Activation.compile c).conclusion w, (Activation.compile c).requirements w) := by
        apply Chip.checkRow_iff.mpr
        refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, hfinite.1.mp hvalidA⟩, ?_⟩
        exact Prod.ext hfinite.2.1 hfinite.2.2
      have hsel0 : (Row.ofAssignment c.name (c.numVars + 1) w).assignment c.numVars = 0 := by
        rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]; exact hoff
      have hnamed : (Row.ofAssignment c.name (c.numVars + 1) w).chip = c.name := rfl
      simp only [Grouping.Plan.inspectRow, hnamed, Aiur.Tiling.Bridge.find_single plan hc,
        hcheck, hsel0, zero_ne_one, ↓reduceIte]
    · intro hon hmem
      have hholds := (lowerSingleChip_rowSatisfied_iff callableId c logBlowup extDegree tr r).mp hsat
      have hactSat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w :=
        fun q hq => hholds q (List.mem_append_left _ hq)
      obtain ⟨_, formedA⟩ := activated c hc
      have hfinite := Chip.finiteAssignment formedA w rom
      have hvalidA : (Activation.compile c).ValidAssignment rom w := ⟨hactSat, hmem⟩
      have hcheck : (Activation.compile c).checkRow rom (Row.ofAssignment c.name (c.numVars + 1) w) =
          .ok ((Activation.compile c).conclusion w, (Activation.compile c).requirements w) := by
        apply Chip.checkRow_iff.mpr
        refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, hfinite.1.mp hvalidA⟩, ?_⟩
        exact Prod.ext hfinite.2.1 hfinite.2.2
      have hsel1 : (Row.ofAssignment c.name (c.numVars + 1) w).assignment c.numVars = 1 := by
        rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]; exact hon
      have hnamed : (Row.ofAssignment c.name (c.numVars + 1) w).chip = c.name := rfl
      simp only [Grouping.Plan.inspectRow, hnamed, Aiur.Tiling.Bridge.find_single plan hc,
        hcheck, hsel1, ↓reduceIte]
  · right
    set g := p.checked.layout
    have hholds := (lowerGroupLayout_rowSatisfied_iff g logBlowup extDegree tr r).mp hsat
    have hvalid : Scalar.Circuit.Satisfies g.constraints w :=
      fun q hq => hholds q (List.mem_append_left _ hq)
    have hpad : (1 - g.activation.denote w) * w g.width = 0 := by
      simpa [Scalar.Circuit.ArithExpr.denote] using
        hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨p, hp, rfl, ?_, ?_, ?_⟩
    · have h := Grouping.exclusive_sum (g.exclusive p.checked.certificate.shapes w hvalid)
      simpa [Grouping.Layout.activation, Grouping.sum_denote, Function.comp_def,
        Scalar.Circuit.ArithExpr.denote] using h
    · intro hoff
      have hmult0 : w g.width = 0 := by rw [hoff, sub_zero, one_mul] at hpad; exact hpad
      refine ⟨hmult0, ?_⟩
      have hfin := p.checked.finite
      have hfn : (fun i => Scalar.Circuit.ArithExpr.denote w (Grouping.restrict g.width i)) =
          (Row.ofAssignment g.name g.width w).assignment :=
        funext fun i => Grouping.restrict_denote g.width i w g.name
      have hconR : Scalar.Circuit.Satisfies g.constraints (Row.ofAssignment g.name g.width w).assignment := by
        intro q hq
        have hsame := (hfin.1 q hq).denote w
        simp only [Optimized.Polynomial.denote_subst] at hsame
        change q.denote (fun i => Scalar.Circuit.ArithExpr.denote w (Grouping.restrict g.width i)) =
          q.denote w at hsame
        rw [hfn] at hsame
        exact hsame.trans (hvalid q hq)
      have hactR : g.activation.denote (Row.ofAssignment g.name g.width w).assignment = 0 := by
        have hsame := hfin.2.1.denote w
        simp only [Optimized.Polynomial.denote_subst] at hsame
        change g.activation.denote (fun i => Scalar.Circuit.ArithExpr.denote w (Grouping.restrict g.width i)) =
          g.activation.denote w at hsame
        rw [hfn] at hsame
        exact hsame.trans hoff
      obtain ⟨_, n2, disj⟩ := List.nodup_append.mp names
      have hnoSingle : plan.singles.find? (·.name == g.name) = none := by
        apply List.find?_eq_none.mpr
        intro c hc same
        simp only [beq_iff_eq] at same
        exact disj _ (List.mem_map.mpr ⟨c, hc, rfl⟩) _ (List.mem_map.mpr ⟨p, hp, rfl⟩) same
      have hgrp : plan.groups.find? (·.checked.layout.name == g.name) = some p := by
        cases hf : plan.groups.find? (·.checked.layout.name == g.name) with
        | none => exact absurd (List.find?_eq_none.mp hf p hp) (by simp [g])
        | some q =>
            have hq := List.mem_of_find?_eq_some hf
            have hname : q.checked.layout.name = g.name := by simpa using List.find?_some hf
            rw [List.inj_on_of_nodup_map n2 hq hp hname]
      unfold Grouping.Plan.inspectRow
      have hchipName : (Row.ofAssignment g.name g.width w).chip = g.name := rfl
      rw [hchipName, hnoSingle]
      simp only [hgrp]
      unfold Grouping.Layout.inspectRow
      dsimp only [g] at hconR hactR
      simp only [Row.ofAssignment_length, hconR, hactR, and_self, ↓reduceIte]
    · intro hon
      obtain ⟨m, hm, hsel, _⟩ := g.select p.checked.certificate.shapes w hvalid hon
      exact ⟨m, hm, hsel, fun hmem =>
        group_inspect plan names hp hm hvalid hon hsel hmem⟩

/-! ### Unified Physical Function Rows (`FnRow`) & Memo-Checker Bridge -/

/-- A physical function row extracted from `lowerPlanFunctionsOrdered`: either an
activated single-chip row or a grouped-layout row. -/
inductive FnRow (F : Type) [Field F] [DecidableEq F] {source : Circuit.System F}
    {id : String → Except String Nat} (plan : Grouping.Plan source id) where
  | single (c : Chip F) (hc : c ∈ plan.singles) (w : Nat → F)
  | group (p : Grouping.Packed F id) (hp : p ∈ plan.groups) (w : Nat → F)

namespace FnRow

variable {source : Circuit.System F} {id : String → Except String Nat}
  {plan : Grouping.Plan source id}

def Holds (callableId : String → Nat) : FnRow F plan → Prop
  | .single c _ w => (Aiur.Tiling.Bridge.lower callableId c).Holds w
  | .group p _ w => (lowerGroup p.checked.layout).Holds w

noncomputable def ledger (callableId : String → Nat) : FnRow F plan → Ledger F
  | .single c _ w => (Aiur.Tiling.Bridge.lower callableId c).rowLedger w
  | .group p _ w => (lowerGroup p.checked.layout).rowLedger w

/-- Number of non-receive (push) lookups on this physical function row. -/
def pushCount : FnRow F plan → Nat
  | .single c _ _ => c.sends.length + c.memory.length
  | .group p _ _ => p.checked.layout.sends.length

/-- Receive-pull contribution of this row at trimmed tuple `k`. -/
def recvVal (callableId : String → Nat) (k : List F) : FnRow F plan → F
  | .single c _ w =>
      if trimZeros (encode callableId (c.conclusion w)) = k then -w (c.numVars + 1) else 0
  | .group p _ w =>
      if trimZeros (p.checked.layout.receive.map (·.denote w)) = k then
        -w p.checked.layout.width
      else 0

/-- Push contributions (sends + memory, or shared group slots) of this row at trimmed tuple `k`. -/
def pushVals (callableId : String → Nat) (k : List F) : FnRow F plan → List F
  | .single c _ w =>
      ((Activation.compile c).sends.map fun s =>
        if trimZeros (encode callableId (s.message w)) = k then s.enable.denote w else 0) ++
      ((Activation.compile c).memory.map fun m =>
        if trimZeros (encodeRom (m.address.denote w, m.value.map (Circuit.ArithExpr.denote w))) = k
        then m.enable.denote w else 0)
  | .group p _ w =>
      p.checked.layout.sends.map fun s =>
        if trimZeros (s.args.map (·.denote w)) = k then s.enable.denote w else 0

theorem pushVals_length (callableId : String → Nat) (k : List F) (row : FnRow F plan) :
    (row.pushVals callableId k).length = row.pushCount := by
  cases row with
  | single c _ w => simp [pushVals, pushCount, Activation.compile]
  | group p _ w => simp [pushVals, pushCount]

theorem trim_ledger_apply (callableId : String → Nat) (k : List F) (row : FnRow F plan) :
    Finsupp.mapDomain trimZeros (row.ledger callableId) k =
      row.recvVal callableId k + (row.pushVals callableId k).sum := by
  cases row with
  | single c _ w =>
      simp only [ledger, recvVal, pushVals]
      rw [Aiur.Tiling.Grouped.lower_instLedger, Aiur.Tiling.Grouped.instLedger_trim,
        List.sum_append, add_assoc]
      rfl
  | group p _ w =>
      simp only [ledger, recvVal, pushVals, lowerGroup, Tiling.Circuit.rowLedger,
        List.map_cons, List.sum_cons, Finsupp.mapDomain_add, Finsupp.add_apply,
        Aiur.Tiling.Grouped.mapDomain_list_sum, Tiling.System.ledger_list_sum,
        List.map_map, Function.comp_def, Tiling.Lookup.entry, Tiling.Lookup.tuple,
        Finsupp.mapDomain_single, Finsupp.single_apply, Scalar.Circuit.ArithExpr.denote, zero_sub]

/-- Every push value of a valid `FnRow` is `0` or `1` under `checkChipEnables`. -/
theorem pushVals_bits (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (henables : ∀ c ∈ allChips plan, checkChipEnables c = true)
    {row : FnRow F plan} (hholds : row.Holds callableId) (k : List F) :
    ∀ x ∈ row.pushVals callableId k, x = 0 ∨ x = 1 := by
  cases row with
  | single c hc w =>
      have hactSat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w :=
        fun q hq => hholds q (List.mem_append_left _ hq)
      have hbool := boolean_of_checkChipEnables (henables c (List.mem_append_left _ hc)) hactSat
      intro x hx
      simp only [pushVals, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨s, hs, rfl⟩ | ⟨m, hm, rfl⟩
      · split_ifs
        · exact hbool.1 s hs
        · exact Or.inl rfl
      · split_ifs
        · exact hbool.2 m hm
        · exact Or.inl rfl
  | group p hp w =>
      have htr : CircuitRowSatisfied
          (compileRetune 0 1 (lowerGroupLayout p.checked.layout)) ⟨1, fun _ => w, fun _ _ => 0⟩ 0 :=
        (lowerGroupLayout_rowSatisfied_iff p.checked.layout 0 1 ⟨1, fun _ => w, fun _ _ => 0⟩ 0).mpr hholds
      have hok : ∀ c ∈ p.sources, checkChipEnables c = true := fun c hc =>
        henables c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩))
      have hslotBool := (checkChipEnables_group_unit_weight callableId idOk p hok 0 1
        ⟨1, fun _ => w, fun _ _ => 0⟩ 0 htr).2.2.1
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      split_ifs
      · exact hslotBool s hs
      · exact Or.inl rfl

/-- Whether a physical `FnRow` is active (non-padding). -/
def isActive : FnRow F plan → Bool
  | .single c _ w => decide (w c.numVars = 1)
  | .group p _ w => decide (p.checked.layout.activation.denote w = 1)

/-- For an active group row, extract the unique selected member and its projected assignment;
for an active single row, return `(c, w)`. -/
def activeChipAssign (row : FnRow F plan) :
    Option (Chip F × (Nat → F)) :=
  match row with
  | .single c _ w => if w c.numVars = 1 then some (c, w) else none
  | .group p _ w =>
      if p.checked.layout.activation.denote w = 1 then
        match p.checked.layout.members.find? (fun m => decide (w m.selector = 1)) with
        | some m => some (m.origin, project m w)
        | none => none
      else none

/-- An active valid `FnRow` produces `some (c, a)` with `c ∈ allChips plan`,
`a c.numVars = 1`, and `(Activation.compile c).constraints` satisfied at `a`. -/
theorem activeChipAssign_spec (callableId : String → Nat) {row : FnRow F plan}
    (hholds : row.Holds callableId) (hact : row.isActive = true) :
    ∃ c a, row.activeChipAssign = some (c, a) ∧ c ∈ allChips plan ∧
      a c.numVars = 1 ∧ Scalar.Circuit.Satisfies (Activation.compile c).constraints a := by
  cases row with
  | single c hc w =>
      simp only [isActive, decide_eq_true_eq] at hact
      refine ⟨c, w, by simp [activeChipAssign, hact], List.mem_append_left _ hc, hact, ?_⟩
      exact fun q hq => hholds q (List.mem_append_left _ hq)
  | group p hp w =>
      simp only [isActive, decide_eq_true_eq] at hact
      have hvalid : Scalar.Circuit.Satisfies p.checked.layout.constraints w :=
        fun q hq => hholds q (List.mem_append_left _ hq)
      obtain ⟨m, hm, hsel, _⟩ :=
        p.checked.layout.select p.checked.certificate.shapes w hvalid hact
      cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
      | none =>
          have := List.find?_eq_none.mp hf m hm
          simp [hsel] at this
      | some m' =>
          have hm' := List.mem_of_find?_eq_some hf
          have hsel' : w m'.selector = 1 := by simpa using List.find?_some hf
          refine ⟨m'.origin, project m' w, by simp [activeChipAssign, hact, hf],
            Aiur.Tiling.Grouped.origin_allChips plan hp hm', ?_,
            Aiur.Tiling.Grouped.member_sat p.checked hm' hvalid hsel'⟩
          rw [Aiur.Tiling.Grouped.project_selector p.checked hm']
          exact hsel'

/-- Any `FnRow` with `recvVal callableId k ≠ 0` is active and its `activeChipAssign`
concludes a message encoding to `k` under `trimZeros`. -/
theorem active_of_recvVal_ne_zero (callableId : String → Nat)
    (idOk : ∀ x n, id x = .ok n → n = callableId x)
    {row : FnRow F plan} (hholds : row.Holds callableId) {k : List F}
    (hne : row.recvVal callableId k ≠ 0) :
    ∃ c a, row.isActive = true ∧ row.activeChipAssign = some (c, a) ∧
      c ∈ allChips plan ∧ a c.numVars = 1 ∧
      trimZeros (encode callableId (c.conclusion a)) = k := by
  cases row with
  | single c hc w =>
      simp only [recvVal] at hne
      split_ifs at hne with heq
      · have hmult : w (c.numVars + 1) ≠ 0 := fun h => hne (by simp [h])
        have hpad : (1 - w c.numVars) * w (c.numVars + 1) = 0 := by
          simpa [Scalar.Circuit.ArithExpr.denote] using
            hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
        have hon : w c.numVars = 1 := by
          rcases mul_eq_zero.mp hpad with h | h
          · exact (sub_eq_zero.mp h).symm
          · exact absurd h hmult
        exact ⟨c, w, by simp [isActive, hon], by simp [activeChipAssign, hon],
          List.mem_append_left _ hc, hon, heq⟩
      · exact absurd rfl hne
  | group p hp w =>
      simp only [recvVal] at hne
      split_ifs at hne with heq
      · have hmult : w p.checked.layout.width ≠ 0 := fun h => hne (by simp [h])
        have hvalid : Scalar.Circuit.Satisfies p.checked.layout.constraints w :=
          fun q hq => hholds q (List.mem_append_left _ hq)
        have hpad : (1 - p.checked.layout.activation.denote w) * w p.checked.layout.width = 0 := by
          simpa [Scalar.Circuit.ArithExpr.denote] using
            hholds _ (List.mem_append_right _ (List.mem_singleton_self _))
        have hon : p.checked.layout.activation.denote w = 1 := by
          rcases mul_eq_zero.mp hpad with h | h
          · exact (sub_eq_zero.mp h).symm
          · exact absurd h hmult
        obtain ⟨m0, hm0, hsel0, _⟩ :=
          p.checked.layout.select p.checked.certificate.shapes w hvalid hon
        cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
        | none =>
            have := List.find?_eq_none.mp hf m0 hm0
            simp [hsel0] at this
        | some m =>
            have hm := List.mem_of_find?_eq_some hf
            have hsel : w m.selector = 1 := by simpa using List.find?_some hf
            obtain ⟨_, provided, _, hmsgs, hsame⟩ :=
              Aiur.Tiling.Grouped.packet_active p.checked m hm w hvalid hon hsel
            obtain ⟨hrecv, _⟩ := Aiur.Tiling.Grouped.messages_ok callableId idOk hmsgs
            have htrimRecv : trimZeros (encode callableId (m.origin.conclusion (project m w))) =
                trimZeros (p.checked.layout.receive.map (·.denote w)) := by
              rw [Aiur.Tiling.Grouped.trim_of_words hsame.1, hrecv,
                ← Aiur.Tiling.Bridge.receive_tuple callableId m.origin 0]
              rfl
            refine ⟨m.origin, project m w, by simp [isActive, hon],
              by simp [activeChipAssign, hon, hf],
              Aiur.Tiling.Grouped.origin_allChips plan hp hm, ?_, htrimRecv.trans heq⟩
            rw [Aiur.Tiling.Grouped.project_selector p.checked hm]; exact hsel
      · exact absurd rfl hne

/-- An enabled memory lookup of an active `FnRow` produces `(1 : F)` in `row.pushVals`. -/
theorem one_mem_pushVals_of_memory (callableId : String → Nat)
    (idOk : ∀ x n, id x = .ok n → n = callableId x)
    {row : FnRow F plan} (hholds : row.Holds callableId)
    {c : Chip F} {a : Nat → F} (hact : row.activeChipAssign = some (c, a))
    {m : MemoryLookup F} (hm : m ∈ (Activation.compile c).memory)
    (hen : m.enable.denote a = 1) :
    (1 : F) ∈ row.pushVals callableId
      (trimZeros (encodeRom (m.address.denote a, m.value.map (Circuit.ArithExpr.denote a)))) := by
  cases row with
  | single c' hc' w =>
      simp only [activeChipAssign] at hact
      split_ifs at hact with hon
      simp only [Option.some.injEq, Prod.mk.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [pushVals, List.mem_append, List.mem_map]
      exact Or.inr ⟨m, hm, by simp [hen]⟩
  | group p hp w =>
      simp only [activeChipAssign] at hact
      split_ifs at hact with hon
      cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
      | none => simp [hf] at hact
      | some mem =>
          simp only [hf, Option.some.injEq, Prod.mk.injEq] at hact
          obtain ⟨rfl, rfl⟩ := hact
          have hmemIn := List.mem_of_find?_eq_some hf
          have hsel : w mem.selector = 1 := by simpa using List.find?_some hf
          have hvalid : Scalar.Circuit.Satisfies p.checked.layout.constraints w :=
            fun q hq => hholds q (List.mem_append_left _ hq)
          obtain ⟨_, provided, required, hmsgs, hsame⟩ :=
            Aiur.Tiling.Grouped.packet_active p.checked mem hmemIn w hvalid hon hsel
          obtain ⟨_, hreqs⟩ := Aiur.Tiling.Grouped.messages_ok callableId idOk hmsgs
          have hselProj : project mem w mem.origin.numVars = 1 := by
            rw [Aiur.Tiling.Grouped.project_selector p.checked hmemIn]; exact hsel
          -- Find the index `idx` of `m` in `required` (offset by `mem.origin.sends.length`).
          obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
          obtain ⟨mi, hmi, rfl⟩ := List.getElem_of_mem hm0
          set idx := mem.origin.sends.length + mi
          have hreqLen : required.length = mem.origin.sends.length + mem.origin.memory.length :=
            Grouping.messages_required_length hmsgs
          have hidxLt : idx < required.length := by omega
          have hreqAt : (Grouping.lookupAt required idx).enable = mem.origin.memory[mi].enable ∧
              (Grouping.lookupAt required idx).args = (Aiur.Tiling.Bridge.memoryLookup mem.origin.memory[mi]).args := by
            have hmapEq := congrArg (fun l => l[idx]?) hreqs
            rw [List.getElem?_map, List.getElem?_eq_getElem hidxLt,
              List.getElem?_append_right (by simp [idx]), List.length_map,
              Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem hmi] at hmapEq
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmapEq
            simpa [Grouping.lookupAt, hidxLt] using hmapEq
          have hen0 : (Grouping.lookupAt required idx).enable.denote (project mem w) = 1 := by
            rw [hreqAt.1]
            simpa [Activation.memory, Activation.polynomial_active _ _ _ hselProj] using hen
          have hslotLt : Grouping.slotOf mem.slotMap idx < p.checked.layout.sends.length :=
            hsame.2.1 idx hidxLt
          set s := Grouping.slotOf mem.slotMap idx
          have hidxInB : idx ∈ Grouping.bucketOf mem.slotMap required.length s := by
            unfold Grouping.bucketOf
            exact List.mem_filter.mpr ⟨List.mem_range.mpr hidxLt, by simp [s]⟩
          have hsl := hsame.2.2 s
          dsimp only at hsl
          have hslotEq : p.checked.layout.slot s = p.checked.layout.sends[s] := by
            simp [Grouping.Layout.slot, hslotLt]
          have hslotMatch : (p.checked.layout.slot s).enable.denote w = 1 ∧
              trimZeros ((p.checked.layout.slot s).args.map (·.denote w)) =
                trimZeros ((Grouping.lookupAt required idx).args.map (·.denote (project mem w))) := by
            generalize hB : Grouping.bucketOf mem.slotMap required.length s = B at hsl hidxInB
            cases B with
            | nil => cases hidxInB
            | cons k1 rest =>
                cases rest with
                | nil =>
                    simp only [List.mem_singleton] at hidxInB
                    subst hidxInB
                    exact ⟨hsl.1.trans hen0, Aiur.Tiling.Grouped.trim_of_words hsl.2⟩
                | cons k2 tail =>
                    rcases hsl with ⟨_, _, hall0⟩ | ⟨k, _, _, hrest0, hs1, hargs⟩
                    · exfalso
                      have h0 : (Grouping.lookupAt required idx).enable.denote (project mem w) = 0 :=
                        hall0 idx hidxInB
                      rw [hen0] at h0
                      exact one_ne_zero h0
                    · have hkEq : idx = k := by
                        by_contra hne
                        have h0 : (Grouping.lookupAt required idx).enable.denote (project mem w) = 0 :=
                          hrest0 idx hidxInB hne
                        rw [hen0] at h0
                        exact one_ne_zero h0
                      subst hkEq
                      exact ⟨hs1, Aiur.Tiling.Grouped.trim_of_words hargs⟩
          have htuple : (Grouping.lookupAt required idx).args.map (·.denote (project mem w)) =
              encodeRom ((Activation.memory mem.origin.numVars mem.origin.memory[mi]).address.denote (project mem w),
                (Activation.memory mem.origin.numVars mem.origin.memory[mi]).value.map
                  (Circuit.ArithExpr.denote (project mem w))) := by
            rw [hreqAt.2]
            simpa [Activation.memory, Tiling.Lookup.tuple] using
              Aiur.Tiling.Bridge.memory_tuple mem.origin.memory[mi] (project mem w)
          simp only [pushVals, List.mem_map]
          refine ⟨p.checked.layout.sends[s], List.getElem_mem hslotLt, ?_⟩
          rw [← hslotEq, hslotMatch.1, hslotMatch.2, htuple]
          simp

/-- A required send of an active `FnRow` produces `(1 : F)` in `row.pushVals`. -/
theorem one_mem_pushVals_of_requirement (callableId : String → Nat)
    (idOk : ∀ x n, id x = .ok n → n = callableId x)
    {row : FnRow F plan} (hholds : row.Holds callableId)
    {c : Chip F} {a : Nat → F} (hact : row.activeChipAssign = some (c, a))
    {q : Message F} (hq : q ∈ (Activation.compile c).requirements a) :
    (1 : F) ∈ row.pushVals callableId (trimZeros (encode callableId q)) := by
  obtain ⟨s0, hs0, rfl, s', hs', hen, hmsg⟩ := Aiur.Tiling.Bridge.requirement_send hq
  cases row with
  | single c' hc' w =>
      simp only [activeChipAssign] at hact
      split_ifs at hact with hon
      simp only [Option.some.injEq, Prod.mk.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [pushVals, List.mem_append, List.mem_map]
      exact Or.inl ⟨s', hs', by simp [hmsg, hen]⟩
  | group p hp w =>
      simp only [activeChipAssign] at hact
      split_ifs at hact with hon
      cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
      | none => simp [hf] at hact
      | some mem =>
          simp only [hf, Option.some.injEq, Prod.mk.injEq] at hact
          obtain ⟨rfl, rfl⟩ := hact
          have hmemIn := List.mem_of_find?_eq_some hf
          have hsel : w mem.selector = 1 := by simpa using List.find?_some hf
          have hvalid : Scalar.Circuit.Satisfies p.checked.layout.constraints w :=
            fun p' hp' => hholds p' (List.mem_append_left _ hp')
          obtain ⟨_, provided, required, hmsgs, hsame⟩ :=
            Aiur.Tiling.Grouped.packet_active p.checked mem hmemIn w hvalid hon hsel
          obtain ⟨_, hreqs⟩ := Aiur.Tiling.Grouped.messages_ok callableId idOk hmsgs
          have hselProj : project mem w mem.origin.numVars = 1 := by
            rw [Aiur.Tiling.Grouped.project_selector p.checked hmemIn]; exact hsel
          obtain ⟨si, hsi, rfl⟩ := List.getElem_of_mem hs0
          have hreqLen : required.length = mem.origin.sends.length + mem.origin.memory.length :=
            Grouping.messages_required_length hmsgs
          have hq' : mem.origin.sends[si].message (project mem w) ∈
              (Activation.compile mem.origin).requirements (project mem w) := hq
          rw [Activation.requirements_active _ _ hselProj] at hq'
          simp only [Chip.requirements, List.mem_filterMap] at hq'
          obtain ⟨sAct, hsAct, hsome⟩ := hq'
          split at hsome
          · rename_i henAct
            simp only [Option.some.injEq] at hsome
            obtain ⟨si', hsi', rfl⟩ := List.getElem_of_mem hsAct
            have hidxLt' : si' < required.length := by omega
            have hreqAt' : (Grouping.lookupAt required si').enable = mem.origin.sends[si'].enable ∧
                (Grouping.lookupAt required si').args =
                  (Aiur.Tiling.Bridge.sendLookup callableId mem.origin.sends[si']).args := by
              have hmapEq := congrArg (fun l => l[si']?) hreqs
              rw [List.getElem?_map, List.getElem?_eq_getElem hidxLt',
                List.getElem?_append_left (by simp [hsi']), List.getElem?_map,
                List.getElem?_eq_getElem hsi'] at hmapEq
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmapEq
              simpa [Grouping.lookupAt, hidxLt'] using hmapEq
            have hen0 : (Grouping.lookupAt required si').enable.denote (project mem w) = 1 := by
              rw [hreqAt'.1]; exact henAct
            have hslotLt : Grouping.slotOf mem.slotMap si' < p.checked.layout.sends.length :=
              hsame.2.1 si' hidxLt'
            set s := Grouping.slotOf mem.slotMap si'
            have hidxInB : si' ∈ Grouping.bucketOf mem.slotMap required.length s := by
              unfold Grouping.bucketOf
              exact List.mem_filter.mpr ⟨List.mem_range.mpr hidxLt', by simp [s]⟩
            have hsl := hsame.2.2 s
            dsimp only at hsl
            have hslotEq : p.checked.layout.slot s = p.checked.layout.sends[s] := by
              simp [Grouping.Layout.slot, hslotLt]
            have hslotMatch : (p.checked.layout.slot s).enable.denote w = 1 ∧
                trimZeros ((p.checked.layout.slot s).args.map (·.denote w)) =
                  trimZeros ((Grouping.lookupAt required si').args.map (·.denote (project mem w))) := by
              generalize hB : Grouping.bucketOf mem.slotMap required.length s = B at hsl hidxInB
              cases B with
              | nil => cases hidxInB
              | cons k1 rest =>
                  cases rest with
                  | nil =>
                      simp only [List.mem_singleton] at hidxInB
                      subst hidxInB
                      exact ⟨hsl.1.trans hen0, Aiur.Tiling.Grouped.trim_of_words hsl.2⟩
                  | cons k2 tail =>
                      rcases hsl with ⟨_, _, hall0⟩ | ⟨k, _, _, hrest0, hs1, hargs⟩
                      · exfalso
                        have h0 : (Grouping.lookupAt required si').enable.denote (project mem w) = 0 :=
                          hall0 si' hidxInB
                        rw [hen0] at h0
                        exact one_ne_zero h0
                      · have hkEq : si' = k := by
                          by_contra hne
                          have h0 : (Grouping.lookupAt required si').enable.denote (project mem w) = 0 :=
                            hrest0 si' hidxInB hne
                          rw [hen0] at h0
                          exact one_ne_zero h0
                        subst hkEq
                        exact ⟨hs1, Aiur.Tiling.Grouped.trim_of_words hargs⟩
            have htuple : (Grouping.lookupAt required si').args.map (·.denote (project mem w)) =
                encode callableId (mem.origin.sends[si].message (project mem w)) := by
              rw [hreqAt'.2, ← hsome]
              exact Aiur.Tiling.Bridge.send_tuple callableId mem.origin.sends[si'] (project mem w)
            simp only [pushVals, List.mem_map]
            refine ⟨p.checked.layout.sends[s], List.getElem_mem hslotLt, ?_⟩
            rw [← hslotEq, hslotMatch.1, hslotMatch.2, htuple]
            simp
          · simp at hsome

/-- Any valid `FnRow` has zero trimmed ledger at every `MEMSEG` tuple when `16 < bound`
and `SmallCast F bound`. -/
theorem trim_ledger_memseg_zero {bound : Nat} (small : SmallCast F bound) (htags : 16 < bound)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    {row : FnRow F plan} (hholds : row.Holds callableId)
    {k : List F} (hk : k.head? = some (memsegTag : F)) :
    Finsupp.mapDomain trimZeros (row.ledger callableId) k = 0 := by
  have hmemNe0 : (memsegTag : F) ≠ 0 := by
    intro h; have := small memsegTag htags h; simp [memsegTag] at this
  have hcallNeMem : (Aiur.Tiling.Bridge.CALL : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.CALL) (b := memsegTag)
      (by simp [Aiur.Tiling.Bridge.CALL]; omega) htags h
    simp [Aiur.Tiling.Bridge.CALL, memsegTag] at this
  have hromNeMem : (Aiur.Tiling.Bridge.ROM : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.ROM) (b := memsegTag)
      (by simp [Aiur.Tiling.Bridge.ROM]; omega) htags h
    simp [Aiur.Tiling.Bridge.ROM, memsegTag] at this
  have hcallNe0 : (Aiur.Tiling.Bridge.CALL : F) ≠ 0 := by
    intro h
    have := small Aiur.Tiling.Bridge.CALL (by simp [Aiur.Tiling.Bridge.CALL]; omega) h
    simp [Aiur.Tiling.Bridge.CALL] at this
  have hromNe0 : (Aiur.Tiling.Bridge.ROM : F) ≠ 0 := by
    intro h
    have := small Aiur.Tiling.Bridge.ROM (by simp [Aiur.Tiling.Bridge.ROM]; omega) h
    simp [Aiur.Tiling.Bridge.ROM] at this
  have hinstZero : ∀ (p : Aiur.Tiling.Grouped.Inst F),
      Finsupp.mapDomain trimZeros (instLedger callableId p) k = 0 := by
    intro p
    rw [Aiur.Tiling.Grouped.instLedger_trim]
    have hnotCall : ∀ m : Message F, trimZeros (encode callableId m) ≠ k := by
      intro m heq
      have hh := congrArg List.head? heq
      rw [hk] at hh
      simp [encode, trimZeros, hcallNe0] at hh
      exact hcallNeMem hh
    have hnotRom : ∀ e : F × WireValue F, trimZeros (encodeRom e) ≠ k := by
      intro e heq
      have hh := congrArg List.head? heq
      rw [hk] at hh
      simp [encodeRom, trimZeros, hromNe0] at hh
      exact hromNeMem hh
    have hr0 : Aiur.Tiling.Grouped.recvK callableId p k = 0 := by
      simp [Aiur.Tiling.Grouped.recvK, hnotCall]
    have hs0 : (Aiur.Tiling.Grouped.sendK callableId p k).sum = 0 := by
      apply List.sum_eq_zero; intro v hv
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv
      simp [hnotCall]
    have hm0 : (Aiur.Tiling.Grouped.memK p k).sum = 0 := by
      apply List.sum_eq_zero; intro v hv
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hv
      simp [hnotRom]
    rw [hr0, hs0, hm0, add_zero, add_zero]
  cases row with
  | single c _ w =>
      simp only [ledger, Aiur.Tiling.Grouped.lower_instLedger]
      exact hinstZero _
  | group p _ w =>
      simp only [ledger]
      rcases group_row callableId idOk p.checked hholds with h0 | ⟨m, _, _, _, _, heq⟩
      · rw [h0]; rfl
      · rw [heq]; exact hinstZero _

/-- Extract the flat list of `FnRow`s from the function circuits of `lowerFullSystem`. -/
theorem extract_fnRows {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (logBlowup extDegree : Nat) :
    ∀ (inps : List (CircuitInput F)) (trs : List (CircuitTrace F)),
      (∀ inp ∈ inps, inp ∈ lowerPlanFunctionsOrdered callableId plan) →
      List.Forall₂ CircuitAirSatisfied (inps.map (compileRetune logBlowup extDegree)) trs →
      ∃ rows : List (FnRow F plan),
        rows.length = totalRows trs ∧
        (∀ row ∈ rows, row.Holds callableId) ∧
        (rows.map (FnRow.ledger callableId)).sum =
          (List.zipWith circuitLedger (inps.map (compileRetune logBlowup extDegree)) trs).sum ∧
        (rows.map FnRow.pushCount).sum ≤
          (List.zipWith (fun c tr => tr.height * c.lookups.length)
            (inps.map (compileRetune logBlowup extDegree)) trs).sum
  | [], [], _, _ => ⟨[], rfl, (fun _ h => by cases h), rfl, Nat.zero_le _⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | inp :: inps, tr :: trs, hinps, hsat => by
      obtain ⟨hsatH, hsatT⟩ := List.forall₂_cons.mp hsat
      obtain ⟨rest, hlenR, hholdsR, hledR, hpushR⟩ :=
        extract_fnRows callableId plan logBlowup extDegree inps trs
          (fun x hx => hinps x (List.mem_cons_of_mem _ hx)) hsatT
      have hlookLen : (compileRetune logBlowup extDegree inp).lookups.length = inp.lookups.length := by
        unfold compileRetune
        exact ((retune_lookups_perm (compileCircuit inp extDegree) (2 ^ logBlowup) extDegree).1).length_eq
      rcases mem_lowerPlanFunctionsOrdered callableId plan (hinps inp List.mem_cons_self) with
        ⟨c, hc, rfl⟩ | ⟨p, hp, rfl⟩
      · let here : List (FnRow F plan) :=
          (List.range tr.height).map fun r => FnRow.single c hc (tr.mainRow r)
        refine ⟨here ++ rest, ?_, ?_, ?_, ?_⟩
        · simp [here, totalRows, hlenR]
        · intro row hrow
          rcases List.mem_append.mp hrow with h1 | h2
          · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h1
            exact (lowerSingleChip_rowSatisfied_iff callableId c logBlowup extDegree tr r).mp
              (hsatH r (List.mem_range.mp hr))
          · exact hholdsR row h2
        · simp only [List.map_append, List.sum_append, List.map_cons, List.zipWith_cons_cons,
            List.sum_cons, hledR]
          refine congrArg (· + _) ?_
          simp only [here, List.map_map, circuitLedger]
          refine congrArg List.sum ?_
          apply List.map_congr_left
          intro r _
          exact (lowerSingleChip_rowLedger_eq callableId c logBlowup extDegree tr r).symm
        · simp only [List.map_append, List.sum_append, List.map_cons, List.zipWith_cons_cons,
            List.sum_cons, hlookLen]
          have hherePush : (here.map FnRow.pushCount).sum =
              tr.height * (c.sends.length + c.memory.length) := by
            simp [here, List.map_map, Function.comp_def, FnRow.pushCount]
          have hle1 : c.sends.length + c.memory.length ≤
              (lowerSingleChip callableId (Activation.compile c) c.numVars).lookups.length := by
            simp [lowerSingleChip, Activation.compile]
          have hmul : tr.height * (c.sends.length + c.memory.length) ≤
              tr.height * (lowerSingleChip callableId (Activation.compile c) c.numVars).lookups.length :=
            Nat.mul_le_mul_left tr.height hle1
          omega
      · let here : List (FnRow F plan) :=
          (List.range tr.height).map fun r => FnRow.group p hp (tr.mainRow r)
        refine ⟨here ++ rest, ?_, ?_, ?_, ?_⟩
        · simp [here, totalRows, hlenR]
        · intro row hrow
          rcases List.mem_append.mp hrow with h1 | h2
          · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h1
            exact (lowerGroupLayout_rowSatisfied_iff p.checked.layout logBlowup extDegree tr r).mp
              (hsatH r (List.mem_range.mp hr))
          · exact hholdsR row h2
        · simp only [List.map_append, List.sum_append, List.map_cons, List.zipWith_cons_cons,
            List.sum_cons, hledR]
          refine congrArg (· + _) ?_
          simp only [here, List.map_map, circuitLedger]
          refine congrArg List.sum ?_
          apply List.map_congr_left
          intro r _
          exact (lowerGroupLayout_rowLedger_eq p.checked.layout logBlowup extDegree tr r).symm
        · simp only [List.map_append, List.sum_append, List.map_cons, List.zipWith_cons_cons,
            List.sum_cons, hlookLen]
          have hherePush : (here.map FnRow.pushCount).sum =
              tr.height * p.checked.layout.sends.length := by
            simp [here, List.map_map, Function.comp_def, FnRow.pushCount]
          have hle1 : p.checked.layout.sends.length ≤
              (lowerGroupLayout p.checked.layout).lookups.length := by
            simp [lowerGroupLayout]
          have hmul : tr.height * p.checked.layout.sends.length ≤
              tr.height * (lowerGroupLayout p.checked.layout).lookups.length :=
            Nat.mul_le_mul_left tr.height hle1
          omega

end FnRow

/-- **Headline Row-to-Memo Bridge (`lowerFullSystem_satisfied_implies_checkMemo`):**
For any lowered Multi-STARK system produced by `Aiur.MultiStarkSpec.lowerFullSystem`
whose traces satisfy `LoweredSystemSatisfied` (lowered AIR constraints on every
compiled and retuned circuit, trusted fixed-table rows, `checkChipEnables` on
all chips of `plan`, and global trimmed LogUp balance), with `SmallCast F bound`
(`16 < bound`), physical lookup budget `< bound`, static `Shaped` and `checkContext`,
there exist weighted rows `wrows` of length at most `totalRows (fnTracesOf callableId plan traces)`
such that `plan.checkMemo (Erasure.rawROM rom) root wrows = .ok ()`
(where `rom = extractWidthROM romWidths romLayout (romTracesOf ...)`). -/
theorem lowerFullSystem_satisfied_implies_checkMemo
    {source : Circuit.System F} {id : String → Except String Nat}
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (plan : Grouping.Plan source id)
    (activated : plan.WellFormedActivation) (names : (circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat)
    (logBlowup : Nat) (segmented : Bool) (extDegree : Nat) (romLayout : RomLayout)
    (root : Circuit.Message F) (boundaryLedger : Ledger F)
    (traces : List (CircuitTrace F))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup segmented
      extDegree romLayout root boundaryLedger traces)
    {bound : Nat} (small : SmallCast F bound) (htags : 16 < bound)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup segmented extDegree romLayout)
      traces < bound)
    (hromWidths : ∀ w ∈ romWidths, w < bound)
    (hmemWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < bound)
    (hshaped : Shaped.check source (allChips plan) callableId root bound = true)
    (hctx : source.checkContext
      (Erasure.rawROM (extractWidthROM romWidths romLayout
        (romTracesOf callableId plan fixedMaps logBlowup traces))) root = .ok ()) :
    ∃ wrows : List (WeightedRow F),
      wrows.length ≤ totalRows (fnTracesOf callableId plan traces) ∧
      plan.checkMemo
        (Erasure.rawROM (extractWidthROM romWidths romLayout
          (romTracesOf callableId plan fixedMaps logBlowup traces)))
        root wrows = .ok () := by
  classical
  obtain ⟨hFnAir, hTblAir, hRomAir, hledSplit, hbudFn⟩ := hsat.split
  set fnTrs := fnTracesOf callableId plan traces
  set tblTrs := tblTracesOf callableId plan fixedMaps logBlowup traces
  set romTrs := romTracesOf callableId plan fixedMaps logBlowup traces
  set rom := extractWidthROM romWidths romLayout romTrs
  have hshapedP : Shaped source (allChips plan) callableId root bound := Shaped.of_check hshaped
  obtain ⟨fnRows, hfnLen, hfnHolds, hfnLed, hfnPush⟩ :=
    FnRow.extract_fnRows callableId plan logBlowup extDegree
      (lowerPlanFunctionsOrdered callableId plan) fnTrs (fun _ h => h) hFnAir
  -- Tag inequalities from `SmallCast F bound` and `16 < bound`
  have hcallNe0 : (Aiur.Tiling.Bridge.CALL : F) ≠ 0 := by simp [Aiur.Tiling.Bridge.CALL]
  have hromNe0 : (Aiur.Tiling.Bridge.ROM : F) ≠ 0 := by
    intro h; have := small Aiur.Tiling.Bridge.ROM (by simp [Aiur.Tiling.Bridge.ROM]; omega) h
    simp [Aiur.Tiling.Bridge.ROM] at this
  have hmemNe0 : (memsegTag : F) ≠ 0 := by
    intro h; have := small memsegTag htags h; simp [memsegTag] at this
  have hcallNeRom : (Aiur.Tiling.Bridge.CALL : F) ≠ (Aiur.Tiling.Bridge.ROM : F) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.CALL) (b := Aiur.Tiling.Bridge.ROM)
      (by simp [Aiur.Tiling.Bridge.CALL]; omega) (by simp [Aiur.Tiling.Bridge.ROM]; omega) h
    simp [Aiur.Tiling.Bridge.CALL, Aiur.Tiling.Bridge.ROM] at this
  have hcallNeMem : (Aiur.Tiling.Bridge.CALL : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.CALL) (b := memsegTag)
      (by simp [Aiur.Tiling.Bridge.CALL]; omega) htags h
    simp [Aiur.Tiling.Bridge.CALL, memsegTag] at this
  have hromNeMem : (Aiur.Tiling.Bridge.ROM : F) ≠ (memsegTag : F) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.ROM) (b := memsegTag)
      (by simp [Aiur.Tiling.Bridge.ROM]; omega) htags h
    simp [Aiur.Tiling.Bridge.ROM, memsegTag] at this
  -- Total ledger split
  set tblLed := (List.zipWith circuitLedger
    ((lowerFixedTables (F := F) fixedMaps logBlowup).map (compileRetune logBlowup extDegree)) tblTrs).sum
  set romLed := (List.zipWith circuitLedger
    ((lowerRomCircuitsWithLayout (F := F) romWidths segmented romLayout).map
      (compileRetune logBlowup extDegree)) romTrs).sum
  have hbalAt : ∀ k : List F,
      (fnRows.map fun row => row.recvVal callableId k + (row.pushVals callableId k).sum).sum +
        Finsupp.mapDomain trimZeros tblLed k +
        Finsupp.mapDomain trimZeros romLed k +
        (if trimZeros (encode callableId root) = k then 1 else 0) +
        Finsupp.mapDomain trimZeros boundaryLedger k = 0 := by
    intro k
    have h := congrArg (fun L : Ledger F => L k) hsat.logupBalanced
    rw [hledSplit, ← hfnLed] at h
    simp only [Finsupp.mapDomain_add, Aiur.Tiling.Grouped.mapDomain_list_sum, Finsupp.add_apply,
      Finsupp.coe_zero, Pi.zero_apply, Tiling.System.ledger_list_sum, List.map_map,
      Function.comp_def, Finsupp.mapDomain_single, Finsupp.single_apply,
      FnRow.trim_ledger_apply] at h
    exact h
  -- Fixed-table support
  have htblSupp : ∀ t, tblLed t ≠ 0 → t ∈ source.mapClaims.map (encode callableId) :=
    fixedTables_ledger_support callableId fixedMaps logBlowup extDegree tblTrs hTblAir hsat.fixedValid
  -- ROM ledger support
  have hromSupp : ∀ t, romLed t ≠ 0 →
      (∃ e ∈ (Erasure.rawROM rom).entries, t = encodeRom e) ∨
      t.head? = some (memsegTag : F) := by
    have hstep : ∀ (ws : List Nat) (trs : List (CircuitTrace F)),
        List.Forall₂ CircuitAirSatisfied
          ((lowerRomCircuitsWithLayout (F := F) ws segmented romLayout).map
            (compileRetune logBlowup extDegree)) trs →
        ∀ t, (List.zipWith circuitLedger
          ((lowerRomCircuitsWithLayout (F := F) ws segmented romLayout).map
            (compileRetune logBlowup extDegree)) trs).sum t ≠ 0 →
        (∃ e ∈ (Erasure.rawROM (extractWidthROM ws romLayout trs)).entries, t = encodeRom e) ∨
        t.head? = some (memsegTag : F) := by
      intro ws trs hR
      induction ws generalizing trs with
      | nil =>
          cases trs with
          | nil => intro t ht; simp [lowerRomCircuitsWithLayout_eq] at ht
          | cons _ _ => rw [lowerRomCircuitsWithLayout_eq] at hR; cases hR
      | cons w ws ih =>
          cases trs with
          | nil => rw [lowerRomCircuitsWithLayout_eq] at hR; cases hR
          | cons tr trs' =>
              rw [lowerRomCircuitsWithLayout_eq] at hR ⊢
              simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons,
                Finsupp.add_apply] at hR ⊢
              obtain ⟨hRH, hRT⟩ := List.forall₂_cons.mp hR
              intro t ht
              by_cases hh : circuitLedger (compileRetune logBlowup extDegree
                  (lowerKLaneRomCircuit w (romLayoutLanes romLayout w) segmented)) tr t = 0
              · rw [hh, zero_add] at ht
                rcases ih trs' (by rw [lowerRomCircuitsWithLayout_eq]; exact hRT) t
                    (by rw [lowerRomCircuitsWithLayout_eq]; exact ht) with ⟨e, he, rfl⟩ | hmem
                · left
                  refine ⟨e, ?_, rfl⟩
                  simp only [Erasure.rawROM, extractWidthROM, List.zipWith_cons_cons,
                    List.flatten_cons, List.map_append, List.mem_append] at he ⊢
                  exact Or.inr he
                · exact Or.inr hmem
              · rcases klaneRom_circuitLedger_support w (romLayoutLanes romLayout w) segmented
                    logBlowup extDegree tr hRH t hh with ⟨e, he, rfl⟩ | ⟨_, hhead, _, _⟩
                · left
                  refine ⟨(e.1, Erasure.pack e.2), ?_, rfl⟩
                  simp only [Erasure.rawROM, extractWidthROM, List.zipWith_cons_cons,
                    List.flatten_cons, List.map_append, List.mem_append, List.mem_map]
                  exact Or.inl ⟨e, he, rfl⟩
                · exact Or.inr hhead
    exact hstep romWidths romTrs hRomAir
  -- ROM width bound for every entry of `Erasure.rawROM rom`
  have hromEntryWidth : ∀ e ∈ (Erasure.rawROM rom).entries, e.2.words.length < bound := by
    intro e he
    simp only [rom, Erasure.rawROM, extractWidthROM, List.mem_map, List.mem_flatten] at he
    obtain ⟨⟨addr, ws⟩, ⟨xs, hxs, hmem⟩, rfl⟩ := he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxs
    have hlenR : romTrs.length = romWidths.length := by
      have := hRomAir.length_eq
      rw [lowerRomCircuitsWithLayout_eq] at this
      simp at this
      exact this.symm
    have hiLt : i < romWidths.length := by simp [List.length_zipWith, hlenR] at hi; exact hi
    rw [List.getElem_zipWith] at hmem
    have hlenWs : ws.length = romWidths[i] := klaneRomEntries_payload_length _ _ _ hmem
    simpa [Erasure.pack_words, hlenWs] using hromWidths romWidths[i] (List.getElem_mem hiLt)
  -- Push-length bound from `systemLookupBudget < bound`
  have hpushLenBound : (fnRows.map FnRow.pushCount).sum + 1 < bound := by
    unfold systemLookupBudget at hbudFn hbudget
    omega
  -- Helper: head separation for `CALL` / `ROM` / `MEMSEG`
  have hcallRom : ∀ (m : Message F) (e : F × WireValue F),
      trimZeros (encode callableId m) ≠ trimZeros (encodeRom e) := by
    intro m e heq
    have hh := trimZeros_head heq (by simp [encode]) hcallNe0
    simp [encodeRom] at hh
    exact hcallNeRom hh.symm
  have hcallMem : ∀ (m : Message F) (u : List F), u.head? = some (memsegTag : F) →
      trimZeros (encode callableId m) ≠ trimZeros u := by
    intro m u hu heq
    have hh := trimZeros_head heq (by simp [encode]) hcallNe0
    rw [hu, Option.some.injEq] at hh
    exact hcallNeMem hh.symm
  have hromMem : ∀ (e : F × WireValue F) (u : List F), u.head? = some (memsegTag : F) →
      trimZeros (encodeRom e) ≠ trimZeros u := by
    intro e u hu heq
    have hh := trimZeros_head heq (by simp [encodeRom]) hromNe0
    rw [hu, Option.some.injEq] at hh
    exact hromNeMem hh.symm
  -- Step 1: Every active `FnRow`'s enabled memory lookups are valid in `Erasure.rawROM rom`!
  have hmemValid : ∀ row ∈ fnRows, ∀ c a, row.activeChipAssign = some (c, a) →
      ∀ m ∈ (Activation.compile c).memory, MemoryLookup.Valid (Erasure.rawROM rom) a m := by
    intro row hrow c a hact m hm henab
    set x := (m.address.denote a, m.value.map (Circuit.ArithExpr.denote a))
    set k := trimZeros (encodeRom x)
    have hbal := hbalAt k
    -- Every `recvVal` is 0 on a ROM tuple (because every receive has head `CALL ≠ ROM`)
    have hrecv0 : ∀ r' ∈ fnRows, r'.recvVal callableId k = 0 := by
      intro r' hr'
      by_contra hne
      obtain ⟨c', a', _, _, _, _, heq⟩ :=
        FnRow.active_of_recvVal_ne_zero callableId idOk (hfnHolds r' hr') hne
      exact hcallRom (c'.conclusion a') x heq
    have hfnSum : (fnRows.map fun r' => r'.recvVal callableId k + (r'.pushVals callableId k).sum).sum =
        (fnRows.flatMap fun r' => r'.pushVals callableId k).sum := by
      rw [Aiur.Tiling.Bridge.sum_flatMap']
      congr 1
      apply List.map_congr_left
      intro r' hr'
      rw [hrecv0 r' hr', zero_add]
    have htbl0 : Finsupp.mapDomain trimZeros tblLed k = 0 := by
      by_contra hne
      obtain ⟨u, hu, heq⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
      obtain ⟨mc, _, rfl⟩ := List.mem_map.mp (htblSupp u hu)
      exact hcallRom mc x heq
    have hbnd0 : Finsupp.mapDomain trimZeros boundaryLedger k = 0 := by
      by_contra hne
      obtain ⟨u, hu, heq⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
      exact hromMem x u (hsat.boundaryOk u hu) heq.symm
    have hroot0 : trimZeros (encode callableId root) ≠ k := hcallRom root x
    simp only [hfnSum, htbl0, hbnd0, hroot0, ↓reduceIte, add_zero] at hbal
    have hpushNe : (fnRows.flatMap fun r' => r'.pushVals callableId k).sum ≠ 0 := by
      apply Aiur.Tiling.Bridge.zero_one_sum small
      · intro v hv
        obtain ⟨r', hr', hv'⟩ := List.mem_flatMap.mp hv
        exact FnRow.pushVals_bits callableId idOk hsat.enablesOk (hfnHolds r' hr') k v hv'
      · exact List.mem_flatMap.mpr ⟨row, hrow,
          FnRow.one_mem_pushVals_of_memory callableId idOk (hfnHolds row hrow) hact hm henab⟩
      · rw [List.length_flatMap]
        have hlenEq : (fnRows.map fun r' => (r'.pushVals callableId k).length).sum =
            (fnRows.map FnRow.pushCount).sum := by
          congr 1; apply List.map_congr_left; intro r' _; exact FnRow.pushVals_length callableId k r'
        omega
    have hromNe : Finsupp.mapDomain trimZeros romLed k ≠ 0 := by
      intro h0; rw [h0, add_zero] at hbal; exact hpushNe hbal
    obtain ⟨u, hu, eu⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hromNe
    rcases hromSupp u hu with ⟨e, he, rfl⟩ | hheadMem
    · have htypeM : m.value.type = .tuple (List.replicate m.value.words.length .field) ∧
          m.value.words.length < bound := by
        have hactSpec := FnRow.activeChipAssign_spec callableId (hfnHolds row hrow)
          (by
            cases row with
            | single _ _ _ =>
                simp only [FnRow.activeChipAssign] at hact
                split_ifs at hact with h1
                simp [FnRow.isActive, h1]
            | group _ _ _ =>
                simp only [FnRow.activeChipAssign] at hact
                split_ifs at hact with h1
                simp [FnRow.isActive, h1])
        obtain ⟨c1, a1, hact1, hc1In, _, _⟩ := hactSpec
        rw [hact] at hact1
        simp only [Option.some.injEq, Prod.mk.injEq] at hact1
        obtain ⟨rfl, rfl⟩ := hact1
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
        exact ⟨hshapedP.memory c hc1In m0 hm0, hmemWidth c hc1In m0 hm0⟩
      have hone := trimZeros_eq_iff.mp eu 1
      rw [Aiur.Tiling.Grouped.encodeRom_getD_one, Aiur.Tiling.Grouped.encodeRom_getD_one] at hone
      have hwlen : e.2.words.length = x.2.words.length :=
        small.inj (hromEntryWidth e he) (by simpa [x, WireValue.map] using htypeM.2) hone
      have hsame : encodeRom e = encodeRom x :=
        trimZeros_inj_of_length (by simp [encodeRom, hwlen]) eu
      simp only [encodeRom, List.cons.injEq] at hsame
      obtain ⟨_, _, haddr, hwords⟩ := hsame
      have heq : e = x := by
        obtain ⟨ea, ev⟩ := e
        have hty : ev.type = .tuple (List.replicate ev.words.length .field) :=
          Aiur.Tiling.WideStage.rawROM_packed rom (ea, ev) he
        cases ev
        simp only [x, WireValue.map, WireValue.mk.injEq, Prod.mk.injEq] at *
        refine ⟨haddr, ?_, hwords⟩
        rw [hty, htypeM.1, hwords]; simp
      rw [← heq]; exact he
    · exact absurd eu.symm (hromMem x u hheadMem)
  -- Step 2: Every non-static required claim has an active provider in `fnRows`!
  have hprovider : ∀ {q : Message F}, ¬ source.MapClaim q →
      (q = root ∨ ∃ row ∈ fnRows, ∃ c a, row.activeChipAssign = some (c, a) ∧
        q ∈ (Activation.compile c).requirements a) →
      ∃ row ∈ fnRows, ∃ c a, row.isActive = true ∧ row.activeChipAssign = some (c, a) ∧
        (Activation.compile c).conclusion a = q := by
    intro q hnotStatic hreq
    have hchipOfAct : ∀ {row : FnRow F plan} {c : Chip F} {a : Nat → F},
        row.activeChipAssign = some (c, a) → c ∈ allChips plan := by
      intro row c a hact
      cases row with
      | single c' hc' w =>
          simp only [FnRow.activeChipAssign] at hact
          split_ifs at hact
          simp only [Option.some.injEq, Prod.mk.injEq] at hact
          exact hact.1 ▸ List.mem_append_left _ hc'
      | group p hp w =>
          simp only [FnRow.activeChipAssign] at hact
          split_ifs at hact
          cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
          | none => simp [hf] at hact
          | some mem =>
              simp only [hf, Option.some.injEq, Prod.mk.injEq] at hact
              exact hact.1 ▸ Aiur.Tiling.Grouped.origin_allChips plan hp
                (List.mem_of_find?_eq_some hf)
    have hqChan : q.channel ∈ Aiur.Tiling.Bridge.channels source (allChips plan) root := by
      rcases hreq with rfl | ⟨row, hrow, c, a, hact, hq⟩
      · simp [Aiur.Tiling.Bridge.channels]
      · obtain ⟨s, hs, rfl, _⟩ := Aiur.Tiling.Bridge.requirement_send hq
        simp only [Aiur.Tiling.Bridge.channels, List.mem_append, List.mem_map, List.mem_flatMap,
          List.mem_singleton]
        exact Or.inl (Or.inl (Or.inr ⟨c, hchipOfAct hact, s, hs, rfl⟩))
    have hchipShape : ∀ c ∈ allChips plan, c.name = q.channel →
        Erasure.messageShape q = Erasure.signature c := by
      intro c hc hname
      rcases hreq with rfl | ⟨row, hrow, c0, a0, hact0, hq⟩
      · exact hshapedP.rootChip c hc hname
      · obtain ⟨s, hs, rfl, _⟩ := Aiur.Tiling.Bridge.requirement_send hq
        rw [Aiur.Tiling.Bridge.message_shape]
        exact hshapedP.calls c0 (hchipOfAct hact0) s hs c hc hname
    have hmapShape : ∀ mc ∈ source.mapClaims, mc.channel = q.channel →
        Erasure.messageShape mc = Erasure.messageShape q := by
      intro mc hmc hname
      rcases hreq with rfl | ⟨row, hrow, c0, a0, hact0, hq⟩
      · exact hshapedP.rootMaps mc hmc hname
      · obtain ⟨s, hs, rfl, _⟩ := Aiur.Tiling.Bridge.requirement_send hq
        rw [Aiur.Tiling.Bridge.message_shape]
        exact hshapedP.maps c0 (hchipOfAct hact0) s hs mc hmc hname
    have hidEq : ∀ x ∈ Aiur.Tiling.Bridge.channels source (allChips plan) root,
        ∀ y ∈ Aiur.Tiling.Bridge.channels source (allChips plan) root,
        (callableId x : F) = (callableId y : F) → x = y := fun x hx y hy h =>
      hshapedP.ids x hx y hy (small.inj (hshapedP.idBound x hx) (hshapedP.idBound y hy) h)
    set k := trimZeros (encode callableId q)
    have hbal := hbalAt k
    have htbl0 : Finsupp.mapDomain trimZeros tblLed k = 0 := by
      by_contra hne
      obtain ⟨u, hu, eu⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
      obtain ⟨mc, hmc, rfl⟩ := List.mem_map.mp (htblSupp u hu)
      have hids := trimZeros_eq_iff.mp eu 1
      rw [Aiur.Tiling.Grouped.encode_getD_one, Aiur.Tiling.Grouped.encode_getD_one] at hids
      have hsame : mc.channel = q.channel := hidEq _ (by
        simp only [Aiur.Tiling.Bridge.channels, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨mc, hmc, rfl⟩)) _ hqChan hids
      have hsh := hmapShape mc hmc hsame
      have heqT := trimZeros_inj_of_length (Aiur.Tiling.Grouped.encode_length callableId hsh) eu
      exact hnotStatic (Aiur.Tiling.Bridge.encode_inj heqT hsame hsh ▸ hmc)
    have hrom0 : Finsupp.mapDomain trimZeros romLed k = 0 := by
      by_contra hne
      obtain ⟨u, hu, eu⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
      rcases hromSupp u hu with ⟨e, _, rfl⟩ | hmem
      · exact hcallRom q e eu.symm
      · exact hcallMem q u hmem eu.symm
    have hbnd0 : Finsupp.mapDomain trimZeros boundaryLedger k = 0 := by
      by_contra hne
      obtain ⟨u, hu, eu⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
      exact hcallMem q u (hsat.boundaryOk u hu) eu.symm
    rw [htbl0, hrom0, hbnd0, add_zero, add_zero, add_zero] at hbal
    have hsplit :
        (fnRows.map fun r' => r'.recvVal callableId k + (r'.pushVals callableId k).sum).sum =
        (fnRows.map fun r' => r'.recvVal callableId k).sum +
          (fnRows.map fun r' => (r'.pushVals callableId k).sum).sum := by
      rw [← List.sum_map_add]
    rw [hsplit] at hbal
    have hySum : ((fnRows.flatMap fun r' => r'.pushVals callableId k) ++
        [if trimZeros (encode callableId root) = k then (1 : F) else 0]).sum ≠ 0 := by
      apply Aiur.Tiling.Bridge.zero_one_sum small
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨r', hr', hv'⟩ := List.mem_flatMap.mp hv
          exact FnRow.pushVals_bits callableId idOk hsat.enablesOk (hfnHolds r' hr') k v hv'
        · simp only [List.mem_singleton] at hv
          split_ifs at hv <;> simp [hv]
      · rcases hreq with rfl | ⟨row, hrow, c, a, hact, hq⟩
        · simp [k]
        · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨row, hrow,
            FnRow.one_mem_pushVals_of_requirement callableId idOk (hfnHolds row hrow) hact hq⟩)
      · rw [List.length_append, List.length_flatMap, List.length_singleton]
        have hlenEq : (fnRows.map fun r' => (r'.pushVals callableId k).length).sum =
            (fnRows.map FnRow.pushCount).sum := by
          congr 1; apply List.map_congr_left; intro r' _; exact FnRow.pushVals_length callableId k r'
        omega
    rw [List.sum_append, List.sum_singleton, Aiur.Tiling.Bridge.sum_flatMap'] at hySum
    have hrecvNe : (fnRows.map fun r' => r'.recvVal callableId k).sum ≠ 0 := by
      intro h0
      apply hySum
      rw [h0, zero_add] at hbal
      linear_combination hbal
    obtain ⟨v, hv, hne⟩ := Aiur.Tiling.Bridge.exists_ne_zero_of_sum hrecvNe
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hv
    obtain ⟨c, a, hisAct, hact, hcIn, _, henc⟩ :=
      FnRow.active_of_recvVal_ne_zero callableId idOk (hfnHolds row hrow) hne
    have hids := trimZeros_eq_iff.mp henc 1
    rw [Aiur.Tiling.Grouped.encode_getD_one, Aiur.Tiling.Grouped.encode_getD_one] at hids
    have hcChan : c.name ∈ Aiur.Tiling.Bridge.channels source (allChips plan) root := by
      simp only [Aiur.Tiling.Bridge.channels, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨c, hcIn, rfl⟩))
    have hsame : c.name = q.channel := hidEq _ hcChan _ hqChan (by simpa [Chip.conclusion] using hids)
    have hsh : Erasure.messageShape (c.conclusion a) = Erasure.messageShape q := by
      rw [Aiur.Tiling.Bridge.conclusion_shape]
      exact (hchipShape c hcIn hsame).symm
    have hconc : c.conclusion a = q :=
      Aiur.Tiling.Bridge.encode_inj
        (trimZeros_inj_of_length (Aiur.Tiling.Grouped.encode_length callableId hsh) henc) hsame hsh
    exact ⟨row, hrow, c, a, hisAct, hact, by rw [Activation.conclusion_eq]; exact hconc⟩
  -- Step 3: Build weighted physical rows for active `fnRows` and discharge `plan.checkMemo`!
  let actives := fnRows.filter FnRow.isActive
  have hactMem : ∀ r ∈ actives, r ∈ fnRows ∧ r.isActive = true := fun r hr => by
    simpa [actives] using hr
  let claimsOf : FnRow F plan → RuleClaims (Message F) := fun row =>
    match row.activeChipAssign with
    | some (c, a) => ((Activation.compile c).conclusion a, (Activation.compile c).requirements a)
    | none => (root, [])
  let physRowOf : FnRow F plan → Circuit.Row F
    | .single c _ w => Row.ofAssignment c.name (c.numVars + 1) w
    | .group p _ w => Row.ofAssignment p.checked.layout.name p.checked.layout.width w
  have hinspectAct : ∀ row ∈ actives,
      plan.inspectRow (Erasure.rawROM rom) (physRowOf row) = .ok (some (claimsOf row)) := by
    intro row hrow
    obtain ⟨hmem, hisAct⟩ := hactMem row hrow
    obtain ⟨c, a, hact, _, hon, _⟩ := FnRow.activeChipAssign_spec callableId (hfnHolds row hmem) hisAct
    have hmemRow := hmemValid row hmem c a hact
    simp only [claimsOf, hact]
    cases row with
    | single c' hc' w =>
        simp only [FnRow.isActive, decide_eq_true_eq] at hisAct
        simp only [FnRow.activeChipAssign, hisAct, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact
        obtain ⟨_, formedA⟩ := activated c' hc'
        have hactSat : Scalar.Circuit.Satisfies (Activation.compile c').constraints w :=
          fun q hq => hfnHolds _ hmem q (List.mem_append_left _ hq)
        have hfin := Chip.finiteAssignment formedA w (Erasure.rawROM rom)
        have hvalidA : (Activation.compile c').ValidAssignment (Erasure.rawROM rom) w :=
          ⟨hactSat, hmemRow⟩
        have hchk : (Activation.compile c').checkRow (Erasure.rawROM rom)
            (Row.ofAssignment c'.name (c'.numVars + 1) w) =
            .ok ((Activation.compile c').conclusion w, (Activation.compile c').requirements w) := by
          apply Chip.checkRow_iff.mpr
          refine ⟨⟨formedA, Row.ofAssignment_length _ _ _, hfin.1.mp hvalidA⟩, ?_⟩
          exact Prod.ext hfin.2.1 hfin.2.2
        have hsel1 : (Row.ofAssignment c'.name (c'.numVars + 1) w).assignment c'.numVars = 1 := by
          rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]; exact hisAct
        have hnamed : (Row.ofAssignment c'.name (c'.numVars + 1) w).chip = c'.name := rfl
        simp only [physRowOf, Grouping.Plan.inspectRow, hnamed,
          Aiur.Tiling.Bridge.find_single plan hc', hchk, hsel1, ↓reduceIte]
    | group p hp w =>
        simp only [FnRow.isActive, decide_eq_true_eq] at hisAct
        simp only [FnRow.activeChipAssign, hisAct, ↓reduceIte] at hact
        cases hf : p.checked.layout.members.find? (fun n => decide (w n.selector = 1)) with
        | none => simp [hf] at hact
        | some mem =>
            simp only [hf, Option.some.injEq, Prod.mk.injEq] at hact
            obtain ⟨rfl, rfl⟩ := hact
            have hmIn := List.mem_of_find?_eq_some hf
            have hsel : w mem.selector = 1 := by simpa using List.find?_some hf
            have hvalid : Scalar.Circuit.Satisfies p.checked.layout.constraints w :=
              fun q hq => hfnHolds _ hmem q (List.mem_append_left _ hq)
            exact group_inspect plan names hp hmIn hvalid hisAct hsel hmemRow
  let rules := actives.map claimsOf
  let static : Message F → Bool := fun c => decide (source.MapClaim c)
  let weighted := Balance.weigh (Balance.required static root rules) rules
  have hfst : weighted.map Prod.fst = actives.map claimsOf := Balance.weigh_rules _ _
  have hlenW : weighted.length = actives.length := by
    simpa using congrArg List.length hfst
  have hweighOk : ∀ x ∈ actives.zip weighted,
      plan.weigh (Erasure.rawROM rom) ⟨physRowOf x.1, x.2.2⟩ = .ok (some x.2) := by
    intro x hx
    have hr := (List.of_mem_zip hx).1
    have hcl := Aiur.Tiling.Bridge.zip_fst claimsOf actives weighted hfst x hx
    simp only [Grouping.Plan.weigh, hinspectAct x.1 hr]
    rw [show x.2 = (x.2.1, x.2.2) from rfl, hcl]
  let wrows : List (WeightedRow F) := (actives.zip weighted).map fun x => ⟨physRowOf x.1, x.2.2⟩
  have hmapped : wrows.mapM (plan.weigh (Erasure.rawROM rom)) = .ok (weighted.map some) := by
    have := Aiur.Tiling.Bridge.mapM_map_ok (actives.zip weighted)
      (fun x => (⟨physRowOf x.1, x.2.2⟩ : WeightedRow F))
      (plan.weigh (Erasure.rawROM rom)) (fun x => some x.2) hweighOk
    rw [this, show (fun x : FnRow F plan × (RuleClaims (Message F) × Int) => some x.2) =
      some ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by omega)]
  have hactOut : Grouping.activeRules (weighted.map some) = weighted := by
    simp [Grouping.activeRules, List.filterMap_map]
  have hcovered : ∀ claim ∈ Balance.required static root rules, ∃ rule ∈ rules, rule.1 = claim := by
    intro claim hclaim
    simp only [Balance.required, List.mem_filter, Bool.not_eq_true', static,
      decide_eq_false_iff_not] at hclaim
    obtain ⟨hmemC, hnotStatic⟩ := hclaim
    have hreq : claim = root ∨ ∃ row ∈ fnRows, ∃ c a, row.activeChipAssign = some (c, a) ∧
        claim ∈ (Activation.compile c).requirements a := by
      rcases List.mem_cons.mp hmemC with rfl | hmemC
      · exact Or.inl rfl
      · obtain ⟨rule, hrule, hcl⟩ := List.mem_flatMap.mp hmemC
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hrule
        obtain ⟨hrIn, hrAct⟩ := hactMem row hrow
        obtain ⟨c, a, hact, _, _, _⟩ := FnRow.activeChipAssign_spec callableId (hfnHolds row hrIn) hrAct
        simp only [claimsOf, hact] at hcl
        exact Or.inr ⟨row, hrIn, c, a, hact, hcl⟩
    obtain ⟨row, hrow, c, a, hisAct, hact, hconc⟩ := hprovider hnotStatic hreq
    refine ⟨claimsOf row, List.mem_map.mpr ⟨row, ?_, rfl⟩, by simp [claimsOf, hact, hconc]⟩
    exact List.mem_filter.mpr ⟨hrow, hisAct⟩
  refine ⟨wrows, ?_, ?_⟩
  · have hlenLe : actives.length ≤ fnRows.length := List.length_filter_le _ _
    simp only [wrows, List.length_map, List.length_zip, hlenW, min_self]
    omega
  · have hzero := Balance.weigh_balanced (static := static) (root := root) hcovered
    simp only [Grouping.Plan.checkMemo, hctx, hmapped, hactOut]
    simp only [weighted]
    simp only [static] at hzero ⊢
    simp only [hzero, ↓reduceIte]

/-! ### Segmented `MEMSEG` ROM Validity from `LoweredSystemSatisfied` over `ZMod p` -/

/-- **Segmented `ZMod p` ROM Validity (`extractWidthROM_valid_segmented_zmod`):**
When `segmented = true` over any prime field `ZMod p` (`16 < p`), if
`LoweredSystemSatisfied` holds with `boundaryLedger = memsegPreambleLedger romWidths ivlsOf`
where each `ivlsOf w` is sorted disjoint in `[0, p)` and each width's active entry
count satisfies `count + 1 < p`, then the extracted `WidthROM (ZMod p)` is `Valid`! -/
theorem extractWidthROM_valid_segmented_zmod {p : Nat} [Fact (Nat.Prime p)]
    (hp16 : 16 < p)
    {source : Circuit.System (ZMod p)} {id : String → Except String Nat}
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hnd : romWidths.Nodup)
    (hwLt : ∀ w ∈ romWidths, w < p)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (root : Circuit.Message (ZMod p))
    (ivlsOf : Nat → List (Nat × Nat))
    (hdisj : ∀ w ∈ romWidths, DisjointIntervalsP p (ivlsOf w))
    (traces : List (CircuitTrace (ZMod p)))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup true
      extDegree romLayout root (memsegPreambleLedger romWidths ivlsOf) traces)
    (hromCnt : List.Forall₂ (fun w tr => (extractRomEntries w romLayout tr).length + 1 < p)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces)) :
    (extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)).Valid := by
  have small : SmallCast (ZMod p) p := smallCast_zmod p le_rfl
  obtain ⟨hFnAir, hTblAir, hRomAir, hledSplit, _⟩ := hsat.split
  set fnTrs := fnTracesOf callableId plan traces
  set tblTrs := tblTracesOf callableId plan fixedMaps logBlowup traces
  set romTrs := romTracesOf callableId plan fixedMaps logBlowup traces
  obtain ⟨fnRows, _, hfnHolds, hfnLed, _⟩ :=
    FnRow.extract_fnRows callableId plan logBlowup extDegree
      (lowerPlanFunctionsOrdered callableId plan) fnTrs (fun _ h => h) hFnAir
  have hmemNe0 : (memsegTag : ZMod p) ≠ 0 := by
    intro h; have := small memsegTag hp16 h; simp [memsegTag] at this
  have hcallNeMem : (Aiur.Tiling.Bridge.CALL : ZMod p) ≠ (memsegTag : ZMod p) := by
    intro h
    have := small.inj (a := Aiur.Tiling.Bridge.CALL) (b := memsegTag)
      (by simp [Aiur.Tiling.Bridge.CALL]; omega) hp16 h
    simp [Aiur.Tiling.Bridge.CALL, memsegTag] at this
  have htblSupp := fixedTables_ledger_support callableId fixedMaps logBlowup extDegree tblTrs
    hTblAir hsat.fixedValid
  have hlenR : romTrs.length = romWidths.length := hromCnt.length_eq.symm
  -- Helper: within one width index `i`, every address appears at most once in `extractRomEntries`.
  have hsingleCount : ∀ (i : Nat) (hi : i < romWidths.length),
      let w := romWidths[i]
      let tr := romTrs[i]'(hlenR ▸ hi)
      ∀ x : ZMod p, ((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x)).length ≤ 1 := by
    intro i hi
    dsimp only
    set w := romWidths[i]
    set tr := romTrs[i]'(hlenR ▸ hi)
    have hwP : w < p := hwLt w (List.getElem_mem hi)
    have hbalW : ∀ x : ZMod p,
        ((((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x)).length : ZMod p) -
         (((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x - 1)).length : ZMod p)) +
        memsegBoundaryZ p (ivlsOf w) x = 0 := by
      intro x
      set k := trimZeros [(memsegTag : ZMod p), (w : ZMod p), x]
      have hkHead : k.head? = some (memsegTag : ZMod p) := by
        simp [k, trimZeros, hmemNe0]
      have hbal := congrArg (fun L : Ledger (ZMod p) => L k) hsat.logupBalanced
      rw [hledSplit, ← hfnLed] at hbal
      simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at hbal
      -- 1. Function ledger vanishes at `k`
      have hfn0 : Finsupp.mapDomain trimZeros (fnRows.map (FnRow.ledger callableId)).sum k = 0 := by
        rw [Aiur.Tiling.Grouped.mapDomain_list_sum]
        simp only [Tiling.System.ledger_list_sum, List.map_map]
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hv
        exact FnRow.trim_ledger_memseg_zero small hp16 callableId idOk (hfnHolds row hrow) hkHead
      -- 2. Fixed-table ledger vanishes at `k`
      have htbl0 : Finsupp.mapDomain trimZeros
          (List.zipWith circuitLedger
            ((lowerFixedTables (F := ZMod p) fixedMaps logBlowup).map (compileRetune logBlowup extDegree))
            tblTrs).sum k = 0 := by
        by_contra hne
        obtain ⟨u, hu, eu⟩ := Aiur.Tiling.Grouped.exists_of_mapDomain hne
        obtain ⟨mc, _, rfl⟩ := List.mem_map.mp (htblSupp u hu)
        have hh := trimZeros_head (t := [(memsegTag : ZMod p), (w : ZMod p), x]) eu.symm (by simp) hmemNe0
        simp [encode] at hh
        exact hcallNeMem hh
      -- 3. Public root vanishes at `k`
      have hrootNe : trimZeros (encode callableId root) ≠ k := by
        intro heq
        have hh := trimZeros_head (t := [(memsegTag : ZMod p), (w : ZMod p), x]) heq.symm (by simp) hmemNe0
        simp [encode] at hh
        exact hcallNeMem hh
      -- 4. ROM ledger at `k` equals width `w`'s scalar delta
      have hmapSum : ∀ (ls : List (Ledger (ZMod p))),
          Finsupp.mapDomain trimZeros ls.sum = (ls.map (Finsupp.mapDomain trimZeros)).sum := by
        intro ls
        induction ls with
        | nil => simp
        | cons a as ih => simp [Finsupp.mapDomain_add, ih]
      have hromEq : Finsupp.mapDomain trimZeros
          (List.zipWith circuitLedger
            ((lowerRomCircuitsWithLayout (F := ZMod p) romWidths true romLayout).map
              (compileRetune logBlowup extDegree)) romTrs).sum k =
          (((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x)).length : ZMod p) -
          (((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x - 1)).length : ZMod p) := by
        rw [hmapSum]
        simp only [Tiling.System.ledger_list_sum, List.map_map, Function.comp_def]
        have hsumIdx :
            ((List.zipWith circuitLedger
                ((lowerRomCircuitsWithLayout (F := ZMod p) romWidths true romLayout).map
                  (compileRetune logBlowup extDegree)) romTrs).map
              (fun L => Finsupp.mapDomain trimZeros L k)).sum =
            ((List.range romWidths.length).map fun j =>
              if hj : j < romWidths.length then
                Finsupp.mapDomain trimZeros
                  (circuitLedger (compileRetune logBlowup extDegree
                    (lowerKLaneRomCircuit romWidths[j] (romLayoutLanes romLayout romWidths[j]) true))
                    (romTrs[j]'(hlenR ▸ hj))) k
              else 0).sum := by
          refine congrArg List.sum ?_
          apply List.ext_getElem
          · simp [lowerRomCircuitsWithLayout_eq, hlenR]
          · intro j hj1 hj2
            have hj : j < romWidths.length := by simpa using hj2
            simp only [List.getElem_map, List.getElem_zipWith, List.getElem_range, hj, ↓reduceDIte]
            refine congrArg (fun L => Finsupp.mapDomain trimZeros L k) ?_
            refine congrArg (fun c => circuitLedger c (romTrs[j]'(hlenR ▸ hj))) ?_
            simp [lowerRomCircuitsWithLayout_eq]
        rw [hsumIdx]
        have hsingle : ∀ j ∈ List.range romWidths.length, j ≠ i →
            (if hj : j < romWidths.length then
              Finsupp.mapDomain trimZeros
                (circuitLedger (compileRetune logBlowup extDegree
                  (lowerKLaneRomCircuit romWidths[j] (romLayoutLanes romLayout romWidths[j]) true))
                  (romTrs[j]'(hlenR ▸ hj))) k
            else 0) = 0 := by
          intro j hj hne
          have hjLt : j < romWidths.length := List.mem_range.mp hj
          simp only [hjLt, ↓reduceDIte]
          have hwNe : romWidths[j] ≠ w := fun heq =>
            hne (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd)
              (a₁ := ⟨j, hjLt⟩) (a₂ := ⟨i, hi⟩) heq))
          have hsatJ : CircuitAirSatisfied
              (compileRetune logBlowup extDegree
                (lowerKLaneRomCircuit romWidths[j] (romLayoutLanes romLayout romWidths[j]) true))
              (romTrs[j]'(hlenR ▸ hjLt)) := by
            have := (List.forall₂_iff_get.mp hRomAir).2 j
              (by simp [lowerRomCircuitsWithLayout_eq, hjLt]) (by simp [hlenR, hjLt])
            simpa [lowerRomCircuitsWithLayout_eq] using this
          exact klaneRom_memseg_trim_other_width small hp16 hwP (hwLt _ (List.getElem_mem hjLt))
            hwNe logBlowup extDegree (romTrs[j]'(hlenR ▸ hjLt)) hsatJ x
        have hpick : ∀ (xs : List Nat) (f : Nat → ZMod p), xs.Nodup → i ∈ xs →
            (∀ j ∈ xs, j ≠ i → f j = 0) → (xs.map f).sum = f i := by
          intro xs f hndX hiX hzeroX
          induction xs with
          | nil => cases hiX
          | cons a as ih =>
              obtain ⟨haNot, hndAs⟩ := List.nodup_cons.mp hndX
              simp only [List.map_cons, List.sum_cons]
              rcases List.mem_cons.mp hiX with rfl | hmemAs
              · have hrest0 : (as.map f).sum = 0 :=
                  List.sum_eq_zero fun v hv => by
                    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
                    exact hzeroX b (List.mem_cons_of_mem _ hb) (fun h => haNot (h ▸ hb))
                rw [hrest0, add_zero]
              · rw [hzeroX a List.mem_cons_self (fun h => haNot (h ▸ hmemAs)), zero_add]
                exact ih hndAs hmemAs (fun b hb => hzeroX b (List.mem_cons_of_mem _ hb))
        rw [hpick (List.range romWidths.length) _ List.nodup_range (List.mem_range.mpr hi) hsingle]
        simp only [hi, ↓reduceDIte]
        have hsatI : CircuitAirSatisfied
            (compileRetune logBlowup extDegree
              (lowerKLaneRomCircuit w (romLayoutLanes romLayout w) true)) tr := by
          have := (List.forall₂_iff_get.mp hRomAir).2 i
            (by simp [lowerRomCircuitsWithLayout_eq, hi]) (by simp [hlenR, hi])
          simpa [lowerRomCircuitsWithLayout_eq, w, tr] using this
        exact klaneRom_memseg_trim_apply small hp16 w (romLayoutLanes romLayout w)
          logBlowup extDegree tr hsatI x
      -- 5. Preamble ledger at `k` equals `memsegBoundaryZ p (ivlsOf w) x`
      have hpreEq : Finsupp.mapDomain trimZeros (memsegPreambleLedger romWidths ivlsOf) k =
          memsegBoundaryZ p (ivlsOf w) x := by
        unfold memsegPreambleLedger
        rw [Aiur.Tiling.Grouped.mapDomain_list_sum]
        simp only [Tiling.System.ledger_list_sum, List.map_map]
        have hpair3 : ∀ (w' : Nat) (a : ZMod p),
            trimZeros [(memsegTag : ZMod p), (w' : ZMod p), a] = k ↔
              (w' : ZMod p) = (w : ZMod p) ∧ a = x := by
          intro w' a
          constructor
          · intro heq
            have h3 := trimZeros_inj_of_length (by simp) heq
            simp only [List.cons.injEq] at h3
            exact ⟨h3.2.1, h3.2.2.1⟩
          · rintro ⟨hw', ha⟩; simp [k, hw', ha]
        have hwidthEval : ∀ w' ∈ romWidths,
            Finsupp.mapDomain trimZeros
              (((ivlsOf w').map fun iv =>
                Finsupp.single [(memsegTag : ZMod p), (w' : ZMod p), (iv.2 : ZMod p)] 1 +
                Finsupp.single [(memsegTag : ZMod p), (w' : ZMod p), (iv.1 : ZMod p)] (-1)).sum) k =
            if w' = w then memsegBoundaryZ p (ivlsOf w) x else 0 := by
          intro w' hw'
          rw [Aiur.Tiling.Grouped.mapDomain_list_sum]
          simp only [Tiling.System.ledger_list_sum, List.map_map, Function.comp_def,
            Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.single_apply,
            hpair3]
          by_cases heqW : w' = w
          · subst heqW
            simp only [↓reduceIte, true_and]
            unfold memsegBoundaryZ
            congr 1
            apply List.map_congr_left
            intro iv _
            have h2' : ((iv.2 : ZMod p) = x) ↔ (x = (iv.2 : ZMod p)) := eq_comm
            have h1' : ((iv.1 : ZMod p) = x) ↔ (x = (iv.1 : ZMod p)) := eq_comm
            simp only [h1', h2']
            have hif : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
                ((if P then (1 : ZMod p) else 0) + if Q then (-1 : ZMod p) else 0) =
                (if P then (1 : ZMod p) else 0) - (if Q then (1 : ZMod p) else 0) := by
              intro P Q _ _
              by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
            exact hif (x = (iv.2 : ZMod p)) (x = (iv.1 : ZMod p))
          · have hcastNe : (w' : ZMod p) ≠ (w : ZMod p) := fun h =>
              heqW (small.inj (hwLt w' hw') hwP h)
            simp only [heqW, ↓reduceIte, hcastNe, false_and]
            apply List.sum_eq_zero
            intro v hv
            obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
            simp
        have hpickW : ∀ (ws : List Nat) (f : Nat → ZMod p), ws.Nodup → w ∈ ws →
            (∀ w' ∈ ws, w' ≠ w → f w' = 0) → (ws.map f).sum = f w := by
          intro ws f hndW hwIn hzeroW
          induction ws with
          | nil => cases hwIn
          | cons a as ih =>
              obtain ⟨haNot, hndAs⟩ := List.nodup_cons.mp hndW
              simp only [List.map_cons, List.sum_cons]
              rcases List.mem_cons.mp hwIn with rfl | hmemAs
              · have hrest0 : (as.map f).sum = 0 :=
                  List.sum_eq_zero fun v hv => by
                    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
                    exact hzeroW b (List.mem_cons_of_mem _ hb) (fun h => haNot (h ▸ hb))
                rw [hrest0, add_zero]
              · rw [hzeroW a List.mem_cons_self (fun h => haNot (h ▸ hmemAs)), zero_add]
                exact ih hndAs hmemAs (fun b hb => hzeroW b (List.mem_cons_of_mem _ hb))
        rw [hpickW romWidths _ hnd (List.getElem_mem hi) (fun w' hw' hne => by
          have := hwidthEval w' hw'; simpa [hne] using this)]
        simpa using hwidthEval w (List.getElem_mem hi)
      rw [hfn0, htbl0, hromEq, hpreEq] at hbal
      simp only [Finsupp.mapDomain_single, Finsupp.single_apply, hrootNe, ↓reduceIte] at hbal
      linear_combination hbal
    -- Apply `memseg_balance_implies_unique_zmod`
    have hsumLe : (∑ x : ZMod p,
        ((extractRomEntries w romLayout tr).filter fun e => decide (e.1 = x)).length) =
        (extractRomEntries w romLayout tr).length := by
      have hcard : ∀ (es : List (ZMod p × List (ZMod p))),
          (∑ x : ZMod p, (es.filter fun e => decide (e.1 = x)).length) = es.length := by
        intro es
        induction es with
        | nil => simp
        | cons e rest ih =>
            simp only [List.filter_cons, apply_ite List.length, List.length_cons]
            have hstep : (∑ x : ZMod p,
                (if decide (e.1 = x) = true then
                  (rest.filter fun e' => decide (e'.1 = x)).length + 1
                else (rest.filter fun e' => decide (e'.1 = x)).length)) =
                (∑ x : ZMod p, (rest.filter fun e' => decide (e'.1 = x)).length) +
                (∑ x : ZMod p, if e.1 = x then 1 else 0) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun x _ => ?_
              by_cases hx : e.1 = x <;> simp [hx]
            rw [hstep, ih]
            simp
      exact hcard (extractRomEntries w romLayout tr)
    have hcntI : (extractRomEntries w romLayout tr).length + 1 < p :=
      (List.forall₂_iff_get.mp hromCnt).2 i hi (by simp [hlenR, hi])
    intro x
    exact (memseg_balance_implies_unique_zmod (hdisj w (List.getElem_mem hi))
      (hsumLe ▸ hcntI) hbalW x).2
  -- Deduce `WidthROM.Valid` from per-width count ≤ 1 and `romWidths.Nodup`!
  intro a ha b hb haddrEq hlenEq
  unfold extractWidthROM at ha hb
  obtain ⟨xsA, hxsA, haIn⟩ := List.mem_flatten.mp ha
  obtain ⟨xsB, hxsB, hbIn⟩ := List.mem_flatten.mp hb
  obtain ⟨iA, hiA, hxsAEq⟩ := List.mem_iff_getElem.mp hxsA
  obtain ⟨iB, hiB, hxsBEq⟩ := List.mem_iff_getElem.mp hxsB
  have hiALt : iA < romWidths.length := by simp [List.length_zipWith, hlenR] at hiA; exact hiA
  have hiBLt : iB < romWidths.length := by simp [List.length_zipWith, hlenR] at hiB; exact hiB
  rw [List.getElem_zipWith] at hxsAEq hxsBEq
  subst hxsAEq; subst hxsBEq
  have hlenA : a.2.length = romWidths[iA] := klaneRomEntries_payload_length _ _ _ haIn
  have hlenB : b.2.length = romWidths[iB] := klaneRomEntries_payload_length _ _ _ hbIn
  have hwEq : romWidths[iA] = romWidths[iB] := hlenA.symm.trans (hlenEq.trans hlenB)
  have hiEq : iA = iB := congrArg Fin.val
    ((List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨iA, hiALt⟩) (a₂ := ⟨iB, hiBLt⟩) hwEq)
  subst hiEq
  have hle1 := hsingleCount iA hiALt a.1
  set es := extractRomEntries romWidths[iA] romLayout (romTrs[iA]'(hlenR ▸ hiALt))
  have haF : a ∈ es.filter fun e => decide (e.1 = a.1) :=
    List.mem_filter.mpr ⟨haIn, decide_eq_true rfl⟩
  have hbF : b ∈ es.filter fun e => decide (e.1 = a.1) :=
    List.mem_filter.mpr ⟨hbIn, decide_eq_true haddrEq.symm⟩
  cases hfilt : es.filter fun e => decide (e.1 = a.1) with
  | nil => rw [hfilt] at haF; cases haF
  | cons x rest =>
      rw [hfilt, List.length_cons] at hle1
      have hrestNil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrestNil
      rw [hfilt, List.mem_singleton] at haF hbF
      rw [haF, hbF]

/-! ### End-to-End Composition Corollaries with `Physical.Prepared.checkDepthPlan_sound` -/

section GoldilocksEndToEnd

open Aiur.Library.U32.Goldilocks (modulus)

local notation "GF" => Library.U32.Goldilocks.F

/-- Goldilocks `SmallCast` bound for `2^63 < Goldilocks.modulus`. -/
theorem goldilocks_smallCast_63 : SmallCast GF (2 ^ 63) :=
  smallCast_zmod modulus (by norm_num [modulus])

theorem goldilocks_sixteen_lt_63 : 16 < 2 ^ 63 := by norm_num

/-- **End-to-End CheckDepthPlan + Memo Bridge (Unsegmented Goldilocks):**
Explicitly composes `Physical.Prepared.checkDepthPlan_sound`,
`extractWidthROM_valid_unsegmented`, and `lowerFullSystem_satisfied_implies_checkMemo`.
Delivers the exact triple `(DepthCertified ∧ cfg.bits ≤ 24 ∧ WellFormedActivation)`,
`rom.Valid`, and `∃ wrows, wrows.length ≤ maxBatchRows ∧ plan.checkMemo (Erasure.rawROM rom) root wrows = .ok ()`
consumed by downstream compiled-certificate soundness theorems. -/
theorem lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks
    {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries}
    (compiled : GenericArtifact specialized)
    (physical : Physical.Prepared compiled.artifact)
    {cfg : Depth.Config} {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    {measures : Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.inlined.program cfg measures plan = true)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (root : Circuit.Message GF)
    (traces : List (CircuitTrace GF))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Shaped.check (Depth.system cfg physical.system) (allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Depth.system cfg physical.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    let rom := extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)
    (Physical.Prepared.DepthCertified compiled physical cfg ∧ cfg.bits ≤ 24 ∧ plan.WellFormedActivation) ∧
    rom.Valid ∧
    ∃ wrows : List (WeightedRow GF),
      wrows.length ≤ maxBatchRows ∧
      plan.checkMemo (Erasure.rawROM rom) root wrows = .ok () := by
  have hplan := Physical.Prepared.checkDepthPlan_sound certOK
  obtain ⟨_, _, hRomAir, _, _⟩ := hsat.split
  set rom := extractWidthROM romWidths romLayout
    (romTracesOf callableId plan fixedMaps logBlowup traces)
  have hromValid : rom.Valid :=
    extractWidthROM_valid_unsegmented goldilocks_smallCast_63 romWidths hndRom romLayout
      logBlowup extDegree _ hRomAir hromCap
  have hctx : (Depth.system cfg physical.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨hformed, hpub, _, hwf⟩ := System.checkContext_iff.mp hctxEmpty
    exact System.checkContext_iff.mpr ⟨hformed, hpub, Erasure.rawROM_valid hromValid, hwf⟩
  obtain ⟨wrows, hlen, hchecked⟩ :=
    lowerFullSystem_satisfied_implies_checkMemo callableId idOk plan hplan.2.2 names fixedMaps
      romWidths logBlowup false extDegree romLayout root 0 traces hsat
      goldilocks_smallCast_63 goldilocks_sixteen_lt_63 hbudget hromWidths hmemWidth hshaped hctx
  exact ⟨hplan, hromValid, wrows, hlen.trans hrowsBound, hchecked⟩

/-- **End-to-End Lowered Multi-STARK → Source Evaluation (Unsegmented Goldilocks):**
Composes `Physical.Prepared.checkDepthPlan_sound` + `extractWidthROM_valid_unsegmented`
+ `lowerFullSystem_satisfied_implies_checkMemo` +
`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`.
Neither `hinsp`, nor `hbal`, nor `rom.Valid` is assumed. -/
theorem lowerFullSystem_checkDepthPlan_eval_goldilocks
    {program : Aiur.Modules.Program GF}
    (prepared : Aiur.Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    {measures : Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.circuit.inlined.program cfg measures plan = true)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {args : List (SourceValue GF)} {result : Value GF}
    {wires : List (WireValue GF)} {output : WireValue GF}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (traces : List (CircuitTrace GF))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Shaped.check (Depth.system cfg physical.system) (allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Depth.system cfg physical.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    let rom := extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)
    rom.Valid ∧
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  obtain ⟨⟨certified, bits, activated⟩, hromValid, wrows, hbound, hchecked⟩ :=
    lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks compiled.circuit physical plan
      certOK callableId idOk names fixedMaps romWidths hndRom logBlowup extDegree romLayout root
      traces hsat hrowsBound hbudget hromCap hromWidths hmemWidth hshaped hctxEmpty
  exact ⟨hromValid,
    prepared.depth_grouped_activated_heap_sound_goldilocks compiled physical certified bits plan
      activated selected hromValid signed rooted outside hbound hchecked arguments decoded⟩

/-- **End-to-End Lowered Multi-STARK → Source Evaluation (Segmented Goldilocks with `MEMSEG` Preamble):**
Composes `Physical.Prepared.checkDepthPlan_sound` + `extractWidthROM_valid_segmented_zmod`
+ `lowerFullSystem_satisfied_implies_checkMemo` +
`Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks` for batched/sharded
proofs with sorted disjoint `MEMSEG` closure intervals. -/
theorem lowerFullSystem_checkDepthPlan_eval_segmented_goldilocks
    {program : Aiur.Modules.Program GF}
    (prepared : Aiur.Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    {measures : Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.circuit.inlined.program cfg measures plan = true)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {args : List (SourceValue GF)} {result : Value GF}
    {wires : List (WireValue GF)} {output : WireValue GF}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (ivlsOf : Nat → List (Nat × Nat))
    (hdisj : ∀ w ∈ romWidths, DisjointIntervalsP modulus (ivlsOf w))
    (traces : List (CircuitTrace GF))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup true
      extDegree romLayout root (memsegPreambleLedger romWidths ivlsOf) traces)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup true extDegree romLayout)
      traces < 2 ^ 63)
    (hromCnt : List.Forall₂ (fun w tr => (extractRomEntries w romLayout tr).length + 1 < modulus)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Shaped.check (Depth.system cfg physical.system) (allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Depth.system cfg physical.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    let rom := extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)
    rom.Valid ∧
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  obtain ⟨certified, bits, activated⟩ := Physical.Prepared.checkDepthPlan_sound certOK
  set rom := extractWidthROM romWidths romLayout
    (romTracesOf callableId plan fixedMaps logBlowup traces)
  have hp16 : 16 < modulus := by norm_num [modulus]
  have h63lt : 2 ^ 63 < modulus := by norm_num [modulus]
  have hromValid : rom.Valid :=
    extractWidthROM_valid_segmented_zmod hp16 callableId idOk plan fixedMaps romWidths hndRom
      (fun w hw => lt_trans (hromWidths w hw) h63lt) logBlowup extDegree romLayout root ivlsOf
      hdisj traces hsat hromCnt
  have hctx : (Depth.system cfg physical.system).checkContext (Erasure.rawROM rom) root = .ok () := by
    obtain ⟨hformed, hpub, _, hwf⟩ := System.checkContext_iff.mp hctxEmpty
    exact System.checkContext_iff.mpr ⟨hformed, hpub, Erasure.rawROM_valid hromValid, hwf⟩
  obtain ⟨wrows, hlen, hchecked⟩ :=
    lowerFullSystem_satisfied_implies_checkMemo callableId idOk plan activated names fixedMaps
      romWidths logBlowup true extDegree romLayout root (memsegPreambleLedger romWidths ivlsOf)
      traces hsat goldilocks_smallCast_63 goldilocks_sixteen_lt_63 hbudget hromWidths hmemWidth
      hshaped hctx
  exact ⟨hromValid,
    prepared.depth_grouped_activated_heap_sound_goldilocks compiled physical certified bits plan
      activated selected hromValid signed rooted outside (hlen.trans hrowsBound) hchecked
      arguments decoded⟩

/-- **Full Stage-2 Grouped Rational LogUp → Source Evaluation (Goldilocks):**
Starts directly from the retuned degree-3 stage-2 chained accumulator constraints
(`CircuitStage2Satisfied`) over any extension field `embed : GF →+* K` with
non-degenerate challenges `(β, γ)`, derives `LoweredSystemSatisfied` via
`batch_stage2_logup_eq_trimmed_sum` + `trimmed_ledger_zero_of_logup_sum`, and
reaches `prepared.EvalFn` with zero intermediate assumptions. -/
theorem lowerFullSystem_stage2_checkDepthPlan_eval_goldilocks
    {K : Type} [Field K] (embed : GF →+* K) (β γ : K)
    {program : Aiur.Modules.Program GF}
    (prepared : Aiur.Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    {measures : Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.circuit.inlined.program cfg measures plan = true)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {args : List (SourceValue GF)} {result : Value GF}
    {wires : List (WireValue GF)} {output : WireValue GF}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (traces : List (CircuitTrace GF))
    (airOk : List.Forall₂ CircuitAirSatisfied
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces)
    (fixedValid : FixedTablesValid (Depth.system cfg physical.system) callableId
      (lowerFixedTables (F := GF) fixedMaps logBlowup)
      (tblTracesOf callableId plan fixedMaps logBlowup traces))
    (enablesOk : ∀ c ∈ allChips plan, checkChipEnables c = true)
    (acc : Nat → Nat → Nat → K) (accInitial accFinal : Nat → K)
    (hstage2 : ∀ (i : Nat)
      (hi : i < (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
        extDegree romLayout).length),
      CircuitStage2Satisfied embed β γ
        (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
          extDegree romLayout)[i]
        (traces[i]'(airOk.length_eq.symm ▸ hi))
        (acc i) (accInitial i) (accFinal i))
    (hclose :
      ((List.range (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
        extDegree romLayout).length).map fun i => accFinal i - accInitial i).sum +
        (fingerprint β γ ((encode callableId root).map embed))⁻¹ = 0)
    (hden :
      let L := Finsupp.mapDomain trimZeros
        ((List.zipWith circuitLedger
            (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
              extDegree romLayout) traces).sum +
          Finsupp.single (encode callableId root) 1)
      ∀ k ∈ L.support, fingerprint β γ (k.map embed) ≠ 0)
    (hsep :
      let L := Finsupp.mapDomain trimZeros
        ((List.zipWith circuitLedger
            (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
              extDegree romLayout) traces).sum +
          Finsupp.single (encode callableId root) 1)
      ∀ k ∈ L.support, ∀ k' ∈ L.support, k' ≠ k →
        rlcEval γ (k'.map embed) ≠ rlcEval γ (k.map embed))
    (hnonroot :
      let L := Finsupp.mapDomain trimZeros
        ((List.zipWith circuitLedger
            (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
              extDegree romLayout) traces).sum +
          Finsupp.single (encode callableId root) 1)
      let Q := logupClearedPoly L.support (fun k => rlcEval γ (k.map embed)) (fun k => embed (L k))
      Q ≠ 0 → Q.eval β ≠ 0)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Shaped.check (Depth.system cfg physical.system) (allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Depth.system cfg physical.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    let rom := extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)
    rom.Valid ∧
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  have hsum0 := batch_stage2_logup_eq_trimmed_sum embed β γ
    (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
    traces acc accInitial accFinal (encode callableId root) 0
    airOk.length_eq.symm hstage2 (by simpa [ledgerLogUpSum_zero] using hclose)
  simp only [add_zero] at hsum0
  have hbal : Finsupp.mapDomain trimZeros
      ((List.zipWith circuitLedger
          (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false
            extDegree romLayout) traces).sum +
        Finsupp.single (encode callableId root) 1 + 0) = 0 := by
    rw [add_zero]
    exact trimmed_ledger_zero_of_logup_sum embed β γ _ hden hsep hnonroot hsum0
  have hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces :=
    ⟨airOk, fixedValid, enablesOk, fun _ h => absurd rfl h, hbal⟩
  exact lowerFullSystem_checkDepthPlan_eval_goldilocks prepared compiled physical plan certOK
    selected signed rooted outside arguments decoded callableId idOk names fixedMaps romWidths
    hndRom logBlowup extDegree romLayout traces hsat hrowsBound hbudget hromCap hromWidths
    hmemWidth hshaped hctxEmpty

end GoldilocksEndToEnd

end PlanBridge

/-! ## 7. Axiom Audit Guards -/

/-- info: 'Aiur.MultiStarkBridge.circuitRowSatisfied_retune_compile_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms circuitRowSatisfied_retune_compile_iff

/-- info: 'Aiur.MultiStarkBridge.circuitRowLedger_retune_compile_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms circuitRowLedger_retune_compile_eq

/-- info: 'Aiur.MultiStarkBridge.batch_stage2_logup_eq_trimmed_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batch_stage2_logup_eq_trimmed_sum

/-- info: 'Aiur.MultiStarkBridge.trimmed_ledger_zero_of_logup_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trimmed_ledger_zero_of_logup_sum

/-- info: 'Aiur.MultiStarkBridge.card_stage2_logup_bad_beta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_stage2_logup_bad_beta_le

/-- info: 'Aiur.MultiStarkBridge.checkEnables_implies_unit_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkEnables_implies_unit_weight

/-- info: 'Aiur.MultiStarkBridge.extractWidthROM_valid_unsegmented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extractWidthROM_valid_unsegmented

/-- info: 'Aiur.MultiStarkBridge.extractWidthROM_valid_segmented_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extractWidthROM_valid_segmented_zmod

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_row_implies_inspectRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_row_implies_inspectRow

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_satisfied_implies_checkMemo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_satisfied_implies_checkMemo

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_checkDepthPlan_eval_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_checkDepthPlan_eval_goldilocks

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_checkDepthPlan_eval_segmented_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_checkDepthPlan_eval_segmented_goldilocks

/-- info: 'Aiur.MultiStarkBridge.lowerFullSystem_stage2_checkDepthPlan_eval_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerFullSystem_stage2_checkDepthPlan_eval_goldilocks

end Aiur.MultiStarkBridge
