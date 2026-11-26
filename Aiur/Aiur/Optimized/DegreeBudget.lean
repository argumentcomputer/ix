import Aiur.MultiStarkSpec
import Aiur.Optimized.CheckedLayout

/-!
# Quotient-Aware Degree Budgeting (`C7b`)

In `multi-stark`, a circuit's quotient polynomial degree is determined by the
maximum of its user constraint degree and its LogUp lookup-group degree:

  `quotientDegree = nextPow2 (max (max userMaxDegree logupMaxDegree) 2 - 1)`

For a STARK with blowup factor `B = 2 ^ logBlowup`:
* `logBlowup = 1` (`B = 2`) supports `q ≤ 2`, i.e. algebraic constraint degree `≤ 3`.
* `logBlowup = 2` (`B = 4`, v6 default) supports `q ≤ 4`, i.e. algebraic constraint degree `≤ 5`.
* `logBlowup = 3` (`B = 8`) supports `q ≤ 8`, i.e. algebraic constraint degree `≤ 9`.

Whenever a chip has LogUp lookups chunked by `lookup_groups::retune` at
`lookup_group_size ≥ 3` (for degree-1 lookups, `chunkLogupDegree ≥ 4`, forcing
`q = 4`), raising `Aiur.Optimized.Config.maxDegree` from `3` to `5` (`q + 1`)
incurs **zero** additional quotient degree while allowing `Aiur.Optimized.Degree`
and `Layout` to eliminate auxiliary witness columns that were previously allocated
solely to split degree-4/5 expressions down to degree-3.

This module provides:
1. Exact quotient-degree budget arithmetic and `C7b` free-degree-slack theorems
   (`quotientDegreeFromMax_le_blowup`, `quotientDegreeFromMax_gt_blowup`,
   `quotient_free_slack`, `logup_group3_free_degree5`, `logup_group7_free_degree9`).
2. Per-chip and system-wide Multi-STARK cost analysis (`analyzeChip`,
   `budgetAnalysis`, `compareBudgets`) matching `Aiur.MultiStarkSpec.retune`.
3. Quotient-aware configuration selection and compilation (`recommendedConfig`,
   `chooseConfig`, `compileQuotientAware`, `layOutQuotientAware`).
4. Certified end-to-end soundness (`compileQuotientAware_degreeBound`,
   `compileQuotientAware_sound`, `compileQuotientAware_sound_goldilocks`,
   `compileQuotientAware_check_sound`, `compileQuotientAware_check_complete`,
   `compile_degree_invariance`, `layOutQuotientAware_correct`) composing directly
   with `DegreeCertificate`, `AllocationCertificate`, and
   `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound`.

Zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only.
-/

set_option autoImplicit false

namespace Aiur.Optimized.DegreeBudget

open Aiur Aiur.Circuit Aiur.Optimized Aiur.MultiStarkSpec

/-! ## 1. STARK Blowup & Quotient Degree Arithmetic (`C7b`) -/

/-- Default v6 Goldilocks cubic extension degree (`ExtVal3`). -/
def v6ExtDegree : Nat := 3

/-- STARK LDE blowup factor `B = 2 ^ logBlowup`. -/
def starkBlowup (logBlowup : Nat) : Nat := 2 ^ logBlowup

/-- Maximum algebraic constraint degree supported at blowup `2 ^ logBlowup`.
Non-ZK STARKs satisfy `quotientDegree = nextPow2 (max d 2 - 1) ≤ 2 ^ logBlowup`
iff `d ≤ 2 ^ logBlowup + 1`; ZK STARKs satisfy `nextPow2 (max d 1) ≤ 2 ^ logBlowup`
iff `d ≤ 2 ^ logBlowup`. -/
def maxConstraintDegreeForBlowup (logBlowup : Nat) (isZk : Bool := false) : Nat :=
  if isZk then 2 ^ logBlowup else 2 ^ logBlowup + 1

/-- Effective `Aiur.Optimized.Config.maxDegree` cap for `logBlowup`, clamped to at
least `3` (the minimum degree cap required by `Aiur.Optimized.compile`). -/
def effectiveMaxDegree (logBlowup : Nat) (isZk : Bool := false) : Nat :=
  max 3 (maxConstraintDegreeForBlowup logBlowup isZk)

/-- Maximum algebraic constraint degree that fits inside a given quotient degree
`q` with zero increase to `q`, clamped to `≥ 3`. -/
def freeConstraintDegreeForQuotient (quotient : Nat) (isZk : Bool := false) : Nat :=
  max 3 (if isZk then quotient else quotient + 1)

/-- Candidate `maxDegree` budgets for `logBlowup`: ascending power-of-2
thresholds up to `effectiveMaxDegree logBlowup isZk` (e.g., `[3]` for
`logBlowup ≤ 1`, `[3, 5]` for `logBlowup = 2`, `[3, 5, 9]` for `logBlowup = 3`). -/
def candidateMaxDegrees (logBlowup : Nat) (isZk : Bool := false) : List Nat :=
  if logBlowup ≤ 1 then [3]
  else
    ((List.range logBlowup).map fun i =>
      effectiveMaxDegree (i + 1) isZk).dedup

theorem nextPow2_pos {n : Nat} (hn : 1 ≤ n) : 1 ≤ nextPow2 n := by
  unfold nextPow2
  split_ifs with h0 h1
  · omega
  · omega
  · exact Nat.one_le_two_pow

theorem nextPow2_le_two_pow {n k : Nat} (h : n ≤ 2 ^ k) : nextPow2 n ≤ 2 ^ k := by
  unfold nextPow2
  split_ifs with h0 h1
  · exact Nat.zero_le _
  · exact Nat.one_le_two_pow
  · have hpos : n - 1 ≠ 0 := by omega
    have hlt : n - 1 < 2 ^ k := by omega
    have hlog : Nat.log2 (n - 1) < k := (Nat.log2_lt hpos).mpr hlt
    exact Nat.pow_le_pow_right (by omega) hlog

theorem nextPow2_gt_two_pow {n k : Nat} (h : 2 ^ k < n) : 2 ^ k < nextPow2 n := by
  have hkpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hge2 : ¬ n ≤ 1 := by omega
  have hne0 : n ≠ 0 := by omega
  unfold nextPow2
  simp only [hne0, ↓reduceIte, hge2]
  have hpos : n - 1 ≠ 0 := by omega
  have hle : 2 ^ k ≤ n - 1 := by omega
  have hlog : k ≤ Nat.log2 (n - 1) := (Nat.le_log2 hpos).mpr hle
  exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_of_le hlog)

theorem nextPow2_mono {a b : Nat} (h : a ≤ b) : nextPow2 a ≤ nextPow2 b := by
  unfold nextPow2
  split_ifs with ha0 ha1 hb0 hb1
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · omega
  · exact le_rfl
  · exact Nat.one_le_two_pow
  · omega
  · omega
  · have haPos : a - 1 ≠ 0 := by omega
    have hbPos : b - 1 ≠ 0 := by omega
    have hlog : Nat.log2 (a - 1) ≤ Nat.log2 (b - 1) := by
      have hpow : 2 ^ Nat.log2 (a - 1) ≤ a - 1 := (Nat.le_log2 haPos).mp le_rfl
      exact (Nat.le_log2 hbPos).mpr (Nat.le_trans hpow (by omega))
    exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_succ hlog)

theorem quotientDegreeFromMax_mono {a b : Nat} (h : a ≤ b) :
    quotientDegreeFromMax a ≤ quotientDegreeFromMax b := by
  unfold quotientDegreeFromMax
  apply nextPow2_mono
  omega

/-- Any algebraic constraint degree `d ≤ 2 ^ logBlowup + 1` fits within the STARK
blowup `2 ^ logBlowup` (non-ZK). -/
theorem quotientDegreeFromMax_le_blowup {d logBlowup : Nat} (hlog : 1 ≤ logBlowup)
    (hd : d ≤ maxConstraintDegreeForBlowup logBlowup false) :
    quotientDegreeFromMax d ≤ 2 ^ logBlowup := by
  unfold quotientDegreeFromMax
  apply nextPow2_le_two_pow
  have h2 : 2 ≤ 2 ^ logBlowup := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hlog
    simpa using this
  unfold maxConstraintDegreeForBlowup at hd
  simp only [Bool.false_eq_true, ↓reduceIte] at hd
  omega

/-- Any algebraic constraint degree `d > 2 ^ logBlowup + 1` exceeds the STARK
blowup `2 ^ logBlowup` (non-ZK). -/
theorem quotientDegreeFromMax_gt_blowup {d logBlowup : Nat} (hlog : 1 ≤ logBlowup)
    (hd : maxConstraintDegreeForBlowup logBlowup false < d) :
    2 ^ logBlowup < quotientDegreeFromMax d := by
  unfold quotientDegreeFromMax
  apply nextPow2_gt_two_pow
  have h2 : 2 ≤ 2 ^ logBlowup := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hlog
    simpa using this
  unfold maxConstraintDegreeForBlowup at hd
  simp only [Bool.false_eq_true, ↓reduceIte] at hd
  omega

/-- **Core `C7b` Free-Degree-Slack Theorem**: if LogUp lookup chunking already
determines quotient degree `q = 2 ^ k` (`k ≥ 1`), then any user constraint degree
`userDeg ≤ 2 ^ k + 1` (`= q + 1`) keeps the circuit's Multi-STARK quotient degree
strictly unchanged at `2 ^ k`. -/
theorem quotient_free_slack {userDeg logupDeg k : Nat}
    (hlogup : quotientDegreeFromMax logupDeg = 2 ^ k)
    (hk : 1 ≤ k) (huser : userDeg ≤ 2 ^ k + 1) :
    quotientDegreeFromMax (max userDeg logupDeg) = 2 ^ k := by
  apply Nat.le_antisymm
  · by_cases hle : userDeg ≤ logupDeg
    · rw [Nat.max_eq_right hle, hlogup]
    · rw [Nat.max_eq_left (Nat.le_of_not_le hle)]
      exact quotientDegreeFromMax_le_blowup hk huser
  · rw [← hlogup]
    exact quotientDegreeFromMax_mono (Nat.le_max_right userDeg logupDeg)

/-- Concrete `C7b` corollary at `logBlowup = 2` (`q = 4`): a 3-lookup degree-1
LogUp chunk already has `chunkLogupDegree = 4` (`q = 4`), so any user constraint
degree `≤ 5` has zero quotient-degree cost. -/
theorem logup_group3_free_degree5 {userDeg : Nat} (huser : userDeg ≤ 5) :
    quotientDegreeFromMax (max userDeg (chunkLogupDegree [(1, 1), (1, 1), (1, 1)])) = 4 := by
  have hchunk : chunkLogupDegree [(1, 1), (1, 1), (1, 1)] = 4 := by decide
  rw [hchunk]
  exact quotient_free_slack (k := 2) (by decide) (by omega) huser

/-- Concrete `C7b` corollary at `logBlowup = 3` (`q = 8`): a 7-lookup degree-1
LogUp chunk already has `chunkLogupDegree = 8` (`q = 8`), so any user constraint
degree `≤ 9` has zero quotient-degree cost. -/
theorem logup_group7_free_degree9 {userDeg : Nat} (huser : userDeg ≤ 9) :
    quotientDegreeFromMax
      (max userDeg (chunkLogupDegree [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1)])) = 8 := by
  have hchunk :
      chunkLogupDegree [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1)] = 8 := by
    decide
  rw [hchunk]
  exact quotient_free_slack (k := 3) (by decide) (by omega) huser

theorem effectiveMaxDegree_mono {a b : Nat} (hab : a ≤ b) (isZk : Bool) :
    effectiveMaxDegree a isZk ≤ effectiveMaxDegree b isZk := by
  unfold effectiveMaxDegree maxConstraintDegreeForBlowup
  have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hab
  cases isZk <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem candidateMaxDegrees_nonempty (logBlowup : Nat) (isZk : Bool := false) :
    candidateMaxDegrees logBlowup isZk ≠ [] := by
  unfold candidateMaxDegrees
  split_ifs with h
  · simp
  · intro hemp
    have hmem : effectiveMaxDegree 1 isZk ∈
        ((List.range logBlowup).map fun i => effectiveMaxDegree (i + 1) isZk).dedup := by
      rw [List.mem_dedup, List.mem_map]
      exact ⟨0, List.mem_range.mpr (by omega), rfl⟩
    rw [hemp] at hmem
    cases hmem

theorem candidateMaxDegrees_bounds {logBlowup d : Nat} {isZk : Bool}
    (hd : d ∈ candidateMaxDegrees logBlowup isZk) :
    3 ≤ d ∧ d ≤ effectiveMaxDegree logBlowup isZk := by
  unfold candidateMaxDegrees at hd
  split_ifs at hd with h
  · simp only [List.mem_singleton] at hd
    subst hd
    exact ⟨le_rfl, Nat.le_max_left 3 _⟩
  · rw [List.mem_dedup, List.mem_map] at hd
    rcases hd with ⟨i, hi, rfl⟩
    have hiLt : i < logBlowup := List.mem_range.mp hi
    exact ⟨Nat.le_max_left 3 _, effectiveMaxDegree_mono (by omega) isZk⟩

/-! ## 2. Exact Per-Chip & System Multi-STARK Cost Analysis (`budgetAnalysis`) -/

/-- Per-chip Multi-STARK width, lookup grouping, and quotient-degree report. -/
structure ChipBudgetReport where
  name : String
  rawCols : Nat
  stage1Cols : Nat
  userMaxDegree : Nat
  callLookups : Nat
  romLookups : Nat
  totalLookups : Nat
  hasLookups : Bool
  lookupGroupSize : Nat
  stage2Cols : Nat
  quotientDegree : Nat
  totalCols : Nat
  /-- Column-slope proxy `(stage1 + stage2 + quotient * extDegree)`, proportional
  to the `(blowup + 1)` FFT column work per row in `lookup_groups::FftCost`. -/
  weightedColumnCost : Nat
  /-- Maximum user constraint degree that fits in `quotientDegree` for free. -/
  freeDegreeCap : Nat
  deriving Repr, BEq, DecidableEq

/-- Analyze a single physical chip under Multi-STARK `Activation.compile` +
`lowerSingleChip` + `compileCircuit` + `lookup_groups::retune`. -/
def analyzeChip {F : Type} [Field F] [DecidableEq F] (chip : Circuit.Chip F)
    (logBlowup : Nat) (extDegree : Nat := v6ExtDegree) : ChipBudgetReport :=
  let activated := Activation.compile chip
  let input := lowerSingleChip (fun _ => 0) activated chip.numVars
  let initial := compileCircuit input extDegree
  let tuned := retune initial (starkBlowup logBlowup) extDegree
  let stage1 := tuned.mainWidth
  let stage2 := tuned.stage2Width
  let q := tuned.quotientDegree
  { name := chip.name
    rawCols := chip.numVars
    stage1Cols := stage1
    userMaxDegree := chip.stats.maxConstraintDegree
    callLookups := chip.sends.length
    romLookups := chip.memory.length
    totalLookups := tuned.lookups.length
    hasLookups := chip.sends.length + chip.memory.length > 0
    lookupGroupSize := tuned.lookupGroupSize
    stage2Cols := stage2
    quotientDegree := q
    totalCols := stage1 + stage2
    weightedColumnCost := stage1 + stage2 + q * extDegree
    freeDegreeCap := freeConstraintDegreeForQuotient q }

/-- System-wide Multi-STARK column and quotient-degree budget report. -/
structure SystemBudgetReport where
  maxDegree : Nat
  logBlowup : Nat
  extDegree : Nat
  chips : List ChipBudgetReport
  totalRawCols : Nat
  totalStage1Cols : Nat
  totalStage2Cols : Nat
  totalCols : Nat
  maxChipCols : Nat
  maxQuotientDegree : Nat
  totalWeightedCost : Nat
  hasAnyLookups : Bool
  deriving Repr, BEq, DecidableEq

/-- Compute exact per-chip and aggregate Multi-STARK column + quotient budgets
for a compiled `Circuit.System F`. -/
def budgetAnalysis {F : Type} [Field F] [DecidableEq F] (system : Circuit.System F)
    (maxDegree logBlowup : Nat) (extDegree : Nat := v6ExtDegree) : SystemBudgetReport :=
  let chipReports := system.chips.map (analyzeChip · logBlowup extDegree)
  let totalRaw := chipReports.foldl (fun acc r => acc + r.rawCols) 0
  let totalS1 := chipReports.foldl (fun acc r => acc + r.stage1Cols) 0
  let totalS2 := chipReports.foldl (fun acc r => acc + r.stage2Cols) 0
  let maxChip := chipReports.foldl (fun acc r => max acc r.stage1Cols) 0
  let maxQ := chipReports.foldl (fun acc r => max acc r.quotientDegree) 1
  let totalW := chipReports.foldl (fun acc r => acc + r.weightedColumnCost) 0
  let anyLookups := chipReports.any (·.hasLookups)
  { maxDegree
    logBlowup
    extDegree
    chips := chipReports
    totalRawCols := totalRaw
    totalStage1Cols := totalS1
    totalStage2Cols := totalS2
    totalCols := totalS1 + totalS2
    maxChipCols := maxChip
    maxQuotientDegree := maxQ
    totalWeightedCost := totalW
    hasAnyLookups := anyLookups }

/-- Lexicographic cost comparator: prefers lower total FFT column cost
`(Stage-1 + Stage-2 + quotient * extDegree)`, breaking ties by fewer
`Stage-1 + Stage-2` columns, fewer Stage-1 columns, and smaller max chip width. -/
def betterReport (cand best : SystemBudgetReport) : Bool :=
  cand.totalWeightedCost < best.totalWeightedCost ||
    (cand.totalWeightedCost == best.totalWeightedCost &&
      (cand.totalCols < best.totalCols ||
        (cand.totalCols == best.totalCols &&
          (cand.totalStage1Cols < best.totalStage1Cols ||
            (cand.totalStage1Cols == best.totalStage1Cols &&
              cand.maxChipCols < best.maxChipCols)))))

/-- Per-chip lexicographic cost comparator for `layOutQuotientAware`. -/
def betterChipReport (cand best : ChipBudgetReport) : Bool :=
  cand.weightedColumnCost < best.weightedColumnCost ||
    (cand.weightedColumnCost == best.weightedColumnCost &&
      (cand.totalCols < best.totalCols ||
        (cand.totalCols == best.totalCols && cand.stage1Cols < best.stage1Cols)))

/-! ## 3. Quotient-Aware Config Selection & Compilation -/

/-- Fast structural heuristic: given an existing compiled system and target
`logBlowup`, select `effectiveMaxDegree logBlowup isZk` (e.g. `5` for
`logBlowup = 2`, `9` for `logBlowup = 3`) whenever any chip has
`sends.length + memory.length > 0`, otherwise keep `3`. -/
def recommendedConfig {F : Type} (system : Circuit.System F) (logBlowup : Nat)
    (base : Config := {}) (isZk : Bool := false) : Config :=
  let hasLookups := system.chips.any fun c => c.sends.length + c.memory.length > 0
  let deg :=
    if logBlowup ≥ 2 && hasLookups then effectiveMaxDegree logBlowup isZk
    else 3
  { base with maxDegree := deg }

/-- Certified output of quotient-aware compilation on `Modules.Prepared prog`.
Carries the chosen `Config`, the compiled `ModulesArtifact prepared`, the
winning and candidate `SystemBudgetReport`s, and the exact compilation equality. -/
structure BudgetedArtifact {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} (prepared : Modules.Prepared prog)
    (logBlowup : Nat) (isZk : Bool := false) where
  chosenConfig : Config
  artifact : ModulesArtifact prepared
  report : SystemBudgetReport
  candidates : List SystemBudgetReport
  compiled_eq : prepared.compileOptimized chosenConfig = .ok artifact
  degree_ge_three : 3 ≤ chosenConfig.maxDegree
  degree_within_budget : chosenConfig.maxDegree ≤ effectiveMaxDegree logBlowup isZk

private def tryCandidate {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} (prepared : Modules.Prepared prog)
    (logBlowup extDegree : Nat) (isZk : Bool) (base : Config)
    (d : Nat) (hge : 3 ≤ d) (hle : d ≤ effectiveMaxDegree logBlowup isZk) :
    Except String (BudgetedArtifact prepared logBlowup isZk) :=
  let cfg : Config := { base with maxDegree := d }
  match hcomp : prepared.compileOptimized cfg with
  | .error err => .error err
  | .ok art =>
      let rep := budgetAnalysis art.circuit.system d logBlowup extDegree
      .ok {
        chosenConfig := cfg
        artifact := art
        report := rep
        candidates := [rep]
        compiled_eq := hcomp
        degree_ge_three := hge
        degree_within_budget := hle
      }

private def mergeBest {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup : Nat} {isZk : Bool}
    (best cand : BudgetedArtifact prepared logBlowup isZk) :
    BudgetedArtifact prepared logBlowup isZk :=
  if betterReport cand.report best.report then
    { cand with candidates := best.candidates ++ cand.candidates }
  else
    { best with candidates := best.candidates ++ cand.candidates }

/-- Compile a `Modules.Prepared prog` across all quotient-compatible degree
budgets for `logBlowup` (e.g. `[3, 5]` at `logBlowup = 2`, `[3, 5, 9]` at
`logBlowup = 3`), returning the certified artifact that minimizes exact
Multi-STARK Stage-1 + Stage-2 + quotient column cost. -/
def compileQuotientAware {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} (prepared : Modules.Prepared prog)
    (logBlowup : Nat := 2) (base : Config := {})
    (extDegree : Nat := v6ExtDegree) (isZk : Bool := false) :
    Except String (BudgetedArtifact prepared logBlowup isZk) :=
  let cands := (candidateMaxDegrees logBlowup isZk).attach
  let init : Except String (BudgetedArtifact prepared logBlowup isZk) :=
    .error "no candidate degree budgets"
  cands.foldl (fun acc ⟨d, hd⟩ =>
    let bounds := candidateMaxDegrees_bounds hd
    match acc, tryCandidate prepared logBlowup extDegree isZk base d bounds.1 bounds.2 with
    | .error _, res => res
    | .ok best, .error _ => .ok best
    | .ok best, .ok cand => .ok (mergeBest best cand)) init

/-- Select the optimal `Aiur.Optimized.Config` for `prepared` at STARK blowup
`logBlowup` by comparing exact Stage-1 + Stage-2 + quotient column cost across
all quotient-compatible degree budgets. Falls back to `max 3 base.maxDegree` if
compilation fails. -/
def chooseConfig {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} (prepared : Modules.Prepared prog)
    (logBlowup : Nat := 2) (base : Config := {})
    (extDegree : Nat := v6ExtDegree) (isZk : Bool := false) : Config :=
  match compileQuotientAware prepared logBlowup base extDegree isZk with
  | .ok res => res.chosenConfig
  | .error _ => { base with maxDegree := max 3 base.maxDegree }

/-- Per-chip quotient-aware layout: evaluates `layOut` across all
quotient-compatible `maxDegree` budgets for a single `ScopedChip F` and selects
the lowest-cost physical `LaidOutChip F`. -/
def layOutQuotientAware {F : Type} [Field F] [DecidableEq F]
    (chip : ScopedChip F) (logBlowup : Nat := 2) (base : Config := {})
    (extDegree : Nat := v6ExtDegree) (isZk : Bool := false) :
    Except String (Config × LaidOutChip F × ChipBudgetReport) :=
  let cands := candidateMaxDegrees logBlowup isZk
  let init : Except String (Config × LaidOutChip F × ChipBudgetReport) :=
    .error "no candidate degree budgets"
  cands.foldl (fun acc d =>
    let cfg : Config := { base with maxDegree := d }
    match acc, layOut cfg chip with
    | .error _, .error err => .error err
    | .error _, .ok laid =>
        .ok (cfg, laid, analyzeChip laid.chip logBlowup extDegree)
    | .ok best, .error _ => .ok best
    | .ok (bestCfg, bestLaid, bestRep), .ok laid =>
        let rep := analyzeChip laid.chip logBlowup extDegree
        if betterChipReport rep bestRep then .ok (cfg, laid, rep)
        else .ok (bestCfg, bestLaid, bestRep)) init

/-! ## 4. Certified Soundness, Completeness & Degree-Budget Invariance -/

theorem compile_config_eq {F : Type} [Field F] [DecidableEq F]
    {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (hcomp : compile program entries config = .ok artifact) :
    artifact.config = config :=
  (compile_stages hcomp).2.2.2.1

theorem compileOptimized_config_eq {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {config : Config} {art : ModulesArtifact prepared}
    (hcomp : prepared.compileOptimized config = .ok art) :
    art.circuit.config = config ∧ art.circuit.artifact.config = config := by
  unfold Modules.Prepared.compileOptimized at hcomp
  obtain ⟨spec, _, hspecComp⟩ := except_bind_ok.mp hcomp
  obtain ⟨gen, hgen, hret⟩ := except_bind_ok.mp hspecComp
  obtain rfl := except_pure_ok.mp hret
  unfold Generic.Specialized.compileOptimized at hgen
  obtain ⟨inlined, _, hcompGen⟩ := except_bind_ok.mp hgen
  split at hcompGen
  · cases hcompGen
  · rename_i compiledArt hopt
    obtain rfl := except_pure_ok.mp hcompGen
    exact ⟨rfl, compile_config_eq hopt⟩

/-- Every chip produced by `compileQuotientAware` satisfies the certified degree
bound (`maxConstraintDegree ≤ chosenConfig.maxDegree`, `maxLookupDegree ≤ 2`,
`maxLookupGuardDegree ≤ 1`), and for non-ZK STARKs with `logBlowup ≥ 1`, its
constraint quotient degree stays within `2 ^ logBlowup`. -/
theorem compileQuotientAware_degreeBound {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config}
    {res : BudgetedArtifact prepared logBlowup false}
    (hlog : 1 ≤ logBlowup)
    (hcomp : compileQuotientAware prepared logBlowup base extDegree false = .ok res) :
    ∀ chip ∈ res.artifact.circuit.system.chips,
      chip.stats.maxConstraintDegree ≤ res.chosenConfig.maxDegree ∧
      chip.stats.maxLookupDegree ≤ 2 ∧
      chip.maxLookupGuardDegree ≤ 1 ∧
      quotientDegreeFromMax chip.stats.maxConstraintDegree ≤ 2 ^ logBlowup := by
  have _ := hcomp
  have hcfg := (compileOptimized_config_eq res.compiled_eq).2
  intro chip hmem
  have hdeg := res.artifact.circuit.artifact.degreeBound chip hmem
  rw [hcfg] at hdeg
  have hle : chip.stats.maxConstraintDegree ≤ maxConstraintDegreeForBlowup logBlowup false := by
    have hbudget := res.degree_within_budget
    unfold effectiveMaxDegree maxConstraintDegreeForBlowup at hbudget
    unfold maxConstraintDegreeForBlowup
    simp only [Bool.false_eq_true, ↓reduceIte] at hbudget ⊢
    have h2 : 2 ≤ 2 ^ logBlowup := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) hlog
      simpa using this
    omega
  exact ⟨hdeg.1, hdeg.2.1, hdeg.2.2, quotientDegreeFromMax_le_blowup hlog hle⟩

/-- **Headline End-to-End Soundness of Quotient-Aware Compilation (`compileQuotientAware_sound`)**:
composes directly with Formal Aiur's `DegreeCertificate`, `AllocationCertificate`,
and `Modules.Prepared.depth_grouped_activated_heap_sound`. Any degree budget
selected by `compileQuotientAware` preserves 100% of Formal Aiur's end-to-end
heap and independent source evaluation semantics (`Modules.Prepared.EvalFn`). -/
theorem compileQuotientAware_sound {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {res : BudgetedArtifact prepared logBlowup isZk}
    (_hcomp : compileQuotientAware prepared logBlowup base extDegree isZk = .ok res)
    (physical : Physical.Prepared res.artifact.circuit.artifact)
    {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified res.artifact.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed res.artifact.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root =
      Erasure.message res.artifact.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues res.artifact.specialized.program.enums wires (entryValues args))
    (decoded : output.decode res.artifact.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents
        ((Erasure.typedROM res.artifact.circuit.system rom).decode
          res.artifact.specialized.program.enums)
        heap value result :=
  prepared.depth_grouped_activated_heap_sound res.artifact physical certified bits plan activated
    selected valid signed rooted outside bound characteristic checked arguments decoded

/-- Goldilocks specialization of `compileQuotientAware_sound`, automatically
discharging the characteristic side condition. -/
theorem compileQuotientAware_sound_goldilocks
    {prog : Modules.Program Library.U32.Goldilocks.F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {res : BudgetedArtifact prepared logBlowup isZk}
    (hcomp : compileQuotientAware prepared logBlowup base extDegree isZk = .ok res)
    (physical : Physical.Prepared res.artifact.circuit.artifact)
    {cfg : Depth.Config}
    (certified : Physical.Prepared.DepthCertified res.artifact.circuit physical cfg)
    (bits : cfg.bits ≤ 24)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Library.U32.Goldilocks.F)}
    {result : Value Library.U32.Goldilocks.F}
    {wires : List (WireValue Library.U32.Goldilocks.F)}
    {output : WireValue Library.U32.Goldilocks.F}
    (signed : Erasure.Signed res.artifact.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message Library.U32.Goldilocks.F}
    (rooted : Depth.erase cfg root =
      Erasure.message res.artifact.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow Library.U32.Goldilocks.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues res.artifact.specialized.program.enums wires (entryValues args))
    (decoded : output.decode res.artifact.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents
        ((Erasure.typedROM res.artifact.circuit.system rom).decode
          res.artifact.specialized.program.enums)
        heap value result :=
  compileQuotientAware_sound hcomp physical certified bits plan activated selected
    valid signed rooted outside bound Depth.goldilocks_characteristic checked arguments decoded

/-- Unit-checker soundness for `compileQuotientAware`. -/
theorem compileQuotientAware_check_sound {F : Type} [Field F] [DecidableEq F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {res : BudgetedArtifact prepared logBlowup isZk}
    (_hcomp : compileQuotientAware prepared logBlowup base extDegree isZk = .ok res)
    {name : String} {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : res.artifact.check rom name wires output rows = .ok ())
    (arguments : DecodesValues res.artifact.specialized.program.enums wires (entryValues args))
    (decoded : output.decode res.artifact.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalCall name args value ∧
      Represents (rom.decode res.artifact.specialized.program.enums) heap value result :=
  res.artifact.check_sound checked arguments decoded

/-- Unit-checker completeness for `compileQuotientAware`. -/
theorem compileQuotientAware_check_complete {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {res : BudgetedArtifact prepared logBlowup isZk}
    (_hcomp : compileQuotientAware prepared logBlowup base extDegree isZk = .ok res)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (evaluated : prepared.EvalFn name args value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues res.artifact.circuit.system.enums wires (entryValues args) ∧
      output.decode res.artifact.circuit.system.enums = some (value.mapAddress encode) ∧
      res.artifact.check rom name wires output rows = .ok () :=
  res.artifact.check_complete evaluated capacity

/-- Memo-checker completeness for `compileQuotientAware`. -/
theorem compileQuotientAware_checkMemo_complete {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {prog : Modules.Program F} {prepared : Modules.Prepared prog}
    {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {res : BudgetedArtifact prepared logBlowup isZk}
    (_hcomp : compileQuotientAware prepared logBlowup base extDegree isZk = .ok res)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (evaluated : prepared.EvalFn name args value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues res.artifact.circuit.system.enums wires (entryValues args) ∧
      output.decode res.artifact.circuit.system.enums = some (value.mapAddress encode) ∧
      res.artifact.checkMemo rom name wires output rows = .ok () :=
  res.artifact.checkMemo_complete evaluated capacity

/-- **Degree-Budget Semantic Invariance**: any two optimizer configurations
(e.g. `maxDegree = 3` vs `maxDegree = 5` vs `maxDegree = 9`) accepted by
`Optimized.compile` induce the exact same finite entry derivation relation. -/
theorem compile_degree_invariance {F : Type} [Field F] [DecidableEq F]
    {program : Program F} {entries : List String} {cfg₁ cfg₂ : Config}
    {art₁ art₂ : Artifact F} {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (hcomp₁ : compile program entries cfg₁ = .ok art₁)
    (hcomp₂ : compile program entries cfg₂ = .ok art₂)
    {rom : WireROM F} (valid : rom.Valid) {root : Circuit.Message F}
    (entry : root.channel ∈ entries) (free : root.PublicArguments program.enums) :
    Circuit.Derives art₁.system rom root ↔ Circuit.Derives art₂.system rom root :=
  (Optimized.reference_derives_iff original hcomp₁ entry valid free).symm.trans
    (Optimized.reference_derives_iff original hcomp₂ entry valid free)

/-- Per-chip quotient-aware layout soundness: whichever candidate `maxDegree`
wins in `layOutQuotientAware`, the resulting physical chip faithfully realizes
the source `ScopedChip F`. -/
theorem layOutQuotientAware_correct {F : Type} [Field F] [DecidableEq F]
    {source : ScopedChip F} {logBlowup extDegree : Nat} {base : Config} {isZk : Bool}
    {cfg : Config} {laid : LaidOutChip F} {rep : ChipBudgetReport}
    (hrun : layOutQuotientAware source logBlowup base extDegree isZk = .ok (cfg, laid, rep)) :
    source.Realizes laid.chip := by
  unfold layOutQuotientAware at hrun
  suffices hinv : ∀ (ds : List Nat) (acc : Except String (Config × LaidOutChip F × ChipBudgetReport)),
      (∀ c l r, acc = .ok (c, l, r) → source.Realizes l.chip) →
      ∀ c l r,
        ds.foldl (fun a d =>
          let cfg' : Config := { base with maxDegree := d }
          match a, layOut cfg' source with
          | .error _, .error err => .error err
          | .error _, .ok laid' => .ok (cfg', laid', analyzeChip laid'.chip logBlowup extDegree)
          | .ok best, .error _ => .ok best
          | .ok (bestCfg, bestLaid, bestRep), .ok laid' =>
              let rep' := analyzeChip laid'.chip logBlowup extDegree
              if betterChipReport rep' bestRep then .ok (cfg', laid', rep')
              else .ok (bestCfg, bestLaid, bestRep)) acc = .ok (c, l, r) →
        source.Realizes l.chip by
    exact hinv (candidateMaxDegrees logBlowup isZk) (.error "no candidate degree budgets")
      (fun _ _ _ h => by cases h) cfg laid rep hrun
  intro ds
  induction ds with
  | nil =>
      intro acc hacc c l r hfold
      exact hacc c l r hfold
  | cons d rest ih =>
      intro acc hacc c l r hfold
      simp only [List.foldl_cons] at hfold
      apply ih _ _ c l r hfold
      intro c' l' r' hstep
      cases haccEq : acc with
      | error e =>
          rw [haccEq] at hstep
          cases hlay : layOut { base with maxDegree := d } source with
          | error _ => simp [hlay] at hstep
          | ok laid' =>
              simp only [hlay, Except.ok.injEq, Prod.mk.injEq] at hstep
              rcases hstep with ⟨_, rfl, _⟩
              exact layOut_correct hlay
      | ok best =>
          rcases best with ⟨bestCfg, bestLaid, bestRep⟩
          rw [haccEq] at hstep
          cases hlay : layOut { base with maxDegree := d } source with
          | error _ =>
              simp only [hlay, Except.ok.injEq, Prod.mk.injEq] at hstep
              rcases hstep with ⟨_, rfl, _⟩
              exact hacc bestCfg bestLaid bestRep haccEq
          | ok laid' =>
              simp only [hlay] at hstep
              split_ifs at hstep
              · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
                rcases hstep with ⟨_, rfl, _⟩
                exact layOut_correct hlay
              · simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
                rcases hstep with ⟨_, rfl, _⟩
                exact hacc bestCfg bestLaid bestRep haccEq

/-! ## 5. Executable Smoke Tests (`#guard`) & Axiom Pins -/

section SmokeTests

#guard maxConstraintDegreeForBlowup 1 false == 3
#guard maxConstraintDegreeForBlowup 2 false == 5
#guard maxConstraintDegreeForBlowup 3 false == 9
#guard maxConstraintDegreeForBlowup 2 true == 4
#guard maxConstraintDegreeForBlowup 3 true == 8
#guard candidateMaxDegrees 1 false == [3]
#guard candidateMaxDegrees 2 false == [3, 5]
#guard candidateMaxDegrees 3 false == [3, 5, 9]

/-- Concrete degree-5 polynomial chip (`y = x^5`, with 6 degree-1 calls so
`lookup_groups::retune` at `logBlowup = 2` chooses `q = 4`): demonstrates `C7b`
column savings when moving from `maxDegree = 3` to `maxDegree = 5` at zero
quotient-degree cost. -/
private def sbox5ScopedChip : ScopedChip Library.U32.Goldilocks.F :=
  let x : Polynomial Library.U32.Goldilocks.F := .var 0
  let y : Polynomial Library.U32.Goldilocks.F := .var 1
  let x2 := Polynomial.mul x x
  let x4 := Polynomial.mul x2 x2
  let x5 := Polynomial.mul x4 x
  let callSlot (k : Nat) : Call Library.U32.Goldilocks.F :=
    ⟨0, "helper", [WireValue.field (.var 0)], WireValue.field (2 + k)⟩
  { name := "sbox5_with_lookups"
    inputs := [WireValue.field 0]
    output := WireValue.field 1
    roles := #[.input, .output, .auxiliary 0, .auxiliary 0, .auxiliary 0,
               .auxiliary 0, .auxiliary 0, .auxiliary 0]
    aliases := Array.replicate 8 none
    scopes := #[⟨.const 1, []⟩]
    equations := #[⟨0, .sub x5 y⟩]
    calls := #[(callSlot 0), (callSlot 1), (callSlot 2), (callSlot 3), (callSlot 4), (callSlot 5)]
    cells := #[]
    choices := #[] }

private def sbox5Deg3Cols : Nat :=
  match layOut { maxDegree := 3 } sbox5ScopedChip with
  | .ok l => l.chip.numVars
  | .error _ => 999

private def sbox5Deg5Cols : Nat :=
  match layOut { maxDegree := 5 } sbox5ScopedChip with
  | .ok l => l.chip.numVars
  | .error _ => 999

private def sbox5AutoChoice : Nat × Nat × Nat :=
  match layOutQuotientAware sbox5ScopedChip 2 {} v6ExtDegree false with
  | .ok (cfg, laid, rep) => (cfg.maxDegree, laid.chip.numVars, rep.quotientDegree)
  | .error _ => (0, 999, 0)

-- Degree-3 forces auxiliary columns to split x^5; degree-5 needs zero extra columns!
#guard sbox5Deg5Cols < sbox5Deg3Cols
#guard sbox5Deg5Cols == 8
#guard sbox5Deg3Cols == 10
-- At logBlowup = 2, quotient-aware budgeting automatically selects maxDegree = 5
-- with q = 4 and strictly fewer columns.
#guard sbox5AutoChoice == (5, 8, 4)

/-- Helper: linear-chain power `x ^ (n + 1)` as `x * (x * ... * x)`. -/
private def powChain (x : Polynomial Library.U32.Goldilocks.F) : Nat → Polynomial Library.U32.Goldilocks.F
  | 0 => x
  | n + 1 => .mul x (powChain x n)

/-- Concrete degree-9 sum-of-powers chip (`y = ∑_{k=0}^{lanes-1} x_k ^ 9`):
demonstrates strict column monotonicity `cols(maxDegree=9) < cols(maxDegree=5) < cols(maxDegree=3)`
and verifies that `layOutQuotientAware` at `logBlowup = 3` selects `maxDegree = 9`
when the Stage-1 column savings strictly exceed the quotient-degree delta, while
refusing `maxDegree = 9` on a single-lane chip where quotient cost dominates. -/
private def sbox9SumChip (lanes : Nat) : ScopedChip Library.U32.Goldilocks.F :=
  let inputs := (List.range lanes).map fun k => WireValue.field k
  let roles := (Array.replicate lanes Role.input) ++ #[Role.output]
  let sumPow : Polynomial Library.U32.Goldilocks.F :=
    (List.range lanes).foldl (fun acc k => .add acc (powChain (.var k) 8)) (.const 0)
  { name := s!"sbox9_sum_{lanes}"
    inputs
    output := WireValue.field lanes
    roles
    aliases := Array.replicate (lanes + 1) none
    scopes := #[⟨.const 1, []⟩]
    equations := #[⟨0, .sub sumPow (.var lanes)⟩]
    calls := #[]
    cells := #[]
    choices := #[] }

private def sbox9ColsFor (lanes deg : Nat) : Nat :=
  match layOut { maxDegree := deg } (sbox9SumChip lanes) with
  | .ok l => l.chip.numVars
  | .error _ => 999

private def sbox9AutoDeg (lanes logBlowup : Nat) : Nat :=
  match layOutQuotientAware (sbox9SumChip lanes) logBlowup {} v6ExtDegree false with
  | .ok (cfg, _, _) => cfg.maxDegree
  | .error _ => 0

-- On 16 parallel degree-9 terms: maxDegree = 9 needs 0 extra cols (17), strictly beating
-- maxDegree = 5 (33 cols) and maxDegree = 3 (65 cols)!
#guard sbox9ColsFor 16 9 < sbox9ColsFor 16 5
#guard sbox9ColsFor 16 5 < sbox9ColsFor 16 3
#guard sbox9ColsFor 16 9 == 17
-- Quotient-cost protection: on 1 lane, jumping q=2 -> q=8 (+18 quotient cols) is NOT worth
-- saving 3 Stage-1 cols, so layOutQuotientAware protects quotient cost!
#guard sbox9AutoDeg 1 3 == 3
-- On 16 lanes, saving 48 Stage-1 cols over deg-3 (and 16 over deg-5) strictly beats the
-- quotient-degree delta (+12/+18 cols), so maxDegree = 9 wins automatically!
#guard sbox9AutoDeg 16 3 == 9

end SmokeTests

/-- info: 'Aiur.Optimized.DegreeBudget.quotientDegreeFromMax_le_blowup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms quotientDegreeFromMax_le_blowup

/-- info: 'Aiur.Optimized.DegreeBudget.quotient_free_slack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms quotient_free_slack

/--
info: 'Aiur.Optimized.DegreeBudget.compileQuotientAware_degreeBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compileQuotientAware_degreeBound

/-- info: 'Aiur.Optimized.DegreeBudget.compileQuotientAware_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileQuotientAware_sound

/--
info: 'Aiur.Optimized.DegreeBudget.compileQuotientAware_sound_goldilocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compileQuotientAware_sound_goldilocks

/-- info: 'Aiur.Optimized.DegreeBudget.compile_degree_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_degree_invariance

/-- info: 'Aiur.Optimized.DegreeBudget.layOutQuotientAware_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layOutQuotientAware_correct

end Aiur.Optimized.DegreeBudget
