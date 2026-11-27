import Aiur.Optimized.Depth.Grouped
import Aiur.Optimized.Grouping.Memo
import Aiur.Library.U32.Goldilocks
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Formal Multi-STARK Lowering Specification & `lookup_groups::retune` LogUp Equivalence

This module formalizes the Rust `.ixa` → `multi-stark` lowering layer
(`crates/aiur/src/trace/stark.rs`, `grouping.rs`, `tables.rs`, `rom.rs`, and
`lookup_groups.rs`) and proves:

1. **Executable Reference Lowerer (`lowerSingleChip`, `lowerGroupLayout`,
   `lowerFixedTables`, `lowerRomCircuits`, `lowerPlanFunctions`):**
   Matches `crates/aiur/src/trace/stark/`'s exact channel tags (`CALL = 1`,
   `ROM = 2`, `MEMSEG = 16`), main/preprocessed/stage-2 widths, constraint
   polynomials (including `(1 - activation) * mult = 0`), fixed-table
   grouping and `pair_lookups` heuristic, ROM prefix/segment circuits, and
   `lookup_groups::retune` (`balanced_lookup_order` + `FftCost` dominance).

2. **Algebraic LogUp Equivalence of `lookup_groups::retune`:**
   - `balancedLookupOrder_perm`: mixed-degree bucket packing is a genuine
     permutation of the lookup indices (`List.Perm`).
   - `retune_lookups_perm`: `retune` permutes lookups without dropping,
     duplicating, or altering any lookup expression, and preserves all AIR
     constraints and main/preprocessed widths.
   - `chunk_constraint_iff_sum_inv`: `multi-stark`'s prefix/suffix grouped
     LogUp polynomial constraint
     `(∏ m_j) * (target - source) - ∑ mult_j * ∏_{j' ≠ j} m_{j'} = 0`
     is algebraically equivalent (for nonzero denominators) to
     `target - source = ∑ mult_j / m_j`.
   - `retune_logup_equiv` & `retune_batch_logup_equiv`: repartitioning and
     reordering lookups via `lookup_groups::retune` preserves the exact
     per-row rational sum, per-circuit chained accumulator delta
     `acc_final - acc_initial`, and batch-wide global LogUp balance equation
     `∑ m_i / (β + rlc(γ, args_i)) = 0`.

3. **Soundness Bridge to `Aiur.Optimized.Grouping.Plan` & `Aiur.Audit`:**
   - `lowerSingleChip_row_sound` & `lowerGroupLayout_row_sound`: satisfying
     the lowered Multi-STARK AIR constraints + ROM membership implies
     `Plan.inspectRow` acceptance (and forces padding rows to have zero
     provide multiplicity).
   - `checkMemo_of_inspected_field_balance` & `depth_sound_of_inspected_field_balance_goldilocks`:
     from rows that already pass the model row check (`hinsp : rows.mapM (plan.inspectRow rom) =
     .ok inspected`) and a per-claim field balance over model messages (`hbal`, with an arbitrary
     `provWeight`; `rows.length ≤ 2^39`, demand `< Goldilocks.order`), reach
     `Grouping.Plan.checkMemo` and `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`.
     No lowered circuit, constraint polynomial or LogUp sum occurs in their statements: the steps
     from lowered-AIR satisfaction and one batch-wide LogUp equation to `hinsp` and `hbal` are
     assumed, not proved (formerly named `lowered_trace_checkMemo_sound` and
     `lowered_trace_depth_sound_goldilocks`).

Zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only.
-/

namespace Aiur.MultiStarkSpec

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping

/-! ## 1. Protocol Constants & Multi-STARK AIR IR -/

/-- Separate message namespace tags matching `crates/aiur/src/trace/stark.rs:89-91`. -/
def callTag : Nat := 1
def romTag : Nat := 2
def memsegTag : Nat := 16

/-- Batch row bound matching `crates/aiur/src/trace/stark.rs:86` (`MAX_BATCH_ROWS`). -/
def maxBatchRows : Nat := 2 ^ 39

/-- Maximum LogUp chunk size matching `multi_stark::lookup::MAX_LOOKUP_GROUP`. -/
def maxLookupGroup : Nat := 8

/-- Goldilocks extension degree of the shipped Protocol v6 adapter: the cubic extension `Fp^3`
(`crates/aiur/src/trace/stark.rs`, `GoldilocksBlake3V6Config`). -/
def goldilocksExtDegree : Nat := 3

/-- Symbolic AIR expression matching `multi_stark::expr::Expr<Val>`. -/
inductive AirExpr (F : Type) where
  | const (value : F)
  | main (col : Nat)
  | mainNext (col : Nat)
  | preprocessed (col : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : AirExpr F)
  | sub (a b : AirExpr F)
  | mul (a b : AirExpr F)
  | neg (a : AirExpr F)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Raw syntactic degree matching `crates/aiur/src/trace/stark.rs:218-226`. -/
def AirExpr.degree : AirExpr F → Nat
  | .const _ | .isTransition => 0
  | .main _ | .mainNext _ | .preprocessed _ | .isFirstRow | .isLastRow => 1
  | .add a b | .sub a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree
  | .neg a => a.degree

/-- Constant-folding pass matching `multi_stark::graph::Interner` (`graph.rs:267-326`). -/
def AirExpr.fold [Ring F] [DecidableEq F] : AirExpr F → AirExpr F
  | .const c => .const c
  | .main i => .main i
  | .mainNext i => .mainNext i
  | .preprocessed i => .preprocessed i
  | .isFirstRow => .isFirstRow
  | .isLastRow => .isLastRow
  | .isTransition => .isTransition
  | .add a b =>
      match a.fold, b.fold with
      | .const x, .const y => .const (x + y)
      | .const x, b' => if x = 0 then b' else .add (.const x) b'
      | a', .const y => if y = 0 then a' else .add a' (.const y)
      | a', b' => .add a' b'
  | .sub a b =>
      let a' := a.fold
      let b' := b.fold
      if a' = b' then .const 0
      else match a', b' with
      | .const x, .const y => .const (x - y)
      | a', .const y => if y = 0 then a' else .sub a' (.const y)
      | .const x, b' => if x = 0 then
          match b' with
          | .neg inner => inner
          | _ => .neg b'
        else .sub (.const x) b'
      | a', b' => .sub a' b'
  | .mul a b =>
      match a.fold, b.fold with
      | .const x, .const y => .const (x * y)
      | .const x, b' =>
          if x = 0 then .const 0
          else if x = 1 then b'
          else .mul (.const x) b'
      | a', .const y =>
          if y = 0 then .const 0
          else if y = 1 then a'
          else .mul a' (.const y)
      | a', b' => .mul a' b'
  | .neg a =>
      match a.fold with
      | .const x => .const (-x)
      | .neg inner => inner
      | a' => .neg a'

/-- Degree after `multi-stark` graph constant folding. -/
def AirExpr.foldedDegree [Ring F] [DecidableEq F] (e : AirExpr F) : Nat :=
  e.fold.degree

/-- Evaluate an AIR expression at a single row context in any ring `F`. -/
def AirExpr.eval [Ring F] (mainRow nextRow prepRow : Nat → F)
    (isFirst isLast isTrans : F) : AirExpr F → F
  | .const c => c
  | .main i => mainRow i
  | .mainNext i => nextRow i
  | .preprocessed i => prepRow i
  | .isFirstRow => isFirst
  | .isLastRow => isLast
  | .isTransition => isTrans
  | .add a b => a.eval mainRow nextRow prepRow isFirst isLast isTrans +
      b.eval mainRow nextRow prepRow isFirst isLast isTrans
  | .sub a b => a.eval mainRow nextRow prepRow isFirst isLast isTrans -
      b.eval mainRow nextRow prepRow isFirst isLast isTrans
  | .mul a b => a.eval mainRow nextRow prepRow isFirst isLast isTrans *
      b.eval mainRow nextRow prepRow isFirst isLast isTrans
  | .neg a => -(a.eval mainRow nextRow prepRow isFirst isLast isTrans)

/-- Constant folding preserves AIR expression evaluation identically. -/
theorem AirExpr.eval_fold [Ring F] [DecidableEq F]
    (mainRow nextRow prepRow : Nat → F) (isFirst isLast isTrans : F) (e : AirExpr F) :
    e.fold.eval mainRow nextRow prepRow isFirst isLast isTrans =
      e.eval mainRow nextRow prepRow isFirst isLast isTrans := by
  induction e with
  | const _ | main _ | mainNext _ | preprocessed _ | isFirstRow | isLastRow | isTransition => rfl
  | add a b iha ihb =>
      simp only [AirExpr.fold, AirExpr.eval]
      rw [← iha, ← ihb]
      generalize a.fold = a'
      generalize b.fold = b'
      cases a' <;> cases b' <;> simp only [AirExpr.eval] <;>
        split_ifs <;> simp_all [AirExpr.eval]
  | sub a b iha ihb =>
      simp only [AirExpr.fold, AirExpr.eval]
      rw [← iha, ← ihb]
      generalize a.fold = a'
      generalize b.fold = b'
      split_ifs with heq
      · simp [AirExpr.eval, heq]
      · cases a' <;> cases b' <;> simp only [AirExpr.eval] <;>
          split_ifs <;> simp_all [AirExpr.eval]
  | mul a b iha ihb =>
      simp only [AirExpr.fold, AirExpr.eval]
      rw [← iha, ← ihb]
      generalize a.fold = a'
      generalize b.fold = b'
      cases a' <;> cases b' <;> simp only [AirExpr.eval] <;>
        split_ifs <;> simp_all [AirExpr.eval]
  | neg a iha =>
      simp only [AirExpr.fold, AirExpr.eval]
      rw [← iha]
      generalize a.fold = a'
      cases a' <;> simp [AirExpr.eval]

/-- Lower an Aiur circuit polynomial to a Multi-STARK AIR expression
(`crates/aiur/src/trace/stark.rs:208-216`). -/
def lowerPoly : Circuit.ArithExpr F → AirExpr F
  | .const x => .const x
  | .var i => .main i
  | .add a b => .add (lowerPoly a) (lowerPoly b)
  | .sub a b => .sub (lowerPoly a) (lowerPoly b)
  | .mul a b => .mul (lowerPoly a) (lowerPoly b)

/-- Lowering an Aiur polynomial preserves evaluation on any main-row assignment. -/
theorem eval_lowerPoly [Field F] (mainRow nextRow prepRow : Nat → F)
    (isFirst isLast isTrans : F) (p : Circuit.ArithExpr F) :
    (lowerPoly p).eval mainRow nextRow prepRow isFirst isLast isTrans = p.denote mainRow := by
  induction p with
  | const _ | var _ => rfl
  | add a b iha ihb => simp [lowerPoly, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, iha, ihb]
  | sub a b iha ihb => simp [lowerPoly, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, iha, ihb]
  | mul a b iha ihb => simp [lowerPoly, AirExpr.eval, Scalar.Circuit.ArithExpr.denote, iha, ihb]

/-- A Multi-STARK LogUp interaction matching `multi_stark::lookup::Lookup<Expr<Val>>`.
`push` carries positive multiplicity `+m`; `pull` carries negated multiplicity `-m`. -/
structure AirLookup (F : Type) where
  multiplicity : AirExpr F
  args : List (AirExpr F)
  deriving Repr, BEq, DecidableEq

def AirLookup.push (mult : AirExpr F) (args : List (AirExpr F)) : AirLookup F :=
  ⟨mult, args⟩

def AirLookup.pull (mult : AirExpr F) (args : List (AirExpr F)) : AirLookup F :=
  ⟨.neg mult, args⟩

/-- Preprocessed matrix shape (rows × width) for a fixed-table circuit. -/
structure PreprocessedShape where
  width : Nat := 0
  height : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Frontend circuit inputs matching `multi_stark::system::CircuitInputs<Val>`. -/
structure CircuitInput (F : Type) where
  name : String
  mainWidth : Nat
  preprocessed : PreprocessedShape := {}
  constraints : List (AirExpr F) := []
  lookups : List (AirLookup F) := []
  lookupGroupSize : Nat := 1
  deriving Repr, BEq

/-! ## 2. Exact `.ixa` → Multi-STARK Lowerer (`grouping.rs`, `tables.rs`, `rom.rs`) -/

/-- Lower a single ROM memory access (`crates/aiur/src/trace/stark/rom.rs:31-47`). -/
def lowerRomAccess [Field F] (cell : MemoryLookup F) : AirLookup F :=
  let width := cell.value.words.length
  let args : List (AirExpr F) :=
    [.const (romTag : F), .const (width : F), lowerPoly cell.address] ++
      cell.value.words.map lowerPoly
  AirLookup.push (lowerPoly cell.enable) args

/-- Lower an activated ungrouped function chip (`crates/aiur/src/trace/stark/grouping.rs:113-141`).
`chip` is the activated chip (`Activation.compile source`), whose activation
selector sits at `activationCol` (`source.numVars`), and whose multiplicity
column is appended at `chip.numVars`. -/
def lowerSingleChip [Field F] (callableId : String → Nat)
    (chip : Circuit.Chip F) (activationCol : Nat) : CircuitInput F :=
  let multCol := chip.numVars
  let receiveArgs : List (AirExpr F) :=
    [.const (callTag : F), .const (callableId chip.name : F)] ++
      (chip.inputs.flatMap WireValue.words).map AirExpr.main ++
      chip.output.words.map lowerPoly
  let receiveLookup := AirLookup.pull (.main multCol) receiveArgs
  let sendLookups := chip.sends.map fun send =>
    let args : List (AirExpr F) :=
      [.const (callTag : F), .const (callableId send.channel : F)] ++
        (send.args.flatMap WireValue.words).map lowerPoly ++
        send.result.words.map AirExpr.main
    AirLookup.push (lowerPoly send.enable) args
  let romLookups := chip.memory.map lowerRomAccess
  let paddingConstraint : AirExpr F :=
    .mul (.sub (.const (1 : F)) (.main activationCol)) (.main multCol)
  { name := chip.name
    mainWidth := chip.numVars + 1
    constraints := chip.constraints.map lowerPoly ++ [paddingConstraint]
    lookups := receiveLookup :: sendLookups ++ romLookups
    lookupGroupSize := 1 }

/-- Lower a grouped function layout (`crates/aiur/src/trace/stark/grouping.rs:83-100`). -/
def lowerGroupLayout [Field F] [DecidableEq F] (g : Grouping.Layout F) : CircuitInput F :=
  let multCol := g.width
  let paddingConstraint : AirExpr F :=
    .mul (.sub (.const (1 : F)) (lowerPoly g.activation)) (.main multCol)
  let receiveLookup := AirLookup.pull (.main multCol) (g.receive.map lowerPoly)
  let sendLookups := g.sends.map fun s =>
    AirLookup.push (lowerPoly s.enable) (s.args.map lowerPoly)
  { name := g.name
    mainWidth := g.width + 1
    constraints := g.constraints.map lowerPoly ++ [paddingConstraint]
    lookups := receiveLookup :: sendLookups
    lookupGroupSize := 1 }

/-- Next power of two (`0 ↦ 0`), matching Rust's `checked_next_power_of_two` for `n > 0`. -/
def nextPow2 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ 1 then 1
  else 2 ^ (Nat.log2 (n - 1) + 1)

/-- `pair_lookups` heuristic from `crates/aiur/src/trace/stark/tables.rs:124-135`. -/
def pairLookups (count height logBlowup : Nat) : Bool :=
  if logBlowup == 0 || count < 2 || height == 0 then false
  else
    let fft (n : Nat) : Nat := n * Nat.log2 (max n 2)
    let blowup := 2 ^ logBlowup
    let savedColumns := 2 * (count - (count + 1) / 2)
    let savings := (blowup + 1) * savedColumns * fft height
    let extra := 2 * (fft (2 * height) - fft height) + 2 * fft (blowup * height)
    decide (savings > extra)

/-- Minimal metadata for a fixed map needed by `lowerFixedTables`. -/
structure FixedMapMeta where
  name : String
  callableId : Nat
  inputTableName : String
  inputTableId : Nat
  outputTableId : Nat
  inputWidth : Nat
  outputWidth : Nat
  rowCount : Nat
  deriving Repr, BEq

/-- Group fixed maps by equal input row count, preserving first-seen order
(`crates/aiur/src/trace/stark/tables.rs:17-26`). -/
def groupFixedMaps (maps : List FixedMapMeta) : List (String × Nat × List FixedMapMeta) :=
  maps.foldl (fun groups m =>
    match groups.findIdx? (fun (_, rows, _) => rows == m.rowCount) with
    | some idx =>
        groups.modify idx fun (nm, rows, ms) => (nm, rows, ms ++ [m])
    | none =>
        groups ++ [(m.inputTableName, m.rowCount, [m])]) []

/-- Lower fixed tables into Multi-STARK circuits (`crates/aiur/src/trace/stark/tables.rs:10-122`). -/
def lowerFixedTables [Field F] (maps : List FixedMapMeta) (logBlowup : Nat) :
    List (CircuitInput F) :=
  (groupFixedMaps maps).map fun (inputName, realHeight, groupMaps) =>
    let height := nextPow2 realHeight
    let init : Nat × List (Nat × Nat × Nat) × List (AirLookup F) × List (AirExpr F) :=
      (1, [], [], [])
    let (prepWidth, _, lookups, constraints) :=
      groupMaps.zipIdx.foldl (fun (width, cols, lookups, constraints) (m, colIdx) =>
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
          if height == 0 then
            (prefixArgs ++ List.replicate (m.inputWidth + m.outputWidth) (.const (0 : F)),
              constraints ++ [.main colIdx])
          else
            let inArgs := (List.range m.inputWidth).map fun k => AirExpr.preprocessed (inOff + k)
            let outArgs := (List.range m.outputWidth).map fun k => AirExpr.preprocessed (outOff + k)
            (prefixArgs ++ inArgs ++ outArgs, constraints)
        (width2, cols2, lookups ++ [AirLookup.pull (.main colIdx) args], constraints')) init
    { name := s!"<table:{inputName}>"
      mainWidth := groupMaps.length
      preprocessed := if height == 0 then {} else ⟨prepWidth, height⟩
      constraints := constraints
      lookups := lookups
      lookupGroupSize := if pairLookups groupMaps.length height logBlowup then 2 else 1 }

/-- Lower a single scalar (`K = 1`) width-partitioned ROM circuit
(`crates/aiur/src/trace/stark/rom.rs`). -/
def lowerScalarRomCircuit [Field F] (payloadWidth : Nat) (segmented : Bool) :
    CircuitInput F :=
  let width := payloadWidth + 3
  let count : AirExpr F := .main 0
  let active : AirExpr F := .main 1
  let address : AirExpr F := .main 2
  let payloadArgs := (List.range payloadWidth).map fun k => AirExpr.main (3 + k)
  let romArgs : List (AirExpr F) :=
    [.const (romTag : F), .const (payloadWidth : F), address] ++ payloadArgs
  let transition : AirExpr F := .mul .isTransition (.mainNext 1)
  let baseConstraints : List (AirExpr F) := [
    .mul active (.sub active (.const (1 : F))),
    .mul count (.sub (.const (1 : F)) active),
    .mul transition (.sub active (.const (1 : F))),
    .mul transition (.sub (.sub (.mainNext 2) address) (.const (1 : F)))
  ]
  let baseLookups : List (AirLookup F) := [AirLookup.pull count romArgs]
  let (constraints, lookups) :=
    if segmented then
      let segPush := AirLookup.push active
        [.const (memsegTag : F), .const (payloadWidth : F), address]
      let segPull := AirLookup.pull active
        [.const (memsegTag : F), .const (payloadWidth : F), .add address (.const (1 : F))]
      (baseConstraints, baseLookups ++ [segPush, segPull])
    else
      (baseConstraints ++ [.mul .isFirstRow address], baseLookups)
  { name := s!"<ROM:{payloadWidth}>"
    mainWidth := width
    constraints := constraints
    lookups := lookups
    lookupGroupSize := 1 }

/-- Lower width-partitioned scalar ROM circuits (`crates/aiur/src/trace/stark/rom.rs`). -/
def lowerRomCircuits [Field F] (widths : List Nat) (segmented : Bool) :
    List (CircuitInput F) :=
  widths.map (lowerScalarRomCircuit · segmented)

/-- Number of ROM entries packed per row in `RomLayout::Vectorized`
(`crates/aiur/src/trace/stark/rom.rs`). -/
def romLanes (payloadWidth : Nat) : Nat :=
  if payloadWidth ≤ 4 then 8
  else if payloadWidth ≤ 12 then 4
  else 1

theorem romLanes_pos (payloadWidth : Nat) : 0 < romLanes payloadWidth := by
  unfold romLanes
  split_ifs <;> omega

/-- Column index of `count_lane` in a `K > 1` vectorized `<ROM:w>` circuit. -/
def vecCountCol (payloadWidth lane : Nat) : Nat :=
  1 + lane * (payloadWidth + 2)

/-- Column index of `active_lane` in a `K > 1` vectorized `<ROM:w>` circuit. -/
def vecActiveCol (payloadWidth lane : Nat) : Nat :=
  1 + lane * (payloadWidth + 2) + 1

/-- Column index of `payload_lane[k]` in a `K > 1` vectorized `<ROM:w>` circuit. -/
def vecPayloadCol (payloadWidth lane k : Nat) : Nat :=
  1 + lane * (payloadWidth + 2) + 2 + k

/-- Lower a single `K`-lane vectorized `<ROM:payloadWidth>` circuit (`C6`,
`crates/aiur/src/trace/stark/rom.rs`). Falls back to `lowerScalarRomCircuit`
when `lanes ≤ 1`. -/
def lowerKLaneRomCircuit [Field F] (payloadWidth lanes : Nat) (segmented : Bool) :
    CircuitInput F :=
  if lanes ≤ 1 then
    lowerScalarRomCircuit payloadWidth segmented
  else
    let stride := payloadWidth + 2
    let width := 1 + lanes * stride
    let baseAddr : AirExpr F := .main 0
    let laneConstraints : List (AirExpr F) :=
      (List.range lanes).flatMap fun lane =>
        let count : AirExpr F := .main (vecCountCol payloadWidth lane)
        let active : AirExpr F := .main (vecActiveCol payloadWidth lane)
        [.mul active (.sub active (.const (1 : F))),
         .mul count (.sub (.const (1 : F)) active)]
    let prefixConstraints : List (AirExpr F) :=
      (List.range (lanes - 1)).map fun lane =>
        let cur : AirExpr F := .main (vecActiveCol payloadWidth lane)
        let nxt : AirExpr F := .main (vecActiveCol payloadWidth (lane + 1))
        .mul nxt (.sub (.const (1 : F)) cur)
    let transition : AirExpr F := .mul .isTransition (.mainNext (vecActiveCol payloadWidth 0))
    let lastActive : AirExpr F := .main (vecActiveCol payloadWidth (lanes - 1))
    let baseConstraints : List (AirExpr F) :=
      laneConstraints ++ prefixConstraints ++ [
        .mul transition (.sub lastActive (.const (1 : F))),
        .mul transition (.sub (.sub (.mainNext 0) baseAddr) (.const (lanes : F)))
      ]
    let romLookups : List (AirLookup F) :=
      (List.range lanes).map fun (lane : Nat) =>
        let laneAddr : AirExpr F :=
          if lane == 0 then baseAddr else .add baseAddr (.const (lane : F))
        let payloadArgs := (List.range payloadWidth).map fun k =>
          AirExpr.main (vecPayloadCol payloadWidth lane k)
        AirLookup.pull (.main (vecCountCol payloadWidth lane))
          ([.const (romTag : F), .const (payloadWidth : F), laneAddr] ++ payloadArgs)
    let (constraints, lookups) :=
      if segmented then
        let active0 : AirExpr F := .main (vecActiveCol payloadWidth 0)
        let sumActive : AirExpr F :=
          (List.range (lanes - 1)).foldl
            (fun acc i => .add acc (.main (vecActiveCol payloadWidth (i + 1)))) active0
        let segPush := AirLookup.push active0
          [.const (memsegTag : F), .const (payloadWidth : F), baseAddr]
        let segPull := AirLookup.pull active0
          [.const (memsegTag : F), .const (payloadWidth : F), .add baseAddr sumActive]
        (baseConstraints, romLookups ++ [segPush, segPull])
      else
        (baseConstraints ++ [.mul .isFirstRow baseAddr], romLookups)
    { name := s!"<ROM:{payloadWidth}>"
      mainWidth := width
      constraints := constraints
      lookups := lookups
      lookupGroupSize := 1 }

/-- Lower a single `<ROM:payloadWidth>` circuit using the `C6` lane schedule
(`K = 8` for `w ≤ 4`, `K = 4` for `5 ≤ w ≤ 12`, `K = 1` for `w > 12`). -/
def lowerVectorizedRomCircuit [Field F] (payloadWidth : Nat) (segmented : Bool) :
    CircuitInput F :=
  lowerKLaneRomCircuit payloadWidth (romLanes payloadWidth) segmented

/-- Lower width-partitioned `K`-lane vectorized ROM circuits (`C6`). -/
def lowerVectorizedRomCircuits [Field F] (widths : List Nat) (segmented : Bool) :
    List (CircuitInput F) :=
  widths.map (lowerVectorizedRomCircuit · segmented)

/-- ROM layout selection matching `crates/aiur/src/trace/stark/rom.rs:RomLayout`.
Rust defaults to `RomLayout::Vectorized` (`C6`). -/
inductive RomLayout where
  | scalar
  | vectorized
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Lower width-partitioned ROM circuits under the chosen `RomLayout` (default `.vectorized`). -/
def lowerRomCircuitsWithLayout [Field F] (widths : List Nat) (segmented : Bool)
    (layout : RomLayout := .vectorized) : List (CircuitInput F) :=
  match layout with
  | .scalar => lowerRomCircuits widths segmented
  | .vectorized => lowerVectorizedRomCircuits widths segmented

/-- Lower all function circuits of a `Grouping.Plan` (activated singles + groups). -/
def lowerPlanFunctions [Field F] [DecidableEq F] {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id) : List (CircuitInput F) :=
  let singles := plan.singles.map fun src =>
    lowerSingleChip callableId (Activation.compile src) src.numVars
  let groups := plan.groups.map fun p => lowerGroupLayout p.checked.layout
  singles ++ groups

/-- Lower function circuits in the exact chip-list order emitted by
`crates/aiur/src/trace/stark/grouping.rs:45-142`: iterating `source.chips`,
emitting each single chip in place and each group at the first appearance of
any of its member chips. -/
def lowerPlanFunctionsOrdered [Field F] [DecidableEq F] {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id) : List (CircuitInput F) :=
  let step (acc : List String × List (CircuitInput F)) (chip : Circuit.Chip F) :
      List String × List (CircuitInput F) :=
    let (emittedGroups, out) := acc
    match plan.groups.find? fun p => p.checked.layout.members.any (·.name == chip.name) with
    | some p =>
        let gname := p.checked.layout.name
        if emittedGroups.contains gname then (emittedGroups, out)
        else (gname :: emittedGroups, out ++ [lowerGroupLayout p.checked.layout])
    | none =>
        (emittedGroups, out ++ [lowerSingleChip callableId (Activation.compile chip) chip.numVars])
  (source.chips.foldl step ([], [])).2

/-! ## 3. Exact Lean Mirror of `crates/aiur/src/trace/stark/lookup_groups.rs` -/

/-- Ceiling division `⌈a / b⌉` for `b ≥ 1`. -/
def divCeil (a b : Nat) : Nat :=
  let b' := max b 1
  (a + b' - 1) / b'

/-- Number of LogUp groups (`multi_stark::lookup::lookup_groups`). -/
def lookupGroups (numLookups groupSize : Nat) : Nat :=
  max (divCeil numLookups (max groupSize 1)) 1

/-- Stage-2 base-column width (`multi_stark::lookup::stage2_width`). -/
def stage2Width (numLookups groupSize degree : Nat) : Nat :=
  lookupGroups numLookups groupSize * degree

/-- LogUp base constraint count (`multi_stark::lookup::logup_constraint_count`). -/
def logupConstraintCount (numLookups groupSize degree : Nat) : Nat :=
  lookupGroups numLookups groupSize * degree

/-- Split a list into consecutive chunks of size `max k 1` (last chunk may be shorter). -/
def chunkList (k : Nat) (xs : List α) : List (List α) :=
  let step := max k 1
  let rec go : Nat → List α → List (List α)
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, ys => ys.take step :: go fuel (ys.drop step)
  go xs.length xs

theorem chunkList_flatten (k : Nat) (xs : List α) : (chunkList k xs).flatten = xs := by
  unfold chunkList
  have hstep : 0 < max k 1 := Nat.lt_of_lt_of_le (by omega) (Nat.le_max_right k 1)
  suffices ∀ (fuel : Nat) (ys : List α), ys.length ≤ fuel →
      (chunkList.go (max k 1) fuel ys).flatten = ys from this xs.length xs le_rfl
  intro fuel
  induction fuel with
  | zero =>
      intro ys hlen
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | succ f ih =>
      intro ys hlen
      cases ys with
      | nil => rfl
      | cons y ys' =>
          simp only [chunkList.go, List.flatten_cons]
          have hdrop : (List.drop (max k 1) (y :: ys')).length ≤ f := by
            simp only [List.length_drop, List.length_cons] at hlen ⊢
            omega
          rw [ih _ hdrop, List.take_append_drop]

/-- `(mult_deg, payload_deg)` for each lookup, matching `lookup_groups.rs:62-73`. -/
def lookupDegrees [Ring F] [DecidableEq F] (lookups : List (AirLookup F)) : List (Nat × Nat) :=
  lookups.map fun l =>
    let multDeg := l.multiplicity.foldedDegree
    let payloadDeg := l.args.foldl (fun acc a => max acc a.foldedDegree) 0
    (multDeg, payloadDeg)

/-- Chunk degree formula matching `multi_stark::lookup::logup_max_degree` and
`lookup_groups.rs:75-92`. -/
def chunkLogupDegree (degs : List (Nat × Nat)) : Nat :=
  let sumPayload := (degs.map Prod.snd).sum
  let productTerm := sumPayload + 1
  let multTerm := degs.foldl (fun acc (md, pd) => max acc (md + sumPayload - pd)) 0
  max productTerm multTerm

def logupMaxDegreeForDegs (degs : List (Nat × Nat)) (groupSize : Nat) : Nat :=
  let chunks := chunkList groupSize degs
  if chunks.isEmpty then 1
  else chunks.foldl (fun acc ch => max acc (chunkLogupDegree ch)) 0

def logupMaxDegreeForOrder (degs : List (Nat × Nat)) (order : List Nat) (groupSize : Nat) : Nat :=
  let ordered := order.map fun i => degs.getD i (0, 0)
  logupMaxDegreeForDegs ordered groupSize

def quotientDegreeFromMax (maxDeg : Nat) : Nat :=
  nextPow2 (max maxDeg 2 - 1)

/-- FFT cost dominance model matching `crates/aiur/src/trace/stark/lookup_groups.rs:19-60`. -/
structure FftCost where
  one : Nat
  two : Nat
  slope : Nat
  intercept : Nat
  deriving Repr, BEq, DecidableEq

def isPow2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

def FftCost.make (stage2 quotient blowup degree : Nat) : Option FftCost :=
  if !isPow2 quotient || !isPow2 blowup then none
  else
    let logQ := Nat.log2 quotient
    let logB := Nat.log2 blowup
    let qd := quotient * degree
    let trace := (blowup + 1) * stage2
    let slope := (blowup + 1) * (stage2 + qd)
    let intercept := qd * (logQ + blowup * logB)
    let one := trace + qd * (max logQ 1 + blowup * max logB 1)
    let two := slope + intercept
    some ⟨one, two, slope, intercept⟩

def FftCost.noWorseThan (self other : FftCost) : Bool :=
  self.one ≤ other.one && self.two ≤ other.two && self.slope ≤ other.slope

def FftCost.scoreLt (self other : FftCost) : Bool :=
  self.slope < other.slope ||
    (self.slope == other.slope &&
      (self.intercept < other.intercept ||
        (self.intercept == other.intercept && self.one < other.one)))

def FftCost.scoreEq (self other : FftCost) : Bool :=
  self.slope == other.slope && self.intercept == other.intercept && self.one == other.one

/-- Total bucket append: appends `x` to bucket `b` (clamped to the last bucket if
out-of-range, which never occurs when `b < bs.length`). -/
def insertAtBucket : Nat → α → List (List α) → List (List α)
  | _, x, [] => [[x]]
  | 0, x, b :: bs => (b ++ [x]) :: bs
  | _ + 1, x, [b] => [b ++ [x]]
  | n + 1, x, b :: b' :: bs => b :: insertAtBucket n x (b' :: bs)

theorem flatten_insertAtBucket (n : Nat) (x : α) (bs : List (List α)) :
    (insertAtBucket n x bs).flatten.Perm (x :: bs.flatten) := by
  induction bs generalizing n with
  | nil => simp [insertAtBucket]
  | cons b bs ih =>
      cases n with
      | zero =>
          simp only [insertAtBucket, List.flatten_cons, List.append_assoc]
          simpa [List.append_assoc] using
            (List.perm_middle (a := x) (l₁ := b) (l₂ := bs.flatten)).symm
      | succ m =>
          cases bs with
          | nil =>
              simp only [insertAtBucket, List.flatten_cons, List.flatten_nil, List.append_nil]
              simpa using (List.perm_middle (a := x) (l₁ := b) (l₂ := [])).symm
          | cons b' bs' =>
              simp only [insertAtBucket, List.flatten_cons]
              have h1 : (b ++ (insertAtBucket m x (b' :: bs')).flatten).Perm
                  (b ++ (x :: (b' :: bs').flatten)) :=
                List.Perm.append_left b (ih m)
              exact h1.trans List.perm_middle

/-- Comparator for `sorted` in `balanced_lookup_order` (`lookup_groups.rs:111-113`). -/
def sortKeyLe (degs : List (Nat × Nat)) (a b : Nat) : Bool :=
  let (ma, pa) := degs.getD a (0, 0)
  let (mb, pb) := degs.getD b (0, 0)
  if pa != pb then pa > pb
  else if ma != mb then ma > mb
  else a ≤ b

/-- Bucket key `(maxDeg, newSum, cap, bucketIdx)` matching `lookup_groups.rs:120-129`. -/
def bucketKey (degs : List (Nat × Nat)) (caps : List Nat) (buckets : List (List Nat))
    (idx b : Nat) : Nat × Nat × Nat × Nat :=
  let (multD, payloadD) := degs.getD idx (0, 0)
  let bucket := buckets.getD b []
  let prevSum := (bucket.map fun prev => (degs.getD prev (0, 0)).2).sum
  let newSum := prevSum + payloadD
  let prod := newSum + 1
  let worstMult := bucket.foldl (fun acc prev =>
    let (pm, pp) := degs.getD prev (0, 0)
    max acc (pm + newSum - pp)) (multD + newSum - payloadD)
  (max prod worstMult, newSum, caps.getD b 0, b)

def tuple4Lt (x y : Nat × Nat × Nat × Nat) : Bool :=
  x.1 < y.1 ||
    (x.1 == y.1 &&
      (x.2.1 < y.2.1 ||
        (x.2.1 == y.2.1 &&
          (x.2.2.1 < y.2.2.1 || (x.2.2.1 == y.2.2.1 && x.2.2.2 < y.2.2.2)))))

def pickBestBucket (degs : List (Nat × Nat)) (caps : List Nat) (buckets : List (List Nat))
    (idx : Nat) : Nat :=
  let candidates := (List.range caps.length).filter fun b =>
    (buckets.getD b []).length < caps.getD b 0
  match candidates with
  | [] => 0
  | b0 :: rest =>
      rest.foldl (fun best b =>
        if tuple4Lt (bucketKey degs caps buckets idx b) (bucketKey degs caps buckets idx best)
        then b else best) b0

/-- Place every index of `order` into its optimal bucket. -/
def packBuckets (degs : List (Nat × Nat)) (caps : List Nat) :
    List Nat → List (List Nat) → List (List Nat)
  | [], buckets => buckets
  | idx :: rest, buckets =>
      let b := pickBestBucket degs caps buckets idx
      packBuckets degs caps rest (insertAtBucket b idx buckets)

theorem flatten_packBuckets_perm (degs : List (Nat × Nat)) (caps : List Nat) :
    ∀ (order : List Nat) (buckets : List (List Nat)),
      (packBuckets degs caps order buckets).flatten.Perm (order ++ buckets.flatten)
  | [], buckets => by simp [packBuckets]
  | idx :: rest, buckets => by
      simp only [packBuckets]
      have h1 := flatten_packBuckets_perm degs caps rest
        (insertAtBucket (pickBestBucket degs caps buckets idx) idx buckets)
      have h2 := flatten_insertAtBucket (pickBestBucket degs caps buckets idx) idx buckets
      have h3 : (rest ++ (insertAtBucket (pickBestBucket degs caps buckets idx) idx buckets).flatten).Perm
          (rest ++ (idx :: buckets.flatten)) := List.Perm.append_left rest h2
      exact (h1.trans h3).trans List.perm_middle

/-- Exact Lean mirror of `balanced_lookup_order` (`lookup_groups.rs:97-135`). -/
def balancedLookupOrder (degs : List (Nat × Nat)) (group : Nat) : List Nat :=
  let n := degs.length
  if n ≤ 1 || group ≤ 1 then List.range n
  else
    let numChunks := divCeil n group
    let rem := n % group
    let caps :=
      if rem == 0 then List.replicate numChunks group
      else List.replicate (numChunks - 1) group ++ [rem]
    let sorted := (List.range n).mergeSort (sortKeyLe degs)
    let buckets := packBuckets degs caps sorted (List.replicate numChunks [])
    buckets.flatten

/-- **Permutation soundness of `balancedLookupOrder`:**
for every degree profile and group size, `balancedLookupOrder` produces a genuine
permutation of `0, 1, …, degs.length - 1` (never dropping or duplicating any lookup). -/
theorem balancedLookupOrder_perm (degs : List (Nat × Nat)) (group : Nat) :
    (balancedLookupOrder degs group).Perm (List.range degs.length) := by
  unfold balancedLookupOrder
  dsimp only
  by_cases h : (decide (degs.length ≤ 1) || decide (group ≤ 1)) = true
  · simp [h]
  · simp only [h, ↓reduceIte]
    set numChunks := divCeil degs.length group
    set rem := degs.length % group
    set caps := if (rem == 0) = true then List.replicate numChunks group
      else List.replicate (numChunks - 1) group ++ [rem]
    have hpack := flatten_packBuckets_perm degs caps
      ((List.range degs.length).mergeSort (sortKeyLe degs))
      (List.replicate numChunks [])
    have hflatEmpty : (List.replicate numChunks ([] : List Nat)).flatten = [] := by
      induction numChunks with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih]
    rw [hflatEmpty, List.append_nil] at hpack
    exact hpack.trans (List.mergeSort_perm (List.range degs.length) (sortKeyLe degs))

/-- Reorder a list by an index permutation `order`. -/
def permuteBy [Inhabited α] (xs : List α) (order : List Nat) : List α :=
  order.map fun i => xs.getD i default

theorem permuteBy_perm [Inhabited α] {xs : List α} {order : List Nat}
    (hperm : order.Perm (List.range xs.length)) :
    (permuteBy xs order).Perm xs := by
  unfold permuteBy
  have h1 : (order.map fun i => xs.getD i default).Perm
      ((List.range xs.length).map fun i => xs.getD i default) := hperm.map _
  have h2 : ((List.range xs.length).map fun i => xs.getD i default) = xs := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
      simp [hi2]
  rw [h2] at h1
  exact h1

/-- Compiled circuit metadata matching `multi_stark::system::Circuit<Val>` after
`System::new` + `lookup_groups::retune`. -/
structure CompiledCircuit (F : Type) where
  name : String
  mainWidth : Nat
  preprocessed : PreprocessedShape
  constraints : List (AirExpr F)
  lookups : List (AirLookup F)
  lookupGroupSize : Nat
  stage2Width : Nat
  constraintCount : Nat
  userMaxDegree : Nat
  maxConstraintDegree : Nat
  deriving Repr, BEq

def CompiledCircuit.quotientDegree (c : CompiledCircuit F) : Nat :=
  quotientDegreeFromMax c.maxConstraintDegree

/-- Compile a `CircuitInput` into its initial `CompiledCircuit` (mirroring
`System::new` + `graph::compile`: constant-folds constraints, drops zero
constraints, deduplicates surviving constraints). -/
def compileCircuit [Ring F] [DecidableEq F] (input : CircuitInput F)
    (extDegree : Nat := goldilocksExtDegree) : CompiledCircuit F :=
  let folded := (input.constraints.map AirExpr.fold).filter fun e => e != .const 0
  let zeros := folded.dedup
  let userMax := zeros.foldl (fun acc e => max acc e.degree) 0
  let degs := lookupDegrees input.lookups
  let group := max input.lookupGroupSize 1
  let logupMax := logupMaxDegreeForDegs degs group
  let maxDeg := max userMax logupMax
  { name := input.name
    mainWidth := input.mainWidth
    preprocessed := input.preprocessed
    constraints := zeros
    lookups := input.lookups
    lookupGroupSize := group
    stage2Width := stage2Width input.lookups.length group extDegree
    constraintCount := zeros.length + logupConstraintCount input.lookups.length group extDegree
    userMaxDegree := userMax
    maxConstraintDegree := maxDeg }

private abbrev RetuneCandidate := Nat × FftCost × Nat × Option (List Nat)

private def recordCandidate (byQ : List RetuneCandidate)
    (quotient : Nat) (cost : FftCost) (group : Nat) (order : Option (List Nat)) :
    List RetuneCandidate :=
  match byQ.findIdx? (fun e => e.1 == quotient) with
  | none => byQ ++ [(quotient, cost, group, order)]
  | some idx =>
      match byQ[idx]? with
      | none => byQ
      | some (_, prevCost, _, prevOrder) =>
          let better := cost.scoreLt prevCost ||
            (cost.scoreEq prevCost && order.isNone && prevOrder.isSome)
          if better then byQ.set idx (quotient, cost, group, order) else byQ

private def addPlainCandidate (numLookups userMax blowup extDegree : Nat)
    (degs : List (Nat × Nat)) (acc : List RetuneCandidate) (g0 : Nat) : List RetuneCandidate :=
  let group := g0 + 1
  let maxDeg := max userMax (logupMaxDegreeForDegs degs group)
  let quotient := quotientDegreeFromMax maxDeg
  if quotient > blowup then acc
  else match FftCost.make (stage2Width numLookups group extDegree) quotient blowup extDegree with
    | none => acc
    | some cost => recordCandidate acc quotient cost group none

private def addBalancedCandidate (numLookups userMax blowup extDegree : Nat)
    (degs : List (Nat × Nat)) (acc : List RetuneCandidate) (g0 : Nat) : List RetuneCandidate :=
  let group := g0 + 2
  let order := balancedLookupOrder degs group
  let maxDeg := max userMax (logupMaxDegreeForOrder degs order group)
  let quotient := quotientDegreeFromMax maxDeg
  if quotient > blowup then acc
  else match FftCost.make (stage2Width numLookups group extDegree) quotient blowup extDegree with
    | none => acc
    | some cost => recordCandidate acc quotient cost group (some order)

private def selectBestCandidate (sorted : List RetuneCandidate)
    (initialCost : FftCost) (initialGroup : Nat) : FftCost × Nat × Option (List Nat) :=
  sorted.foldl (fun (bestCost, bestGroup, bestOrder) (_, cost, group, order) =>
    if cost.noWorseThan bestCost && cost.scoreLt bestCost then
      (cost, group, order)
    else (bestCost, bestGroup, bestOrder)) (initialCost, initialGroup, none)

private def hasMixedDegs (degs : List (Nat × Nat)) : Bool :=
  match degs with
  | [] => false
  | first :: rest => rest.any (· != first)

private def retuneSortedCandidates (numLookups userMax blowup extDegree : Nat)
    (degs : List (Nat × Nat)) : List RetuneCandidate :=
  let maxGroup := max 1 (min numLookups maxLookupGroup)
  let byQ1 := (List.range maxGroup).foldl
    (addPlainCandidate numLookups userMax blowup extDegree degs) []
  let byQ2 :=
    if !hasMixedDegs degs then byQ1
    else (List.range (maxGroup - 1)).foldl
      (addBalancedCandidate numLookups userMax blowup extDegree degs) byQ1
  byQ2.mergeSort (fun a b => a.1 ≤ b.1)

/-- Exact Lean mirror of `crates/aiur/src/trace/stark/lookup_groups.rs:167-273`. -/
def retune [Ring F] [DecidableEq F] (c : CompiledCircuit F) (blowup : Nat)
    (extDegree : Nat := goldilocksExtDegree) : CompiledCircuit F :=
  match FftCost.make c.stage2Width c.quotientDegree blowup extDegree with
  | none => c
  | some initialCost =>
      let degs := lookupDegrees c.lookups
      let sorted := retuneSortedCandidates c.lookups.length c.userMaxDegree blowup extDegree degs
      let (_, bestGroup, bestOrder) := selectBestCandidate sorted initialCost c.lookupGroupSize
      let newLookups :=
        match bestOrder with
        | none => c.lookups
        | some order =>
            letI : Inhabited (AirLookup F) := ⟨⟨.const 0, []⟩⟩
            permuteBy c.lookups order
      let newDegs := lookupDegrees newLookups
      let newMaxDeg := max c.userMaxDegree (logupMaxDegreeForDegs newDegs bestGroup)
      { c with
        lookups := newLookups
        lookupGroupSize := bestGroup
        stage2Width := stage2Width newLookups.length bestGroup extDegree
        constraintCount := c.constraints.length + logupConstraintCount newLookups.length bestGroup extDegree
        maxConstraintDegree := newMaxDeg }

private def CandidatesPerm (n : Nat) (cs : List RetuneCandidate) : Prop :=
  ∀ e ∈ cs, ∀ o, e.2.2.2 = some o → o.Perm (List.range n)

private theorem mem_of_mem_set {α : Type*} {xs : List α} {i : Nat} {a b : α}
    (h : b ∈ xs.set i a) : b ∈ xs ∨ b = a := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [List.set_cons_zero, List.mem_cons] at h
          rcases h with rfl | hmem
          · exact Or.inr rfl
          · exact Or.inl (List.mem_cons_of_mem x hmem)
      | succ i =>
          simp only [List.set_cons_succ, List.mem_cons] at h
          rcases h with rfl | hmem
          · exact Or.inl (List.mem_cons_self ..)
          · rcases ih hmem with h1 | h2
            · exact Or.inl (List.mem_cons_of_mem x h1)
            · exact Or.inr h2

private theorem recordCandidate_perm {n : Nat} {byQ : List RetuneCandidate}
    {q : Nat} {cost : FftCost} {g : Nat} {ord : Option (List Nat)}
    (hbyQ : CandidatesPerm n byQ) (hord : ∀ o, ord = some o → o.Perm (List.range n)) :
    CandidatesPerm n (recordCandidate byQ q cost g ord) := by
  unfold recordCandidate
  cases hidx : byQ.findIdx? (fun e => e.1 == q) with
  | none =>
      simp only
      intro e he o ho
      rcases List.mem_append.mp he with h | h
      · exact hbyQ e h o ho
      · simp only [List.mem_singleton] at h
        subst h
        exact hord o ho
  | some idx =>
      simp only
      cases hget : byQ[idx]? with
      | none => exact hbyQ
      | some entry =>
          rcases entry with ⟨_, prevCost, _, prevOrder⟩
          dsimp only
          split_ifs
          · intro e he o ho
            rcases mem_of_mem_set he with h | h
            · exact hbyQ e h o ho
            · subst h
              exact hord o ho
          · exact hbyQ

private theorem addPlainCandidate_perm {n userMax blowup extDegree : Nat}
    {degs : List (Nat × Nat)} {acc : List RetuneCandidate} {g0 : Nat}
    (hacc : CandidatesPerm n acc) :
    CandidatesPerm n (addPlainCandidate n userMax blowup extDegree degs acc g0) := by
  unfold addPlainCandidate
  dsimp only
  split_ifs
  · exact hacc
  · split
    · exact hacc
    · exact recordCandidate_perm hacc (fun _ h => by cases h)

private theorem addBalancedCandidate_perm {n userMax blowup extDegree : Nat}
    {degs : List (Nat × Nat)} (hlen : degs.length = n)
    {acc : List RetuneCandidate} {g0 : Nat}
    (hacc : CandidatesPerm n acc) :
    CandidatesPerm n (addBalancedCandidate n userMax blowup extDegree degs acc g0) := by
  unfold addBalancedCandidate
  dsimp only
  split_ifs
  · exact hacc
  · split
    · exact hacc
    · refine recordCandidate_perm hacc (fun o ho => ?_)
      cases ho
      simpa [hlen] using balancedLookupOrder_perm degs (g0 + 2)

private theorem foldl_candidatesPerm {n : Nat} {f : List RetuneCandidate → Nat → List RetuneCandidate}
    (hstep : ∀ acc g, CandidatesPerm n acc → CandidatesPerm n (f acc g)) :
    ∀ (xs : List Nat) (acc : List RetuneCandidate),
      CandidatesPerm n acc → CandidatesPerm n (xs.foldl f acc)
  | [], _, hacc => hacc
  | x :: xs, acc, hacc => foldl_candidatesPerm hstep xs (f acc x) (hstep acc x hacc)

private theorem retuneSortedCandidates_perm {n userMax blowup extDegree : Nat}
    {degs : List (Nat × Nat)} (hlen : degs.length = n) :
    CandidatesPerm n (retuneSortedCandidates n userMax blowup extDegree degs) := by
  unfold retuneSortedCandidates
  dsimp only
  intro e he o ho
  have hmem := (List.mergeSort_perm _ _).subset he
  have h1 : CandidatesPerm n
      ((List.range (max 1 (min n maxLookupGroup))).foldl
        (addPlainCandidate n userMax blowup extDegree degs) []) :=
    foldl_candidatesPerm (fun _ _ h => addPlainCandidate_perm h) _ [] (fun _ h => by cases h)
  by_cases hmix : (!hasMixedDegs degs) = true
  · simp only [hmix, ↓reduceIte] at hmem
    exact h1 e hmem o ho
  · simp only [hmix, ↓reduceIte] at hmem
    exact (foldl_candidatesPerm (fun _ _ h => addBalancedCandidate_perm hlen h) _ _ h1) e hmem o ho

private theorem selectBestCandidate_perm {n : Nat} (sorted : List RetuneCandidate)
    (initCost : FftCost) (initGroup : Nat) (hsorted : CandidatesPerm n sorted) :
    ∀ o, (selectBestCandidate sorted initCost initGroup).2.2 = some o → o.Perm (List.range n) := by
  unfold selectBestCandidate
  suffices ∀ (xs : List RetuneCandidate) (init : FftCost × Nat × Option (List Nat)),
      CandidatesPerm n xs →
      (∀ o, init.2.2 = some o → o.Perm (List.range n)) →
      ∀ o, (xs.foldl (fun (bestCost, bestGroup, bestOrder) (_, cost, group, order) =>
        if cost.noWorseThan bestCost && cost.scoreLt bestCost then
          (cost, group, order)
        else (bestCost, bestGroup, bestOrder)) init).2.2 = some o → o.Perm (List.range n) from
    this sorted (initCost, initGroup, none) hsorted (fun _ h => by cases h)
  intro xs
  induction xs with
  | nil => intro init _ hinit; exact hinit
  | cons x xs ih =>
      intro init hxs hinit
      simp only [List.foldl_cons]
      apply ih
      · intro e he; exact hxs e (List.mem_cons_of_mem _ he)
      · rcases init with ⟨bc, bg, bo⟩
        rcases x with ⟨q, cost, g, ord⟩
        dsimp only
        split_ifs
        · exact hxs (q, cost, g, ord) List.mem_cons_self
        · exact hinit

/-- **Structural & permutation preservation of `lookup_groups::retune`:**
`retune` preserves `mainWidth`, `preprocessed`, `constraints`, and replaces
`lookups` with a genuine `List.Perm` of the original `lookups`. -/
theorem retune_lookups_perm [Ring F] [DecidableEq F]
    (c : CompiledCircuit F) (blowup extDegree : Nat) :
    (retune c blowup extDegree).lookups.Perm c.lookups ∧
    (retune c blowup extDegree).mainWidth = c.mainWidth ∧
    (retune c blowup extDegree).preprocessed = c.preprocessed ∧
    (retune c blowup extDegree).constraints = c.constraints := by
  unfold retune
  cases hcost : FftCost.make c.stage2Width c.quotientDegree blowup extDegree with
  | none => exact ⟨List.Perm.refl _, rfl, rfl, rfl⟩
  | some initialCost =>
      dsimp only
      have hdegsLen : (lookupDegrees c.lookups).length = c.lookups.length := by
        simp [lookupDegrees]
      have hSorted := retuneSortedCandidates_perm (userMax := c.userMaxDegree)
        (blowup := blowup) (extDegree := extDegree) hdegsLen
      have hSel := selectBestCandidate_perm _ initialCost c.lookupGroupSize hSorted
      refine ⟨?_, rfl, rfl, rfl⟩
      cases hbo : (selectBestCandidate
          (retuneSortedCandidates c.lookups.length c.userMaxDegree blowup extDegree
            (lookupDegrees c.lookups)) initialCost c.lookupGroupSize).2.2 with
      | none => exact List.Perm.refl _
      | some order =>
          letI : Inhabited (AirLookup F) := ⟨⟨.const 0, []⟩⟩
          exact permuteBy_perm (hSel order hbo)

/-! ## 4. Algebraic LogUp Equivalence of `lookup_groups::retune` -/

section LogUpEquivalence

variable {K : Type} [Field K]

/-- Multi-STARK message fingerprint `β + ∑_{k} arg_k * γ^k`, matching
`multi_stark::lookup::logup_constraint_values` (`lookup.rs:212-217`, `270-275`). -/
def fingerprint (β γ : K) (args : List K) : K :=
  args.foldr (fun a acc => acc * γ + a) 0 + β

/-- Evaluate one `AirLookup F` into a `(signed_multiplicity, denominator)` pair in `K`,
given an embedding `embed : F → K` (e.g. `Fp → Fp2`). -/
def evalLookup [Ring F] (embed : F → K) (β γ : K)
    (mainRow nextRow prepRow : Nat → F) (isFirst isLast isTrans : F)
    (l : AirLookup F) : K × K :=
  let m := embed (l.multiplicity.eval mainRow nextRow prepRow isFirst isLast isTrans)
  let args := l.args.map fun a => embed (a.eval mainRow nextRow prepRow isFirst isLast isTrans)
  (m, fingerprint β γ args)

/-- Ungrouped LogUp rational sum `∑ (m_i / d_i)`. -/
def ungroupedLogUpSum (terms : List (K × K)) : K :=
  (terms.map fun (m, d) => m * d⁻¹).sum

theorem ungroupedLogUpSum_append (xs ys : List (K × K)) :
    ungroupedLogUpSum (xs ++ ys) = ungroupedLogUpSum xs + ungroupedLogUpSum ys := by
  simp [ungroupedLogUpSum]

theorem ungroupedLogUpSum_perm {xs ys : List (K × K)} (h : xs.Perm ys) :
    ungroupedLogUpSum xs = ungroupedLogUpSum ys := by
  unfold ungroupedLogUpSum
  exact (h.map _).sum_eq

/-- Product of all denominators in a LogUp chunk: `∏_{j ∈ chunk} d_j`. -/
def chunkDenom (chunk : List (K × K)) : K :=
  (chunk.map Prod.snd).prod

/-- Recursive cleared-denominator numerator: `∑_{j ∈ chunk} m_j * ∏_{j' ≠ j} d_{j'}`. -/
def chunkNumerator : List (K × K) → K
  | [] => 0
  | (m, d) :: rest => m * chunkDenom rest + d * chunkNumerator rest

/-- Exact prefix/suffix product form evaluated by `multi_stark::lookup::logup_constraint_values`
(`lookup.rs:220-231` and `293-318`). -/
def chunkNumeratorPrefixSuffix (chunk : List (K × K)) : K :=
  (chunk.zipIdx.map fun ((m, _), j) =>
    ((chunk.take j).map Prod.snd).prod * ((chunk.drop (j + 1)).map Prod.snd).prod * m).sum

private theorem mul_list_sum (d : K) : ∀ xs : List K, d * xs.sum = (xs.map (d * ·)).sum
  | [] => by simp
  | x :: xs => by simp [mul_add, mul_list_sum d xs]

/-- The prefix/suffix product computation in `multi-stark` equals `chunkNumerator` identically. -/
theorem chunkNumeratorPrefixSuffix_eq (chunk : List (K × K)) :
    chunkNumeratorPrefixSuffix chunk = chunkNumerator chunk := by
  induction chunk with
  | nil => simp [chunkNumeratorPrefixSuffix, chunkNumerator]
  | cons hd rest ih =>
      rcases hd with ⟨m, d⟩
      unfold chunkNumeratorPrefixSuffix at ih ⊢
      rw [List.zipIdx_cons', List.map_cons, List.sum_cons, List.map_map]
      simp only [List.take_zero, List.map_nil, List.prod_nil, one_mul, List.drop_succ_cons,
        List.drop_zero]
      have htail :
          (rest.zipIdx.map ((fun x : (K × K) × Nat =>
              ((((m, d) :: rest).take x.2).map Prod.snd).prod *
                ((rest.drop x.2).map Prod.snd).prod * x.1.1) ∘
              Prod.map id (· + 1))).sum =
          d * (rest.zipIdx.map fun x =>
              ((rest.take x.2).map Prod.snd).prod *
                ((rest.drop (x.2 + 1)).map Prod.snd).prod * x.1.1).sum := by
        rw [mul_list_sum, List.map_map]
        congr 1
        apply List.map_congr_left
        intro x _
        rcases x with ⟨⟨m', d'⟩, j⟩
        simp only [Function.comp_apply, Prod.map_apply, id_eq, List.take_succ_cons, List.map_cons,
          List.prod_cons]
        ring
      rw [htail, ih]
      simp only [chunkNumerator, chunkDenom]
      ring

theorem chunkDenom_ne_zero {chunk : List (K × K)} (hne : ∀ t ∈ chunk, t.2 ≠ 0) :
    chunkDenom chunk ≠ 0 := by
  induction chunk with
  | nil => simp [chunkDenom]
  | cons t rest ih =>
      simp only [chunkDenom, List.map_cons, List.prod_cons]
      exact mul_ne_zero (hne t List.mem_cons_self)
        (ih fun x hx => hne x (List.mem_cons_of_mem _ hx))

/-- Cleared-denominator identity for any chunk with nonzero denominators. -/
theorem chunkNumerator_eq_denom_mul_sum :
    ∀ (chunk : List (K × K)), (∀ t ∈ chunk, t.2 ≠ 0) →
      chunkNumerator chunk = chunkDenom chunk * ungroupedLogUpSum chunk
  | [], _ => by simp [chunkNumerator, chunkDenom, ungroupedLogUpSum]
  | (m, d) :: rest, hne => by
      have hd : d ≠ 0 := hne (m, d) List.mem_cons_self
      have hrest : ∀ t ∈ rest, t.2 ≠ 0 := fun t ht => hne t (List.mem_cons_of_mem _ ht)
      have ih := chunkNumerator_eq_denom_mul_sum rest hrest
      simp only [chunkNumerator, chunkDenom, ungroupedLogUpSum, List.map_cons, List.prod_cons,
        List.sum_cons] at ih ⊢
      rw [ih]
      field_simp [hd]

/-- **Grouped chunk constraint equivalence (`lookup.rs:36`, `304`):**
when every message denominator `d_j = β + rlc(γ, args_j)` in the chunk is nonzero,
`(∏ d_j) * (target - source) - ∑ mult_j * (∏_{j' ≠ j} d_{j'}) = 0` holds
if and only if `target - source = ∑ mult_j / d_j`. -/
theorem chunk_constraint_iff_sum_inv {chunk : List (K × K)} (hne : ∀ t ∈ chunk, t.2 ≠ 0)
    (source target : K) :
    chunkDenom chunk * (target - source) - chunkNumeratorPrefixSuffix chunk = 0 ↔
      target - source = ungroupedLogUpSum chunk := by
  rw [chunkNumeratorPrefixSuffix_eq, chunkNumerator_eq_denom_mul_sum chunk hne, sub_eq_zero,
    mul_eq_mul_left_iff]
  simp [chunkDenom_ne_zero hne]

/-- Chained stage-2 accumulator constraints for one row of a circuit with grouped
chunks `chunks` (matching `lookup.rs:250-321`). -/
def RowLogUpSatisfied (chunks : List (List (K × K))) (acc : Nat → K) (nextAcc0 inj : K) : Prop :=
  if chunks.isEmpty then
    nextAcc0 - acc 0 + inj = 0
  else
    ∀ (g : Nat) (hg : g < chunks.length),
      let target := if g + 1 < chunks.length then acc (g + 1) else nextAcc0 + inj
      chunkDenom (chunks[g]'hg) * (target - acc g) -
        chunkNumeratorPrefixSuffix (chunks[g]'hg) = 0

/-- Telescoping sum across all grouped LogUp chunks in a single row:
`nextAcc0 + inj - acc 0 = ungroupedLogUpSum chunks.flatten`. -/
theorem rowLogUp_telescopes {chunks : List (List (K × K))} {acc : Nat → K} {nextAcc0 inj : K}
    (hsat : RowLogUpSatisfied chunks acc nextAcc0 inj)
    (hne : ∀ ch ∈ chunks, ∀ t ∈ ch, t.2 ≠ 0) :
    (nextAcc0 + inj) - acc 0 = ungroupedLogUpSum chunks.flatten := by
  unfold RowLogUpSatisfied at hsat
  cases chunks with
  | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte] at hsat
      simp only [List.flatten_nil, ungroupedLogUpSum, List.map_nil, List.sum_nil]
      linear_combination hsat
  | cons ch0 rest =>
      set cs := ch0 :: rest
      have hneEmpty : cs.isEmpty = false := rfl
      simp only [hneEmpty, Bool.false_eq_true, ↓reduceIte] at hsat
      have hpos : 0 < cs.length := by simp [cs]
      suffices ∀ k ≤ cs.length,
          (if k < cs.length then acc k else nextAcc0 + inj) - acc 0 =
            ungroupedLogUpSum (cs.take k).flatten by
        have hfull := this cs.length le_rfl
        simpa [cs] using hfull
      intro k hk
      induction k with
      | zero =>
          simp [hpos, ungroupedLogUpSum]
      | succ m ih =>
          have hm : m < cs.length := Nat.lt_of_succ_le hk
          have hstep := hsat m hm
          have hne_m : ∀ t ∈ cs[m]'hm, t.2 ≠ 0 := hne _ (List.getElem_mem hm)
          have hdiff := (chunk_constraint_iff_sum_inv hne_m (acc m) _).mp hstep
          have ihm := ih (Nat.le_of_lt hm)
          simp only [hm, ↓reduceIte] at ihm
          have htake : (cs.take (m + 1)).flatten = (cs.take m).flatten ++ cs[m]'hm := by
            rw [List.take_succ_eq_append_getElem hm, List.flatten_append, List.flatten_singleton]
          rw [htake, ungroupedLogUpSum_append, ← ihm, ← hdiff]
          ring

/-- Circuit-level grouped LogUp constraints over a trace of height `H > 0`. -/
def CircuitLogUpSatisfied (H : Nat) (rowChunks : Nat → List (List (K × K)))
    (acc : Nat → Nat → K) (accInitial accFinal : K) : Prop :=
  0 < H ∧
  ∀ r < H,
    RowLogUpSatisfied (rowChunks r) (acc r) (acc ((r + 1) % H) 0)
      (if r + 1 = H then accFinal - accInitial else 0)

/-- **Circuit-level telescoping (`lookup.rs:176`, `248`):**
over any trace of height `H > 0`, the grouped chained-accumulator LogUp constraints
force `accFinal - accInitial = ∑_{r < H} ungroupedLogUpSum (rowChunks r).flatten`. -/
theorem circuitLogUp_telescopes {H : Nat} {rowChunks : Nat → List (List (K × K))}
    {acc : Nat → Nat → K} {accInitial accFinal : K}
    (hsat : CircuitLogUpSatisfied H rowChunks acc accInitial accFinal)
    (hne : ∀ r < H, ∀ ch ∈ rowChunks r, ∀ t ∈ ch, t.2 ≠ 0) :
    accFinal - accInitial =
      ((List.range H).map fun r => ungroupedLogUpSum (rowChunks r).flatten).sum := by
  rcases hsat with ⟨hH, hrows⟩
  suffices ∀ k ≤ H,
      acc (k % H) 0 + (if k = H then accFinal - accInitial else 0) - acc 0 0 =
        ((List.range k).map fun r => ungroupedLogUpSum (rowChunks r).flatten).sum by
    have hfull := this H le_rfl
    simpa [Nat.mod_self] using hfull
  intro k hk
  induction k with
  | zero =>
      have h0 : (0 : Nat) ≠ H := Nat.ne_of_lt hH
      simp [h0]
  | succ m ih =>
      have hm : m < H := Nat.lt_of_succ_le hk
      have ihm := ih (Nat.le_of_lt hm)
      have hmNe : m ≠ H := Nat.ne_of_lt hm
      have hmMod : m % H = m := Nat.mod_eq_of_lt hm
      simp only [hmNe, ↓reduceIte, add_zero, hmMod] at ihm
      have hrow := rowLogUp_telescopes (hrows m hm) (hne m hm)
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ← ihm, ← hrow]
      ring

/-- **Headline LogUp Equivalence of `lookup_groups::retune` (per-circuit):**
For any circuit `c`, blowup `blowup`, extension degree `extDegree`, and trace of
height `H > 0` whose lookup denominators are nonzero at every row:
if the trace satisfies the **retuned** grouped LogUp constraints (with reordered
lookups `(retune c blowup extDegree).lookups` packed into chunks of size
`(retune c blowup extDegree).lookupGroupSize`), then its accumulator delta
`accFinal - accInitial` equals the **exact ungrouped, unpermuted** LogUp rational sum
of `c.lookups`! -/
theorem retune_logup_equiv [Ring F] [DecidableEq F]
    (c : CompiledCircuit F) (blowup extDegree : Nat)
    (embed : F → K) (β γ : K)
    (H : Nat)
    (mainRow nextRow prepRow : Nat → Nat → F) (isFirst isLast isTrans : Nat → F)
    (acc : Nat → Nat → K) (accInitial accFinal : K)
    (hsat : CircuitLogUpSatisfied H
      (fun r => chunkList (retune c blowup extDegree).lookupGroupSize
        ((retune c blowup extDegree).lookups.map fun l =>
          evalLookup embed β γ (mainRow r) (nextRow r) (prepRow r)
            (isFirst r) (isLast r) (isTrans r) l))
      acc accInitial accFinal)
    (hne : ∀ r < H, ∀ l ∈ c.lookups,
      (evalLookup embed β γ (mainRow r) (nextRow r) (prepRow r)
        (isFirst r) (isLast r) (isTrans r) l).2 ≠ 0) :
    accFinal - accInitial =
      ((List.range H).map fun r =>
        ungroupedLogUpSum (c.lookups.map fun l =>
          evalLookup embed β γ (mainRow r) (nextRow r) (prepRow r)
            (isFirst r) (isLast r) (isTrans r) l)).sum := by
  let evalRow : Nat → AirLookup F → K × K := fun r l =>
    evalLookup embed β γ (mainRow r) (nextRow r) (prepRow r) (isFirst r) (isLast r) (isTrans r) l
  have hperm : (retune c blowup extDegree).lookups.Perm c.lookups :=
    (retune_lookups_perm c blowup extDegree).1
  have hneChunks : ∀ r < H,
      ∀ ch ∈ chunkList (retune c blowup extDegree).lookupGroupSize
          ((retune c blowup extDegree).lookups.map (evalRow r)),
        ∀ t ∈ ch, t.2 ≠ 0 := by
    intro r hr ch hch t ht
    have htFlat : t ∈ (chunkList (retune c blowup extDegree).lookupGroupSize
        ((retune c blowup extDegree).lookups.map (evalRow r))).flatten :=
      List.mem_flatten.mpr ⟨ch, hch, ht⟩
    rw [chunkList_flatten] at htFlat
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp htFlat
    exact hne r hr l (hperm.subset hl)
  rw [circuitLogUp_telescopes hsat hneChunks]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [chunkList_flatten]
  exact ungroupedLogUpSum_perm (hperm.map (evalRow r))

/-- **Batch-wide LogUp Equivalence of `lookup_groups::retune`:**
if a batch of retuned circuits chains its global LogUp accumulator from `0` to `0`
(`∑_i (accFinal_i - accInitial_i) = 0`), then the exact ungrouped, unpermuted
global LogUp rational sum across every row and every lookup of every circuit vanishes! -/
theorem retune_batch_logup_equiv [Ring F] [DecidableEq F]
    {n : Nat}
    (circuits : Fin n → CompiledCircuit F) (blowup extDegree : Nat)
    (embed : F → K) (β γ : K)
    (H : Fin n → Nat)
    (mainRow nextRow prepRow : (i : Fin n) → Nat → Nat → F)
    (isFirst isLast isTrans : (i : Fin n) → Nat → F)
    (acc : (i : Fin n) → Nat → Nat → K) (accInitial accFinal : Fin n → K)
    (hsat : ∀ i : Fin n,
      CircuitLogUpSatisfied (H i)
        (fun r => chunkList (retune (circuits i) blowup extDegree).lookupGroupSize
          ((retune (circuits i) blowup extDegree).lookups.map fun l =>
            evalLookup embed β γ (mainRow i r) (nextRow i r) (prepRow i r)
              (isFirst i r) (isLast i r) (isTrans i r) l))
        (acc i) (accInitial i) (accFinal i))
    (hne : ∀ i : Fin n, ∀ r < H i, ∀ l ∈ (circuits i).lookups,
      (evalLookup embed β γ (mainRow i r) (nextRow i r) (prepRow i r)
        (isFirst i r) (isLast i r) (isTrans i r) l).2 ≠ 0)
    (hbalance : ((List.finRange n).map fun i => accFinal i - accInitial i).sum = 0) :
    ((List.finRange n).map fun i =>
      ((List.range (H i)).map fun r =>
        ungroupedLogUpSum ((circuits i).lookups.map fun l =>
          evalLookup embed β γ (mainRow i r) (nextRow i r) (prepRow i r)
            (isFirst i r) (isLast i r) (isTrans i r) l)).sum).sum = 0 := by
  rw [← hbalance]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (retune_logup_equiv (circuits i) blowup extDegree embed β γ (H i)
    (mainRow i) (nextRow i) (prepRow i) (isFirst i) (isLast i) (isTrans i)
    (acc i) (accInitial i) (accFinal i) (hsat i) (hne i)).symm

end LogUpEquivalence

/-! ## 5. Soundness Bridge: Lowered Multi-STARK AIR + LogUp → `Grouping.Plan` & `Aiur.Audit` -/

section PlanSoundness

variable {F : Type} [Field F] [DecidableEq F]

private theorem arithExpr_denote_congr (n : Nat) {a b : Nat → F}
    (hagree : ∀ i < n, a i = b i) :
    ∀ (p : Circuit.ArithExpr F), p.inBounds n = true → p.denote a = p.denote b
  | .const _, _ => rfl
  | .var i, hi => by
      simp only [Scalar.Circuit.ArithExpr.inBounds, decide_eq_true_eq] at hi
      exact hagree i hi
  | .add p q, hpq => by
      simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hpq
      simp only [Scalar.Circuit.ArithExpr.denote,
        arithExpr_denote_congr n hagree p hpq.1, arithExpr_denote_congr n hagree q hpq.2]
  | .sub p q, hpq => by
      simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hpq
      simp only [Scalar.Circuit.ArithExpr.denote,
        arithExpr_denote_congr n hagree p hpq.1, arithExpr_denote_congr n hagree q hpq.2]
  | .mul p q, hpq => by
      simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hpq
      simp only [Scalar.Circuit.ArithExpr.denote,
        arithExpr_denote_congr n hagree p hpq.1, arithExpr_denote_congr n hagree q hpq.2]

/-- Every AIR constraint of a `CircuitInput` vanishes on a main row (for row-local
function circuits, `nextRow`, `prepRow`, and selector flags are unused). -/
def RowConstraintsZero (input : CircuitInput F) (row : Nat → F) : Prop :=
  ∀ e ∈ input.constraints, e.eval row (fun _ => 0) (fun _ => 0) 0 0 0 = 0

/-- **Ungrouped single-chip lowering soundness:**
If a full Multi-STARK row `fullValues` (length `chip.numVars + 1`, where
`chip = Activation.compile src`) satisfies every constraint of
`lowerSingleChip callableId chip src.numVars` and every active ROM lookup lies in
`rom`, then:
1. If `src.numVars` (the activation selector) is `0`, the padding constraint
   `(1 - active) * mult = 0` forces multiplicity `fullValues[chip.numVars] = 0`.
2. `chip.checkRow rom (take chip.numVars fullValues)` returns
   `.ok (chip.receive row, chip.premises row)`. -/
theorem lowerSingleChip_row_sound (callableId : String → Nat)
    (src : Circuit.Chip F) (rom : WireROM F)
    (fullValues : List F)
    (hlen : fullValues.length = (Activation.compile src).numVars + 1)
    (hformed : (Activation.compile src).wellFormed = true)
    (hcons : RowConstraintsZero (lowerSingleChip callableId (Activation.compile src) src.numVars)
      (fun i => fullValues.getD i 0))
    (hrom : ∀ cell ∈ (Activation.compile src).memory,
      cell.enable.denote (fun i => fullValues.getD i 0) = 1 →
        (cell.address.denote (fun i => fullValues.getD i 0),
          cell.value.map (Circuit.ArithExpr.denote (fun i => fullValues.getD i 0))) ∈ rom.entries) :
    let chip := Activation.compile src
    let row : Circuit.Row F := ⟨src.name, fullValues.take chip.numVars⟩
    let mult := fullValues.getD chip.numVars 0
    (row.assignment src.numVars = 0 → mult = 0) ∧
    chip.checkRow rom row = .ok (chip.receive row, chip.premises row) := by
  intro chip row mult
  have hrowLen : row.values.length = chip.numVars := by
    simp only [row, List.length_take, hlen]
    exact Nat.min_eq_left (Nat.le_succ _)
  have hassignAgree : ∀ i < chip.numVars, row.assignment i = fullValues.getD i 0 := by
    intro i hi
    simp only [row, Circuit.Row.assignment, Scalar.Circuit.Row.assignment,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  have hsrcLt : src.numVars < chip.numVars := by
    simp [chip, Activation.compile]
  have hactAgree : row.assignment src.numVars = fullValues.getD src.numVars 0 :=
    hassignAgree src.numVars hsrcLt
  have hpad : (1 - fullValues.getD src.numVars 0) * mult = 0 := by
    have hmem : AirExpr.mul (.sub (.const (1 : F)) (.main src.numVars)) (.main chip.numVars) ∈
        (lowerSingleChip callableId chip src.numVars).constraints := by
      simp [lowerSingleChip]
    simpa [AirExpr.eval, mult] using hcons _ hmem
  constructor
  · intro hoff
    rw [hactAgree] at hoff
    rw [hoff, sub_zero, one_mul] at hpad
    exact hpad
  · apply (Circuit.Chip.checkRow_iff).mpr
    refine ⟨?_, rfl⟩
    have hformed0 := hformed
    simp only [Circuit.Chip.wellFormed, Bool.and_eq_true, List.all_eq_true] at hformed
    obtain ⟨⟨⟨⟨_, _⟩, hconsB⟩, _⟩, hmemB⟩ := hformed
    refine ⟨hformed0, hrowLen, ?_, ?_⟩
    · intro p hp
      have hmem : lowerPoly p ∈ (lowerSingleChip callableId chip src.numVars).constraints := by
        simp only [lowerSingleChip, List.mem_append, List.mem_map]
        exact Or.inl ⟨p, hp, rfl⟩
      have hzero : p.denote (fun i => fullValues.getD i 0) = 0 := by
        have h := hcons _ hmem
        rwa [eval_lowerPoly] at h
      have hcongr := arithExpr_denote_congr chip.numVars hassignAgree p (hconsB p hp)
      exact hcongr.trans hzero
    · intro cell hcell henab
      have hcb := hmemB cell hcell
      simp only [Circuit.MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at hcb
      obtain ⟨⟨haddrB, henabB⟩, hvalB⟩ := hcb
      have henabFull : cell.enable.denote (fun i => fullValues.getD i 0) = 1 := by
        rwa [← arithExpr_denote_congr chip.numVars hassignAgree cell.enable henabB]
      have haddr : cell.address.denote row.assignment =
          cell.address.denote (fun i => fullValues.getD i 0) :=
        arithExpr_denote_congr chip.numVars hassignAgree cell.address haddrB
      have hval : cell.value.map (Circuit.ArithExpr.denote row.assignment) =
          cell.value.map (Circuit.ArithExpr.denote (fun i => fullValues.getD i 0)) := by
        rcases cell with ⟨addr, ⟨ty, ws⟩, en⟩
        simp only [WireValue.map, WireValue.mk.injEq, true_and]
        apply List.map_congr_left
        intro w hw
        exact arithExpr_denote_congr chip.numVars hassignAgree w (hvalB w hw)
      rw [haddr, hval]
      exact hrom cell hcell henabFull

/-- **Grouped-layout lowering soundness:**
If a full Multi-STARK row `fullValues` (length `g.width + 1`) satisfies every
constraint of `lowerGroupLayout g` (whose polynomials are in-bounds of `g.width`),
then:
1. When `g.activation` evaluates to `0` (padding row), `(1 - activation) * mult = 0`
   forces `fullValues[g.width] = 0` and `g.inspectRow rom (take g.width fullValues) = .ok none`.
2. When `g.activation` evaluates to `1` and a member `m ∈ g.members` has selector `1`
   and valid memory lookups in `rom`, `g.inspectRow rom (take g.width fullValues)`
   returns `.ok (some claims)`. -/
theorem lowerGroupLayout_row_sound (g : Grouping.Layout F) (rom : WireROM F)
    (fullValues : List F)
    (hlen : fullValues.length = g.width + 1)
    (hactBound : g.activation.inBounds g.width = true)
    (hconsBound : ∀ p ∈ g.constraints, p.inBounds g.width = true)
    (hcons : RowConstraintsZero (lowerGroupLayout g) (fun i => fullValues.getD i 0)) :
    let row : Circuit.Row F := ⟨g.name, fullValues.take g.width⟩
    let mult := fullValues.getD g.width 0
    (g.activation.denote row.assignment = 0 →
      mult = 0 ∧ g.inspectRow rom row = .ok none) ∧
    (g.activation.denote row.assignment = 1 →
      (∃ m ∈ g.members, row.assignment m.selector = 1) →
      (∀ m ∈ g.members, row.assignment m.selector = 1 →
        ((g.view m).denote row.assignment).MemoryValid rom) →
      ∃ claims, g.inspectRow rom row = .ok (some claims)) := by
  intro row mult
  have hrowLen : row.values.length = g.width := by
    simp only [row, List.length_take, hlen]
    exact Nat.min_eq_left (Nat.le_succ _)
  have hassignAgree : ∀ i < g.width, row.assignment i = fullValues.getD i 0 := by
    intro i hi
    simp only [row, Circuit.Row.assignment, Scalar.Circuit.Row.assignment,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  have hsat : Circuit.Satisfies g.constraints row.assignment := by
    intro p hp
    have hmem : lowerPoly p ∈ (lowerGroupLayout g).constraints := by
      simp only [lowerGroupLayout, List.mem_append, List.mem_map]
      exact Or.inl ⟨p, hp, rfl⟩
    have hzero : Scalar.Circuit.ArithExpr.denote (fun i => fullValues.getD i 0) p = 0 := by
      have h := hcons _ hmem
      rwa [eval_lowerPoly] at h
    exact (arithExpr_denote_congr g.width hassignAgree p (hconsBound p hp)).trans hzero
  have hpad : (1 - g.activation.denote (fun i => fullValues.getD i 0)) * mult = 0 := by
    have hmem : AirExpr.mul (.sub (.const (1 : F)) (lowerPoly g.activation)) (.main g.width) ∈
        (lowerGroupLayout g).constraints := by
      simp [lowerGroupLayout]
    have hz := hcons _ hmem
    simpa [AirExpr.eval, eval_lowerPoly, mult] using hz
  constructor
  · intro hoff
    have hoffFull : g.activation.denote (fun i => fullValues.getD i 0) = 0 := by
      rw [← arithExpr_denote_congr g.width hassignAgree g.activation hactBound]
      exact hoff
    refine ⟨?_, ?_⟩
    · rw [hoffFull, sub_zero, one_mul] at hpad
      exact hpad
    · simp [Grouping.Layout.inspectRow, hrowLen, hsat, hoff]
  · intro hon hsel hmemValid
    unfold Grouping.Layout.inspectRow
    have hne0 : g.activation.denote row.assignment ≠ 0 := by rw [hon]; exact one_ne_zero
    simp only [hrowLen, hsat, and_self, ↓reduceIte, hne0]
    have hex : ∃ m ∈ g.members, decide (row.assignment m.selector = 1) = true := by
      obtain ⟨m, hm, hs⟩ := hsel
      exact ⟨m, hm, decide_eq_true hs⟩
    obtain ⟨m, hfind⟩ : ∃ m, g.members.find? (fun m => decide (row.assignment m.selector = 1)) = some m := by
      cases h : g.members.find? (fun m => decide (row.assignment m.selector = 1)) with
      | some m => exact ⟨m, rfl⟩
      | none =>
          obtain ⟨m0, hm0, hd0⟩ := hex
          exact absurd hd0 (by simpa [List.find?_eq_none.mp h m0 hm0])
    simp only [hfind]
    have hvalidRow : g.ValidRow rom row.assignment := ⟨hsat, hon, hmemValid⟩
    simp [hvalidRow]

/-- Pair physical rows with integer weights matching `Balance.weigh` (padding rows
get weight `0`; active rows get the next weight from `ws`). -/
def attachPlanWeights :
    List (Circuit.Row F) →
    List (Option (RuleClaims (Circuit.Message F))) →
    List (RuleClaims (Circuit.Message F) × Int) →
    List (Circuit.WeightedRow F)
  | [], _, _ => []
  | r :: rs, none :: os, ws => ⟨r, 0⟩ :: attachPlanWeights rs os ws
  | r :: rs, some _ :: os, w :: ws => ⟨r, w.2⟩ :: attachPlanWeights rs os ws
  | r :: rs, _, _ => ⟨r, 0⟩ :: attachPlanWeights rs [] []

theorem attachPlanWeights_length :
    ∀ (rows : List (Circuit.Row F)) (os : List (Option (RuleClaims (Circuit.Message F))))
      (ws : List (RuleClaims (Circuit.Message F) × Int)),
      (attachPlanWeights rows os ws).length = rows.length
  | [], _, _ => rfl
  | _ :: rs, [], _ => by simp [attachPlanWeights, attachPlanWeights_length]
  | _ :: rs, none :: os, ws => by simp [attachPlanWeights, attachPlanWeights_length]
  | _ :: rs, some _ :: os, [] => by simp [attachPlanWeights, attachPlanWeights_length]
  | _ :: rs, some _ :: os, _ :: ws => by simp [attachPlanWeights, attachPlanWeights_length]

theorem mapM_weigh_attachPlanWeights {source : Circuit.System F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) (rom : WireROM F) :
    ∀ (rows : List (Circuit.Row F)) (os : List (Option (RuleClaims (Circuit.Message F))))
      (ws : List (RuleClaims (Circuit.Message F) × Int)),
      rows.mapM (plan.inspectRow rom) = .ok os →
      ws.map Prod.fst = Grouping.activeRules os →
      ∃ out, (attachPlanWeights rows os ws).mapM (plan.weigh rom) = .ok out ∧
        Grouping.activeRules out = ws
  | [], os, ws, hmap, hws => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      cases ws with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons _ _ => simp [Grouping.activeRules] at hws
  | r :: rs, os, ws, hmap, hws => by
      rw [List.mapM_cons] at hmap
      cases hinsp : plan.inspectRow rom r with
      | error e => simp [hinsp, bind, Except.bind] at hmap
      | ok opt =>
          simp only [hinsp, bind, Except.bind] at hmap
          cases hrest : rs.mapM (plan.inspectRow rom) with
          | error e => simp [hrest] at hmap
          | ok os' =>
              simp only [hrest, pure, Except.pure, Except.ok.injEq] at hmap
              subst hmap
              cases opt with
              | none =>
                  simp only [Grouping.activeRules_none] at hws
                  obtain ⟨out', hout', hact'⟩ := mapM_weigh_attachPlanWeights plan rom rs os' ws hrest hws
                  refine ⟨none :: out', ?_, by simp [hact']⟩
                  simp [attachPlanWeights, List.mapM_cons, Grouping.Plan.weigh, hinsp, hout',
                    bind, Except.bind, pure, Except.pure]
              | some claims =>
                  simp only [Grouping.activeRules_some] at hws
                  cases ws with
                  | nil => simp at hws
                  | cons w ws' =>
                      simp only [List.map_cons, List.cons.injEq] at hws
                      obtain ⟨hw1, hws'⟩ := hws
                      obtain ⟨out', hout', hact'⟩ :=
                        mapM_weigh_attachPlanWeights plan rom rs os' ws' hrest hws'
                      refine ⟨some (claims, w.2) :: out', ?_, ?_⟩
                      · simp [attachPlanWeights, List.mapM_cons, Grouping.Plan.weigh, hinsp, hout',
                          bind, Except.bind, pure, Except.pure]
                      · simp only [Grouping.activeRules_some, hact', List.cons.injEq, and_true]
                        cases w with
                        | mk fst snd => dsimp only at hw1; rw [hw1]

/-- Over Goldilocks `Fp`, if a dynamic claim has positive integer demand `0 < d < p`
and the sum of prover field multiplicities over providing rows equals `(d : Fp)`,
then at least one active row provides that claim. -/
theorem exists_provider_of_goldilocks_balance
    {α : Type} (providers : List α) (w : α → Library.U32.Goldilocks.F) {d : Nat}
    (hpos : 0 < d) (hlt : d < Library.U32.Goldilocks.modulus)
    (hbal : (providers.map w).sum = (d : Library.U32.Goldilocks.F)) :
    providers ≠ [] := by
  intro hnil
  subst hnil
  simp only [List.map_nil, List.sum_nil] at hbal
  have hzero : ((d : Nat) : Library.U32.Goldilocks.F) = 0 := hbal.symm
  have hdvd : Library.U32.Goldilocks.modulus ∣ d :=
    (ZMod.natCast_eq_zero_iff d Library.U32.Goldilocks.modulus).mp hzero
  exact Nat.not_lt.mpr (Nat.le_of_dvd hpos hdvd) hlt

/-- **Inspected rows + field balance → `Grouping.Plan.checkMemo` (Goldilocks):**
Given extracted rows over a plan `plan` satisfying `plan.inspectRow` and Goldilocks
field-level LogUp balance (under total dynamic demand `< Goldilocks.modulus`),
there exist integer-weighted rows of identical length accepted by `plan.checkMemo`. -/
theorem checkMemo_of_inspected_field_balance
    {source : Circuit.System Library.U32.Goldilocks.F} {id : String → Except String Nat}
    (plan : Grouping.Plan source id) (rom : WireROM Library.U32.Goldilocks.F)
    (root : Circuit.Message Library.U32.Goldilocks.F)
    (rows : List (Circuit.Row Library.U32.Goldilocks.F))
    (inspected : List (Option (RuleClaims (Circuit.Message Library.U32.Goldilocks.F))))
    (hctx : source.checkContext rom root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow rom) = .ok inspected)
    (hdemLt : (Balance.required (fun c => decide (source.MapClaim c)) root
      (Grouping.activeRules inspected)).length < Library.U32.Goldilocks.modulus)
    (provWeight : RuleClaims (Circuit.Message Library.U32.Goldilocks.F) → Library.U32.Goldilocks.F)
    (hbal : ∀ claim ∈ Balance.required (fun c => decide (source.MapClaim c)) root
        (Grouping.activeRules inspected),
      (((Grouping.activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
        ((((Balance.required (fun c => decide (source.MapClaim c)) root
          (Grouping.activeRules inspected)).countP fun x => decide (x = claim)) : Nat) :
            Library.U32.Goldilocks.F)) :
    ∃ wrows : List (Circuit.WeightedRow Library.U32.Goldilocks.F),
      wrows.length = rows.length ∧
      plan.checkMemo rom root wrows = .ok () := by
  set rules := Grouping.activeRules inspected
  set demands := Balance.required (fun c => decide (source.MapClaim c)) root rules
  set ws := Balance.weigh demands rules
  have hcov : ∀ claim ∈ demands, ∃ rule ∈ rules, rule.1 = claim := by
    intro claim hmem
    have hpos : 0 < demands.countP (fun x => decide (x = claim)) :=
      List.countP_pos_iff.mpr ⟨claim, hmem, decide_eq_true rfl⟩
    have hle : demands.countP (fun x => decide (x = claim)) ≤ demands.length :=
      List.countP_le_length
    have hne := exists_provider_of_goldilocks_balance
      (rules.filter fun r => decide (r.1 = claim)) provWeight hpos
      (lt_of_le_of_lt hle hdemLt) (hbal claim hmem)
    obtain ⟨rule, hrmem⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hrIn, hrEq⟩ := List.mem_filter.mp hrmem
    exact ⟨rule, hrIn, of_decide_eq_true hrEq⟩
  obtain ⟨out, hout, hact⟩ :=
    mapM_weigh_attachPlanWeights plan rom rows inspected ws hinsp (Balance.weigh_rules demands rules)
  refine ⟨attachPlanWeights rows inspected ws, attachPlanWeights_length rows inspected ws, ?_⟩
  unfold Grouping.Plan.checkMemo
  simp only [hctx, hout, hact]
  rw [Balance.weigh_balanced hcov]
  rfl

/-- **Inspected rows + field balance → certified Aiur source evaluation (Goldilocks).** No lowered
AIR occurs in the statement (see the module header).
Composes `Physical.Prepared.checkDepthPlan` + `checkMemo_of_inspected_field_balance`
+ `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks`! -/
theorem depth_sound_of_inspected_field_balance_goldilocks
    {program : Aiur.Modules.Program Library.U32.Goldilocks.F}
    (prepared : Aiur.Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    {measures : Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.circuit.inlined.program cfg measures plan = true)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Library.U32.Goldilocks.F)}
    {result : Value Library.U32.Goldilocks.F}
    {wires : List (WireValue Library.U32.Goldilocks.F)}
    {output : WireValue Library.U32.Goldilocks.F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Circuit.Message Library.U32.Goldilocks.F}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.Row Library.U32.Goldilocks.F)} (bound : rows.length ≤ maxBatchRows)
    (inspected : List (Option (RuleClaims (Circuit.Message Library.U32.Goldilocks.F))))
    (hctx : (Depth.system cfg physical.system).checkContext (Erasure.rawROM rom) root = .ok ())
    (hinsp : rows.mapM (plan.inspectRow (Erasure.rawROM rom)) = .ok inspected)
    (hdemLt : (Balance.required
        (fun c => decide ((Depth.system cfg physical.system).MapClaim c)) root
        (Grouping.activeRules inspected)).length < Library.U32.Goldilocks.modulus)
    (provWeight : RuleClaims (Circuit.Message Library.U32.Goldilocks.F) → Library.U32.Goldilocks.F)
    (hbal : ∀ claim ∈ Balance.required
          (fun c => decide ((Depth.system cfg physical.system).MapClaim c)) root
          (Grouping.activeRules inspected),
        (((Grouping.activeRules inspected).filter fun r => decide (r.1 = claim)).map provWeight).sum =
          ((((Balance.required
            (fun c => decide ((Depth.system cfg physical.system).MapClaim c)) root
            (Grouping.activeRules inspected)).countP fun x => decide (x = claim)) : Nat) :
              Library.U32.Goldilocks.F))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result := by
  obtain ⟨certified, bits, activated⟩ := Physical.Prepared.checkDepthPlan_sound certOK
  obtain ⟨wrows, hlen, hchecked⟩ :=
    checkMemo_of_inspected_field_balance plan (Erasure.rawROM rom) root rows inspected
      hctx hinsp hdemLt provWeight hbal
  exact prepared.depth_grouped_activated_heap_sound_goldilocks compiled physical certified bits
    plan activated selected valid signed rooted outside (hlen ▸ bound) hchecked arguments decoded

end PlanSoundness

/-- Summary statistics for a lowered + retuned circuit matching
`crates/aiur/src/trace/stark.rs`'s `CircuitStatistics` plus `constraint_count`. -/
structure CircuitSummary where
  name : String
  stage1Width : Nat
  stage2Width : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  lookups : Nat
  lookupGroupSize : Nat
  quotientDegree : Nat
  constraintCount : Nat
  maxConstraintDegree : Nat
  deriving Repr, BEq, DecidableEq

/-- Extract the summary tuple matching Rust's `Backend::statistics()` + `constraint_count`. -/
def CompiledCircuit.summary (c : CompiledCircuit F) : CircuitSummary :=
  { name := c.name
    stage1Width := c.mainWidth
    stage2Width := c.stage2Width
    preprocessedWidth := c.preprocessed.width
    preprocessedHeight := c.preprocessed.height
    lookups := c.lookups.length
    lookupGroupSize := c.lookupGroupSize
    quotientDegree := c.quotientDegree
    constraintCount := c.constraintCount
    maxConstraintDegree := c.maxConstraintDegree }

/-- Lower a complete Multi-STARK system (functions, fixed tables, ROMs) in exact
`crates/aiur/src/trace/stark.rs:360-404` order, compiling each circuit and running
`retune` with `blowup = 2^logBlowup`. Defaults to `RomLayout.vectorized` (`C6`),
matching Rust's `Backend::build`. -/
def lowerFullSystem [Field F] [DecidableEq F] {source : Circuit.System F}
    {id : String → Except String Nat}
    (callableId : String → Nat) (plan : Grouping.Plan source id)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat)
    (logBlowup : Nat) (segmented : Bool) (extDegree : Nat := goldilocksExtDegree)
    (romLayout : RomLayout := .vectorized) :
    List (CompiledCircuit F) :=
  let blowup := 2 ^ logBlowup
  let inputs :=
    lowerPlanFunctionsOrdered callableId plan ++
    lowerFixedTables (F := F) fixedMaps logBlowup ++
    lowerRomCircuitsWithLayout (F := F) romWidths segmented romLayout
  inputs.map fun inp => retune (compileCircuit inp extDegree) blowup extDegree

/-! ## 5b. Grouping Slot Permutation (`C7a`) & Raw-Packet Compaction (`C2`) LogUp Equivalence -/

section GroupingPacketLogUp

variable {F K : Type} [Field F] [DecidableEq F] [Field K]

private theorem foldr_rlc_zero (γ : K) :
    ∀ (xs : List K), (∀ j : Nat, xs[j]?.getD 0 = 0) →
      xs.foldr (fun a acc => acc * γ + a) 0 = 0
  | [], _ => rfl
  | x :: xs, h => by
      have hx : x = 0 := by simpa using h 0
      have hxs : ∀ j : Nat, xs[j]?.getD 0 = 0 := fun j => by simpa using h (j + 1)
      simp [hx, foldr_rlc_zero γ xs hxs]

/-- Multi-STARK's RLC fingerprint `β + ∑ arg_k * γ^k` is invariant under
zero-padded tails: two argument vectors with equal zero-extended entries have
the exact same fingerprint. -/
theorem fingerprint_eq_of_word_eq (β γ : K) :
    ∀ {xs ys : List K}, (∀ j : Nat, xs[j]?.getD 0 = ys[j]?.getD 0) →
      fingerprint β γ xs = fingerprint β γ ys
  | [], ys, h => by
      unfold fingerprint
      have hys : ∀ j : Nat, ys[j]?.getD 0 = 0 := fun j => (h j).symm
      rw [List.foldr_nil, foldr_rlc_zero γ ys hys]
  | x :: xs, [], h => by
      unfold fingerprint
      have hxs : ∀ j : Nat, (x :: xs)[j]?.getD 0 = 0 := fun j => h j
      rw [foldr_rlc_zero γ (x :: xs) hxs, List.foldr_nil]
  | x :: xs, y :: ys, h => by
      have h0 : x = y := by simpa using h 0
      have htail : ∀ j : Nat, xs[j]?.getD 0 = ys[j]?.getD 0 := fun j => by simpa using h (j + 1)
      have ih := fingerprint_eq_of_word_eq β γ htail
      unfold fingerprint at ih ⊢
      have hfold : xs.foldr (fun a acc => acc * γ + a) 0 = ys.foldr (fun a acc => acc * γ + a) 0 :=
        add_right_cancel ih
      simp [h0, hfold]

private theorem flatten_map_append_at {α : Type} (k : α) (s₀ : Nat) :
    ∀ (m : Nat) (f : Nat → List α), s₀ < m →
      ((List.range m).map fun s => if s = s₀ then f s ++ [k] else f s).flatten.Perm
        (k :: ((List.range m).map f).flatten)
  | 0, _, hs => by omega
  | m + 1, f, hs => by
      rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton, List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton]
      by_cases heq : m = s₀
      · subst heq
        have hlt : ∀ s ∈ List.range m, (if s = m then f s ++ [k] else f s) = f s := by
          intro s hsm
          have hne : s ≠ m := Nat.ne_of_lt (List.mem_range.mp hsm)
          simp [hne]
        rw [List.map_congr_left hlt]
        simp only [↓reduceIte, ← List.append_assoc]
        exact List.perm_append_singleton k _
      · have hlt : s₀ < m := by omega
        have hne : m ≠ s₀ := heq
        simp only [hne, ↓reduceIte]
        have ih := flatten_map_append_at k s₀ m f hlt
        exact ih.append_right (f m)

/-- When every logical index `k < n` maps to a physical slot `slotOf slotMap k < m`,
the buckets `{ bucketOf slotMap n s | s < m }` partition `List.range n`. -/
theorem flatten_bucketOf_perm (slotMap : Array Nat) (m : Nat) :
    ∀ (n : Nat), (∀ k < n, slotOf slotMap k < m) →
      ((List.range m).map fun s => bucketOf slotMap n s).flatten.Perm (List.range n)
  | 0, _ => by
      have hnil : ((List.range m).map fun s => bucketOf slotMap 0 s).flatten = [] := by
        apply List.flatten_eq_nil_iff.mpr
        intro xs hxs
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hxs
        rfl
      rw [hnil]
      exact List.Perm.refl _
  | n + 1, hbound => by
      have hstep : ∀ s, bucketOf slotMap (n + 1) s =
          if s = slotOf slotMap n then bucketOf slotMap n s ++ [n] else bucketOf slotMap n s := by
        intro s
        unfold bucketOf
        rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
        by_cases heq : s = slotOf slotMap n
        · simp [heq]
        · have hne : (slotOf slotMap n == s) = false := by
            simp [Ne.symm heq]
          simp [heq, hne]
      have hmap : ((List.range m).map fun s => bucketOf slotMap (n + 1) s) =
          ((List.range m).map fun s =>
            if s = slotOf slotMap n then bucketOf slotMap n s ++ [n] else bucketOf slotMap n s) :=
        List.map_congr_left fun s _ => hstep s
      rw [hmap]
      have h1 := flatten_map_append_at n (slotOf slotMap n) m (bucketOf slotMap n)
        (hbound n (Nat.lt_succ_self n))
      have h2 := flatten_bucketOf_perm slotMap m n (fun k hk => hbound k (Nat.lt_succ_of_lt hk))
      have h3 : (n :: List.range n).Perm (List.range (n + 1)) := by
        rw [List.range_succ]
        exact (List.perm_append_singleton n (List.range n)).symm
      exact (h1.trans (h2.cons n)).trans h3

private theorem sum_map_eq_single_of_nodup {α : Type} {f : α → K} :
    ∀ {xs : List α}, xs.Nodup → ∀ {k : α}, k ∈ xs → (∀ x ∈ xs, x ≠ k → f x = 0) →
      (xs.map f).sum = f k
  | [], _, _, hk, _ => by cases hk
  | x :: xs, hnd, k, hk, hzero => by
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hk with rfl | hmem
      · have htail : (xs.map f).sum = 0 := by
          apply List.sum_eq_zero
          intro v hv
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
          exact hzero y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
        rw [htail, add_zero]
      · have hx : f x = 0 := hzero x List.mem_cons_self (fun heq => hnd.1 (heq ▸ hmem))
        rw [hx, zero_add]
        exact sum_map_eq_single_of_nodup hnd.2 hmem (fun y hy hne =>
          hzero y (List.mem_cons_of_mem _ hy) hne)

/-- Evaluate a `Grouping.Lookup F` into a `(multiplicity, denominator)` LogUp pair in `K`. -/
def evalGroupingLookup (embed : F →+* K) (β γ : K) (a : Nat → F) (l : Grouping.Lookup F) : K × K :=
  (embed (l.enable.denote a), fingerprint β γ (l.args.map fun p => embed (p.denote a)))

private theorem word_list_map_getD (embed : F →+* K) (a : Nat → F)
    (ps : List (Optimized.Polynomial F)) (j : Nat) :
    (ps.map fun p => embed (p.denote a))[j]?.getD 0 = embed ((word ps j).denote a) := by
  by_cases hj : j < ps.length
  · simp [word, hj]
  · have hge : ps.length ≤ j := Nat.not_lt.mp hj
    simp [word, List.getElem?_eq_none hge, Scalar.Circuit.ArithExpr.denote, map_zero]

/-- **Per-row LogUp equivalence for `C7a` slot permutation & `C2` raw-packet compaction:**
`Grouping.SamePackets` preserves both the receive RLC fingerprint and the exact
per-row send LogUp rational sum `∑ m_i / (β + rlc(γ, args_i))` over any field
extension `embed : F →+* K`. -/
theorem samePackets_logup_sum_eq (embed : F →+* K) (β γ : K)
    {g : Grouping.Layout F} {slotMap : Array Nat} {a b : Nat → F}
    {provided : List (Optimized.Polynomial F)} {required : List (Grouping.Lookup F)}
    (hsame : Grouping.SamePackets g slotMap a provided required b) :
    fingerprint β γ (g.receive.map fun p => embed (p.denote a)) =
      fingerprint β γ (provided.map fun p => embed (p.denote b)) ∧
    ungroupedLogUpSum (g.sends.map (evalGroupingLookup embed β γ a)) =
      ungroupedLogUpSum (required.map (evalGroupingLookup embed β γ b)) := by
  obtain ⟨hrecv, hbound, hslots⟩ := hsame
  constructor
  · apply fingerprint_eq_of_word_eq
    intro j
    rw [word_list_map_getD, word_list_map_getD, hrecv j]
  · set slotTerm : Nat → K := fun s =>
      let t := evalGroupingLookup embed β γ a (g.slot s)
      t.1 * t.2⁻¹
    set reqTerm : Nat → K := fun k =>
      let t := evalGroupingLookup embed β γ b (Grouping.lookupAt required k)
      t.1 * t.2⁻¹
    have hlhs : ungroupedLogUpSum (g.sends.map (evalGroupingLookup embed β γ a)) =
        ((List.range g.sends.length).map slotTerm).sum := by
      unfold ungroupedLogUpSum
      rw [List.map_map]
      congr 1
      apply List.ext_getElem
      · simp
      · intro s hs1 hs2
        have hs : s < g.sends.length := by simpa using hs1
        simp [slotTerm, Grouping.Layout.slot, hs]
    have hrhs_range : ungroupedLogUpSum (required.map (evalGroupingLookup embed β γ b)) =
        ((List.range required.length).map reqTerm).sum := by
      unfold ungroupedLogUpSum
      rw [List.map_map]
      congr 1
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        have hk : k < required.length := by simpa using hk1
        simp [reqTerm, Grouping.lookupAt, hk]
    have hperm := flatten_bucketOf_perm slotMap g.sends.length required.length hbound
    have hrhs_part : ((List.range required.length).map reqTerm).sum =
        ((List.range g.sends.length).map fun s =>
          ((bucketOf slotMap required.length s).map reqTerm).sum).sum := by
      rw [← (hperm.map reqTerm).sum_eq, List.map_flatten, List.sum_flatten, List.map_map,
        List.map_map]
      rfl
    rw [hlhs, hrhs_range, hrhs_part]
    congr 1
    apply List.map_congr_left
    intro s _
    have hslot := hslots s
    dsimp only at hslot
    have hnd : (bucketOf slotMap required.length s).Nodup :=
      List.Nodup.filter _ List.nodup_range
    generalize hB : bucketOf slotMap required.length s = B at hslot hnd ⊢
    cases B with
    | nil =>
        simp [slotTerm, evalGroupingLookup, hslot.1, map_zero]
    | cons k1 rest =>
        cases rest with
        | nil =>
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
              slotTerm, reqTerm, evalGroupingLookup]
            have hfp : fingerprint β γ ((g.slot s).args.map fun p => embed (p.denote a)) =
                fingerprint β γ ((Grouping.lookupAt required k1).args.map fun p => embed (p.denote b)) := by
              apply fingerprint_eq_of_word_eq
              intro j
              rw [word_list_map_getD, word_list_map_getD, hslot.2 j]
            rw [hslot.1, hfp]
        | cons k2 tail =>
            set B' := k1 :: k2 :: tail
            rcases hslot with ⟨hs0, _, hall0⟩ | ⟨k, hkmem, hk1, hrest0, hs1, hargs⟩
            · have hr0 : (B'.map reqTerm).sum = 0 := by
                apply List.sum_eq_zero
                intro v hv
                obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
                simp [reqTerm, evalGroupingLookup, hall0 j hj, map_zero]
              simp [slotTerm, evalGroupingLookup, hs0, map_zero, hr0]
            · have hrk : (B'.map reqTerm).sum = reqTerm k := by
                apply sum_map_eq_single_of_nodup hnd hkmem
                intro j hj hne
                simp [reqTerm, evalGroupingLookup, hrest0 j hj hne, map_zero]
              rw [hrk]
              simp only [slotTerm, reqTerm, evalGroupingLookup, hs1, hk1]
              have hfp : fingerprint β γ ((g.slot s).args.map fun p => embed (p.denote a)) =
                  fingerprint β γ ((Grouping.lookupAt required k).args.map fun p => embed (p.denote b)) := by
                apply fingerprint_eq_of_word_eq
                intro j
                rw [word_list_map_getD, word_list_map_getD, hargs j]
              rw [hfp]

/-- **Certified active-row LogUp equivalence for grouped circuits (`C7a` + `C2`):**
any valid active row of a certified `Grouping.Checked` layout produces the exact
same receive fingerprint and send LogUp rational sum as the selected member's
original ungrouped chip. -/
theorem checked_packet_logup_sum_eq {sources : List (Circuit.Chip F)}
    {id : String → Except String Nat} (checked : Grouping.Checked sources id)
    (embed : F →+* K) (β γ : K) {rom : WireROM F}
    (m : Grouping.Member F) (hm : m ∈ checked.layout.members) (a : Nat → F)
    (valid : checked.layout.ValidRow rom a) (active : a m.selector = 1) :
    ∃ provided required, Grouping.messages id m.origin = .ok (provided, required) ∧
      fingerprint β γ (checked.layout.receive.map fun p => embed (p.denote a)) =
        fingerprint β γ (provided.map fun p => embed (p.denote (fun v => a (m.columns[v]?.getD 0)))) ∧
      ungroupedLogUpSum (checked.layout.sends.map (evalGroupingLookup embed β γ a)) =
        ungroupedLogUpSum (required.map (evalGroupingLookup embed β γ (fun v => a (m.columns[v]?.getD 0)))) := by
  obtain ⟨provided, required, hmsg, hsame⟩ := checked.packet_sound m hm a valid active
  exact ⟨provided, required, hmsg, samePackets_logup_sum_eq embed β γ hsame⟩

/-- **Certified padding-row LogUp silence for grouped circuits:**
any padding row (`activation = 0`) of a certified `Grouping.Checked` layout
contributes `0` to the send LogUp rational sum. -/
theorem checked_padding_logup_sum_zero {sources : List (Circuit.Chip F)}
    {id : String → Except String Nat} (checked : Grouping.Checked sources id)
    (embed : F →+* K) (β γ : K) (a : Nat → F)
    (valid : Circuit.Satisfies checked.layout.constraints a)
    (off : checked.layout.activation.denote a = 0) :
    ungroupedLogUpSum (checked.layout.sends.map (evalGroupingLookup embed β γ a)) = 0 := by
  have hsame := checked.padding_sound a valid off
  have h := (samePackets_logup_sum_eq embed β γ hsame).2
  simpa [ungroupedLogUpSum] using h

end GroupingPacketLogUp

/-! ## 5c. `K`-Lane Vectorized ROM Soundness (`C6`) -/

section VectorizedRomSoundness

variable {F E : Type} [Field F] [DecidableEq F] [Field E]

/-- Row-0 base address of a `K > 1` vectorized `<ROM:w>` row. -/
def vecBaseAddr (row : Nat → F) : F := row 0

/-- Lane `l` multiplicity in a `K > 1` vectorized `<ROM:w>` row. -/
def vecCount (w : Nat) (row : Nat → F) (lane : Nat) : F :=
  row (vecCountCol w lane)

/-- Lane `l` active flag in a `K > 1` vectorized `<ROM:w>` row. -/
def vecActive (w : Nat) (row : Nat → F) (lane : Nat) : F :=
  row (vecActiveCol w lane)

/-- Lane `l` payload words in a `K > 1` vectorized `<ROM:w>` row. -/
def vecPayload (w : Nat) (row : Nat → F) (lane : Nat) : List F :=
  (List.range w).map fun k => row (vecPayloadCol w lane k)

/-- Number of active lanes in a `K > 1` vectorized `<ROM:w>` row. -/
def vecRowActiveCount (w K : Nat) (row : Nat → F) : Nat :=
  ((List.range K).filter fun l => decide (vecActive w row l = 1)).length

/-- Extracted `(address, payload)` entries from the active prefix of a `K > 1` row. -/
def vecRowEntries (w K : Nat) (row : Nat → F) : List (F × List F) :=
  (List.range (vecRowActiveCount w K row)).map fun (l : Nat) =>
    (vecBaseAddr row + (l : F), vecPayload w row l)

/-- Extracted `(address, payload)` entries across all rows of a `K > 1` trace. -/
def vecTraceEntries (w K : Nat) (rows : List (Nat → F)) : List (F × List F) :=
  rows.flatMap (vecRowEntries w K)

/-- Per-row `MEMSEG` push-minus-pull multiplicity delta at address `x` emitted by
a segmented `K > 1` vectorized `<ROM:w>` circuit. -/
def vecRowMemsegDelta (w K : Nat) (row : Nat → F) (x : F) : F :=
  let sumAct : F := ((List.range K).map fun l => vecActive w row l).sum
  vecActive w row 0 *
    ((if vecBaseAddr row = x then (1 : F) else 0) -
     (if vecBaseAddr row + sumAct = x then (1 : F) else 0))

/-- Intra-row validity predicate for a `K > 1` vectorized `<ROM:w>` row. -/
def KLaneRomRowValid (w K : Nat) (cur : Nat → F) : Prop :=
  (∀ l < K, vecActive w cur l * (vecActive w cur l - 1) = 0) ∧
  (∀ l < K, vecCount w cur l * (1 - vecActive w cur l) = 0) ∧
  (∀ l, l + 1 < K → vecActive w cur (l + 1) * (1 - vecActive w cur l) = 0)

/-- Full AIR trace validity predicate for `lowerKLaneRomCircuit w K segmented`:
every row `t < rows.length` vanishes on every lowered AIR constraint. -/
def KLaneRomTraceValid (w K : Nat) (segmented : Bool) (rows : List (Nat → F)) : Prop :=
  ∀ (t : Nat) (ht : t < rows.length),
    let cur := rows[t]
    let nxt := if h : t + 1 < rows.length then rows[t + 1] else fun _ => 0
    let isFirst : F := if t = 0 then 1 else 0
    let isLast : F := if t + 1 = rows.length then 1 else 0
    let isTrans : F := if t + 1 < rows.length then 1 else 0
    ∀ c ∈ (lowerKLaneRomCircuit w K segmented).constraints,
      c.eval cur nxt (fun _ => 0) isFirst isLast isTrans = 0

private theorem eval_sumActive (w : Nat) (cur nxt prep : Nat → F)
    (isFirst isLast isTrans : F) :
    ∀ (k : Nat),
      ((List.range k).foldl
        (fun acc i => AirExpr.add acc (.main (vecActiveCol w (i + 1))))
        (.main (vecActiveCol w 0))).eval cur nxt prep isFirst isLast isTrans =
      ((List.range (k + 1)).map fun l => vecActive w cur l).sum
  | 0 => by simp [AirExpr.eval, vecActive]
  | k + 1 => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        AirExpr.eval, eval_sumActive w cur nxt prep isFirst isLast isTrans k]
      conv_rhs => rw [List.range_succ]
      simp [AirExpr.eval, vecActive]

private theorem filter_range_downward {P : Nat → Bool} :
    ∀ (K : Nat), (∀ i, i + 1 < K → P (i + 1) = true → P i = true) →
      ∃ m ≤ K, (List.range K).filter P = List.range m
  | 0, _ => ⟨0, le_rfl, rfl⟩
  | K + 1, hdown => by
      obtain ⟨m, hm, heq⟩ := filter_range_downward K (fun i hi hp => hdown i (by omega) hp)
      rw [List.range_succ, List.filter_append, heq, List.filter_cons, List.filter_nil]
      cases hK : P K with
      | false =>
          exact ⟨m, by omega, by simp⟩
      | true =>
          have hall : ∀ i < K, P i = true := by
            intro i hi
            have hstep : ∀ d j, j + d = K → P j = true := by
              intro d
              induction d with
              | zero =>
                  intro j hj
                  have : j = K := by omega
                  subst this
                  exact hK
              | succ d' ihd =>
                  intro j hj
                  have hnext : P (j + 1) = true := ihd (j + 1) (by omega)
                  exact hdown j (by omega) hnext
            exact hstep (K - i) i (by omega)
          have hfull : (List.range K).filter P = List.range K := by
            rw [List.filter_eq_self]
            intro x hx
            exact hall x (List.mem_range.mp hx)
          have hmK : m = K := by
            have hlen := congrArg List.length (heq.symm.trans hfull)
            simpa using hlen
          rw [hmK]
          exact ⟨K + 1, le_rfl, by simp [List.range_succ]⟩

private theorem sum_range_prefix_indicator (f : Nat → F) (K m : Nat) (hm : m ≤ K)
    (hon : ∀ l < m, f l = 1) (hoff : ∀ l, m ≤ l → l < K → f l = 0) :
    ((List.range K).map f).sum = (m : F) := by
  have hsplit : List.range K = List.range m ++ (List.range (K - m)).map (m + ·) := by
    have h := List.range_add (n := m) (m := K - m)
    rw [Nat.add_sub_of_le hm] at h
    exact h
  rw [hsplit, List.map_append, List.sum_append, List.map_map]
  have h1 : ((List.range m).map f).sum = (m : F) := by
    have hcongr : (List.range m).map f = (List.range m).map (fun _ => (1 : F)) :=
      List.map_congr_left fun l hl => hon l (List.mem_range.mp hl)
    rw [hcongr]
    simp
  have h2 : ((List.range (K - m)).map (f ∘ (m + ·))).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    have hjlt : j < K - m := List.mem_range.mp hj
    exact hoff (m + j) (Nat.le_add_right m j) (by omega)
  rw [h1, h2, add_zero]

/-- **Intra-row prefix structure (`C6`):** any row satisfying `KLaneRomRowValid w K cur`
(`1 < K`) has active lanes forming an exact contiguous prefix `0 .. m` (`m = vecRowActiveCount`),
inactive lanes forced to `count = 0`, `∑ active = m`, `active_0 = (m ≠ 0)`, and
`m = K ↔ active_{K-1} = 1`. -/
theorem vecRow_prefix_of_valid {w K : Nat} (hK : 1 < K) {cur : Nat → F}
    (hrow : KLaneRomRowValid w K cur) :
    let m := vecRowActiveCount w K cur
    m ≤ K ∧
    (∀ l < K, vecActive w cur l = 0 ∨ vecActive w cur l = 1) ∧
    (∀ l < m, vecActive w cur l = 1) ∧
    (∀ l, m ≤ l → l < K → vecActive w cur l = 0 ∧ vecCount w cur l = 0) ∧
    ((List.range K).map fun l => vecActive w cur l).sum = (m : F) ∧
    (vecActive w cur 0 = if m = 0 then 0 else 1) ∧
    (m = K ↔ vecActive w cur (K - 1) = 1) := by
  obtain ⟨hbool, hcnt, hmono⟩ := hrow
  have h01 : ∀ l < K, vecActive w cur l = 0 ∨ vecActive w cur l = 1 := by
    intro l hl
    rcases mul_eq_zero.mp (hbool l hl) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hdown : ∀ l, l + 1 < K →
      decide (vecActive w cur (l + 1) = 1) = true → decide (vecActive w cur l = 1) = true := by
    intro l hl hnext
    have hnext1 : vecActive w cur (l + 1) = 1 := of_decide_eq_true hnext
    have hprod := hmono l hl
    rw [hnext1, one_mul] at hprod
    exact decide_eq_true (sub_eq_zero.mp hprod).symm
  obtain ⟨m, hmK, hfilt⟩ :=
    filter_range_downward (P := fun l => decide (vecActive w cur l = 1)) K hdown
  have hm_eq : vecRowActiveCount w K cur = m := by
    unfold vecRowActiveCount
    rw [hfilt, List.length_range]
  have hon : ∀ l < m, vecActive w cur l = 1 := by
    intro l hl
    have hmem : l ∈ (List.range K).filter (fun i => decide (vecActive w cur i = 1)) := by
      rw [hfilt]
      exact List.mem_range.mpr hl
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hoff : ∀ l, m ≤ l → l < K → vecActive w cur l = 0 ∧ vecCount w cur l = 0 := by
    intro l hml hlK
    have hne1 : vecActive w cur l ≠ 1 := by
      intro h1
      have hmem : l ∈ (List.range K).filter (fun i => decide (vecActive w cur i = 1)) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hlK, decide_eq_true h1⟩
      rw [hfilt, List.mem_range] at hmem
      omega
    have h0 : vecActive w cur l = 0 := (h01 l hlK).resolve_right hne1
    have hc : vecCount w cur l = 0 := by
      have hc' := hcnt l hlK
      rw [h0, sub_zero, mul_one] at hc'
      exact hc'
    exact ⟨h0, hc⟩
  have hsum : ((List.range K).map fun l => vecActive w cur l).sum = (m : F) :=
    sum_range_prefix_indicator (vecActive w cur) K m hmK hon (fun l hml hlK => (hoff l hml hlK).1)
  have hact0 : vecActive w cur 0 = if m = 0 then 0 else 1 := by
    by_cases hm0 : m = 0
    · simp only [hm0, ↓reduceIte]
      exact (hoff 0 (by omega) (by omega)).1
    · simp only [hm0, ↓reduceIte]
      exact hon 0 (by omega)
  have hfull : m = K ↔ vecActive w cur (K - 1) = 1 := by
    constructor
    · intro hEq
      exact hon (K - 1) (by omega)
    · intro h1
      by_contra hne
      have h0 := (hoff (K - 1) (by omega) (by omega)).1
      rw [h1] at h0
      exact one_ne_zero h0
  rw [hm_eq]
  exact ⟨hmK, h01, hon, hoff, hsum, hact0, hfull⟩

private theorem filter_range_addr_telescope (base x : F) :
    ∀ (m : Nat),
      ((((List.range m).filter fun (l : Nat) => decide (base + (l : F) = x)).length : F) -
       (((List.range m).filter fun (l : Nat) => decide (base + (l : F) = x - 1)).length : F)) =
      if m = 0 then 0
      else (if base = x then (1 : F) else 0) - (if base + (m : F) = x then (1 : F) else 0)
  | 0 => by simp
  | m + 1 => by
      have ih := filter_range_addr_telescope base x m
      rw [List.range_succ, List.filter_append, List.filter_append,
        List.length_append, List.length_append, Nat.cast_add, Nat.cast_add]
      have hstep1 : (([m].filter fun (l : Nat) => decide (base + (l : F) = x)).length : F) =
          if base + (m : F) = x then 1 else 0 := by
        by_cases h : base + (m : F) = x <;> simp [h]
      have hstep2 : (([m].filter fun (l : Nat) => decide (base + (l : F) = x - 1)).length : F) =
          if base + ((m + 1 : Nat) : F) = x then 1 else 0 := by
        have heq : (base + (m : F) = x - 1) ↔ (base + ((m + 1 : Nat) : F) = x) := by
          constructor <;> intro h
          · push_cast; linear_combination h
          · push_cast at h; linear_combination h
        by_cases h : base + ((m + 1 : Nat) : F) = x
        · have h' : base + (m : F) = x - 1 := heq.mpr h
          rw [if_pos h]
          simp [h']
        · have h' : ¬(base + (m : F) = x - 1) := fun hc => h (heq.mp hc)
          rw [if_neg h]
          simp [h']
      rw [hstep1, hstep2]
      cases m with
      | zero =>
          simp only [List.range_zero, List.filter_nil, List.length_nil, Nat.cast_zero,
            zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
      | succ m' =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at ih ⊢
          linear_combination ih

/-- **Row-level `MEMSEG` equivalence with scalar ROM (`C6`):**
for any valid `K`-lane row (`1 < K`), its two `MEMSEG` lookups (`push base`,
`pull base + sum_active`) have the EXACT same per-address multiplicity delta as
the scalar `K = 1` entries extracted from its active prefix `vecRowEntries w K cur`. -/
theorem vecRow_memseg_delta_eq_scalar {w K : Nat} (hK : 1 < K) {cur : Nat → F}
    (hrow : KLaneRomRowValid w K cur) (x : F) :
    vecRowMemsegDelta w K cur x =
      (((vecRowEntries w K cur).filter fun e => decide (e.1 = x)).length : F) -
      (((vecRowEntries w K cur).filter fun e => decide (e.1 = x - 1)).length : F) := by
  obtain ⟨_, _, _, _, hsum, hact0, _⟩ := vecRow_prefix_of_valid hK hrow
  unfold vecRowMemsegDelta vecRowEntries
  rw [hsum, hact0]
  have hfilt : ∀ y : F,
      (((List.range (vecRowActiveCount w K cur)).map fun (l : Nat) =>
          (vecBaseAddr cur + (l : F), vecPayload w cur l)).filter
        fun e => decide (e.1 = y)).length =
      ((List.range (vecRowActiveCount w K cur)).filter
        fun (l : Nat) => decide (vecBaseAddr cur + (l : F) = y)).length := by
    intro y
    rw [List.filter_map, List.length_map]
    rfl
  rw [hfilt x, hfilt (x - 1), filter_range_addr_telescope (vecBaseAddr cur) x]
  by_cases hm0 : vecRowActiveCount w K cur = 0 <;> simp [hm0]

private theorem sum_map_sub {α : Type} (f g : α → F) :
    ∀ (xs : List α), (xs.map fun a => f a - g a).sum = (xs.map f).sum - (xs.map g).sum
  | [] => by simp
  | a :: xs => by
      simp only [List.map_cons, List.sum_cons, sum_map_sub f g xs]
      ring

private theorem length_filter_flatMap {α β : Type} (f : α → List β) (p : β → Bool) :
    ∀ (xs : List α), ((xs.flatMap f).filter p).length = (xs.map fun a => ((f a).filter p).length).sum
  | [] => rfl
  | a :: xs => by
      simp [List.flatMap_cons, List.filter_append, length_filter_flatMap f p xs]

/-- **Multi-row / multi-shard `MEMSEG` equivalence with scalar ROM (`C6`):**
summing the `K`-lane `MEMSEG` deltas over any list of valid rows (within one shard or
across an entire sharded batch) yields the EXACT scalar `MEMSEG` delta of `vecTraceEntries`,
directly discharging `Ix.Cert.MultiStark.PlanBridge.prepared_eval_of_extracted_trace`'s `hmemseg`. -/
theorem vecTrace_memseg_delta_eq_scalar {w K : Nat} (hK : 1 < K) {rows : List (Nat → F)}
    (hrows : ∀ r ∈ rows, KLaneRomRowValid w K r) (x : F) :
    (rows.map fun r => vecRowMemsegDelta w K r x).sum =
      (((vecTraceEntries w K rows).filter fun e => decide (e.1 = x)).length : F) -
      (((vecTraceEntries w K rows).filter fun e => decide (e.1 = x - 1)).length : F) := by
  have hcongr : rows.map (fun r => vecRowMemsegDelta w K r x) =
      rows.map (fun r =>
        (((vecRowEntries w K r).filter fun e => decide (e.1 = x)).length : F) -
        (((vecRowEntries w K r).filter fun e => decide (e.1 = x - 1)).length : F)) :=
    List.map_congr_left fun r hr => vecRow_memseg_delta_eq_scalar hK (hrows r hr) x
  rw [hcongr, sum_map_sub]
  unfold vecTraceEntries
  rw [length_filter_flatMap, length_filter_flatMap, Nat.cast_list_sum, Nat.cast_list_sum,
    List.map_map, List.map_map]
  rfl

/-- **Row-level `ROM` channel equivalence (`C6`):**
for any valid `K`-lane row (`1 < K`), evaluating all `K` `ROM` pull lookups gives the
exact same LogUp rational sum as pulling only the `m = vecRowActiveCount` active extracted
entries, because inactive lanes have `count_l = 0`. -/
theorem vecRow_rom_logup_sum_eq_extracted (embed : F →+* E) (β γ : E)
    {w K : Nat} (hK : 1 < K) {cur nxt prep : Nat → F} {isFirst isLast isTrans : F}
    (hrow : KLaneRomRowValid w K cur) :
    let romLookups : List (AirLookup F) :=
      (List.range K).map fun (lane : Nat) =>
        let laneAddr : AirExpr F :=
          if lane == 0 then .main 0 else .add (.main 0) (.const (lane : F))
        let payloadArgs := (List.range w).map fun k => AirExpr.main (vecPayloadCol w lane k)
        AirLookup.pull (.main (vecCountCol w lane))
          ([.const (romTag : F), .const (w : F), laneAddr] ++ payloadArgs)
    ungroupedLogUpSum (romLookups.map (evalLookup embed β γ cur nxt prep isFirst isLast isTrans)) =
      ungroupedLogUpSum ((List.range (vecRowActiveCount w K cur)).map fun (lane : Nat) =>
        (-embed (vecCount w cur lane),
         fingerprint β γ
           ([embed (romTag : F), embed (w : F), embed (vecBaseAddr cur + (lane : F))] ++
            (vecPayload w cur lane).map embed))) := by
  obtain ⟨hmK, _, _, hoff, _, _, _⟩ := vecRow_prefix_of_valid hK hrow
  set m := vecRowActiveCount w K cur
  dsimp only
  have hsplit : List.range K = List.range m ++ (List.range (K - m)).map (m + ·) := by
    have h := List.range_add (n := m) (m := K - m)
    rw [Nat.add_sub_of_le hmK] at h
    exact h
  rw [hsplit, List.map_append, List.map_append, ungroupedLogUpSum_append]
  have hzeroTail :
      ungroupedLogUpSum
        ((((List.range (K - m)).map (m + ·)).map fun (lane : Nat) =>
          let laneAddr : AirExpr F :=
            if lane == 0 then .main 0 else .add (.main 0) (.const (lane : F))
          let payloadArgs := (List.range w).map fun k => AirExpr.main (vecPayloadCol w lane k)
          AirLookup.pull (.main (vecCountCol w lane))
            ([.const (romTag : F), .const (w : F), laneAddr] ++ payloadArgs)).map
          (evalLookup embed β γ cur nxt prep isFirst isLast isTrans)) = 0 := by
    unfold ungroupedLogUpSum
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane, hlane, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hlane
    have hjlt : j < K - m := List.mem_range.mp hj
    have hc0 : vecCount w cur (m + j) = 0 := (hoff (m + j) (Nat.le_add_right m j) (by omega)).2
    simp [evalLookup, AirLookup.pull, AirExpr.eval, show cur (vecCountCol w (m + j)) = 0 from hc0,
      map_zero]
  rw [hzeroTail, add_zero]
  unfold ungroupedLogUpSum
  congr 1
  rw [List.map_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro lane _
  have haddr :
      (if (lane == 0) = true then AirExpr.main (F := F) 0
       else AirExpr.add (.main 0) (.const (lane : F))).eval cur nxt prep isFirst isLast isTrans =
      vecBaseAddr cur + (lane : F) := by
    cases lane with
    | zero => simp [AirExpr.eval, vecBaseAddr]
    | succ l => simp [AirExpr.eval, vecBaseAddr]
  simp only [Function.comp_apply, evalLookup, AirLookup.pull, AirExpr.eval, map_neg,
    List.map_append, List.map_cons, List.map_nil, List.map_map, haddr, vecCount, vecPayload]
  rfl

/-- Extract per-row and transition equations from `KLaneRomTraceValid`. -/
theorem KLaneRomTraceValid.extract {w K : Nat} {segmented : Bool} {rows : List (Nat → F)}
    (hK : 1 < K) (hvalid : KLaneRomTraceValid w K segmented rows) :
    (∀ (t : Nat) (ht : t < rows.length), KLaneRomRowValid w K rows[t]) ∧
    (∀ (t : Nat) (ht1 : t + 1 < rows.length),
      vecActive w rows[t + 1] 0 = 1 →
      vecActive w rows[t] (K - 1) = 1 ∧
      vecBaseAddr rows[t + 1] = vecBaseAddr rows[t] + (K : F)) ∧
    (segmented = false → ∀ (h0 : 0 < rows.length), vecBaseAddr rows[0] = 0) := by
  have hnotle : ¬(K ≤ 1) := by omega
  set baseCs : List (AirExpr F) :=
    ((List.range K).flatMap fun lane =>
      [.mul (.main (vecActiveCol w lane)) (.sub (.main (vecActiveCol w lane)) (.const (1 : F))),
       .mul (.main (vecCountCol w lane)) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))]) ++
    ((List.range (K - 1)).map fun lane =>
      .mul (.main (vecActiveCol w (lane + 1))) (.sub (.const (1 : F)) (.main (vecActiveCol w lane)))) ++
    [.mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
          (.sub (.main (vecActiveCol w (K - 1))) (.const (1 : F))),
     .mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
          (.sub (.sub (.mainNext 0) (.main 0)) (.const (K : F)))]
  have hcs_base : ∀ (t : Nat) (ht : t < rows.length) (c : AirExpr F),
      c ∈ baseCs →
      c.eval rows[t] (if h : t + 1 < rows.length then rows[t + 1] else fun _ => 0)
        (fun _ => 0) (if t = 0 then 1 else 0) (if t + 1 = rows.length then 1 else 0)
        (if t + 1 < rows.length then 1 else 0) = 0 := by
    intro t ht c hc
    apply hvalid t ht c
    unfold lowerKLaneRomCircuit
    simp only [hnotle, ↓reduceIte]
    cases segmented
    · exact List.mem_append_left _ hc
    · exact hc
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · intro l hl
      have hmem : AirExpr.mul (.main (vecActiveCol w l))
          (.sub (.main (vecActiveCol w l)) (.const (1 : F))) ∈ baseCs := by
        apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, by simp⟩
      simpa [AirExpr.eval, vecActive] using hcs_base t ht _ hmem
    · intro l hl
      have hmem : AirExpr.mul (.main (vecCountCol w l))
          (.sub (.const (1 : F)) (.main (vecActiveCol w l))) ∈ baseCs := by
        apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, by simp⟩
      simpa [AirExpr.eval, vecCount, vecActive] using hcs_base t ht _ hmem
    · intro l hl
      have hmem : AirExpr.mul (.main (vecActiveCol w (l + 1)))
          (.sub (.const (1 : F)) (.main (vecActiveCol w l))) ∈ baseCs := by
        apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨l, List.mem_range.mpr (by omega), rfl⟩
      simpa [AirExpr.eval, vecActive] using hcs_base t ht _ hmem
  · intro t ht1 hact1
    have ht : t < rows.length := by omega
    have hfull_c := hcs_base t ht
      (.mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
            (.sub (.main (vecActiveCol w (K - 1))) (.const (1 : F))))
      (List.mem_append_right _ (by simp))
    have haddr_c := hcs_base t ht
      (.mul (.mul .isTransition (.mainNext (vecActiveCol w 0)))
            (.sub (.sub (.mainNext 0) (.main 0)) (.const (K : F))))
      (List.mem_append_right _ (by simp))
    simp only [AirExpr.eval, ht1, ↓reduceDIte, ↓reduceIte, one_mul] at hfull_c haddr_c
    have hact1' : rows[t + 1] (vecActiveCol w 0) = 1 := hact1
    rw [hact1', one_mul] at hfull_c haddr_c
    exact ⟨sub_eq_zero.mp hfull_c, by unfold vecBaseAddr; linear_combination haddr_c⟩
  · intro hseg h0
    subst hseg
    have hc : AirExpr.mul .isFirstRow (.main (F := F) 0) ∈
        (lowerKLaneRomCircuit w K false).constraints := by
      unfold lowerKLaneRomCircuit
      simp [hnotle]
    have hev := hvalid 0 h0 _ hc
    simpa [AirExpr.eval, vecBaseAddr] using hev

/-- **Inter-row contiguity & consecutive address invariant (`C6`):**
in any valid `K`-lane trace (`1 < K`), active rows form a contiguous prefix `0 .. activeRows`,
all active rows except possibly the last have all `K` lanes full, `baseAddr t = baseAddr 0 + K*t`,
every extracted entry `idx` sits at consecutive address `baseAddr 0 + idx`, and when
`segmented = false` the starting address is `0`. -/
theorem vectorizedRom_rows_contiguous {w K : Nat} {segmented : Bool} {rows : List (Nat → F)}
    (hK : 1 < K) (hvalid : KLaneRomTraceValid w K segmented rows) :
    ∃ activeRows : Nat, ∃ ha : activeRows ≤ rows.length,
      (∀ (t : Nat) (ht : t < activeRows),
        vecActive w (rows[t]'(by omega)) 0 = 1 ∧
        vecBaseAddr (rows[t]'(by omega)) = vecBaseAddr (rows[0]'(by omega)) + ((K * t : Nat) : F)) ∧
      (∀ (t : Nat) (ht : t + 1 < activeRows),
        vecRowActiveCount w K (rows[t]'(by omega)) = K) ∧
      (∀ (t : Nat) (_ : activeRows ≤ t) (ht2 : t < rows.length),
        vecActive w rows[t] 0 = 0 ∧ vecRowActiveCount w K rows[t] = 0) ∧
      (segmented = false → 0 < activeRows →
        ∀ (h0 : 0 < rows.length), vecBaseAddr rows[0] = 0) := by
  obtain ⟨hrows, htrans, hfirst⟩ := hvalid.extract hK
  have hrowDown : ∀ (t : Nat) (ht1 : t + 1 < rows.length),
      decide (vecActive w (rows[t + 1]'ht1) 0 = 1) = true →
      decide (vecActive w (rows[t]'(by omega)) 0 = 1) = true := by
    intro t ht1 hnext
    have hnext1 : vecActive w rows[t + 1] 0 = 1 := of_decide_eq_true hnext
    have hlast1 : vecActive w rows[t] (K - 1) = 1 := (htrans t ht1 hnext1).1
    obtain ⟨_, _, _, _, _, hact0, hfull⟩ := vecRow_prefix_of_valid hK (hrows t (by omega))
    have hmK : vecRowActiveCount w K rows[t] = K := hfull.mpr hlast1
    have h0 : vecActive w rows[t] 0 = 1 := by
      rw [hact0, hmK]
      have : K ≠ 0 := by omega
      simp [this]
    exact decide_eq_true h0
  obtain ⟨activeRows, haLe, hfilt⟩ :=
    filter_range_downward (P := fun t => if h : t < rows.length then decide (vecActive w rows[t] 0 = 1) else false)
      rows.length (by
        intro t ht1 hp
        simp only [ht1, show t < rows.length by omega, ↓reduceDIte] at hp ⊢
        exact hrowDown t ht1 hp)
  have hactOn : ∀ (t : Nat) (ht : t < activeRows), vecActive w (rows[t]'(by omega)) 0 = 1 := by
    intro t ht
    have hmem : t ∈ (List.range rows.length).filter
        (fun i => if h : i < rows.length then decide (vecActive w rows[i] 0 = 1) else false) := by
      rw [hfilt]; exact List.mem_range.mpr ht
    have hp := (List.mem_filter.mp hmem).2
    have ht' : t < rows.length := by omega
    simp only [ht', ↓reduceDIte] at hp
    exact of_decide_eq_true hp
  have hactOff : ∀ (t : Nat) (_ : activeRows ≤ t) (ht : t < rows.length),
      vecActive w rows[t] 0 = 0 ∧ vecRowActiveCount w K rows[t] = 0 := by
    intro t hge ht
    have hne1 : vecActive w rows[t] 0 ≠ 1 := by
      intro h1
      have hmem : t ∈ (List.range rows.length).filter
          (fun i => if h : i < rows.length then decide (vecActive w rows[i] 0 = 1) else false) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr ht, by simp [ht, h1]⟩
      rw [hfilt, List.mem_range] at hmem
      omega
    obtain ⟨_, h01, _, _, _, hact0, _⟩ := vecRow_prefix_of_valid hK (hrows t ht)
    have h0 : vecActive w rows[t] 0 = 0 := (h01 0 (by omega)).resolve_right hne1
    have hm0 : vecRowActiveCount w K rows[t] = 0 := by
      by_contra hne0
      rw [hact0, if_neg hne0] at h0
      exact one_ne_zero h0
    exact ⟨h0, hm0⟩
  have hfullPrev : ∀ (t : Nat) (ht : t + 1 < activeRows),
      vecRowActiveCount w K (rows[t]'(by omega)) = K := by
    intro t ht
    have hnext1 := hactOn (t + 1) ht
    have hlast1 := (htrans t (by omega) hnext1).1
    obtain ⟨_, _, _, _, _, _, hfull⟩ := vecRow_prefix_of_valid hK (hrows t (by omega))
    exact hfull.mpr hlast1
  have hbase : ∀ (t : Nat) (ht : t < activeRows),
      vecBaseAddr (rows[t]'(by omega)) = vecBaseAddr (rows[0]'(by omega)) + ((K * t : Nat) : F) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro ht
        have hnext1 := hactOn (t + 1) ht
        have hstep := (htrans t (by omega) hnext1).2
        rw [hstep, ih (by omega)]
        push_cast
        ring
  refine ⟨activeRows, haLe, fun t ht => ⟨hactOn t ht, hbase t ht⟩, hfullPrev, hactOff, ?_⟩
  intro hseg _ h0
  exact hfirst hseg h0

/-- Per-row `MEMSEG` LogUp rational sum (the last two lookups of
`lowerKLaneRomCircuit w K true`) over a field extension `embed : F →+* E`. -/
def vecRowMemsegLogUp (embed : F →+* E) (β γ : E) (w K : Nat) (row : Nat → F) : E :=
  let sumAct : F := ((List.range K).map fun l => vecActive w row l).sum
  let active0 : AirExpr F := .main (vecActiveCol w 0)
  let segPush : AirLookup F :=
    AirLookup.push active0 [.const (memsegTag : F), .const (w : F), .main 0]
  let segPull : AirLookup F :=
    AirLookup.pull active0
      [.const (memsegTag : F), .const (w : F),
       .add (.main 0)
         ((List.range (K - 1)).foldl
           (fun acc i => .add acc (.main (vecActiveCol w (i + 1)))) active0)]
  let _ := sumAct
  ungroupedLogUpSum ([segPush, segPull].map (evalLookup embed β γ row (fun _ => 0) (fun _ => 0) 0 0 0))

private theorem vecRowMemsegLogUp_eq (embed : F →+* E) (β γ : E) {w K : Nat} (hK : 1 < K)
    {row : Nat → F} (hrow : KLaneRomRowValid w K row) :
    let m := vecRowActiveCount w K row
    vecRowMemsegLogUp embed β γ w K row =
      if m = 0 then 0
      else (fingerprint β γ [embed (memsegTag : F), embed (w : F), embed (vecBaseAddr row)])⁻¹ -
           (fingerprint β γ [embed (memsegTag : F), embed (w : F),
             embed (vecBaseAddr row + (m : F))])⁻¹ := by
  obtain ⟨_, _, _, _, hsum, hact0, _⟩ := vecRow_prefix_of_valid hK hrow
  have hsumEval :
      ((List.range (K - 1)).foldl
        (fun acc i => AirExpr.add acc (.main (vecActiveCol w (i + 1))))
        (.main (vecActiveCol w 0))).eval row (fun _ => 0) (fun _ => 0) 0 0 0 =
      (vecRowActiveCount w K row : F) := by
    rw [eval_sumActive w row (fun _ => 0) (fun _ => 0) 0 0 0 (K - 1),
      show K - 1 + 1 = K by omega, hsum]
  unfold vecRowMemsegLogUp ungroupedLogUpSum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    evalLookup, AirLookup.push, AirLookup.pull, AirExpr.eval, hsumEval,
    show row (vecActiveCol w 0) = vecActive w row 0 from rfl, hact0]
  by_cases hm : vecRowActiveCount w K row = 0
  · simp [hm, map_zero]
  · simp only [hm, ↓reduceIte, map_one, map_neg, one_mul, neg_mul, sub_eq_add_neg, vecBaseAddr]

/-- **Trace-level `MEMSEG` LogUp telescoping (`C6`):**
over any field extension `embed : F →+* E`, the total `MEMSEG` LogUp rational sum across all
rows of a valid segmented `K`-lane ROM trace (`1 < K`) telescopes identically to `0` when
no entries are active, and to
`1 / fp(MEMSEG, w, baseAddr 0) - 1 / fp(MEMSEG, w, baseAddr 0 + totalEntries)`
otherwise, matching scalar `K = 1` ROM boundary claims exactly! -/
theorem vectorizedRom_telescopes_memseg (embed : F →+* E) (β γ : E)
    {w K : Nat} {rows : List (Nat → F)}
    (hK : 1 < K) (hvalid : KLaneRomTraceValid w K true rows) :
    let totalEntries := (vecTraceEntries w K rows).length
    (rows.map (vecRowMemsegLogUp embed β γ w K)).sum =
      if h : totalEntries = 0 then 0
      else
        (fingerprint β γ
          [embed (memsegTag : F), embed (w : F),
           embed (vecBaseAddr (rows.headD (fun _ => 0)))])⁻¹ -
        (fingerprint β γ
          [embed (memsegTag : F), embed (w : F),
           embed (vecBaseAddr (rows.headD (fun _ => 0)) + (totalEntries : F))])⁻¹ := by
  obtain ⟨hrows, _, _⟩ := hvalid.extract hK
  obtain ⟨activeRows, haLe, hon, hfull, hoff, _⟩ := vectorizedRom_rows_contiguous hK hvalid
  set fp : F → E := fun a =>
    (fingerprint β γ [embed (memsegTag : F), embed (w : F), embed a])⁻¹
  have hlen_entries : (vecTraceEntries w K rows).length =
      (rows.map (vecRowActiveCount w K)).sum := by
    unfold vecTraceEntries
    rw [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro r _
    simp [vecRowEntries]
  have hsum_rows : (rows.map (vecRowMemsegLogUp embed β γ w K)).sum =
      ((List.range activeRows).map fun t =>
        if ht : t < rows.length then vecRowMemsegLogUp embed β γ w K rows[t] else 0).sum := by
    have hsplit : rows = rows.take activeRows ++ rows.drop activeRows := (List.take_append_drop _ _).symm
    have hdrop0 : ((rows.drop activeRows).map (vecRowMemsegLogUp embed β γ w K)).sum = 0 := by
      apply List.sum_eq_zero
      intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hr
      have hidx_len : activeRows + idx < rows.length := by
        simp only [List.length_drop] at hidx; omega
      have hget : (rows.drop activeRows)[idx] = rows[activeRows + idx] := List.getElem_drop
      rw [hget, vecRowMemsegLogUp_eq embed β γ hK (hrows (activeRows + idx) hidx_len)]
      have hm0 := (hoff (activeRows + idx) (Nat.le_add_right _ _) hidx_len).2
      simp [hm0]
    conv_lhs => rw [hsplit]
    rw [List.map_append, List.sum_append, hdrop0, add_zero]
    congr 1
    apply List.ext_getElem
    · simp [Nat.min_eq_left haLe]
    · intro i hi1 hi2
      have hi : i < activeRows := by simpa using hi2
      have hi_len : i < rows.length := by omega
      simp [hi_len]
  have htot_eq : (rows.map (vecRowActiveCount w K)).sum =
      ((List.range activeRows).map fun t =>
        if ht : t < rows.length then vecRowActiveCount w K rows[t] else 0).sum := by
    have hsplit : rows = rows.take activeRows ++ rows.drop activeRows := (List.take_append_drop _ _).symm
    have hdrop0 : ((rows.drop activeRows).map (vecRowActiveCount w K)).sum = 0 := by
      apply List.sum_eq_zero
      intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hr
      have hidx_len : activeRows + idx < rows.length := by
        simp only [List.length_drop] at hidx; omega
      have hget : (rows.drop activeRows)[idx] = rows[activeRows + idx] := List.getElem_drop
      rw [hget]
      exact (hoff (activeRows + idx) (Nat.le_add_right _ _) hidx_len).2
    conv_lhs => rw [hsplit]
    rw [List.map_append, List.sum_append, hdrop0, add_zero]
    congr 1
    apply List.ext_getElem
    · simp [Nat.min_eq_left haLe]
    · intro i hi1 hi2
      have hi : i < activeRows := by simpa using hi2
      have hi_len : i < rows.length := by omega
      simp [hi_len]
  dsimp only
  rw [hlen_entries, htot_eq, hsum_rows]
  cases activeRows with
  | zero => simp
  | succ r =>
      have h0len : 0 < rows.length := by omega
      have hhead : rows.headD (fun _ => 0) = rows[0] := by
        cases rows with
        | nil => simp at h0len
        | cons x xs => rfl
      have hpos : ∀ t (ht : t < r + 1),
          vecRowActiveCount w K rows[t] ≠ 0 := by
        intro t ht hm0
        have hact1 := (hon t ht).1
        obtain ⟨_, _, _, _, _, hact0, _⟩ := vecRow_prefix_of_valid hK (hrows t (by omega))
        rw [hact0, hm0] at hact1
        exact zero_ne_one hact1
      -- Total entries = K * r + vecRowActiveCount w K rows[r]
      have htot_val :
          ((List.range (r + 1)).map fun t =>
            if ht : t < rows.length then vecRowActiveCount w K rows[t] else 0).sum =
          K * r + vecRowActiveCount w K rows[r] := by
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        have hr_len : r < rows.length := by omega
        simp only [hr_len, ↓reduceDIte]
        have hpref :
            ((List.range r).map fun t =>
              if ht : t < rows.length then vecRowActiveCount w K rows[t] else 0) =
            (List.range r).map fun _ => K := by
          apply List.map_congr_left
          intro t ht
          have htlt : t < r := List.mem_range.mp ht
          have htlen : t < rows.length := by omega
          simp only [htlen, ↓reduceDIte]
          exact hfull t (by omega)
        rw [hpref]
        simp [Nat.mul_comm]
      have htot_ne : K * r + vecRowActiveCount w K rows[r] ≠ 0 := by
        have := hpos r (Nat.lt_succ_self r)
        omega
      -- Telescope sum over 0..r+1
      have htelesc : ∀ n (hn : n < r + 1),
          ((List.range (n + 1)).map fun t =>
            if ht : t < rows.length then vecRowMemsegLogUp embed β γ w K rows[t] else 0).sum =
          fp (vecBaseAddr rows[0]) -
            fp (vecBaseAddr rows[0] + ((K * n + vecRowActiveCount w K rows[n] : Nat) : F)) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hterm := vecRowMemsegLogUp_eq embed β γ hK (hrows 0 h0len)
            have hne := hpos 0 hn
            simp only [List.range_one, List.map_singleton, List.sum_singleton, h0len, ↓reduceDIte,
              hterm, hne, ↓reduceIte, Nat.mul_zero, zero_add, fp]
        | succ n ih =>
            intro hn
            have ih' := ih (by omega)
            rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
              List.sum_singleton, ih']
            have hn1len : n + 1 < rows.length := by omega
            have hterm := vecRowMemsegLogUp_eq embed β γ hK (hrows (n + 1) hn1len)
            have hne := hpos (n + 1) hn
            have hfn : vecRowActiveCount w K rows[n] = K := hfull n hn
            have hbn1 : vecBaseAddr rows[n + 1] = vecBaseAddr rows[0] + ((K * (n + 1) : Nat) : F) :=
              (hon (n + 1) hn).2
            simp only [hn1len, ↓reduceDIte, hterm, hne, ↓reduceIte, hfn, hbn1]
            have hcast1 : ((K * n + K : Nat) : F) = ((K * (n + 1) : Nat) : F) := rfl
            have hcast2 :
                vecBaseAddr rows[0] + ((K * (n + 1) : Nat) : F) + (vecRowActiveCount w K rows[n + 1] : F) =
                vecBaseAddr rows[0] + ((K * (n + 1) + vecRowActiveCount w K rows[n + 1] : Nat) : F) := by
              push_cast; ring
            rw [hcast1, hcast2]
            change (fp (vecBaseAddr rows[0]) - fp (vecBaseAddr rows[0] + ((K * (n + 1) : Nat) : F))) +
                (fp (vecBaseAddr rows[0] + ((K * (n + 1) : Nat) : F)) -
                  fp (vecBaseAddr rows[0] + ((K * (n + 1) + vecRowActiveCount w K rows[n + 1] : Nat) : F))) =
              fp (vecBaseAddr rows[0]) -
                fp (vecBaseAddr rows[0] + ((K * (n + 1) + vecRowActiveCount w K rows[n + 1] : Nat) : F))
            ring
      rw [htot_val, dif_neg htot_ne, hhead]
      exact htelesc r (Nat.lt_succ_self r)

end VectorizedRomSoundness

/-! ## 6. Axiom Audit Guards -/

/-- info: 'Aiur.MultiStarkSpec.AirExpr.eval_fold' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AirExpr.eval_fold

/-- info: 'Aiur.MultiStarkSpec.eval_lowerPoly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_lowerPoly

/-- info: 'Aiur.MultiStarkSpec.balancedLookupOrder_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms balancedLookupOrder_perm

/-- info: 'Aiur.MultiStarkSpec.retune_lookups_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retune_lookups_perm

/-- info: 'Aiur.MultiStarkSpec.chunkNumeratorPrefixSuffix_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chunkNumeratorPrefixSuffix_eq

/-- info: 'Aiur.MultiStarkSpec.chunk_constraint_iff_sum_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chunk_constraint_iff_sum_inv

/-- info: 'Aiur.MultiStarkSpec.retune_logup_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retune_logup_equiv

/-- info: 'Aiur.MultiStarkSpec.retune_batch_logup_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retune_batch_logup_equiv

/-- info: 'Aiur.MultiStarkSpec.lowerSingleChip_row_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerSingleChip_row_sound

/-- info: 'Aiur.MultiStarkSpec.lowerGroupLayout_row_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerGroupLayout_row_sound

/-- info: 'Aiur.MultiStarkSpec.checkMemo_of_inspected_field_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkMemo_of_inspected_field_balance

/-- info: 'Aiur.MultiStarkSpec.depth_sound_of_inspected_field_balance_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms depth_sound_of_inspected_field_balance_goldilocks

/-- info: 'Aiur.MultiStarkSpec.samePackets_logup_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms samePackets_logup_sum_eq

/-- info: 'Aiur.MultiStarkSpec.checked_packet_logup_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_packet_logup_sum_eq

/-- info: 'Aiur.MultiStarkSpec.checked_padding_logup_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_padding_logup_sum_zero

/-- info: 'Aiur.MultiStarkSpec.vecRow_prefix_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vecRow_prefix_of_valid

/-- info: 'Aiur.MultiStarkSpec.vecRow_memseg_delta_eq_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vecRow_memseg_delta_eq_scalar

/-- info: 'Aiur.MultiStarkSpec.vecTrace_memseg_delta_eq_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vecTrace_memseg_delta_eq_scalar

/-- info: 'Aiur.MultiStarkSpec.vecRow_rom_logup_sum_eq_extracted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vecRow_rom_logup_sum_eq_extracted

/-- info: 'Aiur.MultiStarkSpec.vectorizedRom_rows_contiguous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorizedRom_rows_contiguous

/-- info: 'Aiur.MultiStarkSpec.vectorizedRom_telescopes_memseg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorizedRom_telescopes_memseg

end Aiur.MultiStarkSpec
