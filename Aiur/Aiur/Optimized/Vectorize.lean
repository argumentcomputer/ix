import Aiur.Optimized.PhysicalSemantics
import Aiur.Optimized.PolynomialIdentity
import Aiur.Optimized.EndToEnd
import Aiur.Circuit.CheckerContext
import Aiur.Circuit.Stats
import Aiur.Library.U32.Goldilocks
import Mathlib.Tactic.Ring

/-!
# Certified `K`-Lane Horizontal Chip Vectorization (Phase 3.3 / `@[circuit_vectorize(K)]`)

Horizontally replicates any narrow hot `Aiur.Circuit.Chip F` of width `W = orig.numVars`
into `K ≥ 1` disjoint side-by-side lanes of total width `K * W` (lane `j ∈ 0 .. K - 1`
occupying columns `[j * W, (j + 1) * W)`), reducing the chip's physical row count by `K×`
(cutting `max_log` by `log₂ K`) with **zero** increase in polynomial constraint degree!

## Contents

1. **Disjoint Lane Shifting & Exact Degree Invariance (`shiftExpr`, `vectorizeChip`)**:
   * `vectorizeChip orig K`: constructs a `K`-lane `Chip F` of width `K * orig.numVars`
     containing the shifted constraints, sends, and memory lookups for every lane `j < K`,
     alongside per-lane receive descriptors `laneReceives orig K`.
   * `vectorizeChip_maxConstraintDegree`, `vectorizeChip_maxLookupDegree`,
     `vectorizeChip_maxLookupGuardDegree`: exact degree invariance (zero degree increase!).
   * `isZeroSilent` & `activation_isZeroSilent`: decidable zero-row silence check
     satisfied automatically by every `Activation.compile`-activated chip and every
     selector-gated chip, allowing unused tail lanes in partially-filled rows to be
     all-zero with zero sends and zero ROM lookups.
2. **Decidable Fail-Closed Structural Verifier (`checkVectorize`, `checkVectorizeReceives`)**:
   * Verifies `1 ≤ K`, well-formedness, exact width `K * orig.numVars`, variable bounds
     for every lane's receives, and exact shifted copies of all constraints, sends, and
     memory lookups across all `K` lanes.
3. **Certified Bidirectional Chip Soundness & Completeness**:
   * `vectorize_chip_sound` & `vectorize_chip_weighted_sound`: any valid row of
     `vectorizeChip orig K` (with per-lane active flags `sel_j` or per-lane multiplicities
     `m_j`, including uniform outer multiplicity `m`) unpacks into `≤ K` valid active rows
     of `orig` with identical `RuleClaims` and identical LogUp `Balance.accumulator`
     (equal to the exact sum of the `K` lane ledgers).
   * `vectorize_chip_complete`, `vectorize_chip_complete_zeroSilent`, &
     `vectorize_chip_weighted_complete`: any batch of `≤ K` valid rows of `orig` (padded
     with inactive all-zero lanes for zero-silent chips when `< K`) packs into 1 valid
     row of `vectorizeChip orig K` with identical LogUp ledger.
4. **System-Level Soundness, Completeness, Exact `⌈N / K⌉` Row Bound, & End-to-End Proofs**:
   * `VectorizedSystem` with unit (`check`) and weighted LogUp memo (`checkMemo`) checkers.
   * `vectorize_system_sound`, `vectorize_system_memo_sound`: lifts any accepted vectorized
     trace back to an accepted trace of `sys.source`.
   * `vectorize_system_complete`, `vectorize_system_memo_complete`,
     `vectorize_system_complete_row_bound`: packs `N` rows of each vectorized chip into
     **exactly `⌈N / K⌉ = (N + K - 1) / K`** physical rows, preserving exact LogUp balance.
   * `vectorize_system_check_iff`, `vectorize_system_checkMemo_iff`,
     `vectorize_modulesArtifact_sound`, `vectorize_physical_heap_sound`.
5. **Executable `#guard` Smoke Tests, Negative Controls & `#print axioms` Pins**:
   * Demonstrates a concrete 9-column, degree-3 Goldilocks step chip with recursive send
     and ROM lookup at `K = 4` (`N = 100 → 25` rows, `4×`) and `K = 8` (`N = 103 → 13` rows,
     `7.92×`, tail padding lane literally all-zero and inactive!), `checkVectorize == true`,
     `maxConstraintDegree == 3` unchanged, `check` & `checkMemo` round-trip `== .ok ()`,
     and negative controls (dropped lane constraint, dropped lane send, wrong lane shift,
     dropped memory, `K = 0`, wrong width) all rejected fail-closed.

Zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only.
-/

set_option autoImplicit false

namespace Aiur.Optimized.Vectorize

open Aiur Aiur.Circuit Aiur.Optimized

/-! ## 1. Variable Shifting, Lane Layout & Degree Invariance -/

section Shift

variable {F : Type}

/-- Shift a column index `v` into a lane starting at column `offset`. -/
def shiftVar (offset : Nat) (v : Var) : Var :=
  offset + v

/-- Shift every variable in an arithmetic expression by `offset`. -/
def shiftExpr (offset : Nat) : ArithExpr F → ArithExpr F
  | .const c => .const c
  | .var v => .var (offset + v)
  | .add l r => .add (shiftExpr offset l) (shiftExpr offset r)
  | .sub l r => .sub (shiftExpr offset l) (shiftExpr offset r)
  | .mul l r => .mul (shiftExpr offset l) (shiftExpr offset r)

/-- Shift every variable and expression in a `Send` by `offset`. -/
def shiftSend (offset : Nat) (s : Send F) : Send F where
  channel := s.channel
  args := s.args.map (WireValue.map (shiftExpr offset))
  result := s.result.map (shiftVar offset)
  enable := shiftExpr offset s.enable

/-- Shift every expression in a `MemoryLookup` by `offset`. -/
def shiftMemory (offset : Nat) (m : MemoryLookup F) : MemoryLookup F where
  address := shiftExpr offset m.address
  value := m.value.map (shiftExpr offset)
  enable := shiftExpr offset m.enable

/-- Receive / claim interface for a single lane of a horizontally vectorized chip. -/
structure LaneReceive (F : Type) where
  channel : String
  inputs : List (WireValue Var)
  output : WireValue (ArithExpr F)
  deriving Repr, BEq

deriving instance DecidableEq for LaneReceive

/-- Variable bounds check for a single lane's receive interface. -/
def LaneReceive.inBounds (numVars : Nat) (r : LaneReceive F) : Bool :=
  (r.inputs.flatMap WireValue.words).all (· < numVars) &&
    r.output.words.all (ArithExpr.inBounds numVars)

/-- Message provided by a lane receive interface under assignment `a`. -/
def LaneReceive.message [Field F] (r : LaneReceive F) (a : Var → F) : Message F :=
  ⟨r.channel, r.inputs.map (WireValue.map a), r.output.map (ArithExpr.denote a)⟩

/-- Shifted receive interface of `chip` placed at column offset `offset`. -/
def shiftReceive (offset : Nat) (chip : Chip F) : LaneReceive F where
  channel := chip.name
  inputs := chip.inputs.map (WireValue.map (shiftVar offset))
  output := chip.output.map (shiftExpr offset)

/-- Extract the variable assignment of a lane starting at column `offset`. -/
def sliceAssign (offset : Nat) (a : Var → F) : Var → F :=
  fun v => a (offset + v)

/-- Maximum polynomial degree across a chip's constraints (matching `Chip.stats`). -/
def maxConstraintDegree (chip : Chip F) : Nat :=
  chip.stats.maxConstraintDegree

@[simp] theorem shiftExpr_degree (offset : Nat) (e : ArithExpr F) :
    (shiftExpr offset e).degree = e.degree := by
  induction e with
  | const _ => rfl
  | var _ => rfl
  | add l r ihl ihr => simp [shiftExpr, ArithExpr.degree, Scalar.Circuit.ArithExpr.degree, ihl, ihr]
  | sub l r ihl ihr => simp [shiftExpr, ArithExpr.degree, Scalar.Circuit.ArithExpr.degree, ihl, ihr]
  | mul l r ihl ihr => simp [shiftExpr, ArithExpr.degree, Scalar.Circuit.ArithExpr.degree, ihl, ihr]

private theorem foldl_max_init {α : Type} (f : α → Nat) (xs : List α) (init : Nat) :
    xs.foldl (fun acc x => max acc (f x)) init =
      max init (xs.foldl (fun acc x => max acc (f x)) 0) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max init (f x)), ih (max 0 (f x)), Nat.zero_max, Nat.max_assoc]

theorem maxDegree_append (xs ys : List (ArithExpr F)) :
    ArithExpr.maxDegree (xs ++ ys) = max (ArithExpr.maxDegree xs) (ArithExpr.maxDegree ys) := by
  unfold ArithExpr.maxDegree
  rw [List.foldl_append, foldl_max_init (f := ArithExpr.degree)]

theorem maxDegree_cons (x : ArithExpr F) (xs : List (ArithExpr F)) :
    ArithExpr.maxDegree (x :: xs) = max x.degree (ArithExpr.maxDegree xs) := by
  simpa [ArithExpr.maxDegree] using foldl_max_init (f := ArithExpr.degree) xs x.degree

theorem maxDegree_map_shift (offset : Nat) (es : List (ArithExpr F)) :
    ArithExpr.maxDegree (es.map (shiftExpr offset)) = ArithExpr.maxDegree es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, maxDegree_cons, shiftExpr_degree, ih]

private theorem foldl_max_append (xs ys : List Nat) :
    (xs ++ ys).foldl max 0 = max (xs.foldl max 0) (ys.foldl max 0) := by
  rw [List.foldl_append]
  exact foldl_max_init (f := id) ys (xs.foldl max 0)

private theorem foldl_max_flatMap_const {α β : Type} (f : β → Nat)
    (g : α → List β) (d : Nat) :
    ∀ (xs : List α), xs ≠ [] → (∀ x ∈ xs, (g x).foldl (fun acc y => max acc (f y)) 0 = d) →
      (xs.flatMap g).foldl (fun acc y => max acc (f y)) 0 = d
  | [], hne, _ => absurd rfl hne
  | [x], _, hg => by
      simpa using hg x List.mem_cons_self
  | x :: y :: rest, _, hg => by
      have hx := hg x List.mem_cons_self
      have htail := foldl_max_flatMap_const f g d (y :: rest) (List.cons_ne_nil _ _)
        (fun z hz => hg z (List.mem_cons_of_mem x hz))
      rw [List.flatMap_cons, List.foldl_append, foldl_max_init (f := f), hx, htail, Nat.max_self]

theorem maxDegree_flatMap_shift (W : Nat) {K : Nat} (hK : 1 ≤ K) (es : List (ArithExpr F)) :
    ArithExpr.maxDegree ((List.range K).flatMap fun j => es.map (shiftExpr (j * W))) =
      ArithExpr.maxDegree es := by
  unfold ArithExpr.maxDegree
  apply foldl_max_flatMap_const ArithExpr.degree
    (fun j => es.map (shiftExpr (j * W))) (ArithExpr.maxDegree es) (List.range K)
  · intro h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  · intro j _
    exact maxDegree_map_shift (j * W) es

@[simp] theorem shiftSend_maxDegree (offset : Nat) (s : Send F) :
    (shiftSend offset s).maxDegree = s.maxDegree := by
  unfold Send.maxDegree shiftSend
  dsimp only
  have hwords : ((s.args.map (WireValue.map (shiftExpr offset))).flatMap WireValue.words) =
      (s.args.flatMap WireValue.words).map (shiftExpr offset) := by
    induction s.args with
    | nil => rfl
    | cons a rest ih =>
        simp [WireValue.map, List.map_append, ih]
  rw [hwords]
  have hcons : shiftExpr offset s.enable :: (s.args.flatMap WireValue.words).map (shiftExpr offset) =
      (s.enable :: s.args.flatMap WireValue.words).map (shiftExpr offset) := rfl
  rw [hcons, maxDegree_map_shift]
  simp [WireValue.map]

@[simp] theorem shiftMemory_maxDegree (offset : Nat) (m : MemoryLookup F) :
    (shiftMemory offset m).maxDegree = m.maxDegree := by
  unfold MemoryLookup.maxDegree shiftMemory
  dsimp only
  have hcons : shiftExpr offset m.enable :: shiftExpr offset m.address ::
        (m.value.map (shiftExpr offset)).words =
      (m.enable :: m.address :: m.value.words).map (shiftExpr offset) := by
    simp [WireValue.map]
  rw [hcons, maxDegree_map_shift]

theorem shiftExpr_inBounds {offset W N : Nat} (hle : offset + W ≤ N) :
    ∀ {e : ArithExpr F}, e.inBounds W = true → (shiftExpr offset e).inBounds N = true
  | .const _, _ => rfl
  | .var v, hv => by
      simp only [shiftExpr, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds,
        decide_eq_true_eq] at hv ⊢
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv offset) hle
  | .add l r, hlr => by
      simp only [shiftExpr, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds,
        Bool.and_eq_true] at hlr ⊢
      exact ⟨shiftExpr_inBounds hle hlr.1, shiftExpr_inBounds hle hlr.2⟩
  | .sub l r, hlr => by
      simp only [shiftExpr, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds,
        Bool.and_eq_true] at hlr ⊢
      exact ⟨shiftExpr_inBounds hle hlr.1, shiftExpr_inBounds hle hlr.2⟩
  | .mul l r, hlr => by
      simp only [shiftExpr, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds,
        Bool.and_eq_true] at hlr ⊢
      exact ⟨shiftExpr_inBounds hle hlr.1, shiftExpr_inBounds hle hlr.2⟩

theorem shiftSend_inBounds {offset W N : Nat} (hle : offset + W ≤ N) {s : Send F}
    (hs : s.inBounds W = true) : (shiftSend offset s).inBounds N = true := by
  simp only [Send.inBounds, shiftSend, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hs ⊢
  refine ⟨⟨?_, shiftExpr_inBounds hle hs.1.2⟩, ?_⟩
  · intro v hv
    simp only [WireValue.map, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have huLt := hs.1.1 u hu
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left huLt offset) hle
  · intro e he
    obtain ⟨w, hw, hew⟩ := List.mem_flatMap.mp he
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    simp only [WireValue.map, List.mem_map] at hew
    obtain ⟨e0, he0, rfl⟩ := hew
    exact shiftExpr_inBounds hle (hs.2 e0 (List.mem_flatMap.mpr ⟨w0, hw0, he0⟩))

theorem shiftMemory_inBounds {offset W N : Nat} (hle : offset + W ≤ N) {m : MemoryLookup F}
    (hm : m.inBounds W = true) : (shiftMemory offset m).inBounds N = true := by
  simp only [MemoryLookup.inBounds, shiftMemory, Bool.and_eq_true, List.all_eq_true] at hm ⊢
  refine ⟨⟨shiftExpr_inBounds hle hm.1.1, shiftExpr_inBounds hle hm.1.2⟩, ?_⟩
  intro e he
  simp only [WireValue.map, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  exact shiftExpr_inBounds hle (hm.2 e0 he0)

theorem shiftReceive_inBounds {offset N : Nat} {chip : Chip F}
    (hwf : chip.wellFormed = true) (hle : offset + chip.numVars ≤ N) :
    (shiftReceive offset chip).inBounds N = true := by
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  simp only [LaneReceive.inBounds, shiftReceive, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · intro v hv
    obtain ⟨w, hw, hvw⟩ := List.mem_flatMap.mp hv
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    simp only [WireValue.map, List.mem_map] at hvw
    obtain ⟨u, hu, rfl⟩ := hvw
    have huLt := hwf.1.1.1.1 u (List.mem_flatMap.mpr ⟨w0, hw0, hu⟩)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left huLt offset) hle
  · intro e he
    simp only [WireValue.map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact shiftExpr_inBounds hle (hwf.1.1.1.2 e0 he0)

@[simp] theorem shiftExpr_denote [Field F] (offset : Nat) (a : Var → F) (e : ArithExpr F) :
    (shiftExpr offset e).denote a = e.denote (sliceAssign offset a) := by
  induction e with
  | const _ => rfl
  | var _ => rfl
  | add l r ihl ihr => simp [shiftExpr, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, ihl, ihr]
  | sub l r ihl ihr => simp [shiftExpr, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, ihl, ihr]
  | mul l r ihl ihr => simp [shiftExpr, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, ihl, ihr]

@[simp] theorem shiftSend_enable_denote [Field F] (offset : Nat) (a : Var → F) (s : Send F) :
    (shiftSend offset s).enable.denote a = s.enable.denote (sliceAssign offset a) :=
  shiftExpr_denote offset a s.enable

@[simp] theorem shiftSend_message [Field F] (offset : Nat) (a : Var → F) (s : Send F) :
    (shiftSend offset s).message a = s.message (sliceAssign offset a) := by
  unfold Send.message shiftSend
  dsimp only
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro w _
    simp [WireValue.map, List.map_map, Function.comp_def, shiftExpr_denote]
  · simp [WireValue.map, List.map_map, Function.comp_def, shiftVar, sliceAssign]

theorem shiftMemory_valid_iff [Field F] (offset : Nat) (rom : WireROM F) (a : Var → F)
    (m : MemoryLookup F) :
    (shiftMemory offset m).Valid rom a ↔ m.Valid rom (sliceAssign offset a) := by
  unfold MemoryLookup.Valid shiftMemory
  dsimp only
  have hval : (m.value.map (shiftExpr offset)).map (ArithExpr.denote a) =
      m.value.map (ArithExpr.denote (sliceAssign offset a)) := by
    simp [WireValue.map, List.map_map, Function.comp_def, shiftExpr_denote]
  simp [shiftExpr_denote, hval]

@[simp] theorem shiftReceive_message [Field F] (offset : Nat) (chip : Chip F) (a : Var → F) :
    (shiftReceive offset chip).message a = chip.conclusion (sliceAssign offset a) := by
  unfold LaneReceive.message shiftReceive Chip.conclusion
  dsimp only
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro w _
    simp [WireValue.map, List.map_map, Function.comp_def, shiftVar, sliceAssign]
  · simp [WireValue.map, List.map_map, Function.comp_def, shiftExpr_denote]

end Shift

/-! ## 2. Horizontal `K`-Lane Replication (`vectorizeChip`) & Structural Verifier (`checkVectorize`) -/

section ChipVectorize

variable {F : Type}

/-- Expected shifted constraints of `orig` across `K` horizontal lanes. -/
def expectedConstraints (orig : Chip F) (K : Nat) : List (Constraint F) :=
  (List.range K).flatMap fun j => orig.constraints.map (shiftExpr (j * orig.numVars))

/-- Expected shifted sends of `orig` across `K` horizontal lanes. -/
def expectedSends (orig : Chip F) (K : Nat) : List (Send F) :=
  (List.range K).flatMap fun j => orig.sends.map (shiftSend (j * orig.numVars))

/-- Expected shifted memory lookups of `orig` across `K` horizontal lanes. -/
def expectedMemory (orig : Chip F) (K : Nat) : List (MemoryLookup F) :=
  (List.range K).flatMap fun j => orig.memory.map (shiftMemory (j * orig.numVars))

/-- Receive / claim interface for lane `j` of a vectorized `orig` chip. -/
def laneReceive (orig : Chip F) (j : Nat) : LaneReceive F :=
  shiftReceive (j * orig.numVars) orig

/-- All `K` per-lane receive / claim interfaces of a `K`-lane vectorized `orig` chip. -/
def laneReceives (orig : Chip F) (K : Nat) : List (LaneReceive F) :=
  (List.range K).map (laneReceive orig)

/-- Shifted sends owned by lane `j` of a vectorized `orig` chip. -/
def laneSends (orig : Chip F) (j : Nat) : List (Send F) :=
  orig.sends.map (shiftSend (j * orig.numVars))

/-- Horizontally replicate `orig : Chip F` into `K` disjoint lanes of total width
`K * orig.numVars` (lane `j ∈ 0 .. K - 1` occupies columns `[j * W, (j + 1) * W)`).
Lane `0`'s inputs/output sit in `inputs`/`output`, while all `K` lanes have shifted
receive descriptors in `laneReceives orig K`. -/
def vectorizeChip (orig : Chip F) (K : Nat)
    (vecName : String := orig.name ++ s!"#vec{K}") : Chip F where
  name := vecName
  inputs := orig.inputs
  output := orig.output
  numVars := K * orig.numVars
  constraints := expectedConstraints orig K
  sends := expectedSends orig K
  memory := expectedMemory orig K

@[simp] theorem vectorizeChip_numVars (orig : Chip F) (K : Nat)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    (vectorizeChip orig K vecName).numVars = K * orig.numVars := rfl

private theorem lane_bound_le {W K j : Nat} (hj : j < K) :
    j * W + W ≤ K * W := by
  have h1 : (j + 1) * W ≤ K * W := Nat.mul_le_mul_right W hj
  simpa [Nat.add_mul] using h1

theorem laneReceives_inBounds {orig : Chip F} {K : Nat}
    (hwf : orig.wellFormed = true) :
    ∀ r ∈ laneReceives orig K, r.inBounds (K * orig.numVars) = true := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact shiftReceive_inBounds hwf (lane_bound_le (List.mem_range.mp hj))

theorem vectorizeChip_wellFormed {orig : Chip F} {K : Nat}
    (hwf : orig.wellFormed = true) (hK : 1 ≤ K)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    (vectorizeChip orig K vecName).wellFormed = true := by
  have hwf' := hwf
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf'
  have hWle : orig.numVars ≤ K * orig.numVars := Nat.le_mul_of_pos_left _ hK
  simp only [vectorizeChip, Chip.wellFormed, Bool.and_eq_true, List.all_eq_true,
    expectedConstraints, expectedSends, expectedMemory,
    List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro v hv
    exact decide_eq_true (Nat.lt_of_lt_of_le (hwf'.1.1.1.1 v (List.mem_flatMap.mpr hv)) hWle)
  · intro e he
    have h0 : 0 + orig.numVars ≤ K * orig.numVars := by omega
    have hin := shiftExpr_inBounds h0 (hwf'.1.1.1.2 e he)
    have hshift0 : ∀ x : ArithExpr F, shiftExpr 0 x = x := by
      intro x
      induction x with
      | const _ => rfl
      | var _ => simp [shiftExpr]
      | add a b iha ihb => simp [shiftExpr, iha, ihb]
      | sub a b iha ihb => simp [shiftExpr, iha, ihb]
      | mul a b iha ihb => simp [shiftExpr, iha, ihb]
    simpa [hshift0] using hin
  · rintro _ ⟨j, hj, c, hc, rfl⟩
    exact shiftExpr_inBounds (lane_bound_le hj) (hwf'.1.1.2 c hc)
  · rintro _ ⟨j, hj, s, hs, rfl⟩
    exact shiftSend_inBounds (lane_bound_le hj) (hwf'.1.2 s hs)
  · rintro _ ⟨j, hj, m, hm, rfl⟩
    exact shiftMemory_inBounds (lane_bound_le hj) (hwf'.2 m hm)

/-- **Constraint Degree Invariance (`vectorizeChip_maxConstraintDegree`)**:
horizontally replicating `orig` into `K ≥ 1` lanes preserves `maxConstraintDegree`
with **zero** degree increase! -/
theorem vectorizeChip_maxConstraintDegree (orig : Chip F) {K : Nat} (hK : 1 ≤ K)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    maxConstraintDegree (vectorizeChip orig K vecName) = maxConstraintDegree orig := by
  unfold maxConstraintDegree Chip.stats vectorizeChip expectedConstraints
  dsimp only
  exact maxDegree_flatMap_shift orig.numVars hK orig.constraints

/-- Lookup expression degree is also strictly unchanged by `K`-lane vectorization. -/
theorem vectorizeChip_maxLookupDegree (orig : Chip F) {K : Nat} (hK : 1 ≤ K)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    (vectorizeChip orig K vecName).stats.maxLookupDegree = orig.stats.maxLookupDegree := by
  have hne : List.range K ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  have hsends : (((expectedSends orig K).map Send.maxDegree).foldl max 0) =
      ((orig.sends.map Send.maxDegree).foldl max 0) := by
    have hmap : (expectedSends orig K).map Send.maxDegree =
        (List.range K).flatMap fun j => orig.sends.map Send.maxDegree := by
      unfold expectedSends
      rw [List.map_flatMap]
      congr 1
      funext j
      rw [List.map_map]
      apply List.map_congr_left
      intro s _
      exact shiftSend_maxDegree (j * orig.numVars) s
    rw [hmap]
    exact foldl_max_flatMap_const id (fun _ => orig.sends.map Send.maxDegree)
      ((orig.sends.map Send.maxDegree).foldl max 0) (List.range K) hne (fun _ _ => rfl)
  have hmem : (((expectedMemory orig K).map MemoryLookup.maxDegree).foldl max 0) =
      ((orig.memory.map MemoryLookup.maxDegree).foldl max 0) := by
    have hmap : (expectedMemory orig K).map MemoryLookup.maxDegree =
        (List.range K).flatMap fun j => orig.memory.map MemoryLookup.maxDegree := by
      unfold expectedMemory
      rw [List.map_flatMap]
      congr 1
      funext j
      rw [List.map_map]
      apply List.map_congr_left
      intro m _
      exact shiftMemory_maxDegree (j * orig.numVars) m
    rw [hmap]
    exact foldl_max_flatMap_const id (fun _ => orig.memory.map MemoryLookup.maxDegree)
      ((orig.memory.map MemoryLookup.maxDegree).foldl max 0) (List.range K) hne (fun _ _ => rfl)
  unfold Chip.stats vectorizeChip
  dsimp only
  rw [hsends, hmem]

/-- Lookup guard degree is strictly unchanged by `K`-lane vectorization. -/
theorem vectorizeChip_maxLookupGuardDegree (orig : Chip F) {K : Nat} (hK : 1 ≤ K)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    (vectorizeChip orig K vecName).maxLookupGuardDegree = orig.maxLookupGuardDegree := by
  have hs : (expectedSends orig K).map Send.enable =
      (List.range K).flatMap fun j => (orig.sends.map Send.enable).map (shiftExpr (j * orig.numVars)) := by
    unfold expectedSends
    rw [List.map_flatMap]
    congr 1
    funext j
    simp [shiftSend, List.map_map, Function.comp_def]
  have hm : (expectedMemory orig K).map MemoryLookup.enable =
      (List.range K).flatMap fun j => (orig.memory.map MemoryLookup.enable).map (shiftExpr (j * orig.numVars)) := by
    unfold expectedMemory
    rw [List.map_flatMap]
    congr 1
    funext j
    simp [shiftMemory, List.map_map, Function.comp_def]
  unfold Chip.maxLookupGuardDegree vectorizeChip
  dsimp only
  rw [maxDegree_append, maxDegree_append, hs, hm,
    maxDegree_flatMap_shift orig.numVars hK (orig.sends.map Send.enable),
    maxDegree_flatMap_shift orig.numVars hK (orig.memory.map MemoryLookup.enable)]

section DecidableVerifier

variable [Field F] [DecidableEq F]

/-- Decidable fail-closed structural verifier checking that `vec` is a valid `K`-lane
horizontal vectorization of `orig`: `1 ≤ K`, both chips well-formed, width `K * orig.numVars`,
all `K` lane receives in bounds, and exact shifted constraints, sends, and memory lookups. -/
def checkVectorize (orig vec : Chip F) (K : Nat) : Bool :=
  decide (1 ≤ K) &&
    orig.wellFormed &&
    vec.wellFormed &&
    decide (vec.numVars = K * orig.numVars) &&
    decide (vec.inputs = orig.inputs) &&
    decide (vec.output = orig.output) &&
    (laneReceives orig K).all (LaneReceive.inBounds vec.numVars) &&
    decide (vec.constraints = expectedConstraints orig K) &&
    decide (vec.sends = expectedSends orig K) &&
    decide (vec.memory = expectedMemory orig K)

/-- Structural verifier also validating an explicit list of `K` per-lane receives. -/
def checkVectorizeReceives (orig vec : Chip F) (receives : List (LaneReceive F)) (K : Nat) : Bool :=
  checkVectorize orig vec K && decide (receives = laneReceives orig K)

/-- Unpacked structural facts guaranteed whenever `checkVectorize orig vec K = true`. -/
structure CheckVectorizeSpec (orig vec : Chip F) (K : Nat) : Prop where
  lanesPos : 1 ≤ K
  origWf : orig.wellFormed = true
  vecWf : vec.wellFormed = true
  numVarsEq : vec.numVars = K * orig.numVars
  inputsEq : vec.inputs = orig.inputs
  outputEq : vec.output = orig.output
  receivesInBounds : ∀ r ∈ laneReceives orig K, r.inBounds vec.numVars = true
  constraintsEq : vec.constraints = expectedConstraints orig K
  sendsEq : vec.sends = expectedSends orig K
  memoryEq : vec.memory = expectedMemory orig K

omit [Field F] in
theorem checkVectorize_spec {orig vec : Chip F} {K : Nat}
    (h : checkVectorize orig vec K = true) : CheckVectorizeSpec orig vec K := by
  simp only [checkVectorize, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact {
    lanesPos := h.1.1.1.1.1.1.1.1.1
    origWf := h.1.1.1.1.1.1.1.1.2
    vecWf := h.1.1.1.1.1.1.1.2
    numVarsEq := h.1.1.1.1.1.1.2
    inputsEq := h.1.1.1.1.1.2
    outputEq := h.1.1.1.1.2
    receivesInBounds := h.1.1.1.2
    constraintsEq := h.1.1.2
    sendsEq := h.1.2
    memoryEq := h.2
  }

omit [Field F] in
theorem checkVectorize_vectorizeChip {orig : Chip F} {K : Nat}
    (hwf : orig.wellFormed = true) (hK : 1 ≤ K)
    (vecName : String := orig.name ++ s!"#vec{K}") :
    checkVectorize orig (vectorizeChip orig K vecName) K = true := by
  simp only [checkVectorize, vectorizeChip, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hK, hwf⟩, vectorizeChip_wellFormed hwf hK vecName⟩, trivial⟩, trivial⟩, trivial⟩,
    laneReceives_inBounds hwf⟩, trivial⟩, trivial⟩, trivial⟩

omit [Field F] in
theorem checkVectorize_maxConstraintDegree {orig vec : Chip F} {K : Nat}
    (h : checkVectorize orig vec K = true) :
    maxConstraintDegree vec = maxConstraintDegree orig := by
  have spec := checkVectorize_spec h
  unfold maxConstraintDegree Chip.stats
  dsimp only
  rw [spec.constraintsEq]
  exact maxDegree_flatMap_shift orig.numVars spec.lanesPos orig.constraints

/-- Decidable check that the all-zero row of `chip` satisfies every constraint and
keeps every send and memory lookup disabled (`enable ≠ 1`), making all-zero tail
padding lanes completely silent. -/
def isZeroSilent (chip : Chip F) : Bool :=
  chip.constraints.all (fun p => decide (p.denote (fun _ => 0) = 0)) &&
    chip.sends.all (fun s => decide (s.enable.denote (fun _ => 0) ≠ 1)) &&
    chip.memory.all (fun m => decide (m.enable.denote (fun _ => 0) ≠ 1))

omit [DecidableEq F] in
private theorem replicate_zero_assignment (name : String) (W : Nat) :
    Row.assignment (⟨name, List.replicate W (0 : F)⟩ : Row F) = fun _ => 0 := by
  funext v
  simp only [Scalar.Circuit.Row.assignment]
  by_cases hv : v < W
  · simp [hv]
  · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact Nat.le_of_not_lt hv)]
    rfl

theorem zeroRow_valid_of_isZeroSilent {chip : Chip F} (hwf : chip.wellFormed = true)
    (hsilent : isZeroSilent chip = true) (rom : WireROM F) :
    let zeroRow : Row F := ⟨chip.name, List.replicate chip.numVars 0⟩
    chip.ValidRow rom zeroRow ∧ chip.premises zeroRow = [] := by
  simp only [isZeroSilent, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsilent
  dsimp only
  have hassign := replicate_zero_assignment (F := F) chip.name chip.numVars
  refine ⟨⟨hwf, by simp, ?_, ?_⟩, ?_⟩
  · intro p hp
    rw [hassign]
    exact hsilent.1.1 p hp
  · intro m hm hen
    rw [hassign] at hen
    exact absurd hen (hsilent.2 m hm)
  · unfold Chip.premises
    apply List.filterMap_eq_nil_iff.mpr
    intro s hs
    rw [hassign]
    simp [hsilent.1.2 s hs]

/-- Every chip produced by Formal Aiur's `Activation.compile` is automatically
zero-silent (`isZeroSilent = true`), so unused tail lanes in `vectorizeChip` can
simply be set to all zeros (`sel_j = 0`). -/
theorem activation_isZeroSilent (chip : Chip F) :
    isZeroSilent (Activation.compile chip) = true := by
  have hvalid := Activation.zero_valid chip (⟨[]⟩ : WireROM F)
  have hreq := Activation.zero_requirements chip (⟨[]⟩ : WireROM F)
  simp only [isZeroSilent, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨fun p hp => hvalid.1 p hp, fun s hs => ?_⟩, fun m hm => ?_⟩
  · intro hen
    have hnone := List.filterMap_eq_nil_iff.mp hreq s hs
    simp [hen] at hnone
  · have hz := Activation.memory_inactive chip (fun _ => 0) hvalid rfl m hm
    rw [hz]
    exact zero_ne_one

end DecidableVerifier

end ChipVectorize

/-! ## 3. Row Slicing, Packing, Ledger Additivity & Chip-Level Bidirectional Theorems -/

section ChipTheorems

variable {F : Type} [Field F] [DecidableEq F]

/-- Slice lane `j`'s `W`-element sub-row out of a vectorized physical row `row`. -/
def unpackLaneRow (origName : String) (W : Nat) (row : Row F) (j : Nat) : Row F :=
  ⟨origName, (row.values.drop (j * W)).take W⟩

/-- Unpack all active lanes (those with `laneActive[j] = true`) of a `K`-lane row. -/
def unpackActiveRows (origName : String) (W K : Nat) (row : Row F)
    (laneActive : List Bool) : List (Row F) :=
  (List.range K).filterMap fun j =>
    if laneActive.getD j false then some (unpackLaneRow origName W row j) else none

/-- Unpack all active weighted lanes (`laneMults[j] = some m_j`) of a `K`-lane row. -/
def unpackWeightedActiveRows (origName : String) (W K : Nat) (row : Row F)
    (laneMults : List (Option Int)) : List (WeightedRow F) :=
  (List.range K).filterMap fun j =>
    (laneMults.getD j none).map fun m => ⟨unpackLaneRow origName W row j, m⟩

/-- Active call premises emitted by lane `j` of a vectorized row. -/
def lanePremises (orig : Chip F) (row : Row F) (j : Nat) : List (Message F) :=
  (laneSends orig j).filterMap fun send =>
    if send.enable.denote row.assignment = 1 then some (send.message row.assignment) else none

/-- Logical `(receive, premises)` rule claim emitted by lane `j` of a vectorized row. -/
def laneRuleClaims (orig : Chip F) (row : Row F) (j : Nat) : RuleClaims (Message F) :=
  ((laneReceive orig j).message row.assignment, lanePremises orig row j)

/-- Active lane rule claims of a unit-multiplicity vectorized row (`sel_j = 1` lanes only). -/
def vecRowRules (orig : Chip F) (K : Nat) (row : Row F)
    (laneActive : List Bool) : List (RuleClaims (Message F)) :=
  (List.range K).filterMap fun j =>
    if laneActive.getD j false then some (laneRuleClaims orig row j) else none

/-- Active weighted lane rule claims of a memoized vectorized row (`some m_j` lanes only). -/
def vecRowWeightedRules (orig : Chip F) (K : Nat) (row : Row F)
    (laneMults : List (Option Int)) : List (RuleClaims (Message F) × Int) :=
  (List.range K).filterMap fun j =>
    (laneMults.getD j none).map fun m => (laneRuleClaims orig row j, m)

/-- Assign a uniform outer multiplicity `m` to every active lane (`true ↦ some m`,
`false ↦ none`). -/
def uniformLaneMults (laneActive : List Bool) (m : Int) : List (Option Int) :=
  laneActive.map fun b => if b then some m else none

/-- Fill vector used for unused tail lanes (`batch.length ≤ j < K`): all zeros
whenever `isZeroSilent orig = true`, otherwise reusing `batch[0]` so every lane's
polynomial constraints remain satisfied even on unactivated source chips. -/
def padLaneValues (orig : Chip F) (batch : List (Row F)) : List F :=
  if isZeroSilent orig then
    List.replicate orig.numVars 0
  else
    match batch with
    | r :: _ => r.values
    | [] => List.replicate orig.numVars 0

/-- Pack up to `K` rows of `orig` horizontally into a flat `K * orig.numVars` row vector. -/
def packBatchValues (orig : Chip F) (K : Nat) (batch : List (Row F)) : List F :=
  let pad := padLaneValues orig batch
  (List.range K).flatMap fun j =>
    match batch[j]? with
    | some r => r.values
    | none => pad

/-- Pack up to `K` rows of `orig` into a single physical `Row` of `vecName`. -/
def packBatchRow (orig : Chip F) (K : Nat) (vecName : String) (batch : List (Row F)) : Row F :=
  ⟨vecName, packBatchValues orig K batch⟩

/-- Per-lane boolean activity mask for a batch of `n ≤ K` active rows. -/
def packBatchActive (K n : Nat) : List Bool :=
  (List.range K).map fun j => decide (j < n)

/-- Pack up to `K` weighted rows of `orig` into a single physical `Row` of `vecName`. -/
def packWeightedBatchRow (orig : Chip F) (K : Nat) (vecName : String)
    (batch : List (WeightedRow F)) : Row F :=
  packBatchRow orig K vecName (batch.map WeightedRow.row)

/-- Per-lane multiplicity mask for a batch of `≤ K` weighted rows (`none` on tail lanes). -/
def packWeightedBatchMults (K : Nat) (batch : List (WeightedRow F)) : List (Option Int) :=
  (List.range K).map fun j => (batch[j]?).map WeightedRow.multiplicity

/-! ### LogUp Ledger Decomposition, Additivity & Permutation Invariance -/

/-- The dynamic LogUp ledger contribution of a list of weighted rule claims (without
the external `root` entry demand). -/
def rulesLedger (static : Message F → Bool)
    (rules : List (RuleClaims (Message F) × Int)) : Accumulator (Message F) :=
  Accumulator.requires ((rules.flatMap fun r => r.1.2).filter fun c => !static c) ++
    Accumulator.provides (rules.map fun r => (r.1.1, r.2))

/-- Single-lane LogUp ledger value at `claim` (`0` for an inactive tail lane `none`). -/
def laneLedgerValue (static : Message F → Bool) (orig : Chip F) (row : Row F)
    (mult? : Option Int) (j : Nat) (claim : Message F) : Int :=
  match mult? with
  | none => 0
  | some m => Accumulator.value (rulesLedger static [(laneRuleClaims orig row j, m)]) claim

omit [Field F] in
theorem rulesLedger_value_nil (static : Message F → Bool) (claim : Message F) :
    Accumulator.value (rulesLedger static []) claim = 0 := by
  simp [rulesLedger]

omit [Field F] in
theorem rulesLedger_value_append (static : Message F → Bool)
    (xs ys : List (RuleClaims (Message F) × Int)) (claim : Message F) :
    Accumulator.value (rulesLedger static (xs ++ ys)) claim =
      Accumulator.value (rulesLedger static xs) claim +
        Accumulator.value (rulesLedger static ys) claim := by
  simp only [rulesLedger, Accumulator.value_append, Accumulator.value_requires,
    Accumulator.value_provides, List.flatMap_append, List.filter_append, List.count_append,
    List.map_append, Nat.cast_add]
  ring

omit [Field F] in
theorem rulesLedger_value_cons (static : Message F → Bool)
    (x : RuleClaims (Message F) × Int) (xs : List (RuleClaims (Message F) × Int))
    (claim : Message F) :
    Accumulator.value (rulesLedger static (x :: xs)) claim =
      Accumulator.value (rulesLedger static [x]) claim +
        Accumulator.value (rulesLedger static xs) claim := by
  simpa using rulesLedger_value_append static [x] xs claim

omit [Field F] in
theorem balance_accumulator_value_eq_root_add_rulesLedger (static : Message F → Bool)
    (root : Message F) (rules : List (RuleClaims (Message F) × Int)) (claim : Message F) :
    Accumulator.value (Balance.accumulator static root rules) claim =
      (if !static root && decide (root = claim) then (1 : Int) else 0) +
        Accumulator.value (rulesLedger static rules) claim := by
  have hflat : (rules.map Prod.fst).flatMap Prod.snd = rules.flatMap fun r => r.1.2 := by
    induction rules with
    | nil => rfl
    | cons r rs ih => simp [ih]
  simp only [Balance.accumulator, Balance.required, rulesLedger, hflat,
    Accumulator.value_append, List.filter_cons]
  cases hs : !static root with
  | false => simp
  | true =>
      change Accumulator.value ((root, (1 : Int)) ::
          Accumulator.requires ((rules.flatMap fun r => r.1.2).filter fun claim => !static claim)) claim +
        Accumulator.value (Accumulator.provides (rules.map fun rule => (rule.1.1, rule.2))) claim = _
      rw [Accumulator.value_cons]
      by_cases hrc : root = claim
      · subst hrc
        simp only [↓reduceIte, decide_true, Bool.and_true]
        ring
      · simp only [hrc, ↓reduceIte, decide_false, Bool.and_false, Bool.false_eq_true, zero_add]

omit [Field F] in
/-- `Balance.accumulator` value at every claim is invariant under permutations of the
weighted rule list (order of rows has zero effect on LogUp balance). -/
theorem balance_accumulator_value_of_perm (static : Message F → Bool) (root : Message F)
    {xs ys : List (RuleClaims (Message F) × Int)} (hperm : xs.Perm ys) (claim : Message F) :
    Accumulator.value (Balance.accumulator static root xs) claim =
      Accumulator.value (Balance.accumulator static root ys) claim := by
  rw [balance_accumulator_value_eq_root_add_rulesLedger,
    balance_accumulator_value_eq_root_add_rulesLedger]
  congr 1
  induction hperm with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
      rw [rulesLedger_value_cons static x l₁, rulesLedger_value_cons static x l₂, ih]
  | swap x y l =>
      rw [rulesLedger_value_cons static y (x :: l), rulesLedger_value_cons static x l,
        rulesLedger_value_cons static x (y :: l), rulesLedger_value_cons static y l]
      ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

omit [Field F] in
theorem balance_accumulator_isZero_of_perm (static : Message F → Bool) (root : Message F)
    {xs ys : List (RuleClaims (Message F) × Int)} (hperm : xs.Perm ys) :
    (Balance.accumulator static root xs).isZero =
      (Balance.accumulator static root ys).isZero := by
  apply Bool.eq_iff_iff.mpr
  rw [Accumulator.isZero_iff, Accumulator.isZero_iff]
  constructor
  · intro h claim
    rw [← balance_accumulator_value_of_perm static root hperm claim]
    exact h claim
  · intro h claim
    rw [balance_accumulator_value_of_perm static root hperm claim]
    exact h claim

/-- **Exact Per-Lane LogUp Sum Decomposition**: the LogUp ledger of a `K`-lane
vectorized row equals the exact sum of its `K` individual lane ledgers (with inactive
lanes `none` contributing `0`). -/
theorem vecRowWeightedRules_ledger_sum (static : Message F → Bool) (orig : Chip F) (K : Nat)
    (row : Row F) (laneMults : List (Option Int)) (claim : Message F) :
    Accumulator.value (rulesLedger static (vecRowWeightedRules orig K row laneMults)) claim =
      ((List.range K).map fun j => laneLedgerValue static orig row (laneMults.getD j none) j claim).sum := by
  unfold vecRowWeightedRules
  suffices ∀ (js : List Nat),
      Accumulator.value (rulesLedger static (js.filterMap fun j =>
        (laneMults.getD j none).map fun m => (laneRuleClaims orig row j, m))) claim =
      (js.map fun j => laneLedgerValue static orig row (laneMults.getD j none) j claim).sum from
    this (List.range K)
  intro js
  induction js with
  | nil => simp [rulesLedger_value_nil]
  | cons j rest ih =>
      simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
      cases hm : laneMults.getD j none with
      | none =>
          simp only [Option.map_none, laneLedgerValue, zero_add]
          exact ih
      | some m =>
          rw [Option.map_some, rulesLedger_value_cons, ih]
          rfl

/-- Uniform outer multiplicity `m` on a vectorized row yields the exact sum of the
active lanes weighted by `m` and inactive lanes contributing `0`. -/
theorem vecRowRules_outer_mult_ledger_sum (static : Message F → Bool) (orig : Chip F) (K : Nat)
    (row : Row F) (laneActive : List Bool) (m : Int) (claim : Message F) :
    Accumulator.value (rulesLedger static ((vecRowRules orig K row laneActive).map fun r => (r, m))) claim =
      ((List.range K).map fun j =>
        laneLedgerValue static orig row ((uniformLaneMults laneActive m).getD j none) j claim).sum := by
  have heq : (vecRowRules orig K row laneActive).map (fun r => (r, m)) =
      vecRowWeightedRules orig K row (uniformLaneMults laneActive m) := by
    unfold vecRowRules vecRowWeightedRules uniformLaneMults
    rw [List.map_filterMap]
    congr 1
    funext j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases hget : laneActive[j]? with
    | none => simp
    | some b => cases b <;> simp
  rw [heq]
  exact vecRowWeightedRules_ledger_sum static orig K row (uniformLaneMults laneActive m) claim

/-! ### Fixed-Width Block Slicing & Packing Helpers -/

theorem length_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (W : Nat)
    (hf : ∀ x ∈ xs, (f x).length = W) :
    (xs.flatMap f).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy))]
      ring

theorem take_drop_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (W : Nat)
    (hf : ∀ x ∈ xs, (f x).length = W) {j : Nat} (hj : j < xs.length) :
    ((xs.flatMap f).drop (j * W)).take W = f xs[j] := by
  induction xs generalizing j with
  | nil => cases hj
  | cons x rest ih =>
      have hx : (f x).length = W := hf x List.mem_cons_self
      cases j with
      | zero =>
          simp only [Nat.zero_mul, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
          rw [← hx, List.take_left]
      | succ j' =>
          have hj' : j' < rest.length := Nat.lt_of_succ_lt_succ hj
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          have hmul : (j' + 1) * W = (f x).length + j' * W := by rw [hx]; ring
          rw [hmul, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append]
          simp only [Nat.add_sub_cancel_left]
          exact ih (fun y hy => hf y (List.mem_cons_of_mem x hy)) hj'

omit [Field F] [DecidableEq F] in
theorem unpackLaneRow_length (origName : String) {W K : Nat} {row : Row F}
    (hlen : row.values.length = K * W) {j : Nat} (hj : j < K) :
    (unpackLaneRow origName W row j).values.length = W := by
  unfold unpackLaneRow
  dsimp only
  rw [List.length_take, List.length_drop, hlen]
  have hbound : j * W + W ≤ K * W := lane_bound_le hj
  omega

omit [DecidableEq F] in
theorem unpackLaneRow_assignment (origName : String) {W : Nat} (row : Row F)
    (j : Nat) {v : Nat} (hv : v < W) :
    (unpackLaneRow origName W row j).assignment v = row.assignment (j * W + v) := by
  unfold unpackLaneRow Row.assignment Scalar.Circuit.Row.assignment
  dsimp only
  rw [List.getElem?_take_of_lt hv, List.getElem?_drop]

theorem unpackLaneRow_agree {orig : Chip F} (hwf : orig.wellFormed = true)
    (row : Row F) (j : Nat) (rom : WireROM F) :
    (orig.ValidAssignment rom (unpackLaneRow orig.name orig.numVars row j).assignment ↔
      orig.ValidAssignment rom (sliceAssign (j * orig.numVars) row.assignment)) ∧
    orig.conclusion (unpackLaneRow orig.name orig.numVars row j).assignment =
      orig.conclusion (sliceAssign (j * orig.numVars) row.assignment) ∧
    orig.requirements (unpackLaneRow orig.name orig.numVars row j).assignment =
      orig.requirements (sliceAssign (j * orig.numVars) row.assignment) := by
  apply orig.agree
  intro v hv
  exact unpackLaneRow_assignment orig.name row j (orig.wellFormed_variables hwf v hv)

/-- **Row-Validity Decomposition (`validRow_vec_iff`)**: a physical row of a verified
`K`-lane vectorized chip `vec` is valid if and only if every one of its `K` lanes
slices to a valid row of `orig`. -/
theorem validRow_vec_iff {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (rom : WireROM F) {row : Row F}
    (hlen : row.values.length = K * orig.numVars) :
    vec.ValidRow rom row ↔ ∀ j < K, orig.ValidRow rom (unpackLaneRow orig.name orig.numVars row j) := by
  have spec := checkVectorize_spec hchk
  constructor
  · intro hvalid j hj
    have hag := unpackLaneRow_agree spec.origWf row j rom
    refine ⟨spec.origWf, unpackLaneRow_length orig.name hlen hj, ?_⟩
    apply hag.1.mpr
    refine ⟨?_, ?_⟩
    · intro p hp
      have hmem : shiftExpr (j * orig.numVars) p ∈ vec.constraints := by
        rw [spec.constraintsEq]
        exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
      simpa [shiftExpr_denote] using hvalid.2.2.1 _ hmem
    · intro m hm
      have hmem : shiftMemory (j * orig.numVars) m ∈ vec.memory := by
        rw [spec.memoryEq]
        exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨m, hm, rfl⟩⟩
      exact (shiftMemory_valid_iff (j * orig.numVars) rom row.assignment m).mp (hvalid.2.2.2 _ hmem)
  · intro hlanes
    refine ⟨spec.vecWf, by rw [spec.numVarsEq, hlen], ?_, ?_⟩
    · intro p hp
      rw [spec.constraintsEq] at hp
      obtain ⟨j, hj, hp'⟩ := List.mem_flatMap.mp hp
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp'
      have hjLt : j < K := List.mem_range.mp hj
      have hag := unpackLaneRow_agree spec.origWf row j rom
      have hsat := (hag.1.mp (hlanes j hjLt).2.2).1 p0 hp0
      simpa [shiftExpr_denote] using hsat
    · intro m hm
      rw [spec.memoryEq] at hm
      obtain ⟨j, hj, hm'⟩ := List.mem_flatMap.mp hm
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm'
      have hjLt : j < K := List.mem_range.mp hj
      have hag := unpackLaneRow_agree spec.origWf row j rom
      have hmv := (hag.1.mp (hlanes j hjLt).2.2).2 m0 hm0
      exact (shiftMemory_valid_iff (j * orig.numVars) rom row.assignment m0).mpr hmv

theorem laneRuleClaims_eq_unpack {orig : Chip F} (hwf : orig.wellFormed = true)
    (row : Row F) (j : Nat) :
    laneRuleClaims orig row j =
      (orig.receive (unpackLaneRow orig.name orig.numVars row j),
       orig.premises (unpackLaneRow orig.name orig.numVars row j)) := by
  have hag := unpackLaneRow_agree hwf row j (⟨[]⟩ : WireROM F)
  unfold laneRuleClaims laneReceive lanePremises laneSends
  congr 1
  · rw [shiftReceive_message, ← hag.2.1]
    rfl
  · rw [List.filterMap_map]
    simp only [Function.comp_def]
    have hreq : (orig.sends.filterMap fun send =>
        if (shiftSend (j * orig.numVars) send).enable.denote row.assignment = 1 then
          some ((shiftSend (j * orig.numVars) send).message row.assignment)
        else none) = orig.requirements (sliceAssign (j * orig.numVars) row.assignment) := by
      unfold Chip.requirements
      apply List.filterMap_congr
      intro s _
      simp [shiftSend_enable_denote, shiftSend_message]
    rw [hreq, ← hag.2.2]
    rfl

theorem vec_premises_eq_flatMap {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (row : Row F) :
    vec.premises row =
      (List.range K).flatMap fun j => orig.premises (unpackLaneRow orig.name orig.numVars row j) := by
  have spec := checkVectorize_spec hchk
  unfold Chip.premises
  rw [spec.sendsEq]
  unfold expectedSends
  rw [List.filterMap_flatMap]
  apply List.flatMap_congr
  intro j _
  have hl := congrArg Prod.snd (laneRuleClaims_eq_unpack spec.origWf row j)
  simpa [laneRuleClaims, lanePremises, laneSends, Chip.premises] using hl

private theorem length_filterMap_le {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.filterMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.filterMap_cons, List.length_cons]
      cases f x with
      | none => simp; omega
      | some _ => simp; omega

/-- **Chip-Level Vectorization Soundness (Unit Multiplicity — `vectorize_chip_sound`)**:
any valid row of a certified `K`-lane vectorized chip `vec` (with per-lane active flags
`laneActive`) unpacks into `≤ K` valid rows of `orig` with identical `RuleClaims` and
identical LogUp `Balance.accumulator`. -/
theorem vectorize_chip_sound {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (rom : WireROM F)
    {row : Row F} (hvalid : vec.ValidRow rom row) (laneActive : List Bool) :
    let unpacked := unpackActiveRows orig.name orig.numVars K row laneActive
    unpacked.length ≤ K ∧
      (∀ r ∈ unpacked, r.chip = orig.name ∧ orig.ValidRow rom r) ∧
      vecRowRules orig K row laneActive =
        unpacked.map (fun r => (orig.receive r, orig.premises r)) ∧
      ∀ (static : Message F → Bool) (root : Message F),
        Balance.accumulator static root ((vecRowRules orig K row laneActive).map (·, 1)) =
          Balance.accumulator static root
            ((unpacked.map (fun r => (orig.receive r, orig.premises r))).map (·, 1)) := by
  have spec := checkVectorize_spec hchk
  have hlen : row.values.length = K * orig.numVars := by rw [← spec.numVarsEq]; exact hvalid.2.1
  have hlanes := (validRow_vec_iff hchk rom hlen).mp hvalid
  dsimp only
  have hrules : vecRowRules orig K row laneActive =
      (unpackActiveRows orig.name orig.numVars K row laneActive).map
        (fun r => (orig.receive r, orig.premises r)) := by
    unfold vecRowRules unpackActiveRows
    rw [List.map_filterMap]
    apply List.filterMap_congr
    intro j _
    cases laneActive.getD j false with
    | false => rfl
    | true =>
        simp only [↓reduceIte, Option.map_some, Option.some.injEq]
        exact laneRuleClaims_eq_unpack spec.origWf row j
  refine ⟨?_, ?_, hrules, fun static root => by rw [hrules]⟩
  · calc (unpackActiveRows orig.name orig.numVars K row laneActive).length
        ≤ (List.range K).length := length_filterMap_le _ _
      _ = K := List.length_range
  · intro r hr
    unfold unpackActiveRows at hr
    obtain ⟨j, hj, hopt⟩ := List.mem_filterMap.mp hr
    have hjLt : j < K := List.mem_range.mp hj
    simp only [List.getD_eq_getElem?_getD] at hopt
    split at hopt
    · cases hopt
      exact ⟨rfl, hlanes j hjLt⟩
    · cases hopt

/-- **Chip-Level Vectorization Soundness (Weighted LogUp / Memo — `vectorize_chip_weighted_sound`)**:
any valid row of `vec` with per-lane integer multiplicities `laneMults : List (Option Int)`
unpacks into `≤ K` valid weighted rows of `orig` with identical weighted `RuleClaims`,
identical `Balance.accumulator`, and ledger equal to the exact sum of the `K` lane ledgers. -/
theorem vectorize_chip_weighted_sound {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (rom : WireROM F)
    {row : Row F} (hvalid : vec.ValidRow rom row) (laneMults : List (Option Int)) :
    let unpacked := unpackWeightedActiveRows orig.name orig.numVars K row laneMults
    unpacked.length ≤ K ∧
      (∀ w ∈ unpacked, w.row.chip = orig.name ∧ orig.ValidRow rom w.row) ∧
      vecRowWeightedRules orig K row laneMults =
        unpacked.map (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)) ∧
      (∀ (static : Message F → Bool) (root : Message F),
        Balance.accumulator static root (vecRowWeightedRules orig K row laneMults) =
          Balance.accumulator static root
            (unpacked.map (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)))) ∧
      (∀ (static : Message F → Bool) (claim : Message F),
        Accumulator.value (rulesLedger static (vecRowWeightedRules orig K row laneMults)) claim =
          ((List.range K).map fun j =>
            laneLedgerValue static orig row (laneMults.getD j none) j claim).sum) := by
  have spec := checkVectorize_spec hchk
  have hlen : row.values.length = K * orig.numVars := by rw [← spec.numVarsEq]; exact hvalid.2.1
  have hlanes := (validRow_vec_iff hchk rom hlen).mp hvalid
  dsimp only
  have hrules : vecRowWeightedRules orig K row laneMults =
      (unpackWeightedActiveRows orig.name orig.numVars K row laneMults).map
        (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)) := by
    unfold vecRowWeightedRules unpackWeightedActiveRows
    rw [List.map_filterMap]
    apply List.filterMap_congr
    intro j _
    cases hm : laneMults.getD j none with
    | none => rfl
    | some m =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        exact laneRuleClaims_eq_unpack spec.origWf row j
  refine ⟨?_, ?_, hrules, fun static root => by rw [hrules],
    fun static claim => vecRowWeightedRules_ledger_sum static orig K row laneMults claim⟩
  · calc (unpackWeightedActiveRows orig.name orig.numVars K row laneMults).length
        ≤ (List.range K).length := length_filterMap_le _ _
      _ = K := List.length_range
  · intro w hw
    unfold unpackWeightedActiveRows at hw
    obtain ⟨j, hj, hopt⟩ := List.mem_filterMap.mp hw
    have hjLt : j < K := List.mem_range.mp hj
    simp only [List.getD_eq_getElem?_getD, Option.map_eq_some_iff] at hopt
    obtain ⟨m, _, rfl⟩ := hopt
    exact ⟨rfl, hlanes j hjLt⟩

private theorem padLaneValues_length {orig : Chip F} {batch : List (Row F)}
    (hlen : ∀ r ∈ batch, r.values.length = orig.numVars) :
    (padLaneValues orig batch).length = orig.numVars := by
  unfold padLaneValues
  split_ifs
  · simp
  · cases batch with
    | nil => simp
    | cons r rest => exact hlen r List.mem_cons_self

private theorem padLaneValues_valid {orig : Chip F} {rom : WireROM F} {batch : List (Row F)}
    (hwf : orig.wellFormed = true)
    (hnonempty : batch ≠ [] ∨ isZeroSilent orig = true)
    (hvalid : ∀ r ∈ batch, orig.ValidRow rom r) :
    orig.ValidRow rom ⟨orig.name, padLaneValues orig batch⟩ := by
  unfold padLaneValues
  by_cases hs : isZeroSilent orig = true
  · simp only [hs, ↓reduceIte]
    exact (zeroRow_valid_of_isZeroSilent hwf hs rom).1
  · simp only [hs]
    cases batch with
    | nil =>
        rcases hnonempty with hne | hsil
        · exact absurd rfl hne
        · exact absurd hsil hs
    | cons r rest =>
        exact hvalid r List.mem_cons_self

theorem packBatchValues_length {orig : Chip F} (K : Nat) {batch : List (Row F)}
    (hlen : ∀ r ∈ batch, r.values.length = orig.numVars) :
    (packBatchValues orig K batch).length = K * orig.numVars := by
  unfold packBatchValues
  have hf : ∀ j ∈ List.range K,
      (match batch[j]? with | some r => r.values | none => padLaneValues orig batch).length =
        orig.numVars := by
    intro j _
    cases hget : batch[j]? with
    | none => exact padLaneValues_length hlen
    | some r => exact hlen r (List.mem_of_getElem? hget)
  simpa using length_flatMap_const (List.range K) _ orig.numVars hf

theorem unpackLaneRow_packBatchRow {orig : Chip F} (K : Nat) (vecName : String)
    {batch : List (Row F)} (hlen : ∀ r ∈ batch, r.values.length = orig.numVars)
    {j : Nat} (hj : j < K) :
    unpackLaneRow orig.name orig.numVars (packBatchRow orig K vecName batch) j =
      match batch[j]? with
      | some r => ⟨orig.name, r.values⟩
      | none => ⟨orig.name, padLaneValues orig batch⟩ := by
  unfold unpackLaneRow packBatchRow packBatchValues
  dsimp only
  have hf : ∀ i ∈ List.range K,
      (match batch[i]? with | some r => r.values | none => padLaneValues orig batch).length =
        orig.numVars := by
    intro i _
    cases hget : batch[i]? with
    | none => exact padLaneValues_length hlen
    | some r => exact hlen r (List.mem_of_getElem? hget)
  have hslice := take_drop_flatMap_const (List.range K)
    (fun i => match batch[i]? with | some r => r.values | none => padLaneValues orig batch)
    orig.numVars hf (j := j) (by simpa using hj)
  simp only [List.getElem_range] at hslice
  rw [hslice]
  cases batch[j]? <;> rfl

private theorem filterMap_range_lt_eq_map {α β : Type} {K : Nat} (batch : List α)
    (hle : batch.length ≤ K) (g : α → β) :
    ((List.range K).filterMap fun j =>
      if (packBatchActive K batch.length).getD j false then
        (batch[j]?).map g
      else none) = batch.map g := by
  apply List.ext_getElem?
  have haux : ∀ (m : Nat), m ≤ K →
      ((List.range m).filterMap fun j =>
        if decide (j < batch.length) then (batch[j]?).map g else none) =
      (batch.take m).map g := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.filterMap_append, ih (by omega)]
        simp only [List.filterMap_cons, List.filterMap_nil]
        by_cases hlt : m < batch.length
        · simp only [hlt, decide_true, ↓reduceIte, List.getElem?_eq_getElem hlt, Option.map_some]
          rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.map_singleton]
        · have hge : batch.length ≤ m := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [List.take_of_length_le hge, List.take_of_length_le (by omega)]
  have hcongr : ((List.range K).filterMap fun j =>
      if (packBatchActive K batch.length).getD j false then (batch[j]?).map g else none) =
      ((List.range K).filterMap fun j =>
        if decide (j < batch.length) then (batch[j]?).map g else none) := by
    apply List.filterMap_congr
    intro j hj
    have hjLt : j < K := List.mem_range.mp hj
    simp [packBatchActive, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hjLt]
  rw [hcongr, haux K le_rfl, List.take_of_length_le hle]
  intro i
  rfl

/-- **Chip-Level Vectorization Completeness (`vectorize_chip_complete`)**:
any batch of `≤ K` valid rows of `orig` (with tail padding lanes inactive) packs into
1 valid row of a certified `K`-lane vectorized chip `vec` with identical `RuleClaims`
and identical LogUp `Balance.accumulator`. -/
theorem vectorize_chip_complete {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (rom : WireROM F)
    {batch : List (Row F)} (hle : batch.length ≤ K)
    (hnonempty : batch ≠ [] ∨ isZeroSilent orig = true)
    (hvalid : ∀ r ∈ batch, orig.ValidRow rom r) :
    let packed := packBatchRow orig K vec.name batch
    let active := packBatchActive K batch.length
    packed.chip = vec.name ∧
      active.length = K ∧
      vec.ValidRow rom packed ∧
      vecRowRules orig K packed active =
        batch.map (fun r => (orig.receive r, orig.premises r)) ∧
      ∀ (static : Message F → Bool) (root : Message F),
        Balance.accumulator static root ((vecRowRules orig K packed active).map (·, 1)) =
          Balance.accumulator static root
            ((batch.map (fun r => (orig.receive r, orig.premises r))).map (·, 1)) := by
  have spec := checkVectorize_spec hchk
  have hlens : ∀ r ∈ batch, r.values.length = orig.numVars := fun r hr => (hvalid r hr).2.1
  have hpackLen : (packBatchRow orig K vec.name batch).values.length = K * orig.numVars :=
    packBatchValues_length K hlens
  have hpackValid : vec.ValidRow rom (packBatchRow orig K vec.name batch) := by
    apply (validRow_vec_iff hchk rom hpackLen).mpr
    intro j hj
    rw [unpackLaneRow_packBatchRow K vec.name hlens hj]
    cases hget : batch[j]? with
    | none => exact padLaneValues_valid spec.origWf hnonempty hvalid
    | some r => exact hvalid r (List.mem_of_getElem? hget)
  have hrules : vecRowRules orig K (packBatchRow orig K vec.name batch)
      (packBatchActive K batch.length) =
      batch.map (fun r => (orig.receive r, orig.premises r)) := by
    have h1 : vecRowRules orig K (packBatchRow orig K vec.name batch)
        (packBatchActive K batch.length) =
        (List.range K).filterMap fun j =>
          if (packBatchActive K batch.length).getD j false then
            (batch[j]?).map fun r => (orig.receive r, orig.premises r)
          else none := by
      unfold vecRowRules
      apply List.filterMap_congr
      intro j hj
      have hjLt : j < K := List.mem_range.mp hj
      have hact : (packBatchActive K batch.length).getD j false = decide (j < batch.length) := by
        simp [packBatchActive, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hjLt]
      rw [hact]
      by_cases hjb : j < batch.length
      · simp only [hjb, decide_true, ↓reduceIte, List.getElem?_eq_getElem hjb, Option.map_some,
          Option.some.injEq]
        rw [laneRuleClaims_eq_unpack spec.origWf _ j,
          unpackLaneRow_packBatchRow K vec.name hlens hjLt, List.getElem?_eq_getElem hjb]
        rfl
      · simp [hjb]
    rw [h1]
    exact filterMap_range_lt_eq_map batch hle (fun r => (orig.receive r, orig.premises r))
  refine ⟨rfl, by simp [packBatchActive], hpackValid, hrules, fun static root => by rw [hrules]⟩

/-- **Zero-Silent Tail-Padding Corollary (`vectorize_chip_complete_zeroSilent`)**:
when `isZeroSilent orig = true` (including every `Activation.compile` chip and every
selector-gated chip), ANY batch of `≤ K` valid rows (even empty!) packs into 1 valid
row of `vec` whose unused tail lanes are literally all zeros (`List.replicate W 0`)
and whose raw unmasked `vec.premises` equals `batch.flatMap orig.premises`! -/
theorem vectorize_chip_complete_zeroSilent {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (hsilent : isZeroSilent orig = true)
    (rom : WireROM F) {batch : List (Row F)} (hle : batch.length ≤ K)
    (hvalid : ∀ r ∈ batch, orig.ValidRow rom r) :
    let packed := packBatchRow orig K vec.name batch
    let active := packBatchActive K batch.length
    vec.ValidRow rom packed ∧
      (∀ j, batch.length ≤ j → j < K →
        (unpackLaneRow orig.name orig.numVars packed j).values =
          List.replicate orig.numVars 0) ∧
      vec.premises packed = batch.flatMap orig.premises ∧
      vecRowRules orig K packed active =
        batch.map (fun r => (orig.receive r, orig.premises r)) := by
  have spec := checkVectorize_spec hchk
  have hlens : ∀ r ∈ batch, r.values.length = orig.numVars := fun r hr => (hvalid r hr).2.1
  have hcomp := vectorize_chip_complete hchk rom hle (Or.inr hsilent) hvalid
  refine ⟨hcomp.2.2.1, ?_, ?_, hcomp.2.2.2.1⟩
  · intro j hge hj
    rw [unpackLaneRow_packBatchRow K vec.name hlens hj, List.getElem?_eq_none hge]
    simp [padLaneValues, hsilent]
  · rw [vec_premises_eq_flatMap hchk]
    have hzeroPrem : orig.premises ⟨orig.name, List.replicate orig.numVars 0⟩ = [] :=
      (zeroRow_valid_of_isZeroSilent spec.origWf hsilent rom).2
    have haux : ∀ (m : Nat), m ≤ K →
        ((List.range m).flatMap fun j =>
          orig.premises (unpackLaneRow orig.name orig.numVars
            (packBatchRow orig K vec.name batch) j)) =
        (batch.take m).flatMap orig.premises := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
          rw [List.range_succ, List.flatMap_append, ih (by omega), List.flatMap_singleton]
          rw [unpackLaneRow_packBatchRow K vec.name hlens (by omega)]
          by_cases hlt : m < batch.length
          · rw [List.getElem?_eq_getElem hlt, List.take_succ_eq_append_getElem hlt,
              List.flatMap_append, List.flatMap_singleton]
            rfl
          · have hge : batch.length ≤ m := Nat.le_of_not_lt hlt
            rw [List.getElem?_eq_none hge]
            simp only [padLaneValues, hsilent, ↓reduceIte, hzeroPrem, List.append_nil]
            rw [List.take_of_length_le hge, List.take_of_length_le (by omega)]
    rw [haux K le_rfl, List.take_of_length_le hle]

/-- **Chip-Level Weighted Vectorization Completeness (`vectorize_chip_weighted_complete`)**:
any batch of `≤ K` valid weighted rows of `orig` packs into 1 valid row of `vec` with
per-lane multiplicities `packWeightedBatchMults K batch`, preserving exact weighted
`RuleClaims` and exact LogUp `Balance.accumulator`. -/
theorem vectorize_chip_weighted_complete {orig vec : Chip F} {K : Nat}
    (hchk : checkVectorize orig vec K = true) (rom : WireROM F)
    {batch : List (WeightedRow F)} (hle : batch.length ≤ K)
    (hnonempty : batch ≠ [] ∨ isZeroSilent orig = true)
    (hvalid : ∀ w ∈ batch, orig.ValidRow rom w.row) :
    let packed := packWeightedBatchRow orig K vec.name batch
    let mults := packWeightedBatchMults K batch
    packed.chip = vec.name ∧
      mults.length = K ∧
      vec.ValidRow rom packed ∧
      vecRowWeightedRules orig K packed mults =
        batch.map (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)) ∧
      ∀ (static : Message F → Bool) (root : Message F),
        Balance.accumulator static root (vecRowWeightedRules orig K packed mults) =
          Balance.accumulator static root
            (batch.map (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity))) := by
  have spec := checkVectorize_spec hchk
  have hrowsValid : ∀ r ∈ batch.map WeightedRow.row, orig.ValidRow rom r := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hvalid w hw
  have hrowsNe : batch.map WeightedRow.row ≠ [] ∨ isZeroSilent orig = true := by
    rcases hnonempty with hne | hs
    · exact Or.inl (by simp [hne])
    · exact Or.inr hs
  have hlens : ∀ r ∈ batch.map WeightedRow.row, r.values.length = orig.numVars :=
    fun r hr => (hrowsValid r hr).2.1
  have hbase := vectorize_chip_complete hchk rom (by simpa using hle) hrowsNe hrowsValid
  have hrules : vecRowWeightedRules orig K (packWeightedBatchRow orig K vec.name batch)
      (packWeightedBatchMults K batch) =
      batch.map (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)) := by
    have h1 : vecRowWeightedRules orig K (packWeightedBatchRow orig K vec.name batch)
        (packWeightedBatchMults K batch) =
        (List.range K).filterMap fun j =>
          if (packBatchActive K batch.length).getD j false then
            (batch[j]?).map fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity)
          else none := by
      unfold vecRowWeightedRules
      apply List.filterMap_congr
      intro j hj
      have hjLt : j < K := List.mem_range.mp hj
      have hact : (packBatchActive K batch.length).getD j false = decide (j < batch.length) := by
        simp [packBatchActive, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hjLt]
      have hmult : (packWeightedBatchMults K batch).getD j none =
          (batch[j]?).map WeightedRow.multiplicity := by
        simp [packWeightedBatchMults, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hjLt]
      rw [hact, hmult]
      by_cases hjb : j < batch.length
      · simp only [hjb, decide_true, ↓reduceIte, List.getElem?_eq_getElem hjb, Option.map_some,
          Option.some.injEq, Prod.mk.injEq, and_true]
        rw [laneRuleClaims_eq_unpack spec.origWf _ j]
        unfold packWeightedBatchRow
        rw [unpackLaneRow_packBatchRow K vec.name hlens hjLt]
        simp only [List.getElem?_map, List.getElem?_eq_getElem hjb, Option.map_some]
        rfl
      · simp [hjb]
    rw [h1]
    exact filterMap_range_lt_eq_map batch hle
      (fun w => ((orig.receive w.row, orig.premises w.row), w.multiplicity))
  refine ⟨rfl, by simp [packWeightedBatchMults], hbase.2.2.1, hrules,
    fun static root => by rw [hrules]⟩

end ChipTheorems

/-! ## 4. Chunking (`⌈N / K⌉` Exact Row Bound) & System-Level Vectorization (`VectorizedSystem`) -/

section Chunking

/-- Split a list into consecutive non-empty chunks of size `k' + 1` (last chunk `≤ k' + 1`). -/
def chunkListSucc {α : Type} (k' : Nat) : List α → List (List α)
  | [] => []
  | x :: rest => (x :: rest.take k') :: chunkListSucc k' (rest.drop k')
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- Split a list into consecutive non-empty chunks of size `K` (returning `[]` when `K = 0`). -/
def chunkList {α : Type} (K : Nat) (xs : List α) : List (List α) :=
  match K with
  | 0 => []
  | k' + 1 => chunkListSucc k' xs

theorem chunkListSucc_flatten {α : Type} (k' : Nat) (xs : List α) :
    (chunkListSucc k' xs).flatten = xs := by
  match xs with
  | [] => simp [chunkListSucc]
  | x :: rest =>
      rw [chunkListSucc]
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq, true_and]
      rw [chunkListSucc_flatten k' (rest.drop k'), List.take_append_drop]
termination_by xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

theorem chunkList_flatten {α : Type} {K : Nat} (hK : 1 ≤ K) (xs : List α) :
    (chunkList K xs).flatten = xs := by
  cases K with
  | zero => omega
  | succ k' => exact chunkListSucc_flatten k' xs

theorem chunkListSucc_mem_bounds {α : Type} (k' : Nat) (xs : List α) :
    ∀ c ∈ chunkListSucc k' xs, 1 ≤ c.length ∧ c.length ≤ k' + 1 := by
  match xs with
  | [] => intro _ hc; simp [chunkListSucc] at hc
  | x :: rest =>
      intro c hc
      rw [chunkListSucc] at hc
      rcases List.mem_cons.mp hc with rfl | htail
      · simp only [List.length_cons, List.length_take]
        omega
      · exact chunkListSucc_mem_bounds k' (rest.drop k') c htail
termination_by xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

theorem chunkList_mem_bounds {α : Type} {K : Nat} (hK : 1 ≤ K) {xs : List α} {c : List α}
    (hc : c ∈ chunkList K xs) : 1 ≤ c.length ∧ c.length ≤ K := by
  cases K with
  | zero => omega
  | succ k' => exact chunkListSucc_mem_bounds k' xs c hc

theorem chunkListSucc_length {α : Type} (k' : Nat) (xs : List α) :
    (chunkListSucc k' xs).length = (xs.length + k') / (k' + 1) := by
  match xs with
  | [] =>
      simp only [chunkListSucc, List.length_nil, Nat.zero_add]
      exact (Nat.div_eq_of_lt (Nat.lt_succ_self k')).symm
  | x :: rest =>
      rw [chunkListSucc]
      simp only [List.length_cons]
      rw [chunkListSucc_length k' (rest.drop k'), List.length_drop]
      by_cases hle : rest.length ≤ k'
      · have h0 : rest.length - k' = 0 := Nat.sub_eq_zero_of_le hle
        rw [h0, Nat.zero_add, Nat.div_eq_of_lt (Nat.lt_succ_self k')]
        have h1 : (rest.length + 1 + k') / (k' + 1) = 1 := by
          rw [show rest.length + 1 + k' = rest.length + (k' + 1) by omega,
            Nat.add_div_right _ (Nat.succ_pos k'), Nat.div_eq_of_lt (by omega)]
        omega
      · have hgt : k' < rest.length := Nat.lt_of_not_ge hle
        have hsub : rest.length - k' + k' = rest.length := Nat.sub_add_cancel (Nat.le_of_lt hgt)
        rw [hsub]
        have heq : rest.length + 1 + k' = rest.length + (k' + 1) := by omega
        rw [heq, Nat.add_div_right _ (Nat.succ_pos k')]
termination_by xs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- Exact ceiling-division chunk count: `(chunkList K xs).length = (xs.length + K - 1) / K`. -/
theorem chunkList_length {α : Type} {K : Nat} (hK : 1 ≤ K) (xs : List α) :
    (chunkList K xs).length = (xs.length + K - 1) / K := by
  cases K with
  | zero => omega
  | succ k' =>
      simpa [chunkList, show xs.length + (k' + 1) - 1 = xs.length + k' by omega] using
        chunkListSucc_length k' xs

/-- Partitioning a list by a `Nodup` set of keys produces a permutation of the original list. -/
theorem perm_filter_partition {α : Type} (key : α → String) :
    ∀ (keys : List String), keys.Nodup → ∀ (xs : List α),
      ((xs.filter fun x => !keys.contains (key x)) ++
        keys.flatMap (fun k => xs.filter fun x => key x == k)).Perm xs
  | [], _, xs => by
      simp
  | k :: ks, hnd, xs => by
      rw [List.nodup_cons] at hnd
      have hsplit : ∀ (ys : List α) (p : α → Bool),
          (ys.filter (fun y => !p y) ++ ys.filter p).Perm ys := by
        intro ys p
        induction ys with
        | nil => simp
        | cons y ys ih =>
            cases hp : p y with
            | false =>
                simp only [List.filter_cons, hp, Bool.not_false, ↓reduceIte, Bool.false_eq_true,
                  List.cons_append]
                exact ih.cons y
            | true =>
                simp only [List.filter_cons, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact (List.perm_middle (l₁ := ys.filter fun y => !p y)
                  (l₂ := ys.filter p) (a := y)).trans (ih.cons y)
      have hnotk : (xs.filter fun x => !(k :: ks).contains (key x)) =
          (xs.filter fun x => !ks.contains (key x)).filter (fun x => !(key x == k)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases hxk : key x = k
        · subst hxk; simp
        · simp [hxk, beq_false_of_ne hxk]
      have hisk : (xs.filter fun x => key x == k) =
          (xs.filter fun x => !ks.contains (key x)).filter (fun x => key x == k) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases hxk : key x = k
        · subst hxk
          simp [hnd.1]
        · have hbf : (key x == k) = false := beq_false_of_ne hxk
          simp [hbf]
      rw [List.flatMap_cons, ← List.append_assoc, hnotk, hisk]
      have hp1 : ((xs.filter fun x => !ks.contains (key x)).filter (fun x => !(key x == k)) ++
          (xs.filter fun x => !ks.contains (key x)).filter (fun x => key x == k)).Perm
          (xs.filter fun x => !ks.contains (key x)) :=
        hsplit _ (fun x => key x == k)
      exact (hp1.append_right _).trans (perm_filter_partition key ks hnd.2 xs)

end Chunking

section SystemVectorize

variable {F : Type} [Field F] [DecidableEq F]

/-- A certified entry vectorizing source chip `orig` into `K`-lane chip `vec`. -/
structure VectorizedChipEntry (F : Type) where
  orig : Chip F
  vec : Chip F
  lanes : Nat
  receives : List (LaneReceive F)
  deriving Repr, BEq

/-- Construct a certified `VectorizedChipEntry`, failing closed unless `1 ≤ K`,
`orig.wellFormed`, and `checkVectorizeReceives` succeeds. -/
def vectorizeChipEntry (orig : Chip F) (K : Nat)
    (vecName : String := orig.name ++ s!"#vec{K}") : Option (VectorizedChipEntry F) :=
  let vec := vectorizeChip orig K vecName
  let receives := laneReceives orig K
  if checkVectorizeReceives orig vec receives K then
    some ⟨orig, vec, K, receives⟩
  else
    none

/-- A certified vectorized circuit system: every chip in `source` is either kept
unchanged in `unvectorized` or horizontally vectorized in `vectorized`. -/
structure VectorizedSystem (F : Type) where
  source : Circuit.System F
  unvectorized : List (Chip F)
  vectorized : List (VectorizedChipEntry F)
  deriving Repr, BEq

/-- All physical chips in a `VectorizedSystem`. -/
def VectorizedSystem.physicalChips (sys : VectorizedSystem F) : List (Chip F) :=
  sys.unvectorized ++ sys.vectorized.map (·.vec)

/-- Structural validity certificate for a `VectorizedSystem`. -/
def VectorizedSystem.checkValid (sys : VectorizedSystem F) : Bool :=
  (match checkChips [] sys.source.chips with | .ok () => true | .error _ => false) &&
    (match checkChips [] sys.physicalChips with | .ok () => true | .error _ => false) &&
    decide ((sys.vectorized.map (·.orig.name)).Nodup) &&
    sys.unvectorized.all (fun c =>
      decide (sys.source.findChip? c.name = some c) &&
        !(sys.vectorized.any fun e => e.orig.name == c.name)) &&
    sys.vectorized.all (fun e =>
      decide (sys.source.findChip? e.orig.name = some e.orig) &&
        checkVectorizeReceives e.orig e.vec e.receives e.lanes) &&
    sys.source.chips.all (fun c =>
      sys.unvectorized.any (fun u => decide (u = c)) ||
        sys.vectorized.any (fun e => decide (e.orig = c)))

/-- A physical row in a unit-multiplicity vectorized trace:
* `.unvec row`: a single row of an unvectorized chip in `sys.unvectorized`.
* `.vec row laneActive`: a single `K`-lane physical row of a vectorized chip with
  per-lane boolean activity flags `laneActive` (length `K`; `false` = unused tail lane). -/
inductive VecTraceRow (F : Type) where
  | unvec (row : Row F)
  | vec (row : Row F) (laneActive : List Bool)
  deriving Repr, BEq

/-- A physical row in a weighted/memoized LogUp vectorized trace:
* `.unvec row`: a single weighted row of an unvectorized chip.
* `.vec row laneMults`: a single `K`-lane physical row of a vectorized chip with
  per-lane multiplicities `laneMults : List (Option Int)` (length `K`; `none` = inactive
  tail lane `sel_j = 0`, `some m_j` = active lane with integer provide weight `m_j`). -/
inductive WeightedVecTraceRow (F : Type) where
  | unvec (row : WeightedRow F)
  | vec (row : Row F) (laneMults : List (Option Int))
  deriving Repr, BEq

/-- Inspect one physical row of a `VectorizedSystem` (unit trace), returning its
active logical `(receive, premises)` rule claims (`1` for `.unvec`, `≤ K` for `.vec`). -/
def VectorizedSystem.inspectRow (sys : VectorizedSystem F) (rom : WireROM F) :
    VecTraceRow F → Except WitnessError (List (RuleClaims (Message F)))
  | .unvec row => do
      let some chip := sys.unvectorized.find? (·.name == row.chip)
        | throw (.unknownChip row.chip)
      let claims ← chip.checkRow rom row
      return [claims]
  | .vec row laneActive => do
      let some entry := sys.vectorized.find? (·.vec.name == row.chip)
        | throw (.unknownChip row.chip)
      if laneActive.length != entry.lanes then
        throw (.wrongRowSize row.chip entry.lanes laneActive.length)
      let _ ← entry.vec.checkRow rom row
      return vecRowRules entry.orig entry.lanes row laneActive

def VectorizedSystem.inspectRows (sys : VectorizedSystem F) (rom : WireROM F)
    (rows : List (VecTraceRow F)) : Except WitnessError (List (RuleClaims (Message F))) := do
  let groups ← rows.mapM (sys.inspectRow rom)
  return groups.flatten

/-- Inspect one weighted physical row of a `VectorizedSystem` (memo LogUp trace). -/
def VectorizedSystem.inspectWeightedRow (sys : VectorizedSystem F) (rom : WireROM F) :
    WeightedVecTraceRow F → Except WitnessError (List (RuleClaims (Message F) × Int))
  | .unvec wrow => do
      let some chip := sys.unvectorized.find? (·.name == wrow.row.chip)
        | throw (.unknownChip wrow.row.chip)
      let claims ← chip.checkRow rom wrow.row
      return [(claims, wrow.multiplicity)]
  | .vec row laneMults => do
      let some entry := sys.vectorized.find? (·.vec.name == row.chip)
        | throw (.unknownChip row.chip)
      if laneMults.length != entry.lanes then
        throw (.wrongRowSize row.chip entry.lanes laneMults.length)
      let _ ← entry.vec.checkRow rom row
      return vecRowWeightedRules entry.orig entry.lanes row laneMults

def VectorizedSystem.inspectWeightedRows (sys : VectorizedSystem F) (rom : WireROM F)
    (rows : List (WeightedVecTraceRow F)) :
    Except WitnessError (List (RuleClaims (Message F) × Int)) := do
  let groups ← rows.mapM (sys.inspectWeightedRow rom)
  return groups.flatten

/-- Unit-multiplicity LogUp trace checker for a `VectorizedSystem`. -/
def VectorizedSystem.check (sys : VectorizedSystem F) (rom : WireROM F)
    (entry : Message F) (rows : List (VecTraceRow F)) : Except WitnessError Unit := do
  sys.source.checkContext rom entry
  checkChips [] sys.physicalChips
  let rules ← sys.inspectRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
    (rules.map fun rule => (rule, 1))
  if ledger.isZero then pure () else throw .unbalancedMessages

/-- Weighted/memoized LogUp trace checker for a `VectorizedSystem`. -/
def VectorizedSystem.checkMemo (sys : VectorizedSystem F) (rom : WireROM F)
    (entry : Message F) (rows : List (WeightedVecTraceRow F)) : Except WitnessError Unit := do
  sys.source.checkContext rom entry
  checkChips [] sys.physicalChips
  let rules ← sys.inspectWeightedRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry rules
  if ledger.isZero then pure () else throw .unbalancedMessages

/-- Unpack one vectorized trace row back into its active `sys.source` rows (`1` or `≤ K`). -/
def VectorizedSystem.liftTraceRowToSource (sys : VectorizedSystem F) :
    VecTraceRow F → List (Row F)
  | .unvec row => [row]
  | .vec row laneActive =>
      match sys.vectorized.find? (·.vec.name == row.chip) with
      | some e => unpackActiveRows e.orig.name e.orig.numVars e.lanes row laneActive
      | none => []

/-- Unpack an entire vectorized trace back to `sys.source`. -/
def VectorizedSystem.liftRowsToSource (sys : VectorizedSystem F)
    (rows : List (VecTraceRow F)) : List (Row F) :=
  rows.flatMap sys.liftTraceRowToSource

/-- Unpack one weighted vectorized trace row back into its active weighted `sys.source` rows. -/
def VectorizedSystem.liftWeightedTraceRowToSource (sys : VectorizedSystem F) :
    WeightedVecTraceRow F → List (WeightedRow F)
  | .unvec wrow => [wrow]
  | .vec row laneMults =>
      match sys.vectorized.find? (·.vec.name == row.chip) with
      | some e => unpackWeightedActiveRows e.orig.name e.orig.numVars e.lanes row laneMults
      | none => []

/-- Unpack an entire weighted vectorized trace back to `sys.source`. -/
def VectorizedSystem.liftWeightedRowsToSource (sys : VectorizedSystem F)
    (rows : List (WeightedVecTraceRow F)) : List (WeightedRow F) :=
  rows.flatMap sys.liftWeightedTraceRowToSource

/-- Prover packing: pack all rows of each vectorized chip `e` in `rows` into
`⌈N_e / e.lanes⌉` horizontal `K`-lane rows (keeping unvectorized chip rows 1-to-1). -/
def VectorizedSystem.packRowsFromSource (sys : VectorizedSystem F)
    (rows : List (Row F)) : List (VecTraceRow F) :=
  let vecNames := sys.vectorized.map (·.orig.name)
  let unvecRows := (rows.filter fun r => !vecNames.contains r.chip).map VecTraceRow.unvec
  let vecRows := sys.vectorized.flatMap fun e =>
    let chipRows := rows.filter (·.chip == e.orig.name)
    (chunkList e.lanes chipRows).map fun batch =>
      .vec (packBatchRow e.orig e.lanes e.vec.name batch) (packBatchActive e.lanes batch.length)
  unvecRows ++ vecRows

/-- Prover packing for weighted/memoized traces: pack all weighted rows of each
vectorized chip `e` into `⌈N_e / e.lanes⌉` horizontal `K`-lane rows. -/
def VectorizedSystem.packWeightedRowsFromSource (sys : VectorizedSystem F)
    (rows : List (WeightedRow F)) : List (WeightedVecTraceRow F) :=
  let vecNames := sys.vectorized.map (·.orig.name)
  let unvecRows := (rows.filter fun w => !vecNames.contains w.row.chip).map WeightedVecTraceRow.unvec
  let vecRows := sys.vectorized.flatMap fun e =>
    let chipRows := rows.filter (·.row.chip == e.orig.name)
    (chunkList e.lanes chipRows).map fun batch =>
      .vec (packWeightedBatchRow e.orig e.lanes e.vec.name batch) (packWeightedBatchMults e.lanes batch)
  unvecRows ++ vecRows

/-- Count of source rows belonging to `chipName`. -/
def sourceRowCount (chipName : String) (rows : List (Row F)) : Nat :=
  (rows.filter (·.chip == chipName)).length

/-- Count of weighted source rows belonging to `chipName`. -/
def weightedSourceRowCount (chipName : String) (rows : List (WeightedRow F)) : Nat :=
  (rows.filter (·.row.chip == chipName)).length

/-- Count of vectorized `.vec` rows belonging to `vecName`. -/
def vecRowCount (vecName : String) (rows : List (VecTraceRow F)) : Nat :=
  (rows.filter fun
    | .vec r _ => r.chip == vecName
    | .unvec _ => false).length

/-- Count of weighted vectorized `.vec` rows belonging to `vecName`. -/
def weightedVecRowCount (vecName : String) (rows : List (WeightedVecTraceRow F)) : Nat :=
  (rows.filter fun
    | .vec r _ => r.chip == vecName
    | .unvec _ => false).length

/-- Build a certified `VectorizedSystem` by vectorizing every `(chipName, K)` target
in `targets`, failing closed if any chip is missing, `K = 0`, or `checkValid` fails. -/
def vectorizeSystem (source : Circuit.System F) (targets : List (String × Nat)) :
    Option (VectorizedSystem F) := do
  let vecEntries ← targets.mapM fun (name, K) => do
    let orig ← source.findChip? name
    vectorizeChipEntry orig K
  let vecNames := vecEntries.map (·.orig.name)
  let unvec := source.chips.filter fun c => !vecNames.contains c.name
  let sys : VectorizedSystem F := ⟨source, unvec, vecEntries⟩
  if sys.checkValid then some sys else none

/-! ### Internal Helpers for `VectorizedSystem` Soundness & Completeness -/

private theorem find?_eq_some_of_nodup_map {α : Type} (key : α → String)
    {xs : List α} (hnodup : (xs.map key).Nodup) {x : α} (hmem : x ∈ xs) :
    xs.find? (fun y => key y == key x) = some x := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp
      · have hne : key y ≠ key x := fun heq =>
          hnodup.1 (List.mem_map.mpr ⟨x, htail, heq.symm⟩)
        have hbeq : (key y == key x) = false := beq_false_of_ne hne
        simp only [List.find?_cons, hbeq]
        exact ih hnodup.2 htail

omit [Field F] in
private theorem VectorizedSystem.checkChips_physical {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) :
    checkChips [] sys.physicalChips = .ok () := by
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true] at hvalid
  have hp := hvalid.1.1.1.1.2
  cases hchk : checkChips [] sys.physicalChips with
  | error _ => simp [hchk] at hp
  | ok u => cases u; rfl

omit [Field F] in
private theorem VectorizedSystem.physicalNames_nodup {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) :
    (sys.physicalChips.map Chip.name).Nodup :=
  (checkChips_iff.mp (sys.checkChips_physical hvalid)).1

omit [Field F] in
private theorem VectorizedSystem.unvecNames_nodup {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) :
    (sys.unvectorized.map Chip.name).Nodup := by
  have hnd := sys.physicalNames_nodup hvalid
  simp only [VectorizedSystem.physicalChips, List.map_append] at hnd
  exact (List.nodup_append.mp hnd).1

omit [Field F] in
private theorem VectorizedSystem.vecNames_nodup {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) :
    (sys.vectorized.map (fun e => e.vec.name)).Nodup := by
  have hnd := sys.physicalNames_nodup hvalid
  simp only [VectorizedSystem.physicalChips, List.map_append, List.map_map, Function.comp_def] at hnd
  exact (List.nodup_append.mp hnd).2.1

omit [Field F] in
private theorem VectorizedSystem.origNames_nodup {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) :
    (sys.vectorized.map (·.orig.name)).Nodup := by
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  exact hvalid.1.1.1.2

omit [Field F] in
private theorem VectorizedSystem.findUnvec_of_mem {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {c : Chip F} (hmem : c ∈ sys.unvectorized) :
    sys.unvectorized.find? (·.name == c.name) = some c :=
  find?_eq_some_of_nodup_map Chip.name (sys.unvecNames_nodup hvalid) hmem

omit [Field F] in
private theorem VectorizedSystem.findVec_of_mem {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {e : VectorizedChipEntry F} (hmem : e ∈ sys.vectorized) :
    sys.vectorized.find? (·.vec.name == e.vec.name) = some e :=
  find?_eq_some_of_nodup_map (fun e => e.vec.name) (sys.vecNames_nodup hvalid) hmem

private theorem VectorizedSystem.inspectRow_lift {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {trow : VecTraceRow F}
    {rules : List (RuleClaims (Message F))}
    (hinsp : sys.inspectRow rom trow = .ok rules) :
    sys.source.inspectRows rom (sys.liftTraceRowToSource trow) = .ok rules := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hvalid'
  cases trow with
  | unvec row =>
      unfold VectorizedSystem.inspectRow at hinsp
      cases hfind : sys.unvectorized.find? (·.name == row.chip) with
      | none => simp [hfind] at hinsp
      | some chip =>
          simp only [hfind] at hinsp
          obtain ⟨claim, hchk, hret⟩ := except_bind_ok.mp hinsp
          obtain rfl := except_pure_ok.mp hret
          have hmem := List.mem_of_find?_eq_some hfind
          have hname : chip.name = row.chip :=
            beq_iff_eq.mp (List.find?_some (p := fun (c : Chip F) => c.name == row.chip) hfind)
          have hsrcFind : sys.source.findChip? row.chip = some chip := by
            rw [← hname]
            exact (hvalid'.1.1.2 chip hmem).1
          obtain ⟨hval, rfl⟩ := Chip.checkRow_iff.mp hchk
          simp only [VectorizedSystem.liftTraceRowToSource, System.inspectRows, List.mapM_cons,
            List.mapM_nil]
          have h1 : sys.source.inspectRow rom row = .ok (chip.receive row, chip.premises row) :=
            System.inspectRow_iff.mpr ⟨chip, hsrcFind, hval, rfl⟩
          rw [h1]
          rfl
  | vec row laneActive =>
      unfold VectorizedSystem.inspectRow at hinsp
      cases hfind : sys.vectorized.find? (·.vec.name == row.chip) with
      | none => simp [hfind] at hinsp
      | some e =>
          simp only [hfind] at hinsp
          by_cases hlen : (laneActive.length != e.lanes) = true
          · simp [hlen, bind, Except.bind] at hinsp
          · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hinsp
            obtain ⟨_, hchk, hret⟩ := except_bind_ok.mp hinsp
            obtain rfl := except_pure_ok.mp hret
            have heMem := List.mem_of_find?_eq_some hfind
            have heValid := hvalid'.1.2 e heMem
            have hsrcFind : sys.source.findChip? e.orig.name = some e.orig := heValid.1
            have hvecChk : checkVectorize e.orig e.vec e.lanes = true :=
              ((Bool.and_eq_true _ _).mp heValid.2).1
            obtain ⟨hval, _⟩ := Chip.checkRow_iff.mp hchk
            obtain ⟨_, hrowsVal, hrulesEq, _⟩ :=
              vectorize_chip_sound hvecChk rom hval laneActive
            simp only [VectorizedSystem.liftTraceRowToSource, hfind]
            rw [hrulesEq]
            unfold System.inspectRows
            apply mapM_ok_iff.mpr
            rw [List.forall₂_map_right_iff]
            apply List.forall₂_same.mpr
            intro r hr
            obtain ⟨hchip, hrVal⟩ := hrowsVal r hr
            exact System.inspectRow_iff.mpr ⟨e.orig, by simpa [hchip] using hsrcFind, hrVal, rfl⟩

private theorem VectorizedSystem.inspectWeightedRow_lift {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {trow : WeightedVecTraceRow F}
    {rules : List (RuleClaims (Message F) × Int)}
    (hinsp : sys.inspectWeightedRow rom trow = .ok rules) :
    sys.source.inspectWeightedRows rom (sys.liftWeightedTraceRowToSource trow) = .ok rules := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hvalid'
  cases trow with
  | unvec wrow =>
      unfold VectorizedSystem.inspectWeightedRow at hinsp
      cases hfind : sys.unvectorized.find? (·.name == wrow.row.chip) with
      | none => simp [hfind] at hinsp
      | some chip =>
          simp only [hfind] at hinsp
          obtain ⟨claim, hchk, hret⟩ := except_bind_ok.mp hinsp
          obtain rfl := except_pure_ok.mp hret
          have hmem := List.mem_of_find?_eq_some hfind
          have hname : chip.name = wrow.row.chip :=
            beq_iff_eq.mp (List.find?_some (p := fun (c : Chip F) => c.name == wrow.row.chip) hfind)
          have hsrcFind : sys.source.findChip? wrow.row.chip = some chip := by
            rw [← hname]
            exact (hvalid'.1.1.2 chip hmem).1
          obtain ⟨hval, rfl⟩ := Chip.checkRow_iff.mp hchk
          simp only [VectorizedSystem.liftWeightedTraceRowToSource, System.inspectWeightedRows,
            List.mapM_cons, List.mapM_nil]
          have h1 : sys.source.inspectRow rom wrow.row =
              .ok (chip.receive wrow.row, chip.premises wrow.row) :=
            System.inspectRow_iff.mpr ⟨chip, hsrcFind, hval, rfl⟩
          simp [h1, bind, Except.bind, pure, Except.pure]
  | vec row laneMults =>
      unfold VectorizedSystem.inspectWeightedRow at hinsp
      cases hfind : sys.vectorized.find? (·.vec.name == row.chip) with
      | none => simp [hfind] at hinsp
      | some e =>
          simp only [hfind] at hinsp
          by_cases hlen : (laneMults.length != e.lanes) = true
          · simp [hlen, bind, Except.bind] at hinsp
          · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hinsp
            obtain ⟨_, hchk, hret⟩ := except_bind_ok.mp hinsp
            obtain rfl := except_pure_ok.mp hret
            have heMem := List.mem_of_find?_eq_some hfind
            have heValid := hvalid'.1.2 e heMem
            have hsrcFind : sys.source.findChip? e.orig.name = some e.orig := heValid.1
            have hvecChk : checkVectorize e.orig e.vec e.lanes = true :=
              ((Bool.and_eq_true _ _).mp heValid.2).1
            obtain ⟨hval, _⟩ := Chip.checkRow_iff.mp hchk
            obtain ⟨_, hrowsVal, hrulesEq, _, _⟩ :=
              vectorize_chip_weighted_sound hvecChk rom hval laneMults
            simp only [VectorizedSystem.liftWeightedTraceRowToSource, hfind]
            rw [hrulesEq]
            unfold System.inspectWeightedRows
            apply mapM_ok_iff.mpr
            rw [List.forall₂_map_right_iff]
            apply List.forall₂_same.mpr
            intro w hw
            obtain ⟨hchip, hwVal⟩ := hrowsVal w hw
            have h1 : sys.source.inspectRow rom w.row =
                .ok (e.orig.receive w.row, e.orig.premises w.row) :=
              System.inspectRow_iff.mpr ⟨e.orig, by simpa [hchip] using hsrcFind, hwVal, rfl⟩
            simp [h1, bind, Except.bind, pure, Except.pure]

private theorem mapM_append_ok {α β ε : Type} {f : α → Except ε β}
    {xs ys : List α} {rx ry : List β}
    (hx : xs.mapM f = .ok rx) (hy : ys.mapM f = .ok ry) :
    (xs ++ ys).mapM f = .ok (rx ++ ry) := by
  induction xs generalizing rx with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hx
      subst hx
      simpa using hy
  | cons x rest ih =>
      simp only [List.mapM_cons] at hx
      obtain ⟨y, hy1, htail⟩ := except_bind_ok.mp hx
      obtain ⟨rrest, hrest, hret⟩ := except_bind_ok.mp htail
      obtain rfl := except_pure_ok.mp hret
      simp only [List.cons_append, List.mapM_cons, hy1, ih hrest, bind, Except.bind, pure, Except.pure]

private theorem VectorizedSystem.inspectRows_lift {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {rows : List (VecTraceRow F)}
    {rules : List (RuleClaims (Message F))}
    (hinsp : sys.inspectRows rom rows = .ok rules) :
    sys.source.inspectRows rom (sys.liftRowsToSource rows) = .ok rules := by
  unfold VectorizedSystem.inspectRows at hinsp
  obtain ⟨groups, hmap, hret⟩ := except_bind_ok.mp hinsp
  obtain rfl := except_pure_ok.mp hret
  have hrel := mapM_ok_iff.mp hmap
  clear hmap hinsp hret
  induction hrel with
  | nil => rfl
  | @cons trow g rest gs hhead _ ih =>
      simp only [VectorizedSystem.liftRowsToSource, List.flatMap_cons, List.flatten_cons]
      exact mapM_append_ok (sys.inspectRow_lift hvalid hhead) ih

private theorem VectorizedSystem.inspectWeightedRows_lift {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {rows : List (WeightedVecTraceRow F)}
    {rules : List (RuleClaims (Message F) × Int)}
    (hinsp : sys.inspectWeightedRows rom rows = .ok rules) :
    sys.source.inspectWeightedRows rom (sys.liftWeightedRowsToSource rows) = .ok rules := by
  unfold VectorizedSystem.inspectWeightedRows at hinsp
  obtain ⟨groups, hmap, hret⟩ := except_bind_ok.mp hinsp
  obtain rfl := except_pure_ok.mp hret
  have hrel := mapM_ok_iff.mp hmap
  clear hmap hinsp hret
  induction hrel with
  | nil => rfl
  | @cons trow g rest gs hhead _ ih =>
      simp only [VectorizedSystem.liftWeightedRowsToSource, List.flatMap_cons, List.flatten_cons]
      exact mapM_append_ok (sys.inspectWeightedRow_lift hvalid hhead) ih

private theorem inspectRows_perm {sys : Circuit.System F} {rom : WireROM F}
    {xs ys : List (Row F)} (hperm : xs.Perm ys)
    {rx ry : List (RuleClaims (Message F))}
    (hx : sys.inspectRows rom xs = .ok rx) (hy : sys.inspectRows rom ys = .ok ry) :
    rx.Perm ry := by
  have hrelX := mapM_ok_iff.mp hx
  have hrelY := mapM_ok_iff.mp hy
  clear hx hy
  induction hperm generalizing rx ry with
  | nil =>
      cases hrelX; cases hrelY; exact List.Perm.nil
  | cons x _ ih =>
      cases hrelX with | cons hx1 hxt =>
      cases hrelY with | cons hy1 hyt =>
      have heq : _ = _ := Except.ok.inj (hx1.symm.trans hy1)
      subst heq
      exact (ih hxt hyt).cons _
  | swap x y l =>
      cases hrelX with | cons hx1 hxt =>
      cases hxt with | cons hx2 hxt2 =>
      cases hrelY with | cons hy1 hyt =>
      cases hyt with | cons hy2 hyt2 =>
      have heq1 : _ = _ := Except.ok.inj (hx1.symm.trans hy2)
      have heq2 : _ = _ := Except.ok.inj (hx2.symm.trans hy1)
      subst heq1 heq2
      have htail : _ = _ := Except.ok.inj ((mapM_ok_iff.mpr hxt2).symm.trans (mapM_ok_iff.mpr hyt2))
      subst htail
      exact List.Perm.swap _ _ _
  | trans _ _ ih1 ih2 =>
      rename_i l₁ l₂ l₃ hp1 hp2
      have hex : ∀ r ∈ l₂, ∃ c, sys.inspectRow rom r = .ok c := by
        intro r hr
        have hr1 : r ∈ l₁ := hp1.mem_iff.mpr hr
        have hall := List.forall₂_iff_get.mp hrelX
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr1
        exact ⟨rx[i]'(by omega), hall.2 i hi (by omega)⟩
      have hmid : ∃ rm, sys.inspectRows rom l₂ = .ok rm := by
        clear hp1 hp2 ih1 ih2 hrelX hrelY
        induction l₂ with
        | nil => exact ⟨[], rfl⟩
        | cons a as iha =>
            obtain ⟨ca, hca⟩ := hex a List.mem_cons_self
            obtain ⟨rm, hrm⟩ := iha (fun r hr => hex r (List.mem_cons_of_mem a hr))
            refine ⟨ca :: rm, ?_⟩
            unfold System.inspectRows at hrm ⊢
            rw [List.mapM_cons, hca, hrm]
            rfl
      obtain ⟨rm, hrm⟩ := hmid
      exact (ih1 hrelX (mapM_ok_iff.mp hrm)).trans (ih2 (mapM_ok_iff.mp hrm) hrelY)

private theorem inspectWeightedRows_perm {sys : Circuit.System F} {rom : WireROM F}
    {xs ys : List (WeightedRow F)} (hperm : xs.Perm ys)
    {rx ry : List (RuleClaims (Message F) × Int)}
    (hx : sys.inspectWeightedRows rom xs = .ok rx) (hy : sys.inspectWeightedRows rom ys = .ok ry) :
    rx.Perm ry := by
  have hrelX := mapM_ok_iff.mp hx
  have hrelY := mapM_ok_iff.mp hy
  clear hx hy
  induction hperm generalizing rx ry with
  | nil =>
      cases hrelX; cases hrelY; exact List.Perm.nil
  | cons x _ ih =>
      cases hrelX with | cons hx1 hxt =>
      cases hrelY with | cons hy1 hyt =>
      have heq : _ = _ := Except.ok.inj (hx1.symm.trans hy1)
      subst heq
      exact (ih hxt hyt).cons _
  | swap x y l =>
      cases hrelX with | cons hx1 hxt =>
      cases hxt with | cons hx2 hxt2 =>
      cases hrelY with | cons hy1 hyt =>
      cases hyt with | cons hy2 hyt2 =>
      have heq1 : _ = _ := Except.ok.inj (hx1.symm.trans hy2)
      have heq2 : _ = _ := Except.ok.inj (hx2.symm.trans hy1)
      subst heq1 heq2
      have htail : _ = _ := Except.ok.inj ((mapM_ok_iff.mpr hxt2).symm.trans (mapM_ok_iff.mpr hyt2))
      subst htail
      exact List.Perm.swap _ _ _
  | trans _ _ ih1 ih2 =>
      rename_i l₁ l₂ l₃ hp1 hp2
      have hex : ∀ w ∈ l₂, ∃ c, (do let claims ← sys.inspectRow rom w.row; return (claims, w.multiplicity)) = .ok c := by
        intro w hw
        have hw1 : w ∈ l₁ := hp1.mem_iff.mpr hw
        have hall := List.forall₂_iff_get.mp hrelX
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw1
        exact ⟨rx[i]'(by omega), hall.2 i hi (by omega)⟩
      have hmid : ∃ rm, sys.inspectWeightedRows rom l₂ = .ok rm := by
        clear hp1 hp2 ih1 ih2 hrelX hrelY
        induction l₂ with
        | nil => exact ⟨[], rfl⟩
        | cons a as iha =>
            obtain ⟨ca, hca⟩ := hex a List.mem_cons_self
            obtain ⟨rm, hrm⟩ := iha (fun w hw => hex w (List.mem_cons_of_mem a hw))
            refine ⟨ca :: rm, ?_⟩
            unfold System.inspectWeightedRows at hrm ⊢
            rw [List.mapM_cons, hca, hrm]
            rfl
      obtain ⟨rm, hrm⟩ := hmid
      exact (ih1 hrelX (mapM_ok_iff.mp hrm)).trans (ih2 (mapM_ok_iff.mp hrm) hrelY)

private theorem VectorizedSystem.inspectRows_pack {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {rows : List (Row F)}
    {sourceRules : List (RuleClaims (Message F))}
    (hinsp : sys.source.inspectRows rom rows = .ok sourceRules) :
    ∃ packedRules, sys.inspectRows rom (sys.packRowsFromSource rows) = .ok packedRules ∧
      packedRules.Perm sourceRules := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hvalid'
  have hrowOk : ∀ r ∈ rows, ∃ chip, sys.source.findChip? r.chip = some chip ∧ chip.ValidRow rom r := by
    have hrel := mapM_ok_iff.mp hinsp
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hall := List.forall₂_iff_get.mp hrel
    obtain ⟨chip, hfind, hval, _⟩ := System.inspectRow_iff.mp (hall.2 i hi (by omega))
    exact ⟨chip, hfind, hval⟩
  let vecNames := sys.vectorized.map (·.orig.name)
  let unvecSrc := rows.filter fun r => !vecNames.contains r.chip
  -- 1. Unvectorized rows inspect cleanly to their source rules
  have hunvecMap : ∃ ug, (unvecSrc.map VecTraceRow.unvec).mapM (sys.inspectRow rom) = .ok ug ∧
      sys.source.inspectRows rom unvecSrc = .ok ug.flatten := by
    have hmemUnvec : ∀ r ∈ unvecSrc,
        ∃ chip, sys.unvectorized.find? (·.name == r.chip) = some chip ∧
          sys.source.findChip? r.chip = some chip ∧ chip.ValidRow rom r := by
      intro r hr
      have hrMem : r ∈ rows := (List.mem_filter.mp hr).1
      have hnotVec : vecNames.contains r.chip = false := by
        have hb := (List.mem_filter.mp hr).2
        simpa using hb
      obtain ⟨chip, hfind, hval⟩ := hrowOk r hrMem
      have hchipMem := List.mem_of_find?_eq_some hfind
      have hchipName : chip.name = r.chip := System.findChip_name hfind
      rcases hvalid'.2 chip hchipMem with ⟨u, huMem, rfl⟩ | ⟨e, heMem, rfl⟩
      · refine ⟨u, ?_, hfind, hval⟩
        rw [← hchipName]
        exact sys.findUnvec_of_mem hvalid huMem
      · exfalso
        have hmemName : r.chip ∈ vecNames := List.mem_map.mpr ⟨e, heMem, hchipName⟩
        have hcont : vecNames.contains r.chip = true := List.elem_iff.mpr hmemName
        rw [hcont] at hnotVec
        cases hnotVec
    clear hinsp hrowOk
    suffices ∀ (xs : List (Row F)),
        (∀ r ∈ xs, ∃ chip, sys.unvectorized.find? (·.name == r.chip) = some chip ∧
          sys.source.findChip? r.chip = some chip ∧ chip.ValidRow rom r) →
        ∃ ug, (xs.map VecTraceRow.unvec).mapM (sys.inspectRow rom) = .ok ug ∧
          sys.source.inspectRows rom xs = .ok ug.flatten from
      this unvecSrc hmemUnvec
    intro xs hxs
    induction xs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons r rest ih =>
        obtain ⟨chip, hfu, hfs, hval⟩ := hxs r List.mem_cons_self
        obtain ⟨ug, hug, hsrc⟩ := ih (fun x hx => hxs x (List.mem_cons_of_mem r hx))
        have hchk : chip.checkRow rom r = .ok (chip.receive r, chip.premises r) :=
          Chip.checkRow_iff.mpr ⟨hval, rfl⟩
        have h1 : sys.inspectRow rom (.unvec r) = .ok [(chip.receive r, chip.premises r)] := by
          simp [VectorizedSystem.inspectRow, hfu, hchk, bind, Except.bind, pure, Except.pure]
        have h2 : sys.source.inspectRow rom r = .ok (chip.receive r, chip.premises r) :=
          System.inspectRow_iff.mpr ⟨chip, hfs, hval, rfl⟩
        refine ⟨[(chip.receive r, chip.premises r)] :: ug, ?_, ?_⟩
        · simp [List.map_cons, List.mapM_cons, h1, hug, bind, Except.bind, pure, Except.pure]
        · unfold System.inspectRows at hsrc ⊢
          rw [List.mapM_cons, h2, hsrc]
          rfl
  -- 2. For each vectorized entry `e`, its packed batches inspect to the exact rules of `rows.filter (·.chip == e.orig.name)`
  have hvecEntry : ∀ e ∈ sys.vectorized,
      let chipRows := rows.filter (·.chip == e.orig.name)
      let packed := (chunkList e.lanes chipRows).map fun batch =>
        VecTraceRow.vec (packBatchRow e.orig e.lanes e.vec.name batch) (packBatchActive e.lanes batch.length)
      ∃ vg, packed.mapM (sys.inspectRow rom) = .ok vg ∧
        sys.source.inspectRows rom chipRows = .ok vg.flatten := by
    intro e heMem
    have heValid := hvalid'.1.2 e heMem
    have hsrcFind : sys.source.findChip? e.orig.name = some e.orig := heValid.1
    have hvecChk : checkVectorize e.orig e.vec e.lanes = true :=
      ((Bool.and_eq_true _ _).mp heValid.2).1
    have hspec := checkVectorize_spec hvecChk
    have hfindVec : sys.vectorized.find? (·.vec.name == e.vec.name) = some e :=
      sys.findVec_of_mem hvalid heMem
    let chipRows := rows.filter (·.chip == e.orig.name)
    have hchipValid : ∀ r ∈ chipRows, r.chip = e.orig.name ∧ e.orig.ValidRow rom r := by
      intro r hr
      have hrMem : r ∈ rows := (List.mem_filter.mp hr).1
      have hrc : r.chip = e.orig.name := beq_iff_eq.mp (List.mem_filter.mp hr).2
      obtain ⟨c, hfc, hvc⟩ := hrowOk r hrMem
      rw [hrc, hsrcFind] at hfc
      cases Option.some.inj hfc
      exact ⟨hrc, hvc⟩
    have hbatchOk : ∀ batch ∈ chunkList e.lanes chipRows,
        let trow := VecTraceRow.vec (packBatchRow e.orig e.lanes e.vec.name batch)
          (packBatchActive e.lanes batch.length)
        sys.inspectRow rom trow = .ok (batch.map fun r => (e.orig.receive r, e.orig.premises r)) ∧
          sys.source.inspectRows rom batch = .ok (batch.map fun r => (e.orig.receive r, e.orig.premises r)) := by
      intro batch hbMem
      have hsub : ∀ r ∈ batch, r ∈ chipRows := by
        intro r hr
        rw [← chunkList_flatten hspec.lanesPos chipRows]
        exact List.mem_flatten.mpr ⟨batch, hbMem, hr⟩
      have hbBounds := chunkList_mem_bounds hspec.lanesPos hbMem
      have hbNe : batch ≠ [] := by intro h; simp [h] at hbBounds
      have hbVal : ∀ r ∈ batch, e.orig.ValidRow rom r := fun r hr => (hchipValid r (hsub r hr)).2
      obtain ⟨hname, hactLen, hpackVal, hrulesEq, _⟩ :=
        vectorize_chip_complete hvecChk rom hbBounds.2 (Or.inl hbNe) hbVal
      have hchkVec : e.vec.checkRow rom (packBatchRow e.orig e.lanes e.vec.name batch) =
          .ok (e.vec.receive _, e.vec.premises _) := Chip.checkRow_iff.mpr ⟨hpackVal, rfl⟩
      constructor
      · unfold VectorizedSystem.inspectRow
        simp only [hname, hfindVec, hactLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          hchkVec, bind, Except.bind, pure, Except.pure, hrulesEq]
      · unfold System.inspectRows
        apply mapM_ok_iff.mpr
        rw [List.forall₂_map_right_iff]
        apply List.forall₂_same.mpr
        intro r hr
        obtain ⟨hrc, hrv⟩ := hchipValid r (hsub r hr)
        exact System.inspectRow_iff.mpr ⟨e.orig, by simpa [hrc] using hsrcFind, hrv, rfl⟩
    have hchunks := chunkList e.lanes chipRows
    have hbuild : ∀ (cs : List (List (Row F))),
        (∀ b ∈ cs,
          sys.inspectRow rom (.vec (packBatchRow e.orig e.lanes e.vec.name b) (packBatchActive e.lanes b.length)) =
            .ok (b.map fun r => (e.orig.receive r, e.orig.premises r)) ∧
          sys.source.inspectRows rom b = .ok (b.map fun r => (e.orig.receive r, e.orig.premises r))) →
        ∃ vg, (cs.map fun b => VecTraceRow.vec (packBatchRow e.orig e.lanes e.vec.name b)
            (packBatchActive e.lanes b.length)).mapM (sys.inspectRow rom) = .ok vg ∧
          sys.source.inspectRows rom cs.flatten = .ok vg.flatten := by
      intro cs hcs
      induction cs with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons b bs ih =>
          obtain ⟨hb1, hb2⟩ := hcs b List.mem_cons_self
          obtain ⟨vg, hvg1, hvg2⟩ := ih (fun x hx => hcs x (List.mem_cons_of_mem b hx))
          refine ⟨(b.map fun r => (e.orig.receive r, e.orig.premises r)) :: vg, ?_, ?_⟩
          · simp [List.map_cons, List.mapM_cons, hb1, hvg1, bind, Except.bind, pure, Except.pure]
          · simp only [List.flatten_cons]
            exact mapM_append_ok hb2 hvg2
    obtain ⟨vg, hvg1, hvg2⟩ := hbuild (chunkList e.lanes chipRows) hbatchOk
    rw [chunkList_flatten hspec.lanesPos chipRows] at hvg2
    exact ⟨vg, hvg1, hvg2⟩
  -- 3. Combine across all `sys.vectorized` entries
  have hvecAll : ∀ (es : List (VectorizedChipEntry F)),
      (∀ e ∈ es, ∃ vg,
        ((chunkList e.lanes (rows.filter (·.chip == e.orig.name))).map fun batch =>
          VecTraceRow.vec (packBatchRow e.orig e.lanes e.vec.name batch)
            (packBatchActive e.lanes batch.length)).mapM (sys.inspectRow rom) = .ok vg ∧
        sys.source.inspectRows rom (rows.filter (·.chip == e.orig.name)) = .ok vg.flatten) →
      ∃ vgs, (es.flatMap fun e =>
        (chunkList e.lanes (rows.filter (·.chip == e.orig.name))).map fun batch =>
          VecTraceRow.vec (packBatchRow e.orig e.lanes e.vec.name batch)
            (packBatchActive e.lanes batch.length)).mapM (sys.inspectRow rom) = .ok vgs ∧
        sys.source.inspectRows rom (es.flatMap fun e => rows.filter (·.chip == e.orig.name)) = .ok vgs.flatten := by
    intro es hes
    induction es with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons e rest ih =>
        obtain ⟨vg, hvg1, hvg2⟩ := hes e List.mem_cons_self
        obtain ⟨vgs, hvgs1, hvgs2⟩ := ih (fun x hx => hes x (List.mem_cons_of_mem e hx))
        refine ⟨vg ++ vgs, ?_, ?_⟩
        · simp only [List.flatMap_cons]
          exact mapM_append_ok hvg1 hvgs1
        · simp only [List.flatMap_cons, List.flatten_append]
          exact mapM_append_ok hvg2 hvgs2
  obtain ⟨ug, hug1, hug2⟩ := hunvecMap
  obtain ⟨vgs, hvgs1, hvgs2⟩ := hvecAll sys.vectorized hvecEntry
  refine ⟨(ug ++ vgs).flatten, ?_, ?_⟩
  · unfold VectorizedSystem.inspectRows VectorizedSystem.packRowsFromSource
    rw [mapM_append_ok hug1 hvgs1]
    rfl
  · have hpartPerm : (unvecSrc ++ sys.vectorized.flatMap (fun e => rows.filter (·.chip == e.orig.name))).Perm rows := by
      have hfm : (sys.vectorized.flatMap fun e => rows.filter (·.chip == e.orig.name)) =
          vecNames.flatMap (fun k => rows.filter (·.chip == k)) := by
        simp [vecNames, List.flatMap_map]
      rw [hfm]
      exact perm_filter_partition (fun r : Row F => r.chip) vecNames (sys.origNames_nodup hvalid) rows
    have hsrcApp : sys.source.inspectRows rom
        (unvecSrc ++ sys.vectorized.flatMap (fun e => rows.filter (·.chip == e.orig.name))) =
        .ok (ug ++ vgs).flatten := by
      rw [List.flatten_append]
      exact mapM_append_ok hug2 hvgs2
    exact inspectRows_perm hpartPerm hsrcApp hinsp

private theorem VectorizedSystem.inspectWeightedRows_pack {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {rom : WireROM F} {rows : List (WeightedRow F)}
    {sourceRules : List (RuleClaims (Message F) × Int)}
    (hinsp : sys.source.inspectWeightedRows rom rows = .ok sourceRules) :
    ∃ packedRules, sys.inspectWeightedRows rom (sys.packWeightedRowsFromSource rows) = .ok packedRules ∧
      packedRules.Perm sourceRules := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hvalid'
  have hrowOk : ∀ w ∈ rows, ∃ chip, sys.source.findChip? w.row.chip = some chip ∧ chip.ValidRow rom w.row := by
    have hrel := mapM_ok_iff.mp hinsp
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hall := List.forall₂_iff_get.mp hrel
    obtain ⟨_, h1, _⟩ := except_bind_ok.mp (hall.2 i hi (by omega))
    obtain ⟨chip, hfind, hval, _⟩ := System.inspectRow_iff.mp h1
    exact ⟨chip, hfind, hval⟩
  let vecNames := sys.vectorized.map (·.orig.name)
  let unvecSrc := rows.filter fun w => !vecNames.contains w.row.chip
  have hunvecMap : ∃ ug, (unvecSrc.map WeightedVecTraceRow.unvec).mapM (sys.inspectWeightedRow rom) = .ok ug ∧
      sys.source.inspectWeightedRows rom unvecSrc = .ok ug.flatten := by
    have hmemUnvec : ∀ w ∈ unvecSrc,
        ∃ chip, sys.unvectorized.find? (·.name == w.row.chip) = some chip ∧
          sys.source.findChip? w.row.chip = some chip ∧ chip.ValidRow rom w.row := by
      intro w hw
      have hwMem : w ∈ rows := (List.mem_filter.mp hw).1
      have hnotVec : vecNames.contains w.row.chip = false := by
        have hb := (List.mem_filter.mp hw).2
        simpa using hb
      obtain ⟨chip, hfind, hval⟩ := hrowOk w hwMem
      have hchipMem := List.mem_of_find?_eq_some hfind
      have hchipName : chip.name = w.row.chip := System.findChip_name hfind
      rcases hvalid'.2 chip hchipMem with ⟨u, huMem, rfl⟩ | ⟨e, heMem, rfl⟩
      · refine ⟨u, ?_, hfind, hval⟩
        rw [← hchipName]
        exact sys.findUnvec_of_mem hvalid huMem
      · exfalso
        have hmemName : w.row.chip ∈ vecNames := List.mem_map.mpr ⟨e, heMem, hchipName⟩
        have hcont : vecNames.contains w.row.chip = true := List.elem_iff.mpr hmemName
        rw [hcont] at hnotVec
        cases hnotVec
    clear hinsp hrowOk
    suffices ∀ (xs : List (WeightedRow F)),
        (∀ w ∈ xs, ∃ chip, sys.unvectorized.find? (·.name == w.row.chip) = some chip ∧
          sys.source.findChip? w.row.chip = some chip ∧ chip.ValidRow rom w.row) →
        ∃ ug, (xs.map WeightedVecTraceRow.unvec).mapM (sys.inspectWeightedRow rom) = .ok ug ∧
          sys.source.inspectWeightedRows rom xs = .ok ug.flatten from
      this unvecSrc hmemUnvec
    intro xs hxs
    induction xs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons w rest ih =>
        obtain ⟨chip, hfu, hfs, hval⟩ := hxs w List.mem_cons_self
        obtain ⟨ug, hug, hsrc⟩ := ih (fun x hx => hxs x (List.mem_cons_of_mem w hx))
        have hchk : chip.checkRow rom w.row = .ok (chip.receive w.row, chip.premises w.row) :=
          Chip.checkRow_iff.mpr ⟨hval, rfl⟩
        have h1 : sys.inspectWeightedRow rom (.unvec w) =
            .ok [((chip.receive w.row, chip.premises w.row), w.multiplicity)] := by
          simp [VectorizedSystem.inspectWeightedRow, hfu, hchk, bind, Except.bind, pure, Except.pure]
        have h2 : sys.source.inspectRow rom w.row = .ok (chip.receive w.row, chip.premises w.row) :=
          System.inspectRow_iff.mpr ⟨chip, hfs, hval, rfl⟩
        refine ⟨[((chip.receive w.row, chip.premises w.row), w.multiplicity)] :: ug, ?_, ?_⟩
        · simp [List.map_cons, List.mapM_cons, h1, hug, bind, Except.bind, pure, Except.pure]
        · unfold System.inspectWeightedRows at hsrc ⊢
          rw [List.mapM_cons]
          have hw2 : (do let claims ← sys.source.inspectRow rom w.row; pure (claims, w.multiplicity)) =
              .ok ((chip.receive w.row, chip.premises w.row), w.multiplicity) := by
            rw [h2]; rfl
          rw [hw2, hsrc]
          rfl
  have hvecEntry : ∀ e ∈ sys.vectorized,
      let chipRows := rows.filter (·.row.chip == e.orig.name)
      let packed := (chunkList e.lanes chipRows).map fun batch =>
        WeightedVecTraceRow.vec (packWeightedBatchRow e.orig e.lanes e.vec.name batch)
          (packWeightedBatchMults e.lanes batch)
      ∃ vg, packed.mapM (sys.inspectWeightedRow rom) = .ok vg ∧
        sys.source.inspectWeightedRows rom chipRows = .ok vg.flatten := by
    intro e heMem
    have heValid := hvalid'.1.2 e heMem
    have hsrcFind : sys.source.findChip? e.orig.name = some e.orig := heValid.1
    have hvecChk : checkVectorize e.orig e.vec e.lanes = true :=
      ((Bool.and_eq_true _ _).mp heValid.2).1
    have hspec := checkVectorize_spec hvecChk
    have hfindVec : sys.vectorized.find? (·.vec.name == e.vec.name) = some e :=
      sys.findVec_of_mem hvalid heMem
    let chipRows := rows.filter (·.row.chip == e.orig.name)
    have hchipValid : ∀ w ∈ chipRows, w.row.chip = e.orig.name ∧ e.orig.ValidRow rom w.row := by
      intro w hw
      have hwMem : w ∈ rows := (List.mem_filter.mp hw).1
      have hwc : w.row.chip = e.orig.name := beq_iff_eq.mp (List.mem_filter.mp hw).2
      obtain ⟨c, hfc, hvc⟩ := hrowOk w hwMem
      rw [hwc, hsrcFind] at hfc
      cases Option.some.inj hfc
      exact ⟨hwc, hvc⟩
    have hbatchOk : ∀ batch ∈ chunkList e.lanes chipRows,
        let trow := WeightedVecTraceRow.vec (packWeightedBatchRow e.orig e.lanes e.vec.name batch)
          (packWeightedBatchMults e.lanes batch)
        sys.inspectWeightedRow rom trow =
          .ok (batch.map fun w => ((e.orig.receive w.row, e.orig.premises w.row), w.multiplicity)) ∧
        sys.source.inspectWeightedRows rom batch =
          .ok (batch.map fun w => ((e.orig.receive w.row, e.orig.premises w.row), w.multiplicity)) := by
      intro batch hbMem
      have hsub : ∀ w ∈ batch, w ∈ chipRows := by
        intro w hw
        rw [← chunkList_flatten hspec.lanesPos chipRows]
        exact List.mem_flatten.mpr ⟨batch, hbMem, hw⟩
      have hbBounds := chunkList_mem_bounds hspec.lanesPos hbMem
      have hbNe : batch ≠ [] := by intro h; simp [h] at hbBounds
      have hbVal : ∀ w ∈ batch, e.orig.ValidRow rom w.row := fun w hw => (hchipValid w (hsub w hw)).2
      obtain ⟨hname, hmultLen, hpackVal, hrulesEq, _⟩ :=
        vectorize_chip_weighted_complete hvecChk rom hbBounds.2 (Or.inl hbNe) hbVal
      have hchkVec : e.vec.checkRow rom (packWeightedBatchRow e.orig e.lanes e.vec.name batch) =
          .ok (e.vec.receive _, e.vec.premises _) := Chip.checkRow_iff.mpr ⟨hpackVal, rfl⟩
      constructor
      · unfold VectorizedSystem.inspectWeightedRow
        simp only [hname, hfindVec, hmultLen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          hchkVec, bind, Except.bind, pure, Except.pure, hrulesEq]
      · unfold System.inspectWeightedRows
        apply mapM_ok_iff.mpr
        rw [List.forall₂_map_right_iff]
        apply List.forall₂_same.mpr
        intro w hw
        obtain ⟨hwc, hwv⟩ := hchipValid w (hsub w hw)
        have h1 : sys.source.inspectRow rom w.row =
            .ok (e.orig.receive w.row, e.orig.premises w.row) :=
          System.inspectRow_iff.mpr ⟨e.orig, by simpa [hwc] using hsrcFind, hwv, rfl⟩
        simp [h1, bind, Except.bind, pure, Except.pure]
    have hbuild : ∀ (cs : List (List (WeightedRow F))),
        (∀ b ∈ cs,
          sys.inspectWeightedRow rom (.vec (packWeightedBatchRow e.orig e.lanes e.vec.name b)
            (packWeightedBatchMults e.lanes b)) =
            .ok (b.map fun w => ((e.orig.receive w.row, e.orig.premises w.row), w.multiplicity)) ∧
          sys.source.inspectWeightedRows rom b =
            .ok (b.map fun w => ((e.orig.receive w.row, e.orig.premises w.row), w.multiplicity))) →
        ∃ vg, (cs.map fun b => WeightedVecTraceRow.vec (packWeightedBatchRow e.orig e.lanes e.vec.name b)
            (packWeightedBatchMults e.lanes b)).mapM (sys.inspectWeightedRow rom) = .ok vg ∧
          sys.source.inspectWeightedRows rom cs.flatten = .ok vg.flatten := by
      intro cs hcs
      induction cs with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons b bs ih =>
          obtain ⟨hb1, hb2⟩ := hcs b List.mem_cons_self
          obtain ⟨vg, hvg1, hvg2⟩ := ih (fun x hx => hcs x (List.mem_cons_of_mem b hx))
          refine ⟨(b.map fun w => ((e.orig.receive w.row, e.orig.premises w.row), w.multiplicity)) :: vg, ?_, ?_⟩
          · simp [List.map_cons, List.mapM_cons, hb1, hvg1, bind, Except.bind, pure, Except.pure]
          · simp only [List.flatten_cons]
            exact mapM_append_ok hb2 hvg2
    obtain ⟨vg, hvg1, hvg2⟩ := hbuild (chunkList e.lanes chipRows) hbatchOk
    rw [chunkList_flatten hspec.lanesPos chipRows] at hvg2
    exact ⟨vg, hvg1, hvg2⟩
  have hvecAll : ∀ (es : List (VectorizedChipEntry F)),
      (∀ e ∈ es, ∃ vg,
        ((chunkList e.lanes (rows.filter (·.row.chip == e.orig.name))).map fun batch =>
          WeightedVecTraceRow.vec (packWeightedBatchRow e.orig e.lanes e.vec.name batch)
            (packWeightedBatchMults e.lanes batch)).mapM (sys.inspectWeightedRow rom) = .ok vg ∧
        sys.source.inspectWeightedRows rom (rows.filter (·.row.chip == e.orig.name)) = .ok vg.flatten) →
      ∃ vgs, (es.flatMap fun e =>
        (chunkList e.lanes (rows.filter (·.row.chip == e.orig.name))).map fun batch =>
          WeightedVecTraceRow.vec (packWeightedBatchRow e.orig e.lanes e.vec.name batch)
            (packWeightedBatchMults e.lanes batch)).mapM (sys.inspectWeightedRow rom) = .ok vgs ∧
        sys.source.inspectWeightedRows rom (es.flatMap fun e => rows.filter (·.row.chip == e.orig.name)) = .ok vgs.flatten := by
    intro es hes
    induction es with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons e rest ih =>
        obtain ⟨vg, hvg1, hvg2⟩ := hes e List.mem_cons_self
        obtain ⟨vgs, hvgs1, hvgs2⟩ := ih (fun x hx => hes x (List.mem_cons_of_mem e hx))
        refine ⟨vg ++ vgs, ?_, ?_⟩
        · simp only [List.flatMap_cons]
          exact mapM_append_ok hvg1 hvgs1
        · simp only [List.flatMap_cons, List.flatten_append]
          exact mapM_append_ok hvg2 hvgs2
  obtain ⟨ug, hug1, hug2⟩ := hunvecMap
  obtain ⟨vgs, hvgs1, hvgs2⟩ := hvecAll sys.vectorized hvecEntry
  refine ⟨(ug ++ vgs).flatten, ?_, ?_⟩
  · unfold VectorizedSystem.inspectWeightedRows VectorizedSystem.packWeightedRowsFromSource
    rw [mapM_append_ok hug1 hvgs1]
    rfl
  · have hpartPerm : (unvecSrc ++ sys.vectorized.flatMap (fun e => rows.filter (·.row.chip == e.orig.name))).Perm rows := by
      have hfm : (sys.vectorized.flatMap fun e => rows.filter (·.row.chip == e.orig.name)) =
          vecNames.flatMap (fun k => rows.filter (·.row.chip == k)) := by
        simp [vecNames, List.flatMap_map]
      rw [hfm]
      exact perm_filter_partition (fun w : WeightedRow F => w.row.chip) vecNames (sys.origNames_nodup hvalid) rows
    have hsrcApp : sys.source.inspectWeightedRows rom
        (unvecSrc ++ sys.vectorized.flatMap (fun e => rows.filter (·.row.chip == e.orig.name))) =
        .ok (ug ++ vgs).flatten := by
      rw [List.flatten_append]
      exact mapM_append_ok hug2 hvgs2
    exact inspectWeightedRows_perm hpartPerm hsrcApp hinsp

/-! ### Exact `⌈N / K⌉` Packed Row-Count Theorems -/

omit [Field F] [DecidableEq F] in
private theorem filter_vecRow_unvec_map (vecName : String) (rs : List (Row F)) :
    ((rs.map VecTraceRow.unvec).filter fun
      | .vec r _ => r.chip == vecName
      | .unvec _ => false) = [] := by
  induction rs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

omit [Field F] [DecidableEq F] in
private theorem filter_weightedVecRow_unvec_map (vecName : String) (rs : List (WeightedRow F)) :
    ((rs.map WeightedVecTraceRow.unvec).filter fun
      | .vec r _ => r.chip == vecName
      | .unvec _ => false) = [] := by
  induction rs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Exact per-vectorized-chip packed row count: every vectorized entry `e ∈ sys.vectorized`
occupies **exactly `⌈N_e / e.lanes⌉ = (N_e + e.lanes - 1) / e.lanes`** physical rows. -/
theorem VectorizedSystem.packRows_vecRowCount {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) (rows : List (Row F))
    {e : VectorizedChipEntry F} (he : e ∈ sys.vectorized) :
    vecRowCount e.vec.name (sys.packRowsFromSource rows) =
      (sourceRowCount e.orig.name rows + e.lanes - 1) / e.lanes := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, List.all_eq_true] at hvalid'
  have hlanesPos : 1 ≤ e.lanes :=
    (checkVectorize_spec ((Bool.and_eq_true _ _).mp (hvalid'.1.2 e he).2).1).lanesPos
  have hnd := sys.vecNames_nodup hvalid
  unfold vecRowCount VectorizedSystem.packRowsFromSource
  rw [List.filter_append, filter_vecRow_unvec_map, List.nil_append]
  have haux : ∀ (es : List (VectorizedChipEntry F)),
      (es.map (fun x => x.vec.name)).Nodup → e ∈ es →
      ((es.flatMap fun x =>
        (chunkList x.lanes (rows.filter (·.chip == x.orig.name))).map fun batch =>
          VecTraceRow.vec (packBatchRow x.orig x.lanes x.vec.name batch)
            (packBatchActive x.lanes batch.length)).filter fun
          | .vec r _ => r.chip == e.vec.name
          | .unvec _ => false).length =
        (chunkList e.lanes (rows.filter (·.chip == e.orig.name))).length := by
    intro es
    induction es with
    | nil => intro _ h; cases h
    | cons x rest ih =>
        intro hndX hmem
        simp only [List.map_cons, List.nodup_cons] at hndX
        simp only [List.flatMap_cons, List.filter_append, List.length_append]
        have hsingle : ∀ (y : VectorizedChipEntry F) (bs : List (List (Row F))),
            ((bs.map fun batch =>
              VecTraceRow.vec (packBatchRow y.orig y.lanes y.vec.name batch)
                (packBatchActive y.lanes batch.length)).filter fun
              | .vec r _ => r.chip == e.vec.name
              | .unvec _ => false).length =
            if y.vec.name = e.vec.name then bs.length else 0 := by
          intro y bs
          induction bs with
          | nil => simp
          | cons b bs ihb =>
              rw [List.map_cons, List.filter_cons]
              dsimp only
              by_cases hy : y.vec.name = e.vec.name
              · have hchip : ((packBatchRow y.orig y.lanes y.vec.name b).chip == e.vec.name) = true := by
                  simp [packBatchRow, hy]
                simp only [hchip, ↓reduceIte, List.length_cons]
                rw [ihb]; simp [hy]
              · have hchip : ((packBatchRow y.orig y.lanes y.vec.name b).chip == e.vec.name) = false := by
                  simp [packBatchRow, beq_false_of_ne hy]
                simp only [hchip, Bool.false_eq_true, ↓reduceIte]
                rw [ihb]; simp [hy]
        rcases List.mem_cons.mp hmem with rfl | htail
        · rw [hsingle e _]
          simp only [↓reduceIte]
          have hrest0 : ((rest.flatMap fun y =>
              (chunkList y.lanes (rows.filter (·.chip == y.orig.name))).map fun batch =>
                VecTraceRow.vec (packBatchRow y.orig y.lanes y.vec.name batch)
                  (packBatchActive y.lanes batch.length)).filter fun
                | .vec r _ => r.chip == e.vec.name
                | .unvec _ => false).length = 0 := by
            apply List.length_eq_zero_iff.mpr
            apply List.filter_eq_nil_iff.mpr
            intro trow ht
            obtain ⟨y, hyMem, hyMap⟩ := List.mem_flatMap.mp ht
            obtain ⟨b, _, rfl⟩ := List.mem_map.mp hyMap
            have hne : y.vec.name ≠ e.vec.name := fun heq =>
              hndX.1 (List.mem_map.mpr ⟨y, hyMem, heq⟩)
            simp [packBatchRow, beq_false_of_ne hne]
          rw [hrest0, Nat.add_zero]
        · have hne : x.vec.name ≠ e.vec.name := fun heq =>
            hndX.1 (List.mem_map.mpr ⟨e, htail, heq.symm⟩)
          rw [hsingle x _]
          simp only [hne, ↓reduceIte, Nat.zero_add]
          exact ih hndX.2 htail
  rw [haux sys.vectorized hnd he, chunkList_length hlanesPos]
  rfl

/-- Exact per-vectorized-chip packed row count for weighted/memoized traces:
`weightedVecRowCount e.vec.name (packWeightedRowsFromSource rows) = ⌈N_e / e.lanes⌉`. -/
theorem VectorizedSystem.packWeightedRows_vecRowCount {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) (rows : List (WeightedRow F))
    {e : VectorizedChipEntry F} (he : e ∈ sys.vectorized) :
    weightedVecRowCount e.vec.name (sys.packWeightedRowsFromSource rows) =
      (weightedSourceRowCount e.orig.name rows + e.lanes - 1) / e.lanes := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, List.all_eq_true] at hvalid'
  have hlanesPos : 1 ≤ e.lanes :=
    (checkVectorize_spec ((Bool.and_eq_true _ _).mp (hvalid'.1.2 e he).2).1).lanesPos
  have hnd := sys.vecNames_nodup hvalid
  unfold weightedVecRowCount VectorizedSystem.packWeightedRowsFromSource
  rw [List.filter_append, filter_weightedVecRow_unvec_map, List.nil_append]
  have haux : ∀ (es : List (VectorizedChipEntry F)),
      (es.map (fun x => x.vec.name)).Nodup → e ∈ es →
      ((es.flatMap fun x =>
        (chunkList x.lanes (rows.filter (·.row.chip == x.orig.name))).map fun batch =>
          WeightedVecTraceRow.vec (packWeightedBatchRow x.orig x.lanes x.vec.name batch)
            (packWeightedBatchMults x.lanes batch)).filter fun
          | .vec r _ => r.chip == e.vec.name
          | .unvec _ => false).length =
        (chunkList e.lanes (rows.filter (·.row.chip == e.orig.name))).length := by
    intro es
    induction es with
    | nil => intro _ h; cases h
    | cons x rest ih =>
        intro hndX hmem
        simp only [List.map_cons, List.nodup_cons] at hndX
        simp only [List.flatMap_cons, List.filter_append, List.length_append]
        have hsingle : ∀ (y : VectorizedChipEntry F) (bs : List (List (WeightedRow F))),
            ((bs.map fun batch =>
              WeightedVecTraceRow.vec (packWeightedBatchRow y.orig y.lanes y.vec.name batch)
                (packWeightedBatchMults y.lanes batch)).filter fun
              | .vec r _ => r.chip == e.vec.name
              | .unvec _ => false).length =
            if y.vec.name = e.vec.name then bs.length else 0 := by
          intro y bs
          induction bs with
          | nil => simp
          | cons b bs ihb =>
              rw [List.map_cons, List.filter_cons]
              dsimp only
              by_cases hy : y.vec.name = e.vec.name
              · have hchip : ((packWeightedBatchRow y.orig y.lanes y.vec.name b).chip == e.vec.name) = true := by
                  simp [packWeightedBatchRow, packBatchRow, hy]
                simp only [hchip, ↓reduceIte, List.length_cons]
                rw [ihb]; simp [hy]
              · have hchip : ((packWeightedBatchRow y.orig y.lanes y.vec.name b).chip == e.vec.name) = false := by
                  simp [packWeightedBatchRow, packBatchRow, beq_false_of_ne hy]
                simp only [hchip, Bool.false_eq_true, ↓reduceIte]
                rw [ihb]; simp [hy]
        rcases List.mem_cons.mp hmem with rfl | htail
        · rw [hsingle e _]
          simp only [↓reduceIte]
          have hrest0 : ((rest.flatMap fun y =>
              (chunkList y.lanes (rows.filter (·.row.chip == y.orig.name))).map fun batch =>
                WeightedVecTraceRow.vec (packWeightedBatchRow y.orig y.lanes y.vec.name batch)
                  (packWeightedBatchMults y.lanes batch)).filter fun
                | .vec r _ => r.chip == e.vec.name
                | .unvec _ => false).length = 0 := by
            apply List.length_eq_zero_iff.mpr
            apply List.filter_eq_nil_iff.mpr
            intro trow ht
            obtain ⟨y, hyMem, hyMap⟩ := List.mem_flatMap.mp ht
            obtain ⟨b, _, rfl⟩ := List.mem_map.mp hyMap
            have hne : y.vec.name ≠ e.vec.name := fun heq =>
              hndX.1 (List.mem_map.mpr ⟨y, hyMem, heq⟩)
            simp [packWeightedBatchRow, packBatchRow, beq_false_of_ne hne]
          rw [hrest0, Nat.add_zero]
        · have hne : x.vec.name ≠ e.vec.name := fun heq =>
            hndX.1 (List.mem_map.mpr ⟨e, htail, heq.symm⟩)
          rw [hsingle x _]
          simp only [hne, ↓reduceIte, Nat.zero_add]
          exact ih hndX.2 htail
  rw [haux sys.vectorized hnd he, chunkList_length hlanesPos]
  rfl

/-- Total packed row count equals unvectorized rows plus the exact sum of
`⌈N_e / e.lanes⌉` over all vectorized chips `e ∈ sys.vectorized`. -/
theorem VectorizedSystem.packRows_length {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) (rows : List (Row F)) :
    (sys.packRowsFromSource rows).length =
      (rows.filter fun r => !(sys.vectorized.map (·.orig.name)).contains r.chip).length +
        (sys.vectorized.map fun e => (sourceRowCount e.orig.name rows + e.lanes - 1) / e.lanes).sum := by
  have hvalid' := hvalid
  simp only [VectorizedSystem.checkValid, Bool.and_eq_true, List.all_eq_true] at hvalid'
  unfold VectorizedSystem.packRowsFromSource
  simp only [List.length_append, List.length_map, List.length_flatMap]
  congr 1
  congr 1
  apply List.map_congr_left
  intro e he
  have hlanesPos : 1 ≤ e.lanes :=
    (checkVectorize_spec ((Bool.and_eq_true _ _).mp (hvalid'.1.2 e he).2).1).lanesPos
  rw [chunkList_length hlanesPos]
  rfl

/-! ### Headline System-Level Soundness, Completeness & End-to-End Theorems -/

/-- **Headline System-Level Vectorization Soundness (`vectorize_system_sound`)**:
any accepted trace of a certified `VectorizedSystem` unpacks into an accepted trace
of `sys.source` with identical LogUp ledger. -/
theorem vectorize_system_sound {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (VecTraceRow F)}
    (hcheck : sys.check rom entry rows = .ok ()) :
    sys.source.check rom entry (sys.liftRowsToSource rows) = .ok () := by
  unfold VectorizedSystem.check at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨⟨⟩, _, h2⟩ := except_bind_ok.mp h1
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h2
  unfold System.check
  rw [hctx, sys.inspectRows_lift hvalid hinsp]
  exact hbal

/-- **Headline System-Level Weighted / Memo Vectorization Soundness (`vectorize_system_memo_sound`)**:
any accepted weighted LogUp trace of a certified `VectorizedSystem` unpacks into an
accepted weighted LogUp trace of `sys.source` with identical `Balance.accumulator`. -/
theorem vectorize_system_memo_sound {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (WeightedVecTraceRow F)}
    (hcheck : sys.checkMemo rom entry rows = .ok ()) :
    sys.source.checkMemo rom entry (sys.liftWeightedRowsToSource rows) = .ok () := by
  unfold VectorizedSystem.checkMemo at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨⟨⟩, _, h2⟩ := except_bind_ok.mp h1
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h2
  unfold System.checkMemo
  rw [hctx, sys.inspectWeightedRows_lift hvalid hinsp]
  exact hbal

/-- **Headline Prover Completeness (Unit Check — `vectorize_system_complete`)**:
any accepted trace of `sys.source` packs into an accepted trace of `sys` in which
every vectorized chip `e` occupies **exactly `⌈N_e / e.lanes⌉`** rows (and in
particular `vecRowCount ≤ (sourceRowCount + K - 1) / K`). -/
theorem vectorize_system_complete {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (Row F)}
    (hcheck : sys.source.check rom entry rows = .ok ()) :
    sys.check rom entry (sys.packRowsFromSource rows) = .ok () ∧
      ∀ e ∈ sys.vectorized,
        vecRowCount e.vec.name (sys.packRowsFromSource rows) =
          (sourceRowCount e.orig.name rows + e.lanes - 1) / e.lanes := by
  unfold System.check at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨sourceRules, hinsp, hbal⟩ := except_bind_ok.mp h1
  obtain ⟨packedRules, hpackInsp, hperm⟩ := sys.inspectRows_pack hvalid hinsp
  refine ⟨?_, fun e he => sys.packRows_vecRowCount hvalid rows he⟩
  unfold VectorizedSystem.check
  rw [hctx, sys.checkChips_physical hvalid, hpackInsp]
  have hzeroSrc : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
      (sourceRules.map fun rule => (rule, 1))).isZero = true := by
    by_cases hz : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
        (sourceRules.map fun rule => (rule, 1))).isZero = true
    · exact hz
    · simp [hz] at hbal
  have hzeroPack : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
      (packedRules.map fun rule => (rule, 1))).isZero = true := by
    rw [balance_accumulator_isZero_of_perm _ _ (hperm.map fun rule => (rule, 1))]
    exact hzeroSrc
  simp [hzeroPack, bind, Except.bind, pure, Except.pure]

/-- **Headline Prover Completeness (Weighted / Memo Check — `vectorize_system_memo_complete`)**:
any accepted weighted LogUp trace of `sys.source` packs into an accepted weighted
LogUp trace of `sys` where every vectorized chip `e` occupies **exactly
`⌈N_e / e.lanes⌉`** rows. -/
theorem vectorize_system_memo_complete {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (WeightedRow F)}
    (hcheck : sys.source.checkMemo rom entry rows = .ok ()) :
    sys.checkMemo rom entry (sys.packWeightedRowsFromSource rows) = .ok () ∧
      ∀ e ∈ sys.vectorized,
        weightedVecRowCount e.vec.name (sys.packWeightedRowsFromSource rows) =
          (weightedSourceRowCount e.orig.name rows + e.lanes - 1) / e.lanes := by
  unfold System.checkMemo at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨sourceRules, hinsp, hbal⟩ := except_bind_ok.mp h1
  obtain ⟨packedRules, hpackInsp, hperm⟩ := sys.inspectWeightedRows_pack hvalid hinsp
  refine ⟨?_, fun e he => sys.packWeightedRows_vecRowCount hvalid rows he⟩
  unfold VectorizedSystem.checkMemo
  rw [hctx, sys.checkChips_physical hvalid, hpackInsp]
  have hzeroSrc : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
      sourceRules).isZero = true := by
    by_cases hz : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
        sourceRules).isZero = true
    · exact hz
    · simp [hz] at hbal
  have hzeroPack : (Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
      packedRules).isZero = true := by
    rw [balance_accumulator_isZero_of_perm _ _ hperm]
    exact hzeroSrc
  simp [hzeroPack, bind, Except.bind, pure, Except.pure]

/-- Single-vectorized-chip trace row-count corollary: when all `N` rows in `rows` belong
to a single vectorized chip `e` with lane count `K = e.lanes`, the packed trace has
length **exact `⌈N / K⌉`** (`≤ (N + K - 1) / K`). -/
theorem vectorize_system_complete_row_bound {sys : VectorizedSystem F}
    (hvalid : sys.checkValid = true) {e : VectorizedChipEntry F}
    (hsingle : sys.vectorized = [e]) {rom : WireROM F} {entry : Message F}
    {rows : List (Row F)} (hall : ∀ r ∈ rows, r.chip = e.orig.name)
    (hcheck : sys.source.check rom entry rows = .ok ()) :
    sys.check rom entry (sys.packRowsFromSource rows) = .ok () ∧
      (sys.packRowsFromSource rows).length ≤ (rows.length + e.lanes - 1) / e.lanes := by
  refine ⟨(vectorize_system_complete hvalid hcheck).1, ?_⟩
  rw [sys.packRows_length hvalid rows, hsingle]
  have hnoUnvec : (rows.filter fun r => !([e].map (·.orig.name)).contains r.chip) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    simp [hall r hr]
  have hallMatch : sourceRowCount e.orig.name rows = rows.length := by
    unfold sourceRowCount
    have hf : rows.filter (·.chip == e.orig.name) = rows := by
      apply List.filter_eq_self.mpr
      intro r hr
      simp [hall r hr]
    rw [hf]
  rw [hnoUnvec]
  simp [hallMatch]

/-- Bidirectional existential trace equivalence (unit check). -/
theorem vectorize_system_check_iff {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} :
    (∃ rows, sys.check rom entry rows = .ok ()) ↔
      (∃ rows, sys.source.check rom entry rows = .ok ()) :=
  ⟨fun ⟨_, h⟩ => ⟨_, vectorize_system_sound hvalid h⟩,
   fun ⟨_, h⟩ => ⟨_, (vectorize_system_complete hvalid h).1⟩⟩

/-- Bidirectional existential trace equivalence (weighted LogUp / memo check). -/
theorem vectorize_system_checkMemo_iff {sys : VectorizedSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} :
    (∃ rows, sys.checkMemo rom entry rows = .ok ()) ↔
      (∃ rows, sys.source.checkMemo rom entry rows = .ok ()) :=
  ⟨fun ⟨_, h⟩ => ⟨_, vectorize_system_memo_sound hvalid h⟩,
   fun ⟨_, h⟩ => ⟨_, (vectorize_system_memo_complete hvalid h).1⟩⟩

/-- End-to-end composition with Formal Aiur's `ModulesArtifact.check_sound`: an
accepted trace of a certified `K`-lane vectorization of `compiled.circuit.system`
implies independent source evaluation `prepared.EvalCall`. -/
theorem vectorize_modulesArtifact_sound {prog : Modules.Program F}
    {prepared : Modules.Prepared prog} (compiled : ModulesArtifact prepared)
    {sys : VectorizedSystem F} (hsrc : sys.source = compiled.circuit.system)
    (hvalid : sys.checkValid = true)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (VecTraceRow F)}
    (hcheck : sys.check rom ⟨entry.resolved.name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalCall external args value ∧
      Represents (rom.decode compiled.specialized.program.enums) heap value result := by
  have horig := vectorize_system_sound hvalid hcheck
  rw [hsrc] at horig
  have hmem : entry.resolved.name ∈ compiled.circuit.artifact.entries := by
    simpa only [(compile_stages compiled.circuit.compiled).2.2.1] using
      Modules.Prepared.entry_mem selected
  have hart : compiled.check rom external wires output (sys.liftRowsToSource rows) = .ok () := by
    simp only [ModulesArtifact.check, selected]
    exact Artifact.check_iff.mpr ⟨hmem, horig⟩
  exact compiled.check_sound hart arguments decoded

/-- End-to-end composition with Formal Aiur's `Physical.Prepared` +
`Modules.Prepared.physical_heap_sound`: an accepted vectorized trace of the physical
type-erased system yields `Modules.Prepared.EvalFn`. -/
theorem vectorize_physical_heap_sound {prog : Modules.Program F}
    {prepared : Modules.Prepared prog} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {sys : VectorizedSystem F} (hsrc : sys.source = physical.system)
    (hvalid : sys.checkValid = true)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (VecTraceRow F)}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (hcheck : sys.check (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩) rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents
        ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result := by
  have horig := vectorize_system_sound hvalid hcheck
  rw [hsrc] at horig
  exact prepared.physical_heap_sound compiled physical selected valid signed
    (physical.system.check_sound horig) arguments decoded

end SystemVectorize

/-! ## 5. Executable `#guard` Smoke Tests, Negative Controls & `#print axioms` Pins -/

section SmokeTests

private abbrev GF := Library.U32.Goldilocks.F

/-- A concrete 9-column, degree-3 Goldilocks step chip (`step9(n, acc) → out`) with
per-lane boolean selectors (`is_base`, `is_step`), a degree-3 inverse check, a
degree-3 squaring check, a conditional recursive send, and a ROM lookup:
* `var 0` (`n`), `var 1` (`acc`): inputs.
* `var 2` (`out`): output.
* `var 3` (`is_base`), `var 4` (`is_step`): mutually exclusive boolean lane selectors
  (`sel = is_base + is_step ∈ {0, 1}`; setting all 9 columns to `0` sets `sel = 0` so
  `isZeroSilent == true`).
* `var 5` (`n_inv`): inverse of `n` when `is_step = 1` (`is_step * (n * n_inv - 1) = 0`, deg 3).
* `var 6` (`n_sq`): square of `n` (`is_step * (n_sq - n * n) = 0`, deg 3).
* `var 7` (`rom_val`): ROM read at address `is_base` enabled by `is_base + is_step`.
* `var 8` (`rec_out`): recursive send `step9(n - 1, acc + n_sq + rom_val)` enabled by `is_step`. -/
private def stepChip9 : Chip GF :=
  let n : ArithExpr GF := .var 0
  let acc : ArithExpr GF := .var 1
  let out : ArithExpr GF := .var 2
  let isBase : ArithExpr GF := .var 3
  let isStep : ArithExpr GF := .var 4
  let nInv : ArithExpr GF := .var 5
  let nSq : ArithExpr GF := .var 6
  let romVal : ArithExpr GF := .var 7
  let recOut : ArithExpr GF := .var 8
  let sel : ArithExpr GF := .add isBase isStep
  { name := "step9"
    inputs := [WireValue.field 0, WireValue.field 1]
    output := WireValue.field out
    numVars := 9
    constraints :=
      [ .mul isBase (.sub isBase (.const 1)),
        .mul isStep (.sub isStep (.const 1)),
        .mul isBase isStep,
        .mul isBase n,
        .mul isStep (.sub (.mul n nInv) (.const 1)),
        .mul isStep (.sub nSq (.mul n n)),
        .mul isBase (.sub out (.add acc romVal)),
        .mul isStep (.sub out recOut) ]
    sends :=
      [ ⟨"step9",
          [WireValue.field (.sub n (.const 1)),
           WireValue.field (.add (.add acc nSq) romVal)],
          WireValue.field 8,
          isStep⟩ ]
    memory :=
      [ ⟨isBase, WireValue.field romVal, sel⟩ ] }

private def stepSystem9 : Circuit.System GF :=
  { chips := [stepChip9] }

private def stepRom9 : WireROM GF :=
  ⟨[((0 : GF), WireValue.field (5 : GF)),
    ((1 : GF), WireValue.field (11 : GF))]⟩

/-- Generate the exact `N`-row balanced trace for `step9(N - 1, 0)` (for `N ≥ 1`). -/
private def mkStep9Trace (N : Nat) : List (Row GF) × GF :=
  let rec go (k : Nat) (acc : GF) : List (Row GF) × GF :=
    match k with
    | 0 =>
        let romVal : GF := 11
        let out : GF := acc + romVal
        ([⟨"step9", [0, acc, out, 1, 0, 0, 0, romVal, 0]⟩], out)
    | k' + 1 =>
        let nf : GF := ((k' + 1 : Nat) : GF)
        let nSq : GF := nf * nf
        let romVal : GF := 5
        let nextAcc : GF := acc + nSq + romVal
        let (tailRows, finalOut) := go k' nextAcc
        let row : Row GF := ⟨"step9", [nf, acc, finalOut, 0, 1, nf⁻¹, nSq, romVal, finalOut]⟩
        (row :: tailRows, finalOut)
  match N with
  | 0 => ([], 0)
  | n + 1 => go n 0

-- Verify structural properties: 9 cols, maxConstraintDegree = 3, zero-silent = true,
-- vectorization at K = 4 (36 cols) and K = 8 (72 cols) keeps maxConstraintDegree = 3!
private def vec4Chip : Chip GF := vectorizeChip stepChip9 4
private def vec8Chip : Chip GF := vectorizeChip stepChip9 8

#guard stepChip9.wellFormed == true
#guard isZeroSilent stepChip9 == true
#guard stepChip9.numVars == 9
#guard maxConstraintDegree stepChip9 == 3

#guard checkVectorize stepChip9 vec4Chip 4 == true
#guard vec4Chip.numVars == 36
#guard maxConstraintDegree vec4Chip == 3

#guard checkVectorize stepChip9 vec8Chip 8 == true
#guard vec8Chip.numVars == 72
#guard maxConstraintDegree vec8Chip == 3

/-- Concrete end-to-end smoke test at `K = 4` (`N = 100 → 25` rows, exact `4×`!) and
`K = 8` (`N = 103 → 13` rows, `7.92×`, tail padding lane 7 literally all-zero and
inactive!), checking BOTH unit `check` AND weighted LogUp `checkMemo` round-trip! -/
private def smokeTestK4AndK8 : Bool :=
  match vectorizeSystem stepSystem9 [("step9", 4)],
        vectorizeSystem stepSystem9 [("step9", 8)] with
  | some sys4, some sys8 =>
      -- Test 1: N = 100 rows at K = 4 -> 25 rows (exact 4x!)
      let (rows100, out100) := mkStep9Trace 100
      let entry100 : Message GF :=
        ⟨"step9", [WireValue.field (99 : GF), WireValue.field (0 : GF)], WireValue.field out100⟩
      let packed4 := sys4.packRowsFromSource rows100
      let lifted4 := sys4.liftRowsToSource packed4
      let wRows100 : List (WeightedRow GF) := rows100.map (⟨·, 1⟩)
      let wPacked4 := sys4.packWeightedRowsFromSource wRows100
      let wLifted4 := sys4.liftWeightedRowsToSource wPacked4
      -- Test 2: N = 103 rows (non-multiple!) at K = 8 -> 13 rows (7.92x, 12 full + 1 with 7 active & 1 zero tail lane!)
      let (rows103, out103) := mkStep9Trace 103
      let entry103 : Message GF :=
        ⟨"step9", [WireValue.field (102 : GF), WireValue.field (0 : GF)], WireValue.field out103⟩
      let packed8 := sys8.packRowsFromSource rows103
      let lifted8 := sys8.liftRowsToSource packed8
      let wRows103 : List (WeightedRow GF) := rows103.map (⟨·, 1⟩)
      let wPacked8 := sys8.packWeightedRowsFromSource wRows103
      let wLifted8 := sys8.liftWeightedRowsToSource wPacked8
      -- Inspect last row of packed8: lane 7 must be inactive (`false`) and literally all zeros!
      let tailLaneOk : Bool :=
        match packed8.getLast? with
        | some (.vec lastRow activeMask) =>
            (activeMask == [true, true, true, true, true, true, true, false]) &&
              ((unpackLaneRow "step9" 9 lastRow 7).values == List.replicate 9 (0 : GF))
        | _ => false
      (rows100.length == 100) &&
      (packed4.length == 25) &&
      (vecRowCount "step9#vec4" packed4 == 25) &&
      (lifted4.length == 100) &&
      (stepSystem9.check stepRom9 entry100 rows100 == .ok ()) &&
      (sys4.check stepRom9 entry100 packed4 == .ok ()) &&
      (stepSystem9.check stepRom9 entry100 lifted4 == .ok ()) &&
      (stepSystem9.checkMemo stepRom9 entry100 wRows100 == .ok ()) &&
      (sys4.checkMemo stepRom9 entry100 wPacked4 == .ok ()) &&
      (stepSystem9.checkMemo stepRom9 entry100 wLifted4 == .ok ()) &&
      (rows103.length == 103) &&
      (packed8.length == 13) &&
      (vecRowCount "step9#vec8" packed8 == 13) &&
      (lifted8.length == 103) &&
      tailLaneOk &&
      (stepSystem9.check stepRom9 entry103 rows103 == .ok ()) &&
      (sys8.check stepRom9 entry103 packed8 == .ok ()) &&
      (stepSystem9.check stepRom9 entry103 lifted8 == .ok ()) &&
      (stepSystem9.checkMemo stepRom9 entry103 wRows103 == .ok ()) &&
      (sys8.checkMemo stepRom9 entry103 wPacked8 == .ok ()) &&
      (stepSystem9.checkMemo stepRom9 entry103 wLifted8 == .ok ())
  | _, _ => false

#guard smokeTestK4AndK8 == true

/-- Concrete mixed-system weighted LogUp memo test with heterogeneous per-lane
multiplicities (`m_0 = 3, m_1 = 2, m_2 = 1`) and inactive all-zero tail lane `3`:
unvectorized `caller` makes 6 calls to 3 distinct inputs of 4-col leaf `hot_leaf`,
which vectorizes at `K = 4` into a single physical row `[some 3, some 2, some 1, none]`! -/
private def hotLeafChip : Chip GF :=
  let a : ArithExpr GF := .var 0
  let b : ArithExpr GF := .var 1
  let out : ArithExpr GF := .var 2
  let sel : ArithExpr GF := .var 3
  { name := "hot_leaf"
    inputs := [WireValue.field 0, WireValue.field 1]
    output := WireValue.field out
    numVars := 4
    constraints :=
      [ .mul sel (.sub sel (.const 1)),
        .mul sel (.sub out (.add (.mul a b) (.const 1))) ]
    sends := []
    memory := [] }

private def callerChip : Chip GF :=
  -- 6 sends to `hot_leaf`: 3× (2, 3) -> 7, 2× (4, 5) -> 21, 1× (6, 7) -> 43; output = sum
  let r0 : ArithExpr GF := .var 1
  let r1 : ArithExpr GF := .var 2
  let r2 : ArithExpr GF := .var 3
  let r3 : ArithExpr GF := .var 4
  let r4 : ArithExpr GF := .var 5
  let r5 : ArithExpr GF := .var 6
  let out : ArithExpr GF := .var 7
  { name := "caller"
    inputs := [WireValue.field 0]
    output := WireValue.field out
    numVars := 8
    constraints :=
      [ .sub out (.add (.add (.add r0 r1) (.add r2 r3)) (.add r4 r5)) ]
    sends :=
      [ ⟨"hot_leaf", [WireValue.field (.const 2), WireValue.field (.const 3)], WireValue.field 1, .const 1⟩,
        ⟨"hot_leaf", [WireValue.field (.const 2), WireValue.field (.const 3)], WireValue.field 2, .const 1⟩,
        ⟨"hot_leaf", [WireValue.field (.const 2), WireValue.field (.const 3)], WireValue.field 3, .const 1⟩,
        ⟨"hot_leaf", [WireValue.field (.const 4), WireValue.field (.const 5)], WireValue.field 4, .const 1⟩,
        ⟨"hot_leaf", [WireValue.field (.const 4), WireValue.field (.const 5)], WireValue.field 5, .const 1⟩,
        ⟨"hot_leaf", [WireValue.field (.const 6), WireValue.field (.const 7)], WireValue.field 6, .const 1⟩ ]
    memory := [] }

private def mixedMemoSystem : Circuit.System GF :=
  { chips := [callerChip, hotLeafChip] }

private def weightedMemoMultiplicityTest : Bool :=
  match vectorizeSystem mixedMemoSystem [("hot_leaf", 4)] with
  | none => false
  | some sys =>
      let emptyRom : WireROM GF := ⟨[]⟩
      let entry : Message GF := ⟨"caller", [WireValue.field (0 : GF)], WireValue.field (106 : GF)⟩
      let srcWeighted : List (WeightedRow GF) :=
        [ ⟨⟨"caller", [0, 7, 7, 7, 21, 21, 43, 106]⟩, 1⟩,
          ⟨⟨"hot_leaf", [2, 3, 7, 1]⟩, 3⟩,
          ⟨⟨"hot_leaf", [4, 5, 21, 1]⟩, 2⟩,
          ⟨⟨"hot_leaf", [6, 7, 43, 1]⟩, 1⟩ ]
      let packed := sys.packWeightedRowsFromSource srcWeighted
      let lifted := sys.liftWeightedRowsToSource packed
      let multsAndTailOk : Bool :=
        match packed.getLast? with
        | some (.vec vrow mults) =>
            (mults == [some 3, some 2, some 1, none]) &&
              ((unpackLaneRow "hot_leaf" 4 vrow 3).values == List.replicate 4 (0 : GF))
        | _ => false
      (isZeroSilent hotLeafChip) &&
      (weightedVecRowCount "hot_leaf#vec4" packed == 1) &&
      (packed.length == 2) &&
      multsAndTailOk &&
      (mixedMemoSystem.checkMemo emptyRom entry srcWeighted == .ok ()) &&
      (sys.checkMemo emptyRom entry packed == .ok ()) &&
      (mixedMemoSystem.checkMemo emptyRom entry lifted == .ok ())

#guard weightedMemoMultiplicityTest == true

/-- Fail-closed negative controls:
1. Dropped lane constraint → `checkVectorize == false`.
2. Dropped lane send → `checkVectorize == false`.
3. Wrong lane shift (shifting lane 1 by offset `10` instead of `9`) → `checkVectorize == false`.
4. Additional controls: dropped lane memory, wrong width, `K = 0` → all `false`. -/
private def negativeControlsPass : Bool :=
  let badDropConstraint : Chip GF :=
    { vec4Chip with constraints := vec4Chip.constraints.dropLast }
  let badDropSend : Chip GF :=
    { vec4Chip with sends := vec4Chip.sends.dropLast }
  let badWrongShift : Chip GF :=
    let corruptedConstraints :=
      (List.range 4).flatMap fun j =>
        let off := if j == 1 then 10 else j * stepChip9.numVars
        stepChip9.constraints.map (shiftExpr off)
    { vec4Chip with constraints := corruptedConstraints }
  let badDropMemory : Chip GF :=
    { vec4Chip with memory := vec4Chip.memory.dropLast }
  let badWrongWidth : Chip GF :=
    { vec4Chip with numVars := 37 }
  !(checkVectorize stepChip9 badDropConstraint 4) &&
  !(checkVectorize stepChip9 badDropSend 4) &&
  !(checkVectorize stepChip9 badWrongShift 4) &&
  !(checkVectorize stepChip9 badDropMemory 4) &&
  !(checkVectorize stepChip9 badWrongWidth 4) &&
  !(checkVectorize stepChip9 (vectorizeChip stepChip9 0) 0)

#guard negativeControlsPass == true

end SmokeTests

/-- info: 'Aiur.Optimized.Vectorize.vectorizeChip_maxConstraintDegree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vectorizeChip_maxConstraintDegree

/-- info: 'Aiur.Optimized.Vectorize.checkVectorize_maxConstraintDegree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkVectorize_maxConstraintDegree

/-- info: 'Aiur.Optimized.Vectorize.activation_isZeroSilent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms activation_isZeroSilent

/-- info: 'Aiur.Optimized.Vectorize.vecRowWeightedRules_ledger_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vecRowWeightedRules_ledger_sum

/-- info: 'Aiur.Optimized.Vectorize.vecRowRules_outer_mult_ledger_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vecRowRules_outer_mult_ledger_sum

/-- info: 'Aiur.Optimized.Vectorize.vectorize_chip_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_chip_sound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_chip_weighted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_chip_weighted_sound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_chip_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_chip_complete

/-- info: 'Aiur.Optimized.Vectorize.vectorize_chip_complete_zeroSilent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_chip_complete_zeroSilent

/-- info: 'Aiur.Optimized.Vectorize.vectorize_chip_weighted_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_chip_weighted_complete

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_sound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_memo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_memo_sound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_complete

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_memo_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_memo_complete

/--
info: 'Aiur.Optimized.Vectorize.vectorize_system_complete_row_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms vectorize_system_complete_row_bound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_check_iff

/-- info: 'Aiur.Optimized.Vectorize.vectorize_system_checkMemo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_system_checkMemo_iff

/-- info: 'Aiur.Optimized.Vectorize.vectorize_modulesArtifact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_modulesArtifact_sound

/-- info: 'Aiur.Optimized.Vectorize.vectorize_physical_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorize_physical_heap_sound

end Aiur.Optimized.Vectorize
