import Aiur.Tiling.WideStage
import Aiur.Tiling.SingleCircuit
import Aiur.Tiling.BLS12381

/-!
# Certified Vectorized ROM (`C6`)

Packs `K ≥ 1` consecutive width-`w` ROM entries per physical row `r ∈ 0 .. rows - 1`
(covering addresses `K * r + 0, K * r + 1, ..., K * r + (K - 1)`), cutting ROM table
height and preprocessed address storage by `K×` with **zero** extra constraints and
**only 1 single fixed column** (`addr_base = K * r`):

* **Main columns (`K * (w + 1)` total):** for each lane `j ∈ 0 .. K - 1`,
  multiplicity `mult_j` sits at `j * (w + 1)` and payload words `word_{j,0} .. word_{j,w-1}`
  sit at `j * (w + 1) + 1 + t` (`t < w`).
* **Fixed columns (`fixedWidth := 1`):** only ONE fixed column `addr_base = K * r`
  at variable `K * (w + 1)`. Each lane `j`'s address is the degree-1 linear expression
  `.add (.var (K * (w + 1))) (.const (j : F))` — zero extra fixed columns, zero extra
  constraints.
* **Lookups (`K` per row):** for each `j ∈ 0 .. K - 1`,
  `push(-mult_j, [ROM, w, addr_base + j, word_{j,0}, ..., word_{j,w-1}])`.
* **Row count:** `vectorRomRows K cap = (cap + K - 1) / K`, covering `K * rows ≥ cap`
  consecutive addresses `0 .. K * rows - 1` (requiring `K * rows ≤ bound` for address
  injectivity under `SmallCast F bound`).

## Main Theorems

* `vectorRom_inBounds`: every variable in `vectorRomAir w K cap` is within
  `width + fixedWidth`.
* `vectorRom_holds`: `(vectorRomAir w K cap).Holds main` trivially holds (`constraints := []`).
* `vectorRomAir_ledger_eq`: exact `Ledger F` equality
  `(vectorRomAir w K cap).ledger main = (romAir w (K * rows)).ledger (unpackVectorRomMain w K main)`.
* `vectorRomAir_ledger_pack` & `vectorRomAir_ledger_packPadded`: prover completeness
  for both full `K * rows` and tail-padded `cap`-row scalar ROM traces.
* `wide_vector_rom_sound`: generic multi-field soundness composing directly with
  `WideStage.wide_heap_sound`.
* `wide_vector_rom_sound_goldilocks` (Endpoint 1) & `wide_vector_rom_sound_bls12381` (Endpoint 2).
* `wide_vector_rom_single_circuit_sound_goldilocks` & `wide_vector_rom_single_circuit_sound_bls12381`:
  composing `VectorRom` with `SingleCircuit.pack` (`num_circuits == 1`).
-/

namespace Aiur.Tiling.VectorRom

open Aiur.Circuit
open Aiur.Optimized
open Aiur.Tiling
open Aiur.Tiling.WideStage
open Bridge
open Scalar.Circuit (ArithExpr)

/-! ## 1. Row count & column layout -/

/-- Physical row count of a `K`-lane vectorized ROM table with capacity `cap`:
`⌈cap / K⌉ = (cap + K - 1) / K`. -/
def vectorRomRows (K cap : Nat) : Nat :=
  (cap + K - 1) / K

theorem vectorRomRows_one (cap : Nat) : vectorRomRows 1 cap = cap := by
  simp [vectorRomRows]

theorem vectorRomRows_zero (K : Nat) : vectorRomRows K 0 = 0 := by
  unfold vectorRomRows
  cases K with
  | zero => rfl
  | succ k => exact Nat.div_eq_of_lt (by omega)

theorem cap_le_mul_vectorRomRows {K cap : Nat} (hK : 0 < K) :
    cap ≤ K * vectorRomRows K cap := by
  unfold vectorRomRows
  have hdiv := Nat.div_add_mod (cap + K - 1) K
  have hmod := Nat.mod_lt (cap + K - 1) hK
  omega

theorem mul_vectorRomRows_lt_add {K cap : Nat} (hK : 0 < K) :
    K * vectorRomRows K cap < cap + K := by
  unfold vectorRomRows
  have hdiv := Nat.div_add_mod (cap + K - 1) K
  omega

theorem vectorRomRows_mul {K r : Nat} (hK : 0 < K) :
    vectorRomRows K (K * r) = r := by
  unfold vectorRomRows
  have h1 : K * r + K - 1 = K * r + (K - 1) := by omega
  rw [h1, Nat.mul_add_div hK, Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- Main column index of lane `j`'s multiplicity in `vectorRomCircuit w K`. -/
def laneMultCol (w j : Nat) : Nat :=
  j * (w + 1)

/-- Main column index of lane `j`'s `t`-th payload word in `vectorRomCircuit w K`. -/
def laneWordCol (w j t : Nat) : Nat :=
  j * (w + 1) + 1 + t

/-- Variable index of the sole fixed column `addr_base = K * r` in `vectorRomCircuit w K`. -/
def baseAddrVar (w K : Nat) : Nat :=
  K * (w + 1)

theorem laneMultCol_lt {w K j : Nat} (hj : j < K) :
    laneMultCol w j < K * (w + 1) :=
  Nat.mul_lt_mul_of_pos_right hj (Nat.succ_pos w)

theorem laneWordCol_lt {w K j t : Nat} (hj : j < K) (ht : t < w) :
    laneWordCol w j t < K * (w + 1) := by
  unfold laneWordCol
  have h1 : (j + 1) * (w + 1) ≤ K * (w + 1) := Nat.mul_le_mul_right (w + 1) hj
  have h2 : (j + 1) * (w + 1) = j * (w + 1) + (w + 1) := Nat.succ_mul j (w + 1)
  omega

/-! ## 2. Vectorized ROM circuit, fixed matrix, and `Air` -/

section Defs

variable {F : Type} [Field F]

/-- Lane `j`'s ROM lookup in `vectorRomCircuit w K`:
`push(-mult_j, [ROM, w, addr_base + j, word_{j,0}, ..., word_{j,w-1}])`. -/
def vectorRomLaneLookup (w K j : Nat) : Lookup F where
  multiplicity := .sub (.const 0) (.var (laneMultCol w j))
  args :=
    .const (Bridge.ROM : F) ::
    .const (w : F) ::
    .add (.var (baseAddrVar w K)) (.const (j : F)) ::
    (List.range w).map fun t => .var (laneWordCol w j t)

/-- The `K`-lane vectorized ROM circuit for width-`w` entries:
* `width := K * (w + 1)` main columns (`mult_j, word_{j,0}, ..., word_{j,w-1}` for `j < K`);
* `fixedWidth := 1` (single fixed column `addr_base = K * r` at var `K * (w + 1)`);
* `constraints := []`;
* `lookups` = `K` lookups using degree-1 address expressions `addr_base + j`. -/
def vectorRomCircuit (w K : Nat) : Tiling.Circuit F where
  width := K * (w + 1)
  fixedWidth := 1
  constraints := []
  lookups := (List.range K).map (vectorRomLaneLookup (F := F) w K)

/-- Fixed matrix of a `K`-lane vectorized ROM table: column `0` at physical row `r`
holds `addr_base = ((K * r : Nat) : F)`. -/
def vectorRomFixed (K : Nat) (r : Nat) : Nat → F :=
  fun _ => ((K * r : Nat) : F)

/-- A `K`-lane vectorized ROM `Air` for width-`w` entries with capacity `cap`:
`rows := vectorRomRows K cap = (cap + K - 1) / K`, covering `K * rows` consecutive
addresses `0 .. K * rows - 1`. -/
def vectorRomAir (w K cap : Nat) : Air F :=
  ⟨vectorRomCircuit w K, vectorRomRows K cap, vectorRomFixed K⟩

/-- One `K`-lane vectorized ROM table per `(words, capacity)` pair. -/
def vectorRomAirs (K : Nat) (roms : List (Nat × Nat)) : List (Air F) :=
  roms.map fun r => vectorRomAir r.1 K r.2

/-- Effective scalar capacities covered by `vectorRomAirs K roms`: each `(w, cap)`
covers `K * vectorRomRows K cap` consecutive addresses `0 .. K * rows - 1`. -/
def expandedRoms (K : Nat) (roms : List (Nat × Nat)) : List (Nat × Nat) :=
  roms.map fun r => (r.1, K * vectorRomRows K r.2)

/-- Every variable in `vectorRomCircuit w K` is strictly below `width + fixedWidth`. -/
theorem vectorRomCircuit_inBounds (w K : Nat) :
    SingleCircuit.Circuit.inBounds (vectorRomCircuit (F := F) w K) = true := by
  simp only [SingleCircuit.Circuit.inBounds, vectorRomCircuit, SingleCircuit.Lookup.inBounds,
    List.all_nil, Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range]
  rintro _ ⟨j, hj, rfl⟩
  simp only [vectorRomLaneLookup, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    List.mem_map, List.mem_range, SingleCircuit.inBounds_const, SingleCircuit.inBounds_var,
    SingleCircuit.inBounds_sub, SingleCircuit.inBounds_add, true_and]
  have hMult : laneMultCol w j < K * (w + 1) := laneMultCol_lt hj
  refine ⟨by omega, ⟨by unfold baseAddrVar; omega, trivial⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [SingleCircuit.inBounds_var]
  have hWord : laneWordCol w j t < K * (w + 1) := laneWordCol_lt hj ht
  omega

/-- Every variable in `(vectorRomAir w K cap).circuit` is strictly below `width + fixedWidth`. -/
theorem vectorRom_inBounds (w K cap : Nat) :
    SingleCircuit.Circuit.inBounds (vectorRomAir (F := F) w K cap).circuit = true :=
  vectorRomCircuit_inBounds w K

/-- Every `Air` in `vectorRomAirs K roms` passes `SingleCircuit.Circuit.inBounds`. -/
theorem vectorRomAirs_inBounds (K : Nat) (roms : List (Nat × Nat)) :
    ∀ a ∈ vectorRomAirs (F := F) K roms, SingleCircuit.Circuit.inBounds a.circuit = true := by
  intro a ha
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
  exact vectorRom_inBounds r.1 K r.2

/-- `(vectorRomAir w K cap).Holds main` trivially holds (`constraints := []`). -/
theorem vectorRom_holds (w K cap : Nat) (main : Nat → Scalar.Circuit.Var → F) :
    (vectorRomAir w K cap).Holds main := by
  intro _ _ p hp
  cases hp

/-- Every vectorized ROM table trivially holds (`constraints := []`). -/
theorem vectorRomAirs_holds (K : Nat) (roms : List (Nat × Nat))
    (mainR : Nat → Nat → Scalar.Circuit.Var → F) :
    StageHolds (vectorRomAirs K roms) mainR := by
  rintro ⟨a, j⟩ hx
  have hmem := List.fst_mem_of_mem_zipIdx hx
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hmem
  exact vectorRom_holds r.1 K r.2 (mainR j)

end Defs

/-! ## 3. Exact ROM equivalence & ledger theorems -/

section Equivalence

variable {F : Type} [Field F]

/-- Unpack a `K`-lane vectorized ROM trace `main` (`rows` rows, main width `K * (w + 1)`)
into an equivalent scalar ROM trace (`K * rows` rows, main width `w + 1`): scalar row
`i` reads lane `i % K` of physical row `i / K`. -/
def unpackVectorRomMain (w K : Nat) (main : Nat → Scalar.Circuit.Var → F) : Nat → Scalar.Circuit.Var → F :=
  fun i v => main (i / K) ((i % K) * (w + 1) + v)

/-- Pack a scalar ROM trace (`K * rows` rows, main width `w + 1`) into a `K`-lane
vectorized ROM trace (`rows` rows, main width `K * (w + 1)`). -/
def packVectorRomMain (w K : Nat) (scalarMain : Nat → Scalar.Circuit.Var → F) : Nat → Scalar.Circuit.Var → F :=
  fun r v => scalarMain (K * r + v / (w + 1)) (v % (w + 1))

/-- Pack a `cap`-row scalar ROM trace into a `K`-lane vectorized ROM trace of
`vectorRomRows K cap` rows, padding tail lanes `K * r + j ≥ cap` with `0`
(in particular `0` multiplicity). -/
def packVectorRomMainPadded (w K cap : Nat) (scalarMain : Nat → Scalar.Circuit.Var → F) : Nat → Scalar.Circuit.Var → F :=
  fun r v =>
    let j := v / (w + 1)
    let off := v % (w + 1)
    if K * r + j < cap then scalarMain (K * r + j) off else 0

omit [Field F] in
theorem unpackVectorRomMain_at {w K : Nat} (main : Nat → Scalar.Circuit.Var → F) (r : Nat)
    {j : Nat} (hj : j < K) (v : Nat) :
    unpackVectorRomMain w K main (K * r + j) v = main r (j * (w + 1) + v) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  simp only [unpackVectorRomMain]
  rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hj, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

omit [Field F] in
theorem unpack_packVectorRomMain {w K : Nat} (scalarMain : Nat → Scalar.Circuit.Var → F)
    (i : Nat) {v : Nat} (hv : v < w + 1) :
    unpackVectorRomMain w K (packVectorRomMain w K scalarMain) i v = scalarMain i v := by
  have hw : 0 < w + 1 := Nat.succ_pos w
  simp only [unpackVectorRomMain, packVectorRomMain]
  rw [Nat.mul_comm (i % K) (w + 1), Nat.mul_add_div hw, Nat.div_eq_of_lt hv, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hv, Nat.div_add_mod]

theorem unpack_packVectorRomMainPadded {w K cap : Nat}
    (scalarMain : Nat → Scalar.Circuit.Var → F) (i : Nat) {v : Nat} (hv : v < w + 1) :
    unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain) i v =
      if i < cap then scalarMain i v else 0 := by
  have hw : 0 < w + 1 := Nat.succ_pos w
  simp only [unpackVectorRomMain, packVectorRomMainPadded]
  rw [Nat.mul_comm (i % K) (w + 1), Nat.mul_add_div hw, Nat.div_eq_of_lt hv, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hv, Nat.div_add_mod]

omit [Field F] in
theorem pack_unpackVectorRomMain {w K : Nat} (main : Nat → Scalar.Circuit.Var → F) (r : Nat)
    {v : Nat} (hv : v < K * (w + 1)) :
    packVectorRomMain w K (unpackVectorRomMain w K main) r v = main r v := by
  have hw : 0 < w + 1 := Nat.succ_pos w
  have hj : v / (w + 1) < K := by
    rw [Nat.div_lt_iff_lt_mul hw]
    exact hv
  simp only [packVectorRomMain]
  rw [unpackVectorRomMain_at main r hj (v % (w + 1))]
  have hdiv : v / (w + 1) * (w + 1) + v % (w + 1) = v := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod v (w + 1)
  rw [hdiv]

/-- Double-sum flattening: summing `f (K * r + j)` over `r < rows` and `j < K` equals
summing `f i` over `i < K * rows`. -/
theorem sum_range_mul {M : Type} [AddCommMonoid M] (K rows : Nat) (f : Nat → M) :
    ((List.range rows).map fun r => ((List.range K).map fun j => f (K * r + j)).sum).sum =
      ((List.range (K * rows)).map f).sum := by
  induction rows with
  | zero => simp
  | succ rows ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Nat.mul_succ, List.range_add, List.map_append, List.sum_append, List.map_map]
      rfl

/-- Lane `j` of row `r` in `vectorRomAir w K cap` emits the exact lookup entry of scalar
row `K * r + j` in `romAir w N` under `unpackVectorRomMain w K main`. -/
theorem vectorRomAir_lane_entry (w K cap N : Nat) (main : Nat → Scalar.Circuit.Var → F)
    (r : Nat) {j : Nat} (hj : j < K) :
    (vectorRomLaneLookup (F := F) w K j).entry ((vectorRomAir w K cap).assign main r) =
      (romAir w N).circuit.rowLedger ((romAir w N).assign (unpackVectorRomMain w K main) (K * r + j)) := by
  rw [romAir_rowLedger]
  have hMultLt : laneMultCol w j < K * (w + 1) := laneMultCol_lt hj
  have hWords :
      ((List.range w).map fun t =>
        ((Scalar.Circuit.ArithExpr.var (laneWordCol w j t) : Scalar.Circuit.ArithExpr F).denote
          ((vectorRomAir w K cap).assign main r))) =
        romWords w (unpackVectorRomMain w K main) (K * r + j) := by
    unfold romWords
    apply List.map_congr_left
    intro t ht
    have htLt : t < w := List.mem_range.mp ht
    have hWordLt : laneWordCol w j t < K * (w + 1) := laneWordCol_lt hj htLt
    simp only [Scalar.Circuit.ArithExpr.denote, Air.assign_apply, vectorRomAir, vectorRomCircuit,
      hWordLt, ite_true]
    rw [unpackVectorRomMain_at main r hj (t + 1)]
    unfold laneWordCol
    have heq : j * (w + 1) + 1 + t = j * (w + 1) + (t + 1) := by omega
    rw [heq]
  have hMult :
      (Scalar.Circuit.ArithExpr.sub (.const 0) (.var (laneMultCol w j))).denote
        ((vectorRomAir w K cap).assign main r) =
        -(unpackVectorRomMain w K main (K * r + j) 0) := by
    simp only [Scalar.Circuit.ArithExpr.denote, Air.assign_apply, vectorRomAir, vectorRomCircuit,
      hMultLt, ite_true, zero_sub]
    rw [unpackVectorRomMain_at main r hj 0, Nat.add_zero]
    rfl
  have hAddr :
      (Scalar.Circuit.ArithExpr.add (.var (baseAddrVar w K)) (.const (j : F))).denote
        ((vectorRomAir w K cap).assign main r) = ((K * r + j : Nat) : F) := by
    simp only [Scalar.Circuit.ArithExpr.denote, Air.assign_apply, vectorRomAir, vectorRomCircuit,
      baseAddrVar, lt_irrefl, ite_false, vectorRomFixed, Nat.cast_add]
  simp only [Lookup.entry, Lookup.tuple, vectorRomLaneLookup, List.map_cons, List.map_map,
    Function.comp_def, encodeRom, Erasure.pack, hMult]
  congr 1
  simp only [Scalar.Circuit.ArithExpr.denote, List.cons.injEq, romWords_length, true_and]
  exact ⟨hAddr, hWords⟩

/-- Row `r` of `vectorRomAir w K cap` has row ledger equal to the sum of the `K` consecutive
scalar ROM rows `K * r + 0 .. K * r + (K - 1)` under `unpackVectorRomMain w K main`. -/
theorem vectorRomAir_rowLedger (w K cap N : Nat) (main : Nat → Scalar.Circuit.Var → F) (r : Nat) :
    (vectorRomAir w K cap).circuit.rowLedger ((vectorRomAir w K cap).assign main r) =
      ((List.range K).map fun j =>
        (romAir w N).circuit.rowLedger
          ((romAir w N).assign (unpackVectorRomMain w K main) (K * r + j))).sum := by
  simp only [Circuit.rowLedger, vectorRomAir, vectorRomCircuit, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact vectorRomAir_lane_entry w K cap N main r (List.mem_range.mp hj)

/-- **Exact vectorized ROM ledger equivalence:**
`(vectorRomAir w K cap).ledger main` equals the scalar ROM ledger of `romAir w (K * rows)`
on `unpackVectorRomMain w K main`. -/
theorem vectorRomAir_ledger_eq (w K cap : Nat) (main : Nat → Scalar.Circuit.Var → F) :
    (vectorRomAir w K cap).ledger main =
      (romAir w (K * vectorRomRows K cap)).ledger (unpackVectorRomMain w K main) := by
  unfold Air.ledger
  change ((List.range (vectorRomRows K cap)).map fun r =>
      (vectorRomAir w K cap).circuit.rowLedger ((vectorRomAir w K cap).assign main r)).sum = _
  have hrow : ∀ r ∈ List.range (vectorRomRows K cap),
      (vectorRomAir w K cap).circuit.rowLedger ((vectorRomAir w K cap).assign main r) =
        ((List.range K).map fun j =>
          (romAir w (K * vectorRomRows K cap)).circuit.rowLedger
            ((romAir w (K * vectorRomRows K cap)).assign (unpackVectorRomMain w K main) (K * r + j))).sum := by
    intro r _
    exact vectorRomAir_rowLedger w K cap (K * vectorRomRows K cap) main r
  rw [List.map_congr_left hrow]
  exact sum_range_mul K (vectorRomRows K cap) fun i =>
    (romAir w (K * vectorRomRows K cap)).circuit.rowLedger
      ((romAir w (K * vectorRomRows K cap)).assign (unpackVectorRomMain w K main) i)

/-- **Prover completeness (full `K * rows` scalar trace):**
packing `scalarMain` via `packVectorRomMain w K scalarMain` yields the exact ledger of
`romAir w (K * vectorRomRows K cap)`. -/
theorem vectorRomAir_ledger_pack (w K cap : Nat) (scalarMain : Nat → Scalar.Circuit.Var → F) :
    (vectorRomAir w K cap).ledger (packVectorRomMain w K scalarMain) =
      (romAir w (K * vectorRomRows K cap)).ledger scalarMain := by
  rw [vectorRomAir_ledger_eq]
  unfold Air.ledger
  congr 1
  apply List.map_congr_left
  intro i _
  have hassign :
      (romAir w (K * vectorRomRows K cap)).assign
        (unpackVectorRomMain w K (packVectorRomMain w K scalarMain)) i =
      (romAir w (K * vectorRomRows K cap)).assign scalarMain i := by
    funext v
    simp only [Air.assign_apply, romAir, romCircuit]
    split
    · exact unpack_packVectorRomMain scalarMain i ‹_›
    · rfl
  rw [hassign]

/-- **Prover completeness (tail-padded `cap`-row scalar trace):**
for any `K > 0`, packing a `cap`-row scalar trace with `packVectorRomMainPadded`
(zeroing tail lanes `K * r + j ≥ cap`) yields the exact ledger of `romAir w cap`. -/
theorem vectorRomAir_ledger_packPadded {w K cap : Nat} (hK : 0 < K)
    (scalarMain : Nat → Scalar.Circuit.Var → F) :
    (vectorRomAir w K cap).ledger (packVectorRomMainPadded w K cap scalarMain) =
      (romAir w cap).ledger scalarMain := by
  rw [vectorRomAir_ledger_eq]
  have hle : cap ≤ K * vectorRomRows K cap := cap_le_mul_vectorRomRows hK
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  unfold Air.ledger
  change ((List.range (K * vectorRomRows K cap)).map fun i =>
      (romAir w (K * vectorRomRows K cap)).circuit.rowLedger
        ((romAir w (K * vectorRomRows K cap)).assign
          (unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain)) i)).sum = _
  rw [hd, List.range_add, List.map_append, List.sum_append]
  have hActive :
      ((List.range cap).map fun i =>
        (romAir w (cap + d)).circuit.rowLedger
          ((romAir w (cap + d)).assign
            (unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain)) i)) =
      (List.range cap).map fun i =>
        (romAir w cap).circuit.rowLedger ((romAir w cap).assign scalarMain i) := by
    apply List.map_congr_left
    intro i hi
    have hiLt : i < cap := List.mem_range.mp hi
    rw [romAir_rowLedger, romAir_rowLedger]
    have hMult :
        unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain) i 0 =
          scalarMain i 0 := by
      simp [unpack_packVectorRomMainPadded scalarMain i (Nat.succ_pos w), hiLt]
    have hWords :
        romWords w (unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain)) i =
          romWords w scalarMain i := by
      unfold romWords
      apply List.map_congr_left
      intro t ht
      have htLt : t + 1 < w + 1 := Nat.succ_lt_succ (List.mem_range.mp ht)
      simp [unpack_packVectorRomMainPadded scalarMain i htLt, hiLt]
    rw [hMult, hWords]
  have hTail :
      (((List.range d).map (cap + ·)).map fun i =>
        (romAir w (cap + d)).circuit.rowLedger
          ((romAir w (cap + d)).assign
            (unpackVectorRomMain w K (packVectorRomMainPadded w K cap scalarMain)) i)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hi
    rw [romAir_rowLedger,
      unpack_packVectorRomMainPadded scalarMain (cap + e) (Nat.succ_pos w)]
    simp [show ¬ (cap + e < cap) by omega]
  rw [hActive, hTail, add_zero]
  rfl

/-! ### Stage-level vectorized ROM helpers -/

/-- Unpack a family of `K`-lane vectorized ROM traces `mainR` into the equivalent
family of scalar ROM traces for `expandedRoms K roms`. -/
def unpackVectorRomMains (K : Nat) (roms : List (Nat × Nat))
    (mainR : Nat → Nat → Scalar.Circuit.Var → F) : Nat → Nat → Scalar.Circuit.Var → F :=
  fun j => unpackVectorRomMain (roms.getD j (0, 0)).1 K (mainR j)

/-- Pack a family of scalar ROM traces `scalarMainR` into `K`-lane vectorized ROM
traces for `vectorRomAirs K roms`. -/
def packVectorRomMains (K : Nat) (roms : List (Nat × Nat))
    (scalarMainR : Nat → Nat → Scalar.Circuit.Var → F) : Nat → Nat → Scalar.Circuit.Var → F :=
  fun j => packVectorRomMain (roms.getD j (0, 0)).1 K (scalarMainR j)

/-- Pack a family of `cap`-row scalar ROM traces into `K`-lane vectorized ROM traces
for `vectorRomAirs K roms`, zero-padding tail lanes `K * r + j ≥ cap`. -/
def packVectorRomMainsPadded (K : Nat) (roms : List (Nat × Nat))
    (scalarMainR : Nat → Nat → Scalar.Circuit.Var → F) : Nat → Nat → Scalar.Circuit.Var → F :=
  fun j => packVectorRomMainPadded (roms.getD j (0, 0)).1 K (roms.getD j (0, 0)).2 (scalarMainR j)

/-- The `WidthROM` represented by a family of `K`-lane vectorized ROM traces. -/
def wideVectorRom (K : Nat) (roms : List (Nat × Nat))
    (mainR : Nat → Nat → Scalar.Circuit.Var → F) : WidthROM F :=
  WideStage.wideRom (expandedRoms K roms) (unpackVectorRomMains K roms mainR)

theorem vectorRomAirs_ledger_eq (K : Nat) (roms : List (Nat × Nat))
    (mainR : Nat → Nat → Scalar.Circuit.Var → F) :
    stageLedger (vectorRomAirs K roms) mainR =
      stageLedger (romAirs (expandedRoms K roms)) (unpackVectorRomMains K roms mainR) := by
  simp only [stageLedger, vectorRomAirs, romAirs, expandedRoms, ← List.map_zipIdx, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨r, j⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hgetD : roms.getD j (0, 0) = r := by
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  simp only [Function.comp_def, Prod.map, id, unpackVectorRomMains, hgetD]
  exact vectorRomAir_ledger_eq r.1 K r.2 (mainR j)

theorem vectorRomAirs_ledger_pack (K : Nat) (roms : List (Nat × Nat))
    (scalarMainR : Nat → Nat → Scalar.Circuit.Var → F) :
    stageLedger (vectorRomAirs K roms) (packVectorRomMains K roms scalarMainR) =
      stageLedger (romAirs (expandedRoms K roms)) scalarMainR := by
  simp only [stageLedger, vectorRomAirs, romAirs, expandedRoms, ← List.map_zipIdx, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨r, j⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hgetD : roms.getD j (0, 0) = r := by
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  simp only [Function.comp_def, Prod.map, id, packVectorRomMains, hgetD]
  exact vectorRomAir_ledger_pack r.1 K r.2 (scalarMainR j)

theorem vectorRomAirs_ledger_packPadded {K : Nat} (hK : 0 < K) (roms : List (Nat × Nat))
    (scalarMainR : Nat → Nat → Scalar.Circuit.Var → F) :
    stageLedger (vectorRomAirs K roms) (packVectorRomMainsPadded K roms scalarMainR) =
      stageLedger (romAirs roms) scalarMainR := by
  simp only [stageLedger, vectorRomAirs, romAirs, ← List.map_zipIdx, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨r, j⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hgetD : roms.getD j (0, 0) = r := by
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  simp only [Function.comp_def, Prod.map, id, packVectorRomMainsPadded, hgetD]
  exact vectorRomAir_ledger_packPadded hK (scalarMainR j)

end Equivalence

/-! ## 4. End-to-end multi-field soundness corollaries -/

section Soundness

/-- **End-to-end generic wide stage with `K`-lane vectorized ROM tables.**
Composes `vectorRomAirs_ledger_eq` directly with `WideStage.wide_heap_sound` over any
`[Field F] [DecidableEq F]`. -/
theorem wide_vector_rom_sound {F : Type} [Field F] [DecidableEq F]
    {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
    {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip F × Option (Unroll F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, K * vectorRomRows K r.2 ≤ bound)
    (small : SmallCast F bound) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holds : StageHolds (unitAirs idOf units) mainU)
    (balanced : stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (vectorRomAirs K roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideVectorRom K roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideVectorRom K roms mainR)).decode
          specialized.program.enums) heap value result := by
  rw [vectorRomAirs_ledger_eq] at balanced
  have widths' : ((expandedRoms K roms).map Prod.fst).Nodup := by
    simpa [expandedRoms, List.map_map, Function.comp_def] using widths
  have romCaps' : ∀ r ∈ expandedRoms K roms, r.2 ≤ bound := by
    rintro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact romCaps p hp
  exact WideStage.wide_heap_sound compiled prepared certified plan activated entry signed rooted
    outside arguments decoded idOf chipsIn unrolled capacity widths' romCaps' small tags lookups
    characteristic shaped context enablesOk holds balanced

/-- **Endpoint 1 (`Goldilocks`):** end-to-end wide stage with `K`-lane vectorized ROM tables. -/
theorem wide_vector_rom_sound_goldilocks
    {source : Generic.Source (ZMod Aiur.Library.U32.Goldilocks.modulus)} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue (ZMod Aiur.Library.U32.Goldilocks.modulus))}
    {result : Value (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    {wires : List (WireValue (ZMod Aiur.Library.U32.Goldilocks.modulus))}
    {output : WireValue (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat)
    {units : List ((Chip (ZMod Aiur.Library.U32.Goldilocks.modulus) ×
      Option (Unroll (ZMod Aiur.Library.U32.Goldilocks.modulus))) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, K * vectorRomRows K r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → ZMod Aiur.Library.U32.Goldilocks.modulus}
    (holds : StageHolds (unitAirs idOf units) mainU)
    (balanced : stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (vectorRomAirs K roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideVectorRom K roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideVectorRom K roms mainR)).decode
          specialized.program.enums) heap value result :=
  wide_vector_rom_sound compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf chipsIn unrolled capacity widths romCaps
    (Goldilocks.smallCast hbound) tags lookups (Goldilocks.characteristic hbits)
    shaped context enablesOk holds balanced

/-- **Endpoint 2 (`BLS12-381`):** end-to-end wide stage with `K`-lane vectorized ROM tables. -/
theorem wide_vector_rom_sound_bls12381
    {source : Generic.Source Aiur.Library.Field.BLS12381.F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    {result : Value Aiur.Library.Field.BLS12381.F}
    {wires : List (WireValue Aiur.Library.Field.BLS12381.F)}
    {output : WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat)
    {units : List ((Chip Aiur.Library.Field.BLS12381.F ×
      Option (Unroll Aiur.Library.Field.BLS12381.F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, K * vectorRomRows K r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 254) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {mainU mainM mainR : Nat → Nat → Scalar.Circuit.Var → Aiur.Library.Field.BLS12381.F}
    (holds : StageHolds (unitAirs idOf units) mainU)
    (balanced : stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap) mainM +
      stageLedger (vectorRomAirs K roms) mainR + Finsupp.single (encode idOf root) 1 = 0) :
    (wideVectorRom K roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideVectorRom K roms mainR)).decode
          specialized.program.enums) heap value result :=
  wide_vector_rom_sound compiled prepared certified plan activated entry signed rooted outside
    arguments decoded idOf chipsIn unrolled capacity widths romCaps
    (BLS12381.smallCast hbound) tags lookups (BLS12381.characteristic hbits)
    shaped context enablesOk holds balanced

/-! ## 5. Composition with `SingleCircuit.pack` (`num_circuits == 1`) -/

section SingleCircuitComposition

/-- All tables of a wide stage with `K`-lane vectorized ROM tables concatenated in order:
units, map tables, vectorized ROM tables. -/
def wideVectorAirs {F : Type} [Field F] [DecidableEq F] (idOf : String → Nat)
    (units : List ((Chip F × Option (Unroll F)) × Nat))
    (claims : List (List F)) (mapCap : Nat → Nat)
    (K : Nat) (roms : List (Nat × Nat)) : List (Air F) :=
  unitAirs idOf units ++ mapAirs claims mapCap ++ vectorRomAirs K roms

theorem wideVectorAirs_inBounds {F : Type} [Field F] [DecidableEq F] {idOf : String → Nat}
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {claims : List (List F)} {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (hUnits : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true) :
    ∀ a ∈ wideVectorAirs idOf units claims mapCap K roms,
      SingleCircuit.Circuit.inBounds a.circuit = true := by
  intro a ha
  simp only [wideVectorAirs, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact hUnits u hu
  · obtain ⟨L, _, rfl⟩ := List.mem_map.mp ha
    exact SingleCircuit.mapAir_inBounds L (claimsOf claims L) (mapCap L)
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    exact vectorRom_inBounds r.1 K r.2

theorem wideVectorAirs_rows_le {F : Type} [Field F] [DecidableEq F] {idOf : String → Nat}
    {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {claims : List (List F)} {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)} {rows : Nat}
    (hUnits : ∀ u ∈ units, u.2 ≤ rows)
    (hMaps : ∀ L ∈ mapLengths claims, mapCap L ≤ rows)
    (hRoms : ∀ r ∈ roms, vectorRomRows K r.2 ≤ rows) :
    ∀ a ∈ wideVectorAirs idOf units claims mapCap K roms, a.rows ≤ rows := by
  intro a ha
  simp only [wideVectorAirs, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact hUnits u hu
  · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp ha
    exact hMaps L hL
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact hRoms r hr

/-- **End-to-end wide stage with `K`-lane vectorized ROM + horizontal `SingleCircuit.pack`
over Goldilocks (`num_circuits == 1`).**
Notice that `romsTall` only requires `vectorRomRows K r.2 ≤ rows` (cutting the minimum
packed circuit height by `K×` on ROM-dominated programs!). -/
theorem wide_vector_rom_single_circuit_sound_goldilocks
    {source : Generic.Source (ZMod Aiur.Library.U32.Goldilocks.modulus)} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue (ZMod Aiur.Library.U32.Goldilocks.modulus))}
    {result : Value (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    {wires : List (WireValue (ZMod Aiur.Library.U32.Goldilocks.modulus))}
    {output : WireValue (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message (ZMod Aiur.Library.U32.Goldilocks.modulus)}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat)
    {units : List ((Chip (ZMod Aiur.Library.U32.Goldilocks.modulus) ×
      Option (Unroll (ZMod Aiur.Library.U32.Goldilocks.modulus))) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (unitsInBounds : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, K * vectorRomRows K r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {rows : Nat}
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ mapLengths ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)),
      mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, vectorRomRows K r.2 ≤ rows)
    {main : Nat → Nat → ZMod Aiur.Library.U32.Goldilocks.modulus}
    (holds : (SingleCircuit.pack (wideVectorAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap K roms) rows).Holds main)
    (balanced : (SingleCircuit.pack (wideVectorAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap K roms) rows).ledger main +
      Finsupp.single (encode idOf root) 1 = 0) :
    let claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
    let airs := wideVectorAirs idOf units claims mapCap K roms
    let mainR := fun j => SingleCircuit.sliceMain airs main
      (units.length + (mapLengths claims).length + j)
    (wideVectorRom K roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideVectorRom K roms mainR)).decode
          specialized.program.enums) heap value result := by
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set airs := wideVectorAirs idOf units claims mapCap K roms
  set mainU := SingleCircuit.sliceMain airs main
  set mainM := fun j => SingleCircuit.sliceMain airs main (units.length + j)
  set mainR := fun j => SingleCircuit.sliceMain airs main
    (units.length + (mapLengths claims).length + j)
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    wideVectorAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    wideVectorAirs_rows_le unitsTall mapsTall romsTall
  have hStage : StageHolds airs (SingleCircuit.sliceMain airs main) :=
    SingleCircuit.pack_holds_sound hIn hRows holds
  have hUnitsHolds : StageHolds (unitAirs idOf units) mainU := by
    have h1 := (SingleCircuit.stageHolds_append _ _ _).mp hStage
    exact ((SingleCircuit.stageHolds_append _ _ _).mp h1.1).1
  have hLedger : (SingleCircuit.pack airs rows).ledger main =
      stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs claims mapCap) mainM +
      stageLedger (vectorRomAirs K roms) mainR := by
    rw [SingleCircuit.pack_ledger_eq main hIn hRows]
    simp only [airs, wideVectorAirs, SingleCircuit.stageLedger_append, unitAirs, mapAirs,
      List.length_append, List.length_map]
    rfl
  rw [hLedger] at balanced
  exact wide_vector_rom_sound_goldilocks compiled prepared certified plan activated entry signed
    rooted outside arguments decoded idOf chipsIn unrolled capacity widths romCaps hbound tags
    lookups hbits shaped context enablesOk hUnitsHolds balanced

/-- **End-to-end wide stage with `K`-lane vectorized ROM + horizontal `SingleCircuit.pack`
over BLS12-381 (`num_circuits == 1`).** -/
theorem wide_vector_rom_single_circuit_sound_bls12381
    {source : Generic.Source Aiur.Library.Field.BLS12381.F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    {result : Value Aiur.Library.Field.BLS12381.F}
    {wires : List (WireValue Aiur.Library.Field.BLS12381.F)}
    {output : WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat)
    {units : List ((Chip Aiur.Library.Field.BLS12381.F ×
      Option (Unroll Aiur.Library.Field.BLS12381.F)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (unitsInBounds : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (capacity : unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)}
    (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, K * vectorRomRows K r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 254) (tags : 2 < bound) (lookups : unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 214)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {rows : Nat}
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ mapLengths ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)),
      mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, vectorRomRows K r.2 ≤ rows)
    {main : Nat → Nat → Aiur.Library.Field.BLS12381.F}
    (holds : (SingleCircuit.pack (wideVectorAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap K roms) rows).Holds main)
    (balanced : (SingleCircuit.pack (wideVectorAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap K roms) rows).ledger main +
      Finsupp.single (encode idOf root) 1 = 0) :
    let claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
    let airs := wideVectorAirs idOf units claims mapCap K roms
    let mainR := fun j => SingleCircuit.sliceMain airs main
      (units.length + (mapLengths claims).length + j)
    (wideVectorRom K roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (wideVectorRom K roms mainR)).decode
          specialized.program.enums) heap value result := by
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set airs := wideVectorAirs idOf units claims mapCap K roms
  set mainU := SingleCircuit.sliceMain airs main
  set mainM := fun j => SingleCircuit.sliceMain airs main (units.length + j)
  set mainR := fun j => SingleCircuit.sliceMain airs main
    (units.length + (mapLengths claims).length + j)
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    wideVectorAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    wideVectorAirs_rows_le unitsTall mapsTall romsTall
  have hStage : StageHolds airs (SingleCircuit.sliceMain airs main) :=
    SingleCircuit.pack_holds_sound hIn hRows holds
  have hUnitsHolds : StageHolds (unitAirs idOf units) mainU := by
    have h1 := (SingleCircuit.stageHolds_append _ _ _).mp hStage
    exact ((SingleCircuit.stageHolds_append _ _ _).mp h1.1).1
  have hLedger : (SingleCircuit.pack airs rows).ledger main =
      stageLedger (unitAirs idOf units) mainU +
      stageLedger (mapAirs claims mapCap) mainM +
      stageLedger (vectorRomAirs K roms) mainR := by
    rw [SingleCircuit.pack_ledger_eq main hIn hRows]
    simp only [airs, wideVectorAirs, SingleCircuit.stageLedger_append, unitAirs, mapAirs,
      List.length_append, List.length_map]
    rfl
  rw [hLedger] at balanced
  exact wide_vector_rom_sound_bls12381 compiled prepared certified plan activated entry signed
    rooted outside arguments decoded idOf chipsIn unrolled capacity widths romCaps hbound tags
    lookups hbits shaped context enablesOk hUnitsHolds balanced

/-- **Prover completeness for horizontally packed wide stage with `K`-lane vectorized ROM.** -/
theorem wide_vector_rom_single_circuit_complete {F : Type} [Field F] [DecidableEq F]
    {idOf : String → Nat} {units : List ((Chip F × Option (Unroll F)) × Nat)}
    {claims : List (List F)} {mapCap : Nat → Nat} {K : Nat} {roms : List (Nat × Nat)} {rows : Nat}
    (unitsInBounds : ∀ u ∈ units, SingleCircuit.Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ mapLengths claims, mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, vectorRomRows K r.2 ≤ rows)
    {mainU mainM scalarMainR : Nat → Nat → Scalar.Circuit.Var → F}
    (holdsU : StageHolds (unitAirs idOf units) mainU) :
    let airs := wideVectorAirs idOf units claims mapCap K roms
    let mains := SingleCircuit.appendMains (units.length + (mapLengths claims).length)
      (SingleCircuit.appendMains units.length mainU mainM)
      (packVectorRomMains K roms scalarMainR)
    (SingleCircuit.pack airs rows).Holds (SingleCircuit.packMain airs mains) ∧
      (SingleCircuit.pack airs rows).ledger (SingleCircuit.packMain airs mains) =
        stageLedger (unitAirs idOf units) mainU +
        stageLedger (mapAirs claims mapCap) mainM +
        stageLedger (romAirs (expandedRoms K roms)) scalarMainR := by
  set airs := wideVectorAirs idOf units claims mapCap K roms
  set mains := SingleCircuit.appendMains (units.length + (mapLengths claims).length)
    (SingleCircuit.appendMains units.length mainU mainM)
    (packVectorRomMains K roms scalarMainR)
  have hIn : ∀ a ∈ airs, SingleCircuit.Circuit.inBounds a.circuit = true :=
    wideVectorAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    wideVectorAirs_rows_le unitsTall mapsTall romsTall
  have hLenU : (unitAirs idOf units).length = units.length := by simp [unitAirs]
  have hLenM : (mapAirs claims mapCap).length = (mapLengths claims).length := by simp [mapAirs]
  have hLenUM : (unitAirs idOf units ++ mapAirs claims mapCap).length =
      units.length + (mapLengths claims).length := by
    rw [List.length_append, hLenU, hLenM]
  have holdsM : StageHolds (mapAirs claims mapCap) mainM := by
    rintro ⟨a, j⟩ hx i _ p hp
    have hmem := List.fst_mem_of_mem_zipIdx hx
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp hmem
    cases hp
  have holdsR : StageHolds (vectorRomAirs K roms) (packVectorRomMains K roms scalarMainR) :=
    vectorRomAirs_holds K roms (packVectorRomMains K roms scalarMainR)
  have hStage : StageHolds airs mains := by
    simp only [airs, wideVectorAirs, mains, ← hLenUM]
    rw [SingleCircuit.stageHolds_appendMains]
    refine ⟨?_, holdsR⟩
    rw [← hLenU, SingleCircuit.stageHolds_appendMains]
    exact ⟨holdsU, holdsM⟩
  refine ⟨SingleCircuit.pack_holds_complete hIn hRows hStage, ?_⟩
  rw [SingleCircuit.pack_ledger_packMain mains hIn hRows]
  simp only [airs, wideVectorAirs, mains, ← hLenUM]
  rw [SingleCircuit.stageLedger_appendMains, ← hLenU, SingleCircuit.stageLedger_appendMains,
    vectorRomAirs_ledger_pack]

end SingleCircuitComposition

end Soundness

/-! ## 6. Executable `#guard` smoke tests -/

section SmokeTests

private abbrev SmokeGF := ZMod Aiur.Library.U32.Goldilocks.modulus

/-- Evaluate every lookup of an `Air` across all rows as a concrete list of `(tuple, mult)` pairs. -/
private def evalAirLookups (a : Air SmokeGF) (main : Nat → Scalar.Circuit.Var → SmokeGF) :
    List (List SmokeGF × SmokeGF) :=
  (List.range a.rows).flatMap fun r =>
    let env := a.assign main r
    a.circuit.lookups.map fun lk =>
      (lk.args.map (·.denote env), lk.multiplicity.denote env)

/-- Concrete scalar ROM trace with `w = 3`, `16` entries (`addr = 0..15`), distinct
multiplicities and payloads. -/
private def smokeScalarMain : Nat → Scalar.Circuit.Var → SmokeGF := fun i v =>
  match v with
  | 0 => ((i + 1 : Nat) : SmokeGF)
  | 1 => ((100 + i : Nat) : SmokeGF)
  | 2 => ((200 + 3 * i : Nat) : SmokeGF)
  | 3 => ((300 + 7 * i : Nat) : SmokeGF)
  | _ => 0

-- `K = 4, w = 3, cap = 16`: 4 rows & 1 fixed column instead of 16 rows!
#guard (vectorRomAir (F := SmokeGF) 3 4 16).rows == 4
#guard (vectorRomAir (F := SmokeGF) 3 4 16).circuit.width == 16
#guard (vectorRomAir (F := SmokeGF) 3 4 16).circuit.fixedWidth == 1
#guard (vectorRomAir (F := SmokeGF) 3 4 16).circuit.constraints.isEmpty == true
#guard (vectorRomAir (F := SmokeGF) 3 4 16).circuit.lookups.length == 4
#guard SingleCircuit.Circuit.inBounds (vectorRomAir (F := SmokeGF) 3 4 16).circuit == true

-- Row-count compression checks (`1024 → 256 → 128`, non-divisible `17 → 5`):
#guard (vectorRomAir (F := SmokeGF) 3 4 17).rows == 5
#guard (vectorRomAir (F := SmokeGF) 3 4 1024).rows == 256
#guard (vectorRomAir (F := SmokeGF) 3 8 1024).rows == 128
#guard (List.range 4).map (fun r => vectorRomFixed (F := SmokeGF) 4 r 0) == [0, 4, 8, 12]

-- Exact lookup-by-lookup equality between `vectorRomAir 3 4 16` on packed trace and `romAir 3 16`:
#guard evalAirLookups (vectorRomAir (F := SmokeGF) 3 4 16)
    (packVectorRomMain 3 4 smokeScalarMain) ==
  evalAirLookups (romAir (F := SmokeGF) 3 16) smokeScalarMain

-- Exact roundtrip unpack(pack(scalar)) == scalar on all 16 rows × 4 columns:
#guard (List.range 16).all fun i =>
  (List.range 4).all fun v =>
    unpackVectorRomMain 3 4 (packVectorRomMain 3 4 smokeScalarMain) i v == smokeScalarMain i v

-- Exact `Ledger` equality on `K = 4, w = 3, cap = 16` and tail-padded `cap = 17`:
example :
    (vectorRomAir (F := SmokeGF) 3 4 16).ledger (packVectorRomMain 3 4 smokeScalarMain) =
      (romAir (F := SmokeGF) 3 16).ledger smokeScalarMain := by
  simpa [vectorRomRows] using vectorRomAir_ledger_pack (F := SmokeGF) 3 4 16 smokeScalarMain

example :
    (vectorRomAir (F := SmokeGF) 3 4 17).ledger (packVectorRomMainPadded 3 4 17 smokeScalarMain) =
      (romAir (F := SmokeGF) 3 17).ledger smokeScalarMain :=
  vectorRomAir_ledger_packPadded (F := SmokeGF) (by omega) smokeScalarMain

end SmokeTests

/-! ## 7. Axiom audit guards -/

/-- info: 'Aiur.Tiling.VectorRom.vectorRom_inBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorRom_inBounds

/-- info: 'Aiur.Tiling.VectorRom.vectorRom_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorRom_holds

/-- info: 'Aiur.Tiling.VectorRom.vectorRomAir_ledger_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorRomAir_ledger_eq

/-- info: 'Aiur.Tiling.VectorRom.vectorRomAir_ledger_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorRomAir_ledger_pack

/-- info: 'Aiur.Tiling.VectorRom.vectorRomAir_ledger_packPadded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vectorRomAir_ledger_packPadded

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_sound

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_sound_goldilocks

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_sound_bls12381

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_single_circuit_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_single_circuit_sound_goldilocks

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_single_circuit_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_single_circuit_sound_bls12381

/-- info: 'Aiur.Tiling.VectorRom.wide_vector_rom_single_circuit_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_vector_rom_single_circuit_complete

end Aiur.Tiling.VectorRom
