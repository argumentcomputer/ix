import Aiur.Tiling.Goldilocks

/-!
# Certified Horizontal Single-Circuit Packing (`num_circuits == 1`)

This module formalizes horizontal packing of an arbitrary list of row-local
`WideStage.Air` circuits (`airs : List (Air F)`) into a single packed circuit
`pack airs rows : Air F` of uniform height `rows` over any `[Field F] [DecidableEq F]`.

## Design

1. **Disjoint column layout & expression remapping (`remapExpr`, `remapLookup`):**
   Constituent `idx` with `a := airs[idx]` is placed at main column offset
   `mOff = mainOffset airs idx` and fixed column offset `fOff = fixedOffset airs rows idx`
   inside a packed circuit of total main width `W_main = totalMainWidth airs`:
   * Main variable `v < a.circuit.width` maps to `mOff + v`.
   * Fixed variable `v ≥ a.circuit.width` maps to `W_main + fOff + (v - a.circuit.width)`.

2. **Smart active-selector gating (zero overhead on full-height tables):**
   * If `a.rows == rows` (when `a.rows ≤ rows`, equivalently `¬ (a.rows < rows)`):
     **no active selector column is allocated**, and every constraint and lookup
     is simply remapped — zero `+1` constraint degree overhead and zero extra
     fixed column.
   * If `a.rows < rows`: one fixed column `actCol = fOff + a.circuit.fixedWidth`
     is allocated holding `1` for `i < a.rows` and `0` for `a.rows ≤ i < rows`.
     Every remapped constraint `e` is gated to `.mul (.var (W_main + actCol)) e`
     and every remapped lookup multiplicity `m` is gated to
     `.mul (.var (W_main + actCol)) m`, making padding rows `a.rows ≤ i < rows`
     trivially satisfy all constraints and contribute `0` to the lookup ledger.

3. **Soundness & completeness:**
   * `pack_holds_sound`: single-circuit `Holds` implies `StageHolds` on `sliceMain`.
   * `pack_ledger_eq`: single-circuit `ledger` equals `stageLedger` on `sliceMain`.
   * `pack_holds_complete` & `pack_ledger_packMain`: prover completeness via `packMain`.

4. **Goldilocks Endpoint 1 (`num_circuits == 1`) corollaries:**
   * `wide_single_circuit_sound_goldilocks`: composes with `Goldilocks.wide_heap_sound_goldilocks`.
   * `shardAir` / `compactAir` adapters + `narrow_compact_single_circuit_sound_goldilocks`:
     composes with `Goldilocks.narrow_heap_sound_compact_goldilocks`.
-/

namespace Aiur.Tiling.SingleCircuit

open Aiur.Tiling
open Aiur.Tiling.WideStage
open Aiur.Scalar.Circuit (ArithExpr Constraint)

/-! ## 1. Circuit variable bounds -/

section InBounds

variable {F : Type}

/-- Every variable in lookup `l` lies below `numVars`. -/
def Lookup.inBounds (numVars : Nat) (l : Lookup F) : Bool :=
  l.multiplicity.inBounds numVars && l.args.all (·.inBounds numVars)

/-- Every variable in circuit `c` lies below `c.width + c.fixedWidth`
(main columns `0 .. width - 1`, fixed columns `width .. width + fixedWidth - 1`). -/
def Circuit.inBounds (c : Tiling.Circuit F) : Bool :=
  let n := c.width + c.fixedWidth
  c.constraints.all (·.inBounds n) && c.lookups.all (Lookup.inBounds n)

/-- Every constituent `Air` in `airs` has all variables in bounds. -/
def allInBounds (airs : List (Air F)) : Bool :=
  airs.all fun a => Circuit.inBounds a.circuit

/-- Unfold `ArithExpr.inBounds` on each constructor into `Nat` inequalities. -/
theorem inBounds_const (n : Nat) (c : F) :
    (ArithExpr.const c).inBounds n = true := rfl

theorem inBounds_var (n v : Nat) :
    (ArithExpr.var v : ArithExpr F).inBounds n = true ↔ v < n :=
  Iff.of_eq (@decide_eq_true_eq (v < n) _)

theorem inBounds_add (n : Nat) (l r : ArithExpr F) :
    (ArithExpr.add l r).inBounds n = true ↔ l.inBounds n = true ∧ r.inBounds n = true :=
  Iff.of_eq (Bool.and_eq_true _ _)

theorem inBounds_sub (n : Nat) (l r : ArithExpr F) :
    (ArithExpr.sub l r).inBounds n = true ↔ l.inBounds n = true ∧ r.inBounds n = true :=
  Iff.of_eq (Bool.and_eq_true _ _)

theorem inBounds_mul (n : Nat) (l r : ArithExpr F) :
    (ArithExpr.mul l r).inBounds n = true ↔ l.inBounds n = true ∧ r.inBounds n = true :=
  Iff.of_eq (Bool.and_eq_true _ _)

theorem arithExpr_inBounds_mono {n m : Nat} (h : n ≤ m) :
    ∀ {e : ArithExpr F}, e.inBounds n = true → e.inBounds m = true
  | .const _, _ => rfl
  | .var v, hv => by
      rw [inBounds_var] at hv ⊢
      omega
  | .add l r, hlr => by
      rw [inBounds_add] at hlr ⊢
      exact ⟨arithExpr_inBounds_mono h hlr.1, arithExpr_inBounds_mono h hlr.2⟩
  | .sub l r, hlr => by
      rw [inBounds_sub] at hlr ⊢
      exact ⟨arithExpr_inBounds_mono h hlr.1, arithExpr_inBounds_mono h hlr.2⟩
  | .mul l r, hlr => by
      rw [inBounds_mul] at hlr ⊢
      exact ⟨arithExpr_inBounds_mono h hlr.1, arithExpr_inBounds_mono h hlr.2⟩

theorem circuit_inBounds_constraint {c : Tiling.Circuit F} (hc : Circuit.inBounds c = true)
    {e : Constraint F} (he : e ∈ c.constraints) :
    e.inBounds (c.width + c.fixedWidth) = true := by
  simp only [Circuit.inBounds, Bool.and_eq_true, List.all_eq_true] at hc
  exact hc.1 e he

theorem circuit_inBounds_lookup {c : Tiling.Circuit F} (hc : Circuit.inBounds c = true)
    {l : Lookup F} (hl : l ∈ c.lookups) :
    Lookup.inBounds (c.width + c.fixedWidth) l = true := by
  simp only [Circuit.inBounds, Bool.and_eq_true, List.all_eq_true] at hc
  exact hc.2 l hl

theorem lookup_inBounds_mult {n : Nat} {l : Lookup F} (hl : Lookup.inBounds n l = true) :
    l.multiplicity.inBounds n = true := by
  simp only [Lookup.inBounds, Bool.and_eq_true] at hl
  exact hl.1

theorem lookup_inBounds_arg {n : Nat} {l : Lookup F} (hl : Lookup.inBounds n l = true)
    {e : ArithExpr F} (he : e ∈ l.args) :
    e.inBounds n = true := by
  simp only [Lookup.inBounds, Bool.and_eq_true, List.all_eq_true] at hl
  exact hl.2 e he

end InBounds

/-! ## 2. Expression and lookup remapping -/

section Remap

variable {F : Type}

/-- Remap a variable `v` of a constituent circuit of main width `width` placed
inside a packed circuit of total main width `W_main` at main offset `mOff` and
fixed offset `fOff`:
* main variable `v < width` maps to `mOff + v`;
* fixed variable `v ≥ width` maps to `W_main + fOff + (v - width)`. -/
def remapVar (width W_main mOff fOff : Nat) (v : Nat) : Nat :=
  if v < width then mOff + v else W_main + fOff + (v - width)

/-- Remap every variable in an arithmetic expression. -/
def remapExpr (width W_main mOff fOff : Nat) : ArithExpr F → ArithExpr F
  | .const c => .const c
  | .var v => .var (remapVar width W_main mOff fOff v)
  | .add l r => .add (remapExpr width W_main mOff fOff l) (remapExpr width W_main mOff fOff r)
  | .sub l r => .sub (remapExpr width W_main mOff fOff l) (remapExpr width W_main mOff fOff r)
  | .mul l r => .mul (remapExpr width W_main mOff fOff l) (remapExpr width W_main mOff fOff r)

/-- Remap every expression in a lookup. -/
def remapLookup (width W_main mOff fOff : Nat) (l : Lookup F) : Lookup F where
  multiplicity := remapExpr width W_main mOff fOff l.multiplicity
  args := l.args.map (remapExpr width W_main mOff fOff)

theorem remapVar_lt {width fixedWidth W_main W_fixed mOff fOff v : Nat}
    (hm : mOff + width ≤ W_main) (hf : fOff + fixedWidth ≤ W_fixed)
    (hv : v < width + fixedWidth) :
    remapVar width W_main mOff fOff v < W_main + W_fixed := by
  unfold remapVar
  split <;> omega

theorem remapExpr_inBounds {width fixedWidth W_main W_fixed mOff fOff : Nat}
    (hm : mOff + width ≤ W_main) (hf : fOff + fixedWidth ≤ W_fixed) :
    ∀ {e : ArithExpr F}, e.inBounds (width + fixedWidth) = true →
      (remapExpr width W_main mOff fOff e).inBounds (W_main + W_fixed) = true
  | .const _, _ => rfl
  | .var v, hv => (inBounds_var _ _).mpr (remapVar_lt hm hf ((inBounds_var _ _).mp hv))
  | .add l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.inBounds, Bool.and_eq_true]
      exact ⟨remapExpr_inBounds hm hf hlr.1, remapExpr_inBounds hm hf hlr.2⟩
  | .sub l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.inBounds, Bool.and_eq_true]
      exact ⟨remapExpr_inBounds hm hf hlr.1, remapExpr_inBounds hm hf hlr.2⟩
  | .mul l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.inBounds, Bool.and_eq_true]
      exact ⟨remapExpr_inBounds hm hf hlr.1, remapExpr_inBounds hm hf hlr.2⟩

theorem remapLookup_inBounds {width fixedWidth W_main W_fixed mOff fOff : Nat}
    (hm : mOff + width ≤ W_main) (hf : fOff + fixedWidth ≤ W_fixed)
    {l : Lookup F} (hl : Lookup.inBounds (width + fixedWidth) l = true) :
    Lookup.inBounds (W_main + W_fixed) (remapLookup width W_main mOff fOff l) = true := by
  simp only [Lookup.inBounds, remapLookup, Bool.and_eq_true, List.all_eq_true, List.mem_map] at hl ⊢
  refine ⟨remapExpr_inBounds hm hf hl.1, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  exact remapExpr_inBounds hm hf (hl.2 e he)

theorem remapVar_denote {width fixedWidth W_main mOff fOff v : Nat}
    {packed orig : Nat → F}
    (hMain : ∀ u < width, packed (mOff + u) = orig u)
    (hFixed : ∀ k < fixedWidth, packed (W_main + fOff + k) = orig (width + k))
    (hv : v < width + fixedWidth) :
    packed (remapVar width W_main mOff fOff v) = orig v := by
  unfold remapVar
  by_cases hlt : v < width
  · simp only [hlt, ite_true]
    exact hMain v hlt
  · simp only [hlt, ite_false]
    have hk : v - width < fixedWidth := by omega
    have heq : width + (v - width) = v := by omega
    rw [hFixed (v - width) hk, heq]

theorem remapExpr_denote_of_eq [Field F] {width fixedWidth W_main mOff fOff : Nat}
    {packed orig : Nat → F}
    (hMain : ∀ v < width, packed (mOff + v) = orig v)
    (hFixed : ∀ k < fixedWidth, packed (W_main + fOff + k) = orig (width + k)) :
    ∀ {e : ArithExpr F}, e.inBounds (width + fixedWidth) = true →
      (remapExpr width W_main mOff fOff e).denote packed = e.denote orig
  | .const _, _ => rfl
  | .var v, hv => remapVar_denote hMain hFixed ((inBounds_var _ _).mp hv)
  | .add l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.denote]
      rw [remapExpr_denote_of_eq hMain hFixed hlr.1, remapExpr_denote_of_eq hMain hFixed hlr.2]
  | .sub l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.denote]
      rw [remapExpr_denote_of_eq hMain hFixed hlr.1, remapExpr_denote_of_eq hMain hFixed hlr.2]
  | .mul l r, hlr => by
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at hlr
      simp only [remapExpr, ArithExpr.denote]
      rw [remapExpr_denote_of_eq hMain hFixed hlr.1, remapExpr_denote_of_eq hMain hFixed hlr.2]

end Remap

/-! ## 3. Smart active-selector gating and horizontal packing -/

section Pack

variable {F : Type}

/-- Total main width across all constituent `Air`s. -/
def totalMainWidth (airs : List (Air F)) : Nat :=
  (airs.map fun a => a.circuit.width).sum

/-- Whether constituent `a` needs a dedicated active-selector fixed column when
packed into height `rows`. Full-height tables (`a.rows == rows`) require none. -/
def needsAct (rows : Nat) (a : Air F) : Bool :=
  decide (a.rows < rows)

/-- Number of fixed columns allocated to `a` inside a packed circuit of height `rows`:
`a.circuit.fixedWidth` when `a.rows = rows`, and `a.circuit.fixedWidth + 1` when `a.rows < rows`. -/
def fixedSlotWidth (rows : Nat) (a : Air F) : Nat :=
  a.circuit.fixedWidth + if needsAct rows a then 1 else 0

/-- Total fixed width across all constituent `Air`s at packed height `rows`. -/
def totalFixedWidth (airs : List (Air F)) (rows : Nat) : Nat :=
  (airs.map (fixedSlotWidth rows)).sum

/-- Main column offset of constituent `idx` in `airs`. -/
def mainOffset (airs : List (Air F)) (idx : Nat) : Nat :=
  ((airs.take idx).map fun a => a.circuit.width).sum

/-- Fixed column offset of constituent `idx` in `airs` at packed height `rows`. -/
def fixedOffset (airs : List (Air F)) (rows idx : Nat) : Nat :=
  ((airs.take idx).map (fixedSlotWidth rows)).sum

theorem fixedSlotWidth_eq_of_eq {rows : Nat} {a : Air F} (h : a.rows = rows) :
    fixedSlotWidth rows a = a.circuit.fixedWidth := by
  simp [fixedSlotWidth, needsAct, h]

theorem fixedSlotWidth_eq_of_lt {rows : Nat} {a : Air F} (h : a.rows < rows) :
    fixedSlotWidth rows a = a.circuit.fixedWidth + 1 := by
  simp [fixedSlotWidth, needsAct, h]

theorem totalFixedWidth_uniform {airs : List (Air F)} {rows : Nat}
    (h : ∀ a ∈ airs, a.rows = rows) :
    totalFixedWidth airs rows = (airs.map fun a => a.circuit.fixedWidth).sum := by
  unfold totalFixedWidth
  congr 1
  apply List.map_congr_left
  intro a ha
  exact fixedSlotWidth_eq_of_eq (h a ha)

theorem sum_take_add_getElem {α : Type} (g : α → Nat) :
    ∀ (l : List α) {idx : Nat} (hidx : idx < l.length),
      ((l.take idx).map g).sum + g l[idx] ≤ (l.map g).sum
  | [], _, hidx => absurd hidx (by simp)
  | x :: xs, 0, _ => by simp
  | x :: xs, idx + 1, hidx => by
      have ih := sum_take_add_getElem g xs (idx := idx) (by simpa using hidx)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

theorem mainOffset_add_le (airs : List (Air F)) {idx : Nat} (hidx : idx < airs.length) :
    mainOffset airs idx + airs[idx].circuit.width ≤ totalMainWidth airs :=
  sum_take_add_getElem (fun a : Air F => a.circuit.width) airs hidx

theorem fixedOffset_add_le (airs : List (Air F)) (rows : Nat) {idx : Nat} (hidx : idx < airs.length) :
    fixedOffset airs rows idx + fixedSlotWidth rows airs[idx] ≤ totalFixedWidth airs rows :=
  sum_take_add_getElem (fixedSlotWidth rows) airs hidx

theorem fixedOffset_add_fixedWidth_le (airs : List (Air F)) (rows : Nat)
    {idx : Nat} (hidx : idx < airs.length) :
    fixedOffset airs rows idx + airs[idx].circuit.fixedWidth ≤ totalFixedWidth airs rows := by
  have h := fixedOffset_add_le airs rows hidx
  unfold fixedSlotWidth at h
  omega

/-- Packed fixed matrix: column `c` at row `i`.
For each constituent `a` in order:
* columns `0 .. a.circuit.fixedWidth - 1` hold `a.fixed i c`;
* if `a.rows < rows`, column `a.circuit.fixedWidth` holds the active selector
  (`1` for `i < a.rows`, `0` otherwise). -/
def packFixed [Zero F] [One F] (rows : Nat) : List (Air F) → Nat → Nat → F
  | [], _, _ => 0
  | a :: rest, i, c =>
      let fw := a.circuit.fixedWidth
      let slot := fixedSlotWidth rows a
      if c < fw then a.fixed i c
      else if c < slot then (if i < a.rows then 1 else 0)
      else packFixed rows rest i (c - slot)

theorem packFixed_at_fixed [Zero F] [One F] (rows : Nat) :
    ∀ (airs : List (Air F)) {idx : Nat} (hidx : idx < airs.length) (i : Nat) {k : Nat},
      k < airs[idx].circuit.fixedWidth →
      packFixed rows airs i (fixedOffset airs rows idx + k) = airs[idx].fixed i k
  | [], _, hidx, _, _, _ => absurd hidx (by simp)
  | a :: rest, 0, _, i, k, hk => by
      simp only [fixedOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.getElem_cons_zero] at hk ⊢
      simp [packFixed, hk]
  | a :: rest, idx + 1, hidx, i, k, hk => by
      have hidx' : idx < rest.length := by simpa using hidx
      have ih := packFixed_at_fixed rows rest hidx' i (by simpa using hk)
      simp only [fixedOffset, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ] at ih ⊢
      have hfw : a.circuit.fixedWidth ≤ fixedSlotWidth rows a := by
        unfold fixedSlotWidth; omega
      unfold packFixed
      have h1 : ¬ (fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum + k <
          a.circuit.fixedWidth) := by omega
      have h2 : ¬ (fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum + k <
          fixedSlotWidth rows a) := by omega
      simp only [h1, h2, ite_false]
      rw [show fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum + k -
          fixedSlotWidth rows a = ((rest.take idx).map (fixedSlotWidth rows)).sum + k by omega]
      exact ih

theorem packFixed_at_act [Zero F] [One F] (rows : Nat) :
    ∀ (airs : List (Air F)) {idx : Nat} (hidx : idx < airs.length) (i : Nat),
      airs[idx].rows < rows →
      packFixed rows airs i (fixedOffset airs rows idx + airs[idx].circuit.fixedWidth) =
        if i < airs[idx].rows then 1 else 0
  | [], _, hidx, _, _ => absurd hidx (by simp)
  | a :: rest, 0, _, i, hlt => by
      simp only [fixedOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.getElem_cons_zero] at hlt ⊢
      have hslot : fixedSlotWidth rows a = a.circuit.fixedWidth + 1 := fixedSlotWidth_eq_of_lt hlt
      unfold packFixed
      simp only [hslot, lt_irrefl, ite_false, show a.circuit.fixedWidth < a.circuit.fixedWidth + 1 by omega,
        ite_true]
  | a :: rest, idx + 1, hidx, i, hlt => by
      have hidx' : idx < rest.length := by simpa using hidx
      have ih := packFixed_at_act rows rest hidx' i (by simpa using hlt)
      simp only [fixedOffset, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ] at ih ⊢
      have hfw : a.circuit.fixedWidth ≤ fixedSlotWidth rows a := by
        unfold fixedSlotWidth; omega
      unfold packFixed
      have h1 : ¬ (fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum +
          rest[idx].circuit.fixedWidth < a.circuit.fixedWidth) := by omega
      have h2 : ¬ (fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum +
          rest[idx].circuit.fixedWidth < fixedSlotWidth rows a) := by omega
      simp only [h1, h2, ite_false]
      rw [show fixedSlotWidth rows a + ((rest.take idx).map (fixedSlotWidth rows)).sum +
          rest[idx].circuit.fixedWidth - fixedSlotWidth rows a =
          ((rest.take idx).map (fixedSlotWidth rows)).sum + rest[idx].circuit.fixedWidth by omega]
      exact ih

/-- Remap and (when `a.rows < rows`) gate every constraint of constituent `a`. -/
def packConstraintsAt (W_main rows mOff fOff : Nat) (a : Air F) : List (Constraint F) :=
  let remapped := a.circuit.constraints.map (remapExpr a.circuit.width W_main mOff fOff)
  if a.rows < rows then
    let actVar : ArithExpr F := .var (W_main + fOff + a.circuit.fixedWidth)
    remapped.map (.mul actVar)
  else
    remapped

/-- Remap and (when `a.rows < rows`) gate every lookup multiplicity of constituent `a`. -/
def packLookupsAt (W_main rows mOff fOff : Nat) (a : Air F) : List (Lookup F) :=
  let remapped := a.circuit.lookups.map (remapLookup a.circuit.width W_main mOff fOff)
  if a.rows < rows then
    let actVar : ArithExpr F := .var (W_main + fOff + a.circuit.fixedWidth)
    remapped.map fun l => ⟨.mul actVar l.multiplicity, l.args⟩
  else
    remapped

/-- Zero constraint overhead when `a.rows = rows`: constraints are only remapped. -/
theorem packConstraintsAt_eq_of_eq {W_main rows mOff fOff : Nat} {a : Air F} (h : a.rows = rows) :
    packConstraintsAt W_main rows mOff fOff a =
      a.circuit.constraints.map (remapExpr a.circuit.width W_main mOff fOff) := by
  simp [packConstraintsAt, h]

/-- Zero lookup multiplicity overhead when `a.rows = rows`: lookups are only remapped. -/
theorem packLookupsAt_eq_of_eq {W_main rows mOff fOff : Nat} {a : Air F} (h : a.rows = rows) :
    packLookupsAt W_main rows mOff fOff a =
      a.circuit.lookups.map (remapLookup a.circuit.width W_main mOff fOff) := by
  simp [packLookupsAt, h]

/-- The packed single `Tiling.Circuit` combining all constituents of `airs` at height `rows`. -/
def packCircuit (airs : List (Air F)) (rows : Nat) : Tiling.Circuit F :=
  let W_main := totalMainWidth airs
  { width := W_main
    fixedWidth := totalFixedWidth airs rows
    constraints := airs.zipIdx.flatMap fun x =>
      packConstraintsAt W_main rows (mainOffset airs x.2) (fixedOffset airs rows x.2) x.1
    lookups := airs.zipIdx.flatMap fun x =>
      packLookupsAt W_main rows (mainOffset airs x.2) (fixedOffset airs rows x.2) x.1 }

/-- Horizontally pack `airs` into a single `Air` of height `rows`. -/
def pack [Zero F] [One F] (airs : List (Air F)) (rows : Nat) : Air F :=
  ⟨packCircuit airs rows, rows, packFixed rows airs⟩

/-- Extract constituent `idx`'s main trace from the packed main trace `main`. -/
def sliceMain (airs : List (Air F)) (main : Nat → Nat → F) (idx : Nat) : Nat → Nat → F :=
  fun i v => main i (mainOffset airs idx + v)

/-- Helper for `packMain` starting at constituent index `base`. -/
def packMainFrom [Zero F] : List (Air F) → (Nat → Nat → Nat → F) → Nat → Nat → Nat → F
  | [], _, _, _, _ => 0
  | a :: rest, mains, base, i, v =>
      if v < a.circuit.width then mains base i v
      else packMainFrom rest mains (base + 1) i (v - a.circuit.width)

/-- Horizontally concatenate constituent main traces `mains` into one packed main trace. -/
def packMain [Zero F] (airs : List (Air F)) (mains : Nat → Nat → Nat → F) : Nat → Nat → F :=
  packMainFrom airs mains 0

theorem packMainFrom_at [Zero F] :
    ∀ (airs : List (Air F)) (mains : Nat → Nat → Nat → F) (base : Nat)
      {idx : Nat} (hidx : idx < airs.length) (i : Nat) {v : Nat},
      v < airs[idx].circuit.width →
      packMainFrom airs mains base i (mainOffset airs idx + v) = mains (base + idx) i v
  | [], _, _, _, hidx, _, _, _ => absurd hidx (by simp)
  | a :: rest, mains, base, 0, _, i, v, hv => by
      simp only [mainOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.getElem_cons_zero, Nat.add_zero] at hv ⊢
      simp [packMainFrom, hv]
  | a :: rest, mains, base, idx + 1, hidx, i, v, hv => by
      have hidx' : idx < rest.length := by simpa using hidx
      have ih := packMainFrom_at rest mains (base + 1) hidx' i (by simpa using hv)
      simp only [mainOffset, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
      unfold packMainFrom
      have hge : ¬ (a.circuit.width + ((rest.take idx).map fun a => a.circuit.width).sum + v <
          a.circuit.width) := by omega
      simp only [hge, ite_false]
      rw [show a.circuit.width + ((rest.take idx).map fun a => a.circuit.width).sum + v - a.circuit.width =
          ((rest.take idx).map fun a => a.circuit.width).sum + v by omega,
        ih, show base + 1 + idx = base + (idx + 1) by omega]

theorem sliceMain_packMain [Zero F] (airs : List (Air F)) (mains : Nat → Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {v : Nat} (hv : v < airs[idx].circuit.width) :
    sliceMain airs (packMain airs mains) idx i v = mains idx i v := by
  simpa [sliceMain, packMain] using packMainFrom_at airs mains 0 hidx i hv

theorem assign_sliceMain_packMain [Zero F] (airs : List (Air F)) (mains : Nat → Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) :
    airs[idx].assign (sliceMain airs (packMain airs mains) idx) i = airs[idx].assign (mains idx) i := by
  funext v
  simp only [Air.assign]
  split
  · exact sliceMain_packMain airs mains hidx i ‹_›
  · rfl

theorem pack_inBounds [Zero F] [One F] {airs : List (Air F)} {rows : Nat}
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true) :
    Circuit.inBounds (pack airs rows).circuit = true := by
  simp only [Circuit.inBounds, pack, packCircuit, Bool.and_eq_true, List.all_eq_true,
    List.mem_flatMap]
  constructor
  · rintro e ⟨⟨a, idx⟩, hmem, he⟩
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
    have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
    have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
    have haMem : a ∈ airs := List.mem_of_getElem? hget
    have hm : mainOffset airs idx + a.circuit.width ≤ totalMainWidth airs := by
      rw [← haEq]; exact mainOffset_add_le airs hidx
    have hf : fixedOffset airs rows idx + a.circuit.fixedWidth ≤ totalFixedWidth airs rows := by
      rw [← haEq]; exact fixedOffset_add_fixedWidth_le airs rows hidx
    simp only [packConstraintsAt] at he
    split at he
    · rename_i hlt
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he'
      have hact : fixedOffset airs rows idx + a.circuit.fixedWidth < totalFixedWidth airs rows := by
        have hslot := fixedOffset_add_le airs rows hidx
        rw [haEq, fixedSlotWidth_eq_of_lt hlt] at hslot
        omega
      rw [inBounds_mul]
      refine ⟨(inBounds_var _ _).mpr (by omega),
        remapExpr_inBounds hm hf (circuit_inBounds_constraint (hIn a haMem) hc)⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
      exact remapExpr_inBounds hm hf (circuit_inBounds_constraint (hIn a haMem) hc)
  · rintro l ⟨⟨a, idx⟩, hmem, hl⟩
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
    have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
    have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
    have haMem : a ∈ airs := List.mem_of_getElem? hget
    have hm : mainOffset airs idx + a.circuit.width ≤ totalMainWidth airs := by
      rw [← haEq]; exact mainOffset_add_le airs hidx
    have hf : fixedOffset airs rows idx + a.circuit.fixedWidth ≤ totalFixedWidth airs rows := by
      rw [← haEq]; exact fixedOffset_add_fixedWidth_le airs rows hidx
    simp only [packLookupsAt] at hl
    split at hl
    · rename_i hlt
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl'
      have hact : fixedOffset airs rows idx + a.circuit.fixedWidth < totalFixedWidth airs rows := by
        have hslot := fixedOffset_add_le airs rows hidx
        rw [haEq, fixedSlotWidth_eq_of_lt hlt] at hslot
        omega
      have hrem := remapLookup_inBounds hm hf (circuit_inBounds_lookup (hIn a haMem) hl0)
      simp only [Lookup.inBounds, Bool.and_eq_true] at hrem ⊢
      rw [inBounds_mul]
      exact ⟨⟨(inBounds_var _ _).mpr (by omega), hrem.1⟩, hrem.2⟩
    · obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
      exact remapLookup_inBounds hm hf (circuit_inBounds_lookup (hIn a haMem) hl0)

section Eval

variable [Field F]

theorem pack_assign_main (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {v : Nat} (hv : v < airs[idx].circuit.width) :
    (pack airs rows).assign main i (mainOffset airs idx + v) = sliceMain airs main idx i v := by
  have hm := mainOffset_add_le airs hidx
  have hlt : mainOffset airs idx + v < (pack airs rows).circuit.width := by
    change mainOffset airs idx + v < totalMainWidth airs
    omega
  simp [Air.assign, sliceMain, hlt]

theorem pack_assign_fixed (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {k : Nat} (hk : k < airs[idx].circuit.fixedWidth) :
    (pack airs rows).assign main i (totalMainWidth airs + fixedOffset airs rows idx + k) =
      airs[idx].fixed i k := by
  have hge : ¬ (totalMainWidth airs + fixedOffset airs rows idx + k < (pack airs rows).circuit.width) := by
    change ¬ (totalMainWidth airs + fixedOffset airs rows idx + k < totalMainWidth airs)
    omega
  simp only [Air.assign, hge, ite_false]
  change packFixed rows airs i (totalMainWidth airs + fixedOffset airs rows idx + k - totalMainWidth airs) = _
  rw [show totalMainWidth airs + fixedOffset airs rows idx + k - totalMainWidth airs =
      fixedOffset airs rows idx + k by omega]
  exact packFixed_at_fixed rows airs hidx i hk

theorem pack_assign_act (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) (hlt : airs[idx].rows < rows) :
    (pack airs rows).assign main i
        (totalMainWidth airs + fixedOffset airs rows idx + airs[idx].circuit.fixedWidth) =
      if i < airs[idx].rows then 1 else 0 := by
  have hge : ¬ (totalMainWidth airs + fixedOffset airs rows idx + airs[idx].circuit.fixedWidth <
      (pack airs rows).circuit.width) := by
    change ¬ (totalMainWidth airs + fixedOffset airs rows idx + airs[idx].circuit.fixedWidth <
      totalMainWidth airs)
    omega
  simp only [Air.assign, hge, ite_false]
  change packFixed rows airs i
    (totalMainWidth airs + fixedOffset airs rows idx + airs[idx].circuit.fixedWidth -
      totalMainWidth airs) = _
  rw [show totalMainWidth airs + fixedOffset airs rows idx + airs[idx].circuit.fixedWidth -
      totalMainWidth airs = fixedOffset airs rows idx + airs[idx].circuit.fixedWidth by omega]
  exact packFixed_at_act rows airs hidx i hlt

/-- **Expression remapping semantics:** denoting `remapExpr` under row `i` of the
packed assignment equals denoting the original `ArithExpr` under row `i` of
constituent `idx`'s sliced assignment `airs[idx].assign (sliceMain airs main idx) i`. -/
theorem remapExpr_denote (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {e : ArithExpr F}
    (he : e.inBounds (airs[idx].circuit.width + airs[idx].circuit.fixedWidth) = true) :
    (remapExpr airs[idx].circuit.width (totalMainWidth airs) (mainOffset airs idx)
        (fixedOffset airs rows idx) e).denote ((pack airs rows).assign main i) =
      e.denote (airs[idx].assign (sliceMain airs main idx) i) := by
  apply remapExpr_denote_of_eq (width := airs[idx].circuit.width)
    (fixedWidth := airs[idx].circuit.fixedWidth)
  · intro v hv
    rw [pack_assign_main airs rows main hidx i hv]
    simp [Air.assign, hv]
  · intro k hk
    rw [pack_assign_fixed airs rows main hidx i hk]
    simp [Air.assign]
  · exact he

theorem remapLookup_tuple (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {l : Lookup F}
    (hl : Lookup.inBounds (airs[idx].circuit.width + airs[idx].circuit.fixedWidth) l = true) :
    (remapLookup airs[idx].circuit.width (totalMainWidth airs) (mainOffset airs idx)
        (fixedOffset airs rows idx) l).tuple ((pack airs rows).assign main i) =
      l.tuple (airs[idx].assign (sliceMain airs main idx) i) := by
  simp only [Lookup.tuple, remapLookup, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact remapExpr_denote airs rows main hidx i (lookup_inBounds_arg hl he)

theorem remapLookup_entry (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length) (i : Nat) {l : Lookup F}
    (hl : Lookup.inBounds (airs[idx].circuit.width + airs[idx].circuit.fixedWidth) l = true) :
    (remapLookup airs[idx].circuit.width (totalMainWidth airs) (mainOffset airs idx)
        (fixedOffset airs rows idx) l).entry ((pack airs rows).assign main i) =
      l.entry (airs[idx].assign (sliceMain airs main idx) i) := by
  simp only [Lookup.entry]
  rw [remapLookup_tuple airs rows main hidx i hl]
  congr 1
  exact remapExpr_denote airs rows main hidx i (lookup_inBounds_mult hl)

end Eval

end Pack

/-! ## 4. Core soundness and completeness theorems -/

section CoreTheorems

variable {F : Type} [Field F]

/-- Swap nested sums over two lists. -/
theorem sum_map_swap {α β M : Type} [AddCommMonoid M] (xs : List α) (ys : List β) (f : α → β → M) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      symm
      apply List.sum_eq_zero
      intro m hm
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      clear ih
      induction ys with
      | nil => simp
      | cons y ys ihy =>
          simp only [List.map_cons, List.sum_cons]
          rw [← ihy]
          ac_rfl

/-- `zipIdx` of an appended list shifts indices of the right half by `l₁.length`. -/
theorem zipIdx_append_eq {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).zipIdx = l₁.zipIdx ++ l₂.zipIdx.map fun x => (x.1, l₁.length + x.2) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zipIdx, Nat.zero_add]
    by_cases hi : i < l₁.length
    · rw [List.getElem_append_left hi, List.getElem_append_left (by simpa using hi)]
      simp
    · have hi' : i - l₁.length < l₂.length := by
        simp only [List.length_zipIdx, List.length_append] at h1; omega
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp; omega)]
      simp only [List.length_zipIdx, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
        Prod.mk.injEq, true_and]
      omega

theorem stageHolds_append (l₁ l₂ : List (Air F)) (mains : Nat → Nat → Nat → F) :
    StageHolds (l₁ ++ l₂) mains ↔
      StageHolds l₁ mains ∧ StageHolds l₂ (fun j => mains (l₁.length + j)) := by
  unfold StageHolds
  rw [zipIdx_append_eq]
  constructor
  · intro h
    refine ⟨fun x hx => h x (List.mem_append_left _ hx), fun x hx => ?_⟩
    exact h (x.1, l₁.length + x.2) (List.mem_append_right _ (List.mem_map_of_mem hx))
  · rintro ⟨h1, h2⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact h2 y hy

theorem stageLedger_append (l₁ l₂ : List (Air F)) (mains : Nat → Nat → Nat → F) :
    stageLedger (l₁ ++ l₂) mains =
      stageLedger l₁ mains + stageLedger l₂ (fun j => mains (l₁.length + j)) := by
  simp only [stageLedger, zipIdx_append_eq, List.map_append, List.sum_append, List.map_map,
    Function.comp_def]

/-- Concatenate two trace families at split point `n`. -/
def appendMains (n : Nat) (m₁ m₂ : Nat → Nat → Nat → F) : Nat → Nat → Nat → F :=
  fun idx => if idx < n then m₁ idx else m₂ (idx - n)

theorem stageHolds_appendMains (l₁ l₂ : List (Air F)) (m₁ m₂ : Nat → Nat → Nat → F) :
    StageHolds (l₁ ++ l₂) (appendMains l₁.length m₁ m₂) ↔
      StageHolds l₁ m₁ ∧ StageHolds l₂ m₂ := by
  rw [stageHolds_append]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hlt : x.2 < l₁.length := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hx)).1
      simpa [appendMains, hlt] using h1 x hx
    · simpa [appendMains, show ¬ (l₁.length + x.2 < l₁.length) by omega] using h2 x hx
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hlt : x.2 < l₁.length := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hx)).1
      simpa [appendMains, hlt] using h1 x hx
    · simpa [appendMains, show ¬ (l₁.length + x.2 < l₁.length) by omega] using h2 x hx

theorem stageLedger_appendMains (l₁ l₂ : List (Air F)) (m₁ m₂ : Nat → Nat → Nat → F) :
    stageLedger (l₁ ++ l₂) (appendMains l₁.length m₁ m₂) =
      stageLedger l₁ m₁ + stageLedger l₂ m₂ := by
  rw [stageLedger_append]
  congr 1
  · unfold stageLedger
    congr 1
    apply List.map_congr_left
    intro x hx
    have hlt : x.2 < l₁.length := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hx)).1
    simp [appendMains, hlt]
  · unfold stageLedger
    congr 1
    apply List.map_congr_left
    intro x _
    simp [appendMains, show ¬ (l₁.length + x.2 < l₁.length) by omega]

/-- **Soundness of horizontal packing (constraints):**
If the packed single circuit holds on every row `i < rows`, and every constituent
is in bounds with `a.rows ≤ rows`, then every constituent `a` holds on its
sliced main trace `sliceMain airs main idx`. -/
theorem pack_holds_sound {airs : List (Air F)} {rows : Nat} {main : Nat → Nat → F}
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true)
    (hRows : ∀ a ∈ airs, a.rows ≤ rows)
    (hHolds : (pack airs rows).Holds main) :
    StageHolds airs (sliceMain airs main) := by
  rintro ⟨a, idx⟩ hmem i hi e he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
  have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
  have haMem : a ∈ airs := List.mem_of_getElem? hget
  have hiRows : i < rows := Nat.lt_of_lt_of_le hi (hRows a haMem)
  have hRowHolds := hHolds i hiRows
  have hRemDenote :
      (remapExpr a.circuit.width (totalMainWidth airs) (mainOffset airs idx)
          (fixedOffset airs rows idx) e).denote ((pack airs rows).assign main i) =
        e.denote (a.assign (sliceMain airs main idx) i) := by
    subst haEq
    exact remapExpr_denote airs rows main hidx i (circuit_inBounds_constraint (hIn _ haMem) he)
  by_cases hlt : a.rows < rows
  · have hcMem : .mul (.var (totalMainWidth airs + fixedOffset airs rows idx + a.circuit.fixedWidth))
        (remapExpr a.circuit.width (totalMainWidth airs) (mainOffset airs idx)
          (fixedOffset airs rows idx) e) ∈ (pack airs rows).circuit.constraints := by
      simp only [pack, packCircuit, List.mem_flatMap]
      refine ⟨(a, idx), hmem, ?_⟩
      simp only [packConstraintsAt, hlt, ite_true]
      exact List.mem_map_of_mem (List.mem_map_of_mem he)
    have hz := hRowHolds _ hcMem
    have hact : (pack airs rows).assign main i
        (totalMainWidth airs + fixedOffset airs rows idx + a.circuit.fixedWidth) = 1 := by
      subst haEq
      rw [pack_assign_act airs rows main hidx i hlt]
      simp [hi]
    simp only [ArithExpr.denote, hact, one_mul] at hz
    rw [← hRemDenote]
    exact hz
  · have hcMem : remapExpr a.circuit.width (totalMainWidth airs) (mainOffset airs idx)
        (fixedOffset airs rows idx) e ∈ (pack airs rows).circuit.constraints := by
      simp only [pack, packCircuit, List.mem_flatMap]
      refine ⟨(a, idx), hmem, ?_⟩
      simp only [packConstraintsAt, hlt, ite_false]
      exact List.mem_map_of_mem he
    have hz := hRowHolds _ hcMem
    rw [← hRemDenote]
    exact hz

/-- Per-constituent lookup ledger contribution on row `i`: equals the
constituent's own `rowLedger` on active rows `i < airs[idx].rows`, and `0` on
gated inactive rows `airs[idx].rows ≤ i < rows`. -/
theorem packLookupsAt_row_sum (airs : List (Air F)) (rows : Nat) (main : Nat → Nat → F)
    {idx : Nat} (hidx : idx < airs.length)
    (hIn : Circuit.inBounds airs[idx].circuit = true)
    (hRow : airs[idx].rows ≤ rows) (i : Nat) (hiRows : i < rows) :
    ((packLookupsAt (totalMainWidth airs) rows (mainOffset airs idx)
        (fixedOffset airs rows idx) airs[idx]).map fun l =>
      l.entry ((pack airs rows).assign main i)).sum =
      if i < airs[idx].rows then
        airs[idx].circuit.rowLedger (airs[idx].assign (sliceMain airs main idx) i)
      else 0 := by
  by_cases hlt : airs[idx].rows < rows
  · have hact := pack_assign_act airs rows main hidx i hlt
    simp only [packLookupsAt, hlt, ite_true, List.map_map, Function.comp_def]
    by_cases hi : i < airs[idx].rows
    · simp only [hi, ite_true] at hact ⊢
      unfold Circuit.rowLedger
      congr 1
      apply List.map_congr_left
      intro l hl
      have hlIn := circuit_inBounds_lookup hIn hl
      have hRem := remapLookup_entry airs rows main hidx i hlIn
      simp only [Lookup.entry, Lookup.tuple, ArithExpr.denote] at hRem ⊢
      rw [hact, one_mul]
      exact hRem
    · simp only [hi, ite_false] at hact ⊢
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
      simp [Lookup.entry, ArithExpr.denote, hact]
  · have heq : airs[idx].rows = rows := by omega
    have hi : i < airs[idx].rows := by omega
    simp only [packLookupsAt, hlt, ite_false, hi, ite_true, List.map_map, Function.comp_def]
    unfold Circuit.rowLedger
    congr 1
    apply List.map_congr_left
    intro l hl
    exact remapLookup_entry airs rows main hidx i (circuit_inBounds_lookup hIn hl)

/-- **Soundness of horizontal packing (ledger):**
The lookup ledger of `pack airs rows` equals `stageLedger airs (sliceMain airs main)`. -/
theorem pack_ledger_eq {airs : List (Air F)} {rows : Nat} (main : Nat → Nat → F)
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true)
    (hRows : ∀ a ∈ airs, a.rows ≤ rows) :
    (pack airs rows).ledger main = stageLedger airs (sliceMain airs main) := by
  unfold Air.ledger stageLedger
  change ((List.range rows).map fun i =>
      (pack airs rows).circuit.rowLedger ((pack airs rows).assign main i)).sum = _
  have hrow : ∀ i ∈ List.range rows,
      (pack airs rows).circuit.rowLedger ((pack airs rows).assign main i) =
        (airs.zipIdx.map fun x =>
          ((packLookupsAt (totalMainWidth airs) rows (mainOffset airs x.2)
              (fixedOffset airs rows x.2) x.1).map fun l =>
            l.entry ((pack airs rows).assign main i)).sum).sum := by
    intro i _
    simp only [Circuit.rowLedger, pack, packCircuit]
    exact System.sum_map_flatMap airs.zipIdx
      (fun x => packLookupsAt (totalMainWidth airs) rows (mainOffset airs x.2)
        (fixedOffset airs rows x.2) x.1)
      (fun l => l.entry ((pack airs rows).assign main i))
  rw [List.map_congr_left hrow, sum_map_swap]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, idx⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
  have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
  have haMem : a ∈ airs := List.mem_of_getElem? hget
  have hle : a.rows ≤ rows := hRows a haMem
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hTerm : ∀ i ∈ List.range rows,
      ((packLookupsAt (totalMainWidth airs) rows (mainOffset airs idx)
          (fixedOffset airs rows idx) a).map fun l =>
        l.entry ((pack airs rows).assign main i)).sum =
        if i < a.rows then a.circuit.rowLedger (a.assign (sliceMain airs main idx) i) else 0 := by
    intro i hi
    subst haEq
    exact packLookupsAt_row_sum airs rows main hidx (hIn _ haMem) hle i (List.mem_range.mp hi)
  rw [List.map_congr_left hTerm, hd, List.range_add, List.map_append, List.sum_append]
  have hActive : ((List.range a.rows).map fun i =>
      if i < a.rows then a.circuit.rowLedger (a.assign (sliceMain airs main idx) i) else 0) =
      (List.range a.rows).map fun i => a.circuit.rowLedger (a.assign (sliceMain airs main idx) i) := by
    apply List.map_congr_left
    intro i hi
    simp [List.mem_range.mp hi]
  have hInactive : (((List.range d).map (a.rows + ·)).map fun i =>
      if i < a.rows then a.circuit.rowLedger (a.assign (sliceMain airs main idx) i) else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hi
    simp [show ¬ (a.rows + e < a.rows) by omega]
  rw [hActive, hInactive, add_zero]
  rfl

/-- **Completeness of horizontal packing (constraints):**
If every constituent holds on `mains`, then `pack airs rows` holds on `packMain airs mains`. -/
theorem pack_holds_complete {airs : List (Air F)} {rows : Nat} {mains : Nat → Nat → Nat → F}
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true)
    (hRows : ∀ a ∈ airs, a.rows ≤ rows)
    (hStage : StageHolds airs mains) :
    (pack airs rows).Holds (packMain airs mains) := by
  intro i hi p hp
  have hiRows : i < rows := hi
  simp only [pack, packCircuit, List.mem_flatMap] at hp
  obtain ⟨⟨a, idx⟩, hmem, hp⟩ := hp
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
  have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
  have haMem : a ∈ airs := List.mem_of_getElem? hget
  simp only [packConstraintsAt] at hp
  split at hp
  · rename_i hlt
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    simp only [ArithExpr.denote]
    have hact : (pack airs rows).assign (packMain airs mains) i
        (totalMainWidth airs + fixedOffset airs rows idx + a.circuit.fixedWidth) =
        if i < a.rows then 1 else 0 := by
      subst haEq
      exact pack_assign_act airs rows (packMain airs mains) hidx i hlt
    rw [hact]
    split
    · rename_i hiA
      rw [one_mul]
      subst haEq
      rw [remapExpr_denote airs rows (packMain airs mains) hidx i
            (circuit_inBounds_constraint (hIn _ haMem) he),
          assign_sliceMain_packMain airs mains hidx i]
      exact hStage _ hmem i hiA e he
    · rw [zero_mul]
  · rename_i hge
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    have hiA : i < a.rows := by have := hRows a haMem; omega
    subst haEq
    rw [remapExpr_denote airs rows (packMain airs mains) hidx i
          (circuit_inBounds_constraint (hIn _ haMem) he),
        assign_sliceMain_packMain airs mains hidx i]
    exact hStage _ hmem i hiA e he

/-- **Completeness of horizontal packing (ledger):**
The lookup ledger of `pack airs rows` on `packMain airs mains` equals `stageLedger airs mains`. -/
theorem pack_ledger_packMain {airs : List (Air F)} {rows : Nat} (mains : Nat → Nat → Nat → F)
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true)
    (hRows : ∀ a ∈ airs, a.rows ≤ rows) :
    (pack airs rows).ledger (packMain airs mains) = stageLedger airs mains := by
  rw [pack_ledger_eq (packMain airs mains) hIn hRows]
  unfold stageLedger
  congr 1
  apply List.map_congr_left
  rintro ⟨a, idx⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
  have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
  subst haEq
  unfold Air.ledger
  congr 1
  apply List.map_congr_left
  intro i _
  rw [assign_sliceMain_packMain airs mains hidx i]

/-- Soundness and completeness combined on `packMain`: `(pack airs rows).Holds (packMain airs mains)`
holds if and only if `StageHolds airs mains`. -/
theorem pack_holds_iff_packMain {airs : List (Air F)} {rows : Nat} {mains : Nat → Nat → Nat → F}
    (hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true)
    (hRows : ∀ a ∈ airs, a.rows ≤ rows) :
    (pack airs rows).Holds (packMain airs mains) ↔ StageHolds airs mains := by
  constructor
  · intro h
    have hs := pack_holds_sound hIn hRows h
    rintro ⟨a, idx⟩ hmem i hi e he
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
    have hidx : idx < airs.length := (List.getElem?_eq_some_iff.mp hget).1
    have haEq : airs[idx] = a := (List.getElem?_eq_some_iff.mp hget).2
    subst haEq
    rw [← assign_sliceMain_packMain airs mains hidx i]
    exact hs _ hmem i hi e he
  · exact pack_holds_complete hIn hRows

end CoreTheorems

/-! ## 5. Adapters for `WideStage` tables and `Periodic` shards / `Compact` tables -/

section Adapters

variable {F : Type} [Field F] [DecidableEq F]

/-! ### 5a. `WideStage` map & ROM table bounds -/

omit [DecidableEq F] in
theorem mapAir_inBounds (L : Nat) (claims : List (List F)) (rows : Nat) :
    Circuit.inBounds (WideStage.mapAir L claims rows).circuit = true := by
  simp only [Circuit.inBounds, WideStage.mapAir, WideStage.mapCircuit, Lookup.inBounds,
    List.all_nil, List.all_cons, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    List.all_eq_true, List.mem_map, List.mem_range,
    inBounds_const, inBounds_var, inBounds_sub, inBounds_mul, true_and]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [inBounds_var]
  omega

omit [DecidableEq F] in
theorem romAir_inBounds (w cap : Nat) :
    Circuit.inBounds (WideStage.romAir (F := F) w cap).circuit = true := by
  simp only [Circuit.inBounds, WideStage.romAir, WideStage.romCircuit, Lookup.inBounds,
    List.all_nil, List.all_cons, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    List.all_eq_true, List.mem_map, List.mem_range,
    inBounds_const, inBounds_var, inBounds_sub, true_and]
  refine ⟨by omega, by omega, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [inBounds_var]
  omega

/-- All tables of a wide stage concatenated in order: units, map tables, ROM tables. -/
def wideAirs (idOf : String → Nat)
    (units : List ((Aiur.Circuit.Chip F × Option (Unroll F)) × Nat))
    (claims : List (List F)) (mapCap : Nat → Nat)
    (roms : List (Nat × Nat)) : List (Air F) :=
  WideStage.unitAirs idOf units ++ WideStage.mapAirs claims mapCap ++ WideStage.romAirs roms

theorem wideAirs_inBounds {idOf : String → Nat}
    {units : List ((Aiur.Circuit.Chip F × Option (Unroll F)) × Nat)}
    {claims : List (List F)} {mapCap : Nat → Nat} {roms : List (Nat × Nat)}
    (hUnits : ∀ u ∈ units, Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true) :
    ∀ a ∈ wideAirs idOf units claims mapCap roms, Circuit.inBounds a.circuit = true := by
  intro a ha
  simp only [wideAirs, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact hUnits u hu
  · obtain ⟨L, _, rfl⟩ := List.mem_map.mp ha
    exact mapAir_inBounds L (WideStage.claimsOf claims L) (mapCap L)
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    exact romAir_inBounds r.1 r.2

theorem wideAirs_rows_le {idOf : String → Nat}
    {units : List ((Aiur.Circuit.Chip F × Option (Unroll F)) × Nat)}
    {claims : List (List F)} {mapCap : Nat → Nat} {roms : List (Nat × Nat)} {rows : Nat}
    (hUnits : ∀ u ∈ units, u.2 ≤ rows)
    (hMaps : ∀ L ∈ WideStage.mapLengths claims, mapCap L ≤ rows)
    (hRoms : ∀ r ∈ roms, r.2 ≤ rows) :
    ∀ a ∈ wideAirs idOf units claims mapCap roms, a.rows ≤ rows := by
  intro a ha
  simp only [wideAirs, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact hUnits u hu
  · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp ha
    exact hMaps L hL
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact hRoms r hr

/-! ### 5b. `Periodic.Sharded` adapter (`shardAir`, `shardAirs`) -/

/-- Wrap shard `k` of a periodic sharded system `S` (of height `rows`) as a `WideStage.Air`. -/
def shardAir (S : Periodic.Sharded F) (k rows : Nat) : Air F where
  circuit := S.circuit k
  rows := rows
  fixed := S.fixedAt (S.layout k)

/-- All shards of `S`, where shard `k` has height `H k`. -/
def shardAirs (S : Periodic.Sharded F) (H : Nat → Nat) : List (Air F) :=
  (List.range S.shards.length).map fun k => shardAir S k (H k)

theorem shardAir_assign (S : Periodic.Sharded F) (k rows : Nat) (main : Nat → Nat → F) (p : Nat) :
    (shardAir S k rows).assign main p = S.assign k main p := rfl

theorem shardAir_holds_iff (S : Periodic.Sharded F) (k rows : Nat) (main : Nat → Nat → F) :
    (shardAir S k rows).Holds main ↔
      ∀ p < rows, Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k main p) :=
  Iff.rfl

theorem shardAirs_holds_iff (S : Periodic.Sharded F) (H : Nat → Nat) (main : Nat → Nat → Nat → F) :
    StageHolds (shardAirs S H) main ↔
      ∀ k < S.shards.length, ∀ p < H k,
        Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (main k) p) := by
  unfold StageHolds shardAirs
  constructor
  · intro h k hk
    have hmem : (shardAir S k (H k), k) ∈
        ((List.range S.shards.length).map fun k => shardAir S k (H k)).zipIdx := by
      rw [List.mk_mem_zipIdx_iff_getElem?]
      simp [hk]
    exact h _ hmem
  · intro h x hx
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hx
    have hk : x.2 < S.shards.length := by simpa using (List.getElem?_eq_some_iff.mp hget).1
    have hxeq : shardAir S x.2 (H x.2) = x.1 := by
      have := (List.getElem?_eq_some_iff.mp hget).2
      simpa [hk] using this
    rw [← hxeq]
    exact h x.2 hk

theorem shardAir_ledger (S : Periodic.Sharded F) (k rows : Nat) (main : Nat → Nat → F) :
    (shardAir S k rows).ledger main =
      ∑ p ∈ Finset.range rows, (S.circuit k).rowLedger (S.assign k main p) := by
  rw [Air.ledger, System.finset_sum_range_list]
  rfl

theorem shardAirs_ledger (S : Periodic.Sharded F) (H : Nat → Nat) (main : Nat → Nat → Nat → F) :
    stageLedger (shardAirs S H) main = S.ledger H main := by
  unfold stageLedger shardAirs Periodic.Sharded.ledger
  rw [System.finset_sum_range_list]
  have hzip : ((List.range S.shards.length).map fun k => shardAir S k (H k)).zipIdx =
      (List.range S.shards.length).map fun k => (shardAir S k (H k), k) := by
    apply List.ext_getElem (by simp)
    intro k hk _
    simp at hk ⊢
  rw [hzip, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  exact shardAir_ledger S k (H k) (main k)

theorem flagCol_lt_bound (W l l' : Nat) (hl : l ≤ l') (hl' : l' < Periodic.lanes W) :
    Periodic.flagCol W l l' < 6 * Periodic.lanes W + Periodic.flagCount W := by
  have le : ((List.range (l + 1)).map (Periodic.flagBlock W)).sum ≤
      ((List.range (Periodic.lanes W)).map (Periodic.flagBlock W)).sum :=
    sum_range_mono _ (by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at le
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at le
  have hfb : Periodic.flagBlock W l = Periodic.lanes W - l := rfl
  unfold Periodic.flagCol Periodic.flagCount
  omega

omit [Field F] [DecidableEq F] in
theorem laneLin_inBounds {W l : Nat} (hW : 4 ≤ W) (hl : l < Periodic.lanes W) :
    (Periodic.laneLin W l : ArithExpr F).inBounds (W + Periodic.fixedWidth W) = true := by
  have hL : 4 * Periodic.lanes W ≤ W := by unfold Periodic.lanes; omega
  have hfw : 6 * Periodic.lanes W ≤ Periodic.fixedWidth W := by
    unfold Periodic.fixedWidth Periodic.rowMsgCol; omega
  simp only [Periodic.laneLin, Periodic.fx, Periodic.cell, Periodic.gateCol,
    inBounds_var, inBounds_add, inBounds_mul]
  omega

omit [DecidableEq F] in
theorem flagged_inBounds {W l : Nat} (hW : 4 ≤ W) :
    ∀ {ls : List Nat}, (∀ l' ∈ ls, l ≤ l' ∧ l' < Periodic.lanes W) →
      (Periodic.flagged W l ls : ArithExpr F).inBounds (W + Periodic.fixedWidth W) = true
  | [], _ => rfl
  | l' :: ls, hls => by
      have ⟨hl, hl'⟩ := hls l' (List.mem_cons_self ..)
      have hfc := flagCol_lt_bound W l l' hl hl'
      have hfw : 6 * Periodic.lanes W + Periodic.flagCount W ≤ Periodic.fixedWidth W := by
        unfold Periodic.fixedWidth Periodic.rowMsgCol; omega
      simp only [Periodic.flagged, Periodic.fx, inBounds_add, inBounds_mul, inBounds_var]
      exact ⟨⟨by omega, laneLin_inBounds hW hl'⟩,
        flagged_inBounds hW fun x hx => hls x (List.mem_cons_of_mem _ hx)⟩

omit [DecidableEq F] in
theorem narrowCircuit_inBounds {W labelOffset idOffset : Nat} (hW : 4 ≤ W) :
    Circuit.inBounds (Periodic.narrowCircuit W labelOffset idOffset : Tiling.Circuit F) = true := by
  have hL : 4 * Periodic.lanes W ≤ W := by unfold Periodic.lanes; omega
  simp only [Circuit.inBounds, Periodic.narrowCircuit, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro c hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
    have hl' : l < Periodic.lanes W := List.mem_range.mp hl
    have hfw : 6 * Periodic.lanes W ≤ Periodic.fixedWidth W := by
      unfold Periodic.fixedWidth Periodic.rowMsgCol; omega
    simp only [Periodic.spanConstraint, Periodic.fx, Periodic.cell, Periodic.gateCol,
      inBounds_add, inBounds_mul, inBounds_var]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, flagged_inBounds hW ?_⟩
    intro x hx
    rw [List.mem_range'_1] at hx
    omega
  · intro lk hlk
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hlk
    rcases hlk with rfl | ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩
    · -- rowMessage
      simp only [Lookup.inBounds, Periodic.rowMessage, Periodic.fx, Periodic.cell,
        Periodic.fixedWidth, Periodic.rowMsgCol, Bool.and_eq_true,
        List.all_cons, List.all_eq_true, List.mem_map, List.mem_range,
        inBounds_const, inBounds_var, inBounds_add, inBounds_mul, and_true]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega, ⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩
      rintro _ ⟨j, hj, rfl⟩
      rw [inBounds_var]
      omega
    · -- laneMessage
      simp only [Lookup.inBounds, Periodic.laneMessage, Periodic.fx, Periodic.cell,
        Periodic.fixedWidth, Periodic.rowMsgCol, Periodic.laneMsgCol, Bool.and_eq_true,
        List.all_cons, List.all_nil, Bool.and_true,
        inBounds_var, inBounds_add, inBounds_mul]
      omega
    · -- copyLookup
      simp only [Lookup.inBounds, Periodic.copyLookup, Periodic.fx, Periodic.cell,
        Periodic.fixedWidth, Periodic.multCol, Periodic.labelCol, Bool.and_eq_true,
        List.all_cons, List.all_nil, Bool.and_true,
        inBounds_const, inBounds_var, inBounds_add, inBounds_mul, true_and, and_true]
      omega

theorem shardAir_inBounds {S : Periodic.Sharded F} (hW : 4 ≤ S.width) (k rows : Nat) :
    Circuit.inBounds (shardAir S k rows).circuit = true :=
  narrowCircuit_inBounds hW

/-! ### 5c. `Periodic.Compact` adapter (`compactAir`, `compactAirs`) -/

/-- Wrap a compact table `T` beside `S` (of height `rows`) as a `WideStage.Air`. -/
def compactAir (S : Periodic.Sharded F) (T : Periodic.Compact F) (rows : Nat) : Air F where
  circuit := T.circuit S.width
  rows := rows
  fixed := T.fixedAt S.buses

/-- All compact tables, where table `t` has height `HT t`. -/
def compactAirs (S : Periodic.Sharded F) (tables : List (Periodic.Compact F))
    (HT : Nat → Nat) : List (Air F) :=
  tables.zipIdx.map fun x => compactAir S x.1 (HT x.2)

theorem compactAir_assign (S : Periodic.Sharded F) (T : Periodic.Compact F) (rows : Nat)
    (main : Nat → Nat → F) (r : Nat) :
    (compactAir S T rows).assign main r = T.assign S.width S.buses main r := rfl

theorem compactAir_holds (S : Periodic.Sharded F) (T : Periodic.Compact F) (rows : Nat)
    (main : Nat → Nat → F) :
    (compactAir S T rows).Holds main := by
  intro _ _ p hp
  cases hp

theorem compactAirs_holds (S : Periodic.Sharded F) (tables : List (Periodic.Compact F))
    (HT : Nat → Nat) (mainT : Nat → Nat → Nat → F) :
    StageHolds (compactAirs S tables HT) mainT := by
  rintro ⟨a, t⟩ hmem
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have ht : t < tables.length := by simpa [compactAirs] using (List.getElem?_eq_some_iff.mp hget).1
  have ha : compactAir S tables[t] (HT t) = a := by
    have := (List.getElem?_eq_some_iff.mp hget).2
    simpa [compactAirs, ht] using this
  rw [← ha]
  exact compactAir_holds S tables[t] (HT t) (mainT t)

theorem compactAir_ledger (S : Periodic.Sharded F) (T : Periodic.Compact F) (rows : Nat)
    (main : Nat → Nat → F) :
    (compactAir S T rows).ledger main = T.ledger S.width S.buses rows main := by
  unfold Air.ledger Periodic.Compact.ledger
  rw [System.finset_sum_range_list]
  rfl

theorem compactAirs_ledger (S : Periodic.Sharded F) (tables : List (Periodic.Compact F))
    (HT : Nat → Nat) (mainT : Nat → Nat → Nat → F) :
    stageLedger (compactAirs S tables HT) mainT = Periodic.compactLedger S tables HT mainT := by
  unfold stageLedger compactAirs Periodic.compactLedger
  have hzip : (tables.zipIdx.map fun x => compactAir S x.1 (HT x.2)).zipIdx =
      tables.zipIdx.map fun x => (compactAir S x.1 (HT x.2), x.2) := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp at hi ⊢
  rw [hzip, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨T, t⟩ _
  exact compactAir_ledger S T (HT t) (mainT t)

omit [DecidableEq F] in
theorem compactCircuit_inBounds {W : Nat} (hW : 4 ≤ W) (T : Periodic.Compact F) :
    Circuit.inBounds (T.circuit W) = true := by
  have hcell : ∀ j < W - 1, (T.cellVar W j : Nat) < T.mainWidth W + (3 + T.nFixed) := by
    intro j hj
    unfold Periodic.Compact.cellVar Periodic.Compact.mainWidth
    split
    · show 1 + (W - 1 - T.nFixed) + 3 + j < 1 + (W - 1 - T.nFixed) + (3 + T.nFixed); omega
    · show 1 + (j - T.nFixed) < 1 + (W - 1 - T.nFixed) + (3 + T.nFixed); omega
  have hmw : 0 < T.mainWidth W := by unfold Periodic.Compact.mainWidth; omega
  simp only [Circuit.inBounds, Periodic.Compact.circuit, Lookup.inBounds,
    Periodic.Compact.lookupL, Periodic.Compact.lookupW, List.all_nil, List.all_cons,
    Bool.true_and, Bool.and_true, Bool.and_eq_true,
    List.all_eq_true, List.mem_map, List.mem_range,
    inBounds_const, inBounds_var, inBounds_sub, inBounds_mul, true_and]
  refine ⟨⟨⟨by omega, by omega⟩, by omega, ?_⟩, ⟨⟨by omega, by omega⟩, by omega, ?_⟩⟩
  · rintro _ ⟨j, hj, rfl⟩
    rw [inBounds_var]
    exact hcell j (by omega)
  · rintro _ ⟨j, hj, rfl⟩
    rw [inBounds_var]
    exact hcell j hj

theorem compactAir_inBounds {S : Periodic.Sharded F} (hW : 4 ≤ S.width)
    (T : Periodic.Compact F) (rows : Nat) :
    Circuit.inBounds (compactAir S T rows).circuit = true :=
  compactCircuit_inBounds hW T

/-- All tables of a periodic sharded + compact system concatenated in order:
shards `0 .. S.shards.length - 1`, followed by compact tables `0 .. tables.length - 1`. -/
def compactSystemAirs (S : Periodic.Sharded F) (H : Nat → Nat)
    (tables : List (Periodic.Compact F)) (HT : Nat → Nat) : List (Air F) :=
  shardAirs S H ++ compactAirs S tables HT

theorem compactSystemAirs_inBounds {S : Periodic.Sharded F} (hW : 4 ≤ S.width)
    (H : Nat → Nat) (tables : List (Periodic.Compact F)) (HT : Nat → Nat) :
    ∀ a ∈ compactSystemAirs S H tables HT, Circuit.inBounds a.circuit = true := by
  intro a ha
  simp only [compactSystemAirs, shardAirs, compactAirs, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨k, _, rfl⟩ | ⟨⟨T, t⟩, _, rfl⟩
  · exact shardAir_inBounds hW k (H k)
  · exact compactAir_inBounds hW T (HT t)

theorem compactSystemAirs_rows_le {S : Periodic.Sharded F} {H : Nat → Nat}
    {tables : List (Periodic.Compact F)} {HT : Nat → Nat} {rows : Nat}
    (hH : ∀ k < S.shards.length, H k ≤ rows)
    (hHT : ∀ t < tables.length, HT t ≤ rows) :
    ∀ a ∈ compactSystemAirs S H tables HT, a.rows ≤ rows := by
  intro a ha
  simp only [compactSystemAirs, shardAirs, compactAirs, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨k, hk, rfl⟩ | ⟨⟨T, t⟩, ht, rfl⟩
  · exact hH k (List.mem_range.mp hk)
  · have hlt : t < tables.length := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp ht)).1
    exact hHT t hlt

end Adapters

/-! ## 6. End-to-end Goldilocks corollaries (Endpoint 1 `num_circuits == 1`) -/

section GoldilocksCorollaries

open Aiur.Circuit
open Aiur.Optimized
open Bridge
open Aiur.Library.U32.Goldilocks (modulus)

local notation "GF" => ZMod modulus

/-- **End-to-end wide stage, single horizontally packed circuit over Goldilocks.**
Packs all unit, map, and ROM tables into ONE circuit `pack airs rows` (`num_circuits == 1`).
A single packed main trace satisfying `(pack airs rows).Holds main` whose single-circuit
ledger balances against `Finsupp.single (encode idOf root) 1` implies `EvalFn` and a valid ROM. -/
theorem wide_single_circuit_sound_goldilocks {source : Generic.Source GF} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Physical.Prepared compiled.artifact) {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    (chipsIn : ∀ u ∈ units, u.1.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u.1 = true)
    (unitsInBounds : ∀ u ∈ units, Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (capacity : WideStage.unitCapRows units ≤ 2 ^ 39)
    {mapCap : Nat → Nat} {roms : List (Nat × Nat)} (widths : (roms.map Prod.fst).Nodup)
    {bound : Nat} (romCaps : ∀ r ∈ roms, r.2 ≤ bound)
    (hbound : bound ≤ 2 ^ 63) (tags : 2 < bound) (lookups : WideStage.unitCapLookups units < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {rows : Nat}
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ WideStage.mapLengths
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)), mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, r.2 ≤ rows)
    {main : Nat → Nat → GF}
    (holds : (pack (wideAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap roms) rows).Holds main)
    (balanced : (pack (wideAirs idOf units
      ((Depth.system cfg prepared.system).mapClaims.map (encode idOf)) mapCap roms) rows).ledger main +
      Finsupp.single (encode idOf root) 1 = 0) :
    let claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
    let airs := wideAirs idOf units claims mapCap roms
    let mainR := fun j => sliceMain airs main (units.length + (WideStage.mapLengths claims).length + j)
    (WideStage.wideRom roms mainR).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (WideStage.wideRom roms mainR)).decode
          specialized.program.enums) heap value result := by
  set claims := (Depth.system cfg prepared.system).mapClaims.map (encode idOf)
  set airs := wideAirs idOf units claims mapCap roms
  set mainU := sliceMain airs main
  set mainM := fun j => sliceMain airs main (units.length + j)
  set mainR := fun j => sliceMain airs main (units.length + (WideStage.mapLengths claims).length + j)
  have hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true := wideAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows := wideAirs_rows_le unitsTall mapsTall romsTall
  have hStage : StageHolds airs (sliceMain airs main) := pack_holds_sound hIn hRows holds
  have hUnitsHolds : StageHolds (WideStage.unitAirs idOf units) mainU := by
    have h1 := (stageHolds_append _ _ _).mp hStage
    exact ((stageHolds_append _ _ _).mp h1.1).1
  have hLedger : (pack airs rows).ledger main =
      WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
      WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM +
      WideStage.stageLedger (WideStage.romAirs roms) mainR := by
    rw [pack_ledger_eq main hIn hRows]
    simp only [airs, wideAirs, stageLedger_append, WideStage.unitAirs, WideStage.mapAirs,
      List.length_append, List.length_map]
    rfl
  rw [hLedger] at balanced
  exact Goldilocks.wide_heap_sound_goldilocks compiled prepared certified plan activated entry signed
    rooted outside arguments decoded idOf chipsIn unrolled capacity widths romCaps hbound tags lookups
    hbits shaped context enablesOk hUnitsHolds balanced

/-- **Prover completeness for a horizontally packed wide stage over Goldilocks.** -/
theorem wide_single_circuit_complete_goldilocks {idOf : String → Nat}
    {units : List ((Chip GF × Option (Unroll GF)) × Nat)}
    {claims : List (List GF)} {mapCap : Nat → Nat} {roms : List (Nat × Nat)} {rows : Nat}
    (unitsInBounds : ∀ u ∈ units, Circuit.inBounds (Bridge.unitCircuit idOf u.1) = true)
    (unitsTall : ∀ u ∈ units, u.2 ≤ rows)
    (mapsTall : ∀ L ∈ WideStage.mapLengths claims, mapCap L ≤ rows)
    (romsTall : ∀ r ∈ roms, r.2 ≤ rows)
    {mainU mainM mainR : Nat → Nat → Nat → GF}
    (holdsU : StageHolds (WideStage.unitAirs idOf units) mainU) :
    let airs := wideAirs idOf units claims mapCap roms
    let mains := appendMains (units.length + (WideStage.mapLengths claims).length)
      (appendMains units.length mainU mainM) mainR
    (pack airs rows).Holds (packMain airs mains) ∧
      (pack airs rows).ledger (packMain airs mains) =
        WideStage.stageLedger (WideStage.unitAirs idOf units) mainU +
        WideStage.stageLedger (WideStage.mapAirs claims mapCap) mainM +
        WideStage.stageLedger (WideStage.romAirs roms) mainR := by
  set airs := wideAirs idOf units claims mapCap roms
  set mains := appendMains (units.length + (WideStage.mapLengths claims).length)
    (appendMains units.length mainU mainM) mainR
  have hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true := wideAirs_inBounds unitsInBounds
  have hRows : ∀ a ∈ airs, a.rows ≤ rows := wideAirs_rows_le unitsTall mapsTall romsTall
  have hLenU : (WideStage.unitAirs idOf units).length = units.length := by simp [WideStage.unitAirs]
  have hLenM : (WideStage.mapAirs claims mapCap).length = (WideStage.mapLengths claims).length := by
    simp [WideStage.mapAirs]
  have hLenUM : (WideStage.unitAirs idOf units ++ WideStage.mapAirs claims mapCap).length =
      units.length + (WideStage.mapLengths claims).length := by
    rw [List.length_append, hLenU, hLenM]
  have holdsM : StageHolds (WideStage.mapAirs claims mapCap) mainM := by
    rintro ⟨a, j⟩ hx i _ p hp
    have hmem := List.fst_mem_of_mem_zipIdx hx
    simp only [WideStage.mapAirs, List.mem_map] at hmem
    obtain ⟨L, _, rfl⟩ := hmem
    cases hp
  have holdsR : StageHolds (WideStage.romAirs roms) mainR := by
    rintro ⟨a, j⟩ hx i _ p hp
    have hmem := List.fst_mem_of_mem_zipIdx hx
    simp only [WideStage.romAirs, List.mem_map] at hmem
    obtain ⟨r, _, rfl⟩ := hmem
    cases hp
  have hStage : StageHolds airs mains := by
    simp only [airs, wideAirs, mains, ← hLenUM]
    rw [stageHolds_appendMains]
    refine ⟨?_, holdsR⟩
    rw [← hLenU, stageHolds_appendMains]
    exact ⟨holdsU, holdsM⟩
  refine ⟨pack_holds_complete hIn hRows hStage, ?_⟩
  rw [pack_ledger_packMain mains hIn hRows]
  simp only [airs, wideAirs, mains, ← hLenUM]
  rw [stageLedger_appendMains, ← hLenU, stageLedger_appendMains]

/-- **End-to-end periodic sharded + compact tables, single horizontally packed circuit
over Goldilocks (`num_circuits == 1`).**
Wraps every shard `k` (`S.circuit k`, `S.assign k`, `H k`) via `shardAir` and every
compact table `t` (`T.circuit S.width`, `T.assign S.width S.buses`, `HT t`) via `compactAir`,
packs them horizontally into ONE single circuit `pack (compactSystemAirs S H tables HT) rows`,
and derives `EvalFn` and a valid `Periodic.compactRom` directly from
`Goldilocks.narrow_heap_sound_compact_goldilocks`. Notice zero extra variable-bounds
hypotheses are required — both `shardAir` and `compactAir` are proved in-bounds
automatically from `ok : S.check = true`! -/
theorem narrow_compact_single_circuit_sound_goldilocks {source : Generic.Source GF}
    {entries : List String} {specialized : Generic.Specialized source entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg prepared.system)
    {id : String → Except String Nat}
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries)
    {args : List (SourceValue GF)} {result : Value GF} {wires : List (WireValue GF)}
    {output : WireValue GF}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Circuit.Message GF}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result)
    (idOf : String → Nat) {S : Periodic.Sharded GF} (ok : S.check = true)
    {units : List (Chip GF × Option (Unroll GF))} (chipsIn : ∀ u ∈ units, u.1 ∈ plan.singles)
    (unrolled : ∀ u ∈ units, unitOk idOf u = true)
    {wide : List (Circuit GF)} {groups : List (List (List Nat))}
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = units.map (unitCircuit idOf))
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    {ν : GF → Nat} {tables : List (Periodic.Compact GF)}
    (tablesOk : Periodic.checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (capacity : Bridge.capacityRowsU units S.system ≤ 2 ^ 39)
    {bound : Nat} (hbound : bound ≤ 2 ^ 63) (tags : 3 < bound)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : Periodic.copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (lookups : Bridge.capacityLookupsU units S.system < bound) (ids : S.system.instances ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 +
      (tables.map (·.parts.length)).sum < bound)
    (hbits : cfg.bits ≤ 24)
    (shaped : Shaped.check (Depth.system cfg prepared.system) plan.singles idOf root bound = true)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (req : (Part.request S.width (encode idOf root)).checkRequest S.system
      (encode idOf root) = true)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true)
    {H : Nat → Nat} {HT : Nat → Nat} {rows : Nat}
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (shardsFit : ∀ k < S.shards.length, H k ≤ rows)
    (tablesFit : ∀ t < tables.length, HT t ≤ rows)
    {main : Nat → Nat → GF}
    (holds : (pack (compactSystemAirs S H tables HT) rows).Holds main)
    (balanced : Finsupp.mapDomain trimZeros
      ((pack (compactSystemAirs S H tables HT) rows).ledger main +
        S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    let airs := compactSystemAirs S H tables HT
    let mainT := fun t => sliceMain airs main (S.shards.length + t)
    (Periodic.compactRom S tables mainT).Valid ∧
      ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
        Represents ((Erasure.typedROM compiled.system (Periodic.compactRom S tables mainT)).decode
          specialized.program.enums) heap value result := by
  set airs := compactSystemAirs S H tables HT
  set mainS := sliceMain airs main
  set mainT := fun t => sliceMain airs main (S.shards.length + t)
  have hW4 : 4 ≤ S.width := by
    have keyed := (Periodic.Sharded.check_parts ok).1
    have valid' := S.system.valid_of_checkKeyed keyed
    simpa [Periodic.Sharded.system] using valid'.width.1
  have hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true :=
    compactSystemAirs_inBounds hW4 H tables HT
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    compactSystemAirs_rows_le shardsFit tablesFit
  have hStage : StageHolds airs (sliceMain airs main) := pack_holds_sound hIn hRows holds
  have hShardRows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (mainS k) p) :=
    (shardAirs_holds_iff S H mainS).mp ((stageHolds_append _ _ _).mp hStage).1
  have hLedger : (pack airs rows).ledger main =
      S.ledger H mainS + Periodic.compactLedger S tables HT mainT := by
    rw [pack_ledger_eq main hIn hRows]
    simp only [airs, compactSystemAirs, stageLedger_append]
    have hLen : (shardAirs S H).length = S.shards.length := by simp [shardAirs]
    rw [hLen, shardAirs_ledger, compactAirs_ledger]
    rfl
  rw [hLedger] at balanced
  exact Goldilocks.narrow_heap_sound_compact_goldilocks compiled prepared certified plan activated
    entry signed rooted outside arguments decoded idOf ok chipsIn unrolled circuits wideEq lenG
    merged tablesOk mapsIn capacity hbound tags codesBound labels shadowBound lookups ids parts
    hbits shaped context req req2 enablesOk tall tallT hShardRows balanced

/-- **Prover completeness for a horizontally packed periodic sharded + compact system.** -/
theorem narrow_compact_single_circuit_complete {F : Type} [Field F] [DecidableEq F]
    {S : Periodic.Sharded F} (hW4 : 4 ≤ S.width)
    {H : Nat → Nat} {tables : List (Periodic.Compact F)} {HT : Nat → Nat} {rows : Nat}
    (shardsFit : ∀ k < S.shards.length, H k ≤ rows)
    (tablesFit : ∀ t < tables.length, HT t ≤ rows)
    {mainS mainT : Nat → Nat → Nat → F}
    (shardRows : ∀ k < S.shards.length, ∀ p < H k,
      Scalar.Circuit.Satisfies (S.circuit k).constraints (S.assign k (mainS k) p)) :
    let airs := compactSystemAirs S H tables HT
    let mains := appendMains S.shards.length mainS mainT
    (pack airs rows).Holds (packMain airs mains) ∧
      (pack airs rows).ledger (packMain airs mains) =
        S.ledger H mainS + Periodic.compactLedger S tables HT mainT := by
  set airs := compactSystemAirs S H tables HT
  set mains := appendMains S.shards.length mainS mainT
  have hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true :=
    compactSystemAirs_inBounds hW4 H tables HT
  have hRows : ∀ a ∈ airs, a.rows ≤ rows :=
    compactSystemAirs_rows_le shardsFit tablesFit
  have hLen : (shardAirs S H).length = S.shards.length := by simp [shardAirs]
  have hStage : StageHolds airs mains := by
    simp only [airs, compactSystemAirs, mains, ← hLen]
    rw [stageHolds_appendMains]
    exact ⟨(shardAirs_holds_iff S H mainS).mpr shardRows, compactAirs_holds S tables HT mainT⟩
  refine ⟨pack_holds_complete hIn hRows hStage, ?_⟩
  rw [pack_ledger_packMain mains hIn hRows]
  simp only [airs, compactSystemAirs, mains, ← hLen]
  rw [stageLedger_appendMains, shardAirs_ledger, compactAirs_ledger]

end GoldilocksCorollaries

/-! ## 7. Smoke tests (smart active-selector gating & concrete Goldilocks packing) -/

section SmokeTests

open Aiur.Library.U32.Goldilocks (modulus)

private abbrev SmokeGF := ZMod modulus

/-- Full-height constituent (`rows = 4`, `width = 2`, `fixedWidth = 1`):
constraint `x₀ - c₀ = 0`, lookup `push(x₁, [x₀])`. -/
private def smokeFullAir : Air SmokeGF where
  circuit := {
    width := 2
    fixedWidth := 1
    constraints := [.sub (.var 0) (.var 2)]
    lookups := [⟨.var 1, [.var 0]⟩]
  }
  rows := 4
  fixed := fun i _ => (i : SmokeGF)

/-- Short constituent (`rows = 2 < 4`, `width = 1`, `fixedWidth = 0`):
constraint `x₀ - 7 = 0`, lookup `push(1, [x₀])`. -/
private def smokeShortAir : Air SmokeGF where
  circuit := {
    width := 1
    fixedWidth := 0
    constraints := [.sub (.var 0) (.const 7)]
    lookups := [⟨.const 1, [.var 0]⟩]
  }
  rows := 2
  fixed := fun _ _ => 0

/-- Mixed-height packing into `rows = 4`: total main width is `2 + 1 = 3`, total fixed width is
`1 + (0 + 1) = 2` (zero extra fixed column for full-height `smokeFullAir`, one active selector
column for short `smokeShortAir`). -/
example : (pack [smokeFullAir, smokeShortAir] 4).circuit.width = 3 := rfl
example : (pack [smokeFullAir, smokeShortAir] 4).circuit.fixedWidth = 2 := rfl

/-- Uniform-height packing allocates zero active-selector columns. -/
example : (pack [smokeFullAir, smokeFullAir] 4).circuit.fixedWidth = 2 := rfl

/-- Full-height `smokeFullAir` gets ungated constraint `.sub (.var 0) (.var 3)` (zero degree overhead),
while short `smokeShortAir` gets gated constraint `.mul (.var 4) (.sub (.var 2) (.const 7))`. -/
example : (pack [smokeFullAir, smokeShortAir] 4).circuit.constraints =
    [.sub (.var 0) (.var 3), .mul (.var 4) (.sub (.var 2) (.const 7))] := rfl

/-- The active selector column (`fixed` col 1) of `smokeShortAir` is `1` on rows `0, 1` and `0` on `2, 3`. -/
example : (pack [smokeFullAir, smokeShortAir] 4).fixed 0 1 = 1 := rfl
example : (pack [smokeFullAir, smokeShortAir] 4).fixed 1 1 = 1 := rfl
example : (pack [smokeFullAir, smokeShortAir] 4).fixed 2 1 = 0 := rfl
example : (pack [smokeFullAir, smokeShortAir] 4).fixed 3 1 = 0 := rfl

/-- Both constituents and their packed circuit pass the decidable `Circuit.inBounds` check. -/
example : Circuit.inBounds (pack [smokeFullAir, smokeShortAir] 4).circuit = true := by decide

/-- Concrete soundness + completeness roundtrip on mixed-height Goldilocks `Air`s:
the short table's witness can be arbitrary on inactive rows `i ≥ 2`, yet the packed
single circuit holds on all 4 rows and has the exact combined ledger. -/
example :
    let airs : List (Air SmokeGF) := [smokeFullAir, smokeShortAir]
    let mains : Nat → Nat → Nat → SmokeGF := fun idx i v =>
      if idx = 0 then (if v = 0 then (i : SmokeGF) else 1)
      else (if i < 2 then 7 else 999)
    (pack airs 4).Holds (packMain airs mains) ∧
      (pack airs 4).ledger (packMain airs mains) = stageLedger airs mains := by
  intro airs mains
  have hIn : ∀ a ∈ airs, Circuit.inBounds a.circuit = true := by
    intro a ha
    simp only [airs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide
  have hRows : ∀ a ∈ airs, a.rows ≤ 4 := by
    intro a ha
    simp only [airs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide
  have hStage : StageHolds airs mains := by
    rintro ⟨a, idx⟩ hmem i hi e he
    simp only [airs, List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [smokeFullAir, List.mem_singleton] at he
      subst he
      simp [Air.assign, smokeFullAir, mains, ArithExpr.denote]
    · simp only [smokeShortAir, List.mem_singleton] at he
      subst he
      have hi1 : i ≤ 1 := Nat.lt_succ_iff.mp hi
      simp [Air.assign, smokeShortAir, mains, ArithExpr.denote, hi1]
  exact ⟨pack_holds_complete hIn hRows hStage, pack_ledger_packMain mains hIn hRows⟩

end SmokeTests

/-! ## 8. Axiom audit guards -/

/-- info: 'Aiur.Tiling.SingleCircuit.remapExpr_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms remapExpr_denote

/-- info: 'Aiur.Tiling.SingleCircuit.pack_inBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_inBounds

/-- info: 'Aiur.Tiling.SingleCircuit.pack_holds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_holds_sound

/-- info: 'Aiur.Tiling.SingleCircuit.pack_ledger_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_ledger_eq

/-- info: 'Aiur.Tiling.SingleCircuit.pack_holds_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_holds_complete

/-- info: 'Aiur.Tiling.SingleCircuit.pack_ledger_packMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_ledger_packMain

/-- info: 'Aiur.Tiling.SingleCircuit.pack_holds_iff_packMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pack_holds_iff_packMain

/-- info: 'Aiur.Tiling.SingleCircuit.shardAirs_holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shardAirs_holds_iff

/-- info: 'Aiur.Tiling.SingleCircuit.shardAirs_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shardAirs_ledger

/-- info: 'Aiur.Tiling.SingleCircuit.compactAirs_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compactAirs_ledger

/-- info: 'Aiur.Tiling.SingleCircuit.wide_single_circuit_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_single_circuit_sound_goldilocks

/-- info: 'Aiur.Tiling.SingleCircuit.wide_single_circuit_complete_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wide_single_circuit_complete_goldilocks

/-- info: 'Aiur.Tiling.SingleCircuit.narrow_compact_single_circuit_sound_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms narrow_compact_single_circuit_sound_goldilocks

/-- info: 'Aiur.Tiling.SingleCircuit.narrow_compact_single_circuit_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms narrow_compact_single_circuit_complete

end Aiur.Tiling.SingleCircuit
