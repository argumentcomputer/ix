import IxAIRefine.Fixed.Specs

/-! # Specs of the middle layer of `Fixed`, up to `step`

Every observed derivation (`ObsFn`) of a function of the formal `Fixed` program between the
leaves of `IxAIRefine.Fixed.Specs` and `Fixed::step` returns the encoding of the corresponding
piece of `IxAICore.Decision`, computed in Lean. The specs compose bottom-up:

* `hidden_unit_spec`, `output_unit_spec`, `back_unit_spec`, `upd_spec`: one entry of the hidden
  pre-activations, of the outputs, of `dz`, and one SGD update `Fx.sub w (Fx.mul lr g)`.
* `hidden_spec`, `outputs_spec`, `sub11_spec`: `Model.hidden` (both components), the outputs
  computed from `h`, and `List.zipWith Fx.sub`.
* `delta_spec`, `deltas_spec`: `Model.delta` and the batch's `ds` in `Model.step`, as the
  triples `(h, dz, dout)` and the three matrices `ds.map (·.h)`, `ds.map (·.dz)`,
  `ds.map (·.dout)`.
* `transpose11x16_spec`, `transpose20x16_spec`, `transpose20x8_spec`, `transpose20x11_spec`:
  `transposeN`. These need no shape hypotheses: the path's array pattern fixes the number of
  rows, every entry is a successful projection of its row, and `transposeN_eq_cols` reads
  `transposeN` column by column.
* `update_row8_spec`, `update_row16_spec`, `update_w1_spec`, `update_w2_spec`,
  `update_bias16_spec`, `update_bias11_spec`: the fields of `Model.step`.
* `step_spec`: `Fixed::step` on the encoded model, batch and learning rate returns
  `encModel (Model.step lr m batch)`; `step_spec_host` restates it with the host's
  `IxAIAiur.stepArgs` and `IxAIAiur.modelValue`.

The encodings `encVec`, `encMat`, `encModel` are the host's `vec`, `mat`, `modelValue`
(`encVec_eq_vec`, `encMat_eq_mat`, `encModel_eq_modelValue`).

Rounding and sign tests are exact only below `2^55` in magnitude, so the specs carry the bounds
of every value that reaches `shr8` or `sign_split`: every dot product before rounding, every
product `lr · g`, and every hidden pre-activation. `StepBounds lr m batch` collects them for one
step; `stepBoundsB` decides them, and `stepBounds_of` turns `stepBoundsB … = true` into
`StepBounds …`. `IxAIRefine.Fixed.Magnitudes` derives `StepBounds` from parameters below `2^13`
(`ModelW`), inputs and targets at most `2^12`, and `|lr| ≤ 2^8`. `Fixed::upd` range-checks every
parameter it returns with `Fixed::bound`, so `upd_spec`, the update specs and `step_spec` also
conclude `ModelW` of the result. Additions and subtractions are field operations and need no
bound: the field value is the cast of the integer result, which is what `fxVal` encodes.

The shapes are fixed: 16 hidden units, 8 inputs, 11 outputs, batches of 20.

Each spec unpacks the generated `«Fixed::f».Path.run` positionally; a comment before it lists
the constructor's fields as the generator (`IxAIRefine.ObsGen`) emits them for the current
program, and which of them the proof uses. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxAIStep.Fixed.Specs

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxAIStep.Fixed.Obs

/-! ## Encodings -/

/-- A vector of fixed-point numbers as a tuple of field values (`IxAIAiur.vec`). -/
def encVec (xs : List IxAICore.Fx) : SourceValue F := .tuple (xs.map fxVal)

/-- A matrix, row by row (`IxAIAiur.mat`). -/
def encMat (xss : List (List IxAICore.Fx)) : SourceValue F := .tuple (xss.map encVec)

/-- A model as `Fixed::step` returns it (`IxAIAiur.modelValue`). -/
def encModel (m : IxAICore.Model) : SourceValue F :=
  .tuple [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2]

theorem encVec_eq_vec (xs : List IxAICore.Fx) : encVec xs = IxAIAiur.vec xs := rfl

theorem encMat_eq_mat (xss : List (List IxAICore.Fx)) : encMat xss = IxAIAiur.mat xss := rfl

theorem encModel_eq_modelValue (m : IxAICore.Model) :
    encModel m = IxAIAiur.modelValue m := rfl

/-! ## The pieces of `Model.step`

Named forms of the subterms of `Model.hidden`, `Model.delta` and `Model.step`; each is
definitionally the subterm it names. -/

/-- The hidden pre-activations: `(Model.hidden m x).1` for `m.w1 = w1`, `m.b1 = b1`. -/
def hiddenZ (w1 : List (List IxAICore.Fx)) (b1 x : List IxAICore.Fx) : List IxAICore.Fx :=
  List.zipWith (fun row b => IxAICore.Fx.add (IxAICore.Fx.dot row x) b) w1 b1

/-- The outputs from the hidden activations `h` (`o` in `Model.delta`). -/
def outputsOf (w2 : List (List IxAICore.Fx)) (b2 h : List IxAICore.Fx) : List IxAICore.Fx :=
  List.zipWith (fun row b => IxAICore.Fx.add (IxAICore.Fx.dot row h) b) w2 b2

/-- `dout` in `Model.delta`. -/
def doutOf (m : IxAICore.Model) (x t : List IxAICore.Fx) : List IxAICore.Fx :=
  List.zipWith IxAICore.Fx.sub (outputsOf m.w2 m.b2 ((hiddenZ m.w1 m.b1 x).map IxAICore.Fx.relu)) t

/-- One row of `w1` or `w2` after the step: `w - lr · (d · col)` for each column. -/
def updRow (lr : IxAICore.Fx) (row d : List IxAICore.Fx) (cols : List (List IxAICore.Fx)) :
    List IxAICore.Fx :=
  List.zipWith (fun w xi => IxAICore.Fx.sub w (IxAICore.Fx.mul lr (IxAICore.Fx.dot d xi))) row cols

/-- A bias vector after the step: `b - lr · Σ d`. -/
def updBias (lr : IxAICore.Fx) (b : List IxAICore.Fx) (ds : List (List IxAICore.Fx)) :
    List IxAICore.Fx :=
  List.zipWith (fun b dzj => IxAICore.Fx.sub b (IxAICore.Fx.mul lr (IxAICore.Fx.sum dzj))) b ds

/-- `ds` in `Model.step`, for a given `w2T`. -/
def deltasOf (m : IxAICore.Model) (w2T : List (List IxAICore.Fx))
    (batch : List (List IxAICore.Fx × List IxAICore.Fx)) : List IxAICore.Delta :=
  batch.map fun (x, t) => m.delta w2T x t

/-- `w2T` in `Model.step`. -/
def w2TOf (m : IxAICore.Model) : List (List IxAICore.Fx) := IxAICore.transposeN m.b1.length m.w2

/-- `dzT` in `Model.step`. -/
def dzTOf (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    List (List IxAICore.Fx) :=
  IxAICore.transposeN m.b1.length ((deltasOf m (w2TOf m) batch).map (·.dz))

/-- `xT` in `Model.step`. -/
def xTOf (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    List (List IxAICore.Fx) :=
  IxAICore.transposeN (IxAICore.getD m.w1 0 []).length ((deltasOf m (w2TOf m) batch).map (·.x))

/-- `hT` in `Model.step`. -/
def hTOf (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    List (List IxAICore.Fx) :=
  IxAICore.transposeN m.b1.length ((deltasOf m (w2TOf m) batch).map (·.h))

/-- `doutT` in `Model.step`. -/
def doutTOf (m : IxAICore.Model) (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    List (List IxAICore.Fx) :=
  IxAICore.transposeN m.b2.length ((deltasOf m (w2TOf m) batch).map (·.dout))

theorem hidden_eq (m : IxAICore.Model) (x : List IxAICore.Fx) :
    m.hidden x = (hiddenZ m.w1 m.b1 x, (hiddenZ m.w1 m.b1 x).map IxAICore.Fx.relu) := rfl

/-- **`Model.step` on a nonempty batch**, with its fields named. -/
theorem step_of_ne {lr : IxAICore.Fx} {m : IxAICore.Model}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)} (hne : batch.isEmpty = false) :
    IxAICore.Model.step lr m batch =
      { w1 := List.zipWith (fun row dzj => updRow lr row dzj (xTOf m batch)) m.w1 (dzTOf m batch)
        b1 := updBias lr m.b1 (dzTOf m batch)
        w2 := List.zipWith (fun row dk => updRow lr row dk (hTOf m batch)) m.w2 (doutTOf m batch)
        b2 := updBias lr m.b2 (doutTOf m batch) } := by
  unfold IxAICore.Model.step
  rw [hne]
  first
    | rfl
    | (simp only [Bool.false_eq_true, if_false]; rfl)
    | (simp only [Bool.false_eq_true, ↓reduceIte]; rfl)

/-! ## Bounds

`Small v` is the range on which `shr8` and `sign_split` are exact. The predicates below list,
per function, every value that reaches them. -/

/-- The range on which `Fixed::shr8` and `Fixed::sign_split` are exact. -/
abbrev Small (v : ℤ) : Prop := |v| < 2 ^ 55

/-- The range `Fixed::bound` admits for a parameter, `[-4096, 4320)`, widened to `|v| < 2^13`. -/
abbrev SmallW (v : ℤ) : Prop := |v| < 2 ^ 13

/-- Every entry of a parameter vector is in `Fixed::bound`'s range. -/
def VecW (l : List IxAICore.Fx) : Prop := ∀ a ∈ l, SmallW a.raw

/-- Every entry of a parameter matrix is in `Fixed::bound`'s range. -/
def MatW (l : List (List IxAICore.Fx)) : Prop := ∀ row ∈ l, VecW row

/-- **Every parameter of the model is below `2^13` in magnitude.** `Fixed::upd` checks this of
every parameter a step returns. -/
def ModelW (m : IxAICore.Model) : Prop := MatW m.w1 ∧ VecW m.b1 ∧ MatW m.w2 ∧ VecW m.b2

/-- The values `Fixed::delta` rounds or sign-tests for one example `(x, t)`: the dot products
of `w1` with `x` (`dot8`), the hidden pre-activations (`relu`, `pos`), the dot products of `w2`
with `h` (`dot16`), and those of `w2T`'s rows with `dout` (`dot11`). -/
structure DeltaBounds (m : IxAICore.Model) (w2T : List (List IxAICore.Fx))
    (x t : List IxAICore.Fx) : Prop where
  dot1 : ∀ row ∈ m.w1, Small (IxAICore.Fx.dotRaw row x)
  pre : ∀ z ∈ hiddenZ m.w1 m.b1 x, Small z.raw
  dot2 : ∀ row ∈ m.w2, Small (IxAICore.Fx.dotRaw row ((hiddenZ m.w1 m.b1 x).map IxAICore.Fx.relu))
  dot3 : ∀ col ∈ w2T, Small (IxAICore.Fx.dotRaw col (doutOf m x t))

/-- The values one row update rounds: each gradient `d · col` (`dot20`) and each product
`lr · (d · col)` (`mul`). -/
def RowBounds (lr : IxAICore.Fx) (d : List IxAICore.Fx) (cols : List (List IxAICore.Fx)) : Prop :=
  ∀ c ∈ cols, Small (IxAICore.Fx.dotRaw d c) ∧ Small (lr.raw * (IxAICore.Fx.dot d c).raw)

/-- The values a bias update rounds: each product `lr · Σ d` (`mul`). -/
def BiasBounds (lr : IxAICore.Fx) (ds : List (List IxAICore.Fx)) : Prop :=
  ∀ d ∈ ds, Small (lr.raw * (IxAICore.Fx.sum d).raw)

/-- **Every value one SGD step rounds or sign-tests is below `2^55` in magnitude.** -/
structure StepBounds (lr : IxAICore.Fx) (m : IxAICore.Model)
    (batch : List (List IxAICore.Fx × List IxAICore.Fx)) : Prop where
  deltas : ∀ p ∈ batch, DeltaBounds m (w2TOf m) p.1 p.2
  w1 : ∀ d ∈ dzTOf m batch, RowBounds lr d (xTOf m batch)
  b1 : BiasBounds lr (dzTOf m batch)
  w2 : ∀ d ∈ doutTOf m batch, RowBounds lr d (hTOf m batch)
  b2 : BiasBounds lr (doutTOf m batch)

/-! ### A decision procedure -/

def smallB (v : ℤ) : Bool := decide (|v| < 2 ^ 55)

def deltaBoundsB (m : IxAICore.Model) (w2T : List (List IxAICore.Fx)) (x t : List IxAICore.Fx) :
    Bool :=
  (m.w1.all fun row => smallB (IxAICore.Fx.dotRaw row x)) &&
  ((hiddenZ m.w1 m.b1 x).all fun z => smallB z.raw) &&
  (m.w2.all fun row =>
    smallB (IxAICore.Fx.dotRaw row ((hiddenZ m.w1 m.b1 x).map IxAICore.Fx.relu))) &&
  (w2T.all fun col => smallB (IxAICore.Fx.dotRaw col (doutOf m x t)))

def rowBoundsB (lr : IxAICore.Fx) (d : List IxAICore.Fx) (cols : List (List IxAICore.Fx)) : Bool :=
  cols.all fun c =>
    smallB (IxAICore.Fx.dotRaw d c) && smallB (lr.raw * (IxAICore.Fx.dot d c).raw)

def biasBoundsB (lr : IxAICore.Fx) (ds : List (List IxAICore.Fx)) : Bool :=
  ds.all fun d => smallB (lr.raw * (IxAICore.Fx.sum d).raw)

/-- Decides `StepBounds lr m batch` (`stepBounds_of`). -/
def stepBoundsB (lr : IxAICore.Fx) (m : IxAICore.Model)
    (batch : List (List IxAICore.Fx × List IxAICore.Fx)) : Bool :=
  (batch.all fun p => deltaBoundsB m (w2TOf m) p.1 p.2) &&
  ((dzTOf m batch).all fun d => rowBoundsB lr d (xTOf m batch)) &&
  biasBoundsB lr (dzTOf m batch) &&
  ((doutTOf m batch).all fun d => rowBoundsB lr d (hTOf m batch)) &&
  biasBoundsB lr (doutTOf m batch)

theorem small_of_smallB {v : ℤ} (h : smallB v = true) : Small v := of_decide_eq_true h

theorem deltaBounds_of {m : IxAICore.Model} {w2T : List (List IxAICore.Fx)}
    {x t : List IxAICore.Fx} (h : deltaBoundsB m w2T x t = true) : DeltaBounds m w2T x t := by
  simp only [deltaBoundsB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun row hr => small_of_smallB (h1 row hr), fun z hz => small_of_smallB (h2 z hz),
    fun row hr => small_of_smallB (h3 row hr), fun c hc => small_of_smallB (h4 c hc)⟩

theorem rowBounds_of {lr : IxAICore.Fx} {d : List IxAICore.Fx} {cols : List (List IxAICore.Fx)}
    (h : rowBoundsB lr d cols = true) : RowBounds lr d cols := by
  intro c hc
  have hc' := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true] at hc'
  exact ⟨small_of_smallB hc'.1, small_of_smallB hc'.2⟩

theorem biasBounds_of {lr : IxAICore.Fx} {ds : List (List IxAICore.Fx)}
    (h : biasBoundsB lr ds = true) : BiasBounds lr ds := by
  intro d hd
  exact small_of_smallB (List.all_eq_true.mp h d hd)

/-- **The bounds of a step can be checked by evaluation.** -/
theorem stepBounds_of {lr : IxAICore.Fx} {m : IxAICore.Model}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)} (h : stepBoundsB lr m batch = true) :
    StepBounds lr m batch := by
  simp only [stepBoundsB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun p hp => deltaBounds_of (h1 p hp), fun d hd => rowBounds_of (h2 d hd),
    biasBounds_of h3, fun d hd => rowBounds_of (h4 d hd), biasBounds_of h5⟩

/-! ## Field operations on encoded numbers -/

theorem add_fx {a b : IxAICore.Fx} {c : SourceValue F}
    (h : evalBinOp .add (fxVal a) (fxVal b) = .ok c) : c = fxVal (IxAICore.Fx.add a b) := by
  rw [add_ff h]
  simp only [fxVal, IxAICore.Fx.add, Int.cast_add]

theorem sub_fx {a b : IxAICore.Fx} {c : SourceValue F}
    (h : evalBinOp .sub (fxVal a) (fxVal b) = .ok c) : c = fxVal (IxAICore.Fx.sub a b) := by
  rw [sub_ff h]
  simp only [fxVal, IxAICore.Fx.sub, Int.cast_sub]

/-- A `0`/`1` flag times an encoded number selects it. -/
theorem mul_pos_fx {z g : IxAICore.Fx} {c : SourceValue F}
    (h : evalBinOp .mul (.field (if IxAICore.Fx.pos z then 1 else 0) : SourceValue F) (fxVal g) =
      .ok c) :
    c = fxVal (if IxAICore.Fx.pos z then g else IxAICore.Fx.zero) := by
  rw [mul_ff h]
  by_cases hp : IxAICore.Fx.pos z = true
  · rw [if_pos hp, if_pos hp, one_mul]
    rfl
  · rw [if_neg hp, if_neg hp, zero_mul]
    simp [fxVal, IxAICore.Fx.zero]

/-! ## Lists -/

theorem length_transposeN (n : ℕ) (rows : List (List IxAICore.Fx)) :
    (IxAICore.transposeN n rows).length = n := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    show (IxAICore.transposeN n (rows.map (·.tail))).length + 1 = n + 1
    rw [ih]

/-- Every column of `transposeN n rows` has one entry per row. -/
theorem col_length_transposeN (n : ℕ) (rows : List (List IxAICore.Fx)) :
    ∀ c ∈ IxAICore.transposeN n rows, c.length = rows.length := by
  induction n generalizing rows with
  | zero =>
    intro c hc
    first | cases hc | simp [IxAICore.transposeN] at hc
  | succ n ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.length_map _
    · exact (ih _ c hc).trans (List.length_map _)

theorem getD_tail (r : List IxAICore.Fx) (j : ℕ) :
    r.tail.getD j IxAICore.Fx.zero = r.getD (j + 1) IxAICore.Fx.zero := by
  cases r <;> simp

theorem getD_zero (r : List IxAICore.Fx) :
    r.getD 0 IxAICore.Fx.zero = r.headD IxAICore.Fx.zero := by
  cases r <;> simp

/-- **`transposeN` by columns**: column `j < n` holds entry `j` of every row, or zero where a
row is shorter. -/
theorem transposeN_eq_cols (n : ℕ) (rows : List (List IxAICore.Fx)) :
    IxAICore.transposeN n rows =
      (List.range n).map fun j => rows.map fun r => r.getD j IxAICore.Fx.zero := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show rows.map (·.headD IxAICore.Fx.zero) :: IxAICore.transposeN n (rows.map (·.tail)) = _
    rw [ih]
    congr 1
    · exact List.map_congr_left (fun r _ => (getD_zero r).symm)
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp, List.map_map]
      exact List.map_congr_left (fun r _ => getD_tail r j)

/-- A successful projection of an encoded vector is the vector's entry. -/
theorem proj_encVec {row : List IxAICore.Fx} {j : ℕ} {v : SourceValue F}
    (h : projectValue (encVec row) j = .ok v) : v = fxVal (row.getD j IxAICore.Fx.zero) := by
  have h1 := proj_ok (items := row.map fxVal) h
  rw [List.getElem?_map] at h1
  cases hj : row[j]? with
  | none => rw [hj] at h1; simp at h1
  | some a =>
    rw [hj] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    rw [← h1, List.getD_eq_getElem?_getD, hj, Option.getD_some]

theorem deltasOf_x (m : IxAICore.Model) (w2T : List (List IxAICore.Fx))
    (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    (deltasOf m w2T batch).map (·.x) = batch.map (·.1) := by
  induction batch with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨x, t⟩ := p
    show x :: (deltasOf m w2T ps).map (·.x) = x :: ps.map (·.1)
    rw [ih]

/-! ## One entry -/

/- Consumes `«Fixed::hidden_unit».Path.run`: 3 binders (`x1` … `cs12`), then the facts
   ev14 : ObsFn W "Fixed::dot8" [x_row, x_x] h x1 m3 cs12
   he32 : h' = m3  (unused)
   op8 : evalBinOp .add (x1 : SourceValue F) (x_b : SourceValue F) = .ok r
   hc33 : calls = ...  (unused) -/
/-- **`Fixed::hidden_unit` is `Fx.add (Fx.dot row x) b`.** -/
theorem hidden_unit_spec {row x : List IxAICore.Fx} {b : IxAICore.Fx} (hr : row.length = 8)
    (hv : x.length = 8) (hb : Small (IxAICore.Fx.dotRaw row x)) {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::hidden_unit" [encVec row, fxVal b, encVec x] h r h' calls) :
    r = fxVal (IxAICore.Fx.add (IxAICore.Fx.dot row x) b) := by
  obtain ⟨x1, m3, cs12, ev14, -, op8, -⟩ :=
    «Fixed::hidden_unit».obs ev
  obtain rfl := dot8_spec hr hv hb ev14
  exact add_fx op8

/- Consumes `«Fixed::output_unit».Path.run`: 3 binders (`x1` … `cs12`), then the facts
   ev14 : ObsFn W "Fixed::dot16" [x_row, x_h] h x1 m3 cs12
   he32 : h' = m3  (unused)
   op8 : evalBinOp .add (x1 : SourceValue F) (x_b : SourceValue F) = .ok r
   hc33 : calls = ...  (unused) -/
/-- **`Fixed::output_unit` is `Fx.add (Fx.dot row hs) b`.** -/
theorem output_unit_spec {row hs : List IxAICore.Fx} {b : IxAICore.Fx} (hr : row.length = 16)
    (hv : hs.length = 16) (hb : Small (IxAICore.Fx.dotRaw row hs)) {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::output_unit" [encVec row, fxVal b, encVec hs] h r h' calls) :
    r = fxVal (IxAICore.Fx.add (IxAICore.Fx.dot row hs) b) := by
  obtain ⟨x1, m3, cs12, ev14, -, op8, -⟩ :=
    «Fixed::output_unit».obs ev
  obtain rfl := dot16_spec hr hv hb ev14
  exact add_fx op8

/- Consumes `«Fixed::back_unit».Path.run`: 5 binders (`x1` … `cs26`), then the facts
   ev14 : ObsFn W "Fixed::pos" [x_z] h x1 m3 cs12
   ev28 : ObsFn W "Fixed::dot11" [x_col, x_dout] m3 y2 h' cs26
   op8 : evalBinOp .mul (x1 : SourceValue F) (y2 : SourceValue F) = .ok r
   hc45 : calls = ...  (unused) -/
/-- **`Fixed::back_unit` is one entry of `dz`**: `Fx.dot col dout` where `Fx.pos z`, else
zero. The dot product is computed either way, so its bound is needed either way. -/
theorem back_unit_spec {z : IxAICore.Fx} {col dout : List IxAICore.Fx} (hz : Small z.raw)
    (hcol : col.length = 11) (hd : dout.length = 11) (hb : Small (IxAICore.Fx.dotRaw col dout))
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::back_unit" [fxVal z, encVec col, encVec dout] h r h' calls) :
    r = fxVal (if IxAICore.Fx.pos z then IxAICore.Fx.dot col dout else IxAICore.Fx.zero) := by
  obtain ⟨x1, y2, m3, cs12, cs26, ev14, ev28, op8, -⟩ :=
    «Fixed::back_unit».obs ev
  obtain rfl := pos_spec hz ev14
  obtain rfl := dot11_spec hcol hd hb ev28
  exact mul_pos_fx op8

/- Consumes `«Fixed::upd».Path.run`: 5 binders (`cs4` … `cs26`), then the facts
   ev28 : ObsFn W "Fixed::mul" [x_lr, x_g] h y15 m9 cs26
   op21 : evalBinOp .sub (x_w : SourceValue F) (y15 : SourceValue F) = .ok v7
   ev6 : ObsFn W "Fixed::bound" [v7] m9 r h' cs4
   hc45 : calls = ...  (unused) -/
/-- **`Fixed::upd` is the SGD update** `Fx.sub w (Fx.mul lr g)` (`upd` in `Model.step`), **and
the result is below `2^13`**: `Fixed::bound` admits only the images of `[-4096, 4320)`, and for
`|w| < 2^13` the exact update is far below the characteristic, so it is one of them. -/
theorem upd_spec {w lr g : IxAICore.Fx} (hw : SmallW w.raw) (hb : Small (lr.raw * g.raw))
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::upd" [fxVal w, fxVal lr, fxVal g] h r h' calls) :
    r = fxVal (IxAICore.Fx.sub w (IxAICore.Fx.mul lr g)) ∧
      SmallW (IxAICore.Fx.sub w (IxAICore.Fx.mul lr g)).raw := by
  obtain ⟨cs4, v7, m9, y15, cs26, ev28, op21, ev6, -⟩ :=
    «Fixed::upd».obs ev
  obtain rfl := mul_spec hb ev28
  obtain rfl := sub_fx op21
  obtain ⟨rfl, k, hk1, hk2, hx⟩ := bound_spec ev6
  refine ⟨rfl, ?_⟩
  have e : (IxAICore.Fx.sub w (IxAICore.Fx.mul lr g)).raw = w.raw - lr.raw * g.raw / 256 := by
    simp only [IxAICore.Fx.sub, IxAICore.Fx.mul, shr8_eq]
  rw [e] at hx ⊢
  obtain ⟨hw1, hw2⟩ := abs_lt.mp hw
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  norm_num at hw1 hw2 hb1 hb2
  generalize lr.raw * g.raw = P at *
  have hk := int_eq_of_cast_eq (a := w.raw - P / 256) (b := k)
    (abs_lt.mpr ⟨by omega, by omega⟩) hx
  show |w.raw - P / 256| < 2 ^ 13
  rw [hk, abs_lt]
  constructor <;> norm_num <;> omega

/-! ## Forward pass -/

/- Consumes `«Fixed::hidden».Path.run`: 128 binders (`x_r0` … `cs1267`), then the facts
   hv11 : x_w1 = (.tuple [x_r0, x_r1, …, x_r15])
   hv103 : x_b1 = (.tuple [x_c0, x_c1, …, x_c15])
   ev198 : ObsFn W "Fixed::hidden_unit" [x_r0, x_c0, x_x] h v185 m186 cs196
   ev236 : ObsFn W "Fixed::hidden_unit" [x_r1, x_c1, x_x] m186 v223 m224 cs234
   ev274 : ObsFn W "Fixed::hidden_unit" [x_r2, x_c2, x_x] m224 v261 m262 cs272
   ev312 : ObsFn W "Fixed::hidden_unit" [x_r3, x_c3, x_x] m262 v299 m300 cs310
   ev350 : ObsFn W "Fixed::hidden_unit" [x_r4, x_c4, x_x] m300 v337 m338 cs348
   ev388 : ObsFn W "Fixed::hidden_unit" [x_r5, x_c5, x_x] m338 v375 m376 cs386
   ev426 : ObsFn W "Fixed::hidden_unit" [x_r6, x_c6, x_x] m376 v413 m414 cs424
   ev464 : ObsFn W "Fixed::hidden_unit" [x_r7, x_c7, x_x] m414 v451 m452 cs462
   ev502 : ObsFn W "Fixed::hidden_unit" [x_r8, x_c8, x_x] m452 v489 m490 cs500
   ev540 : ObsFn W "Fixed::hidden_unit" [x_r9, x_c9, x_x] m490 v527 m528 cs538
   ev578 : ObsFn W "Fixed::hidden_unit" [x_r10, x_c10, x_x] m528 v565 m566 cs576
   ev616 : ObsFn W "Fixed::hidden_unit" [x_r11, x_c11, x_x] m566 v603 m604 cs614
   ev654 : ObsFn W "Fixed::hidden_unit" [x_r12, x_c12, x_x] m604 v641 m642 cs652
   ev692 : ObsFn W "Fixed::hidden_unit" [x_r13, x_c13, x_x] m642 v679 m680 cs690
   ev730 : ObsFn W "Fixed::hidden_unit" [x_r14, x_c14, x_x] m680 v717 m718 cs728
   ev768 : ObsFn W "Fixed::hidden_unit" [x_r15, x_c15, x_x] m718 v755 m756 cs766
   he797 : r = (.tuple [(.tuple [v185, v223, …, v755]), (.tuple [v942, v943, …, v957])])
   ev969 : ObsFn W "Fixed::relu" [v185] m756 v942 m959 cs967
   ev989 : ObsFn W "Fixed::relu" [v223] m959 v943 m979 cs987
   ev1009 : ObsFn W "Fixed::relu" [v261] m979 v944 m999 cs1007
   ev1029 : ObsFn W "Fixed::relu" [v299] m999 v945 m1019 cs1027
   ev1049 : ObsFn W "Fixed::relu" [v337] m1019 v946 m1039 cs1047
   ev1069 : ObsFn W "Fixed::relu" [v375] m1039 v947 m1059 cs1067
   ev1089 : ObsFn W "Fixed::relu" [v413] m1059 v948 m1079 cs1087
   ev1109 : ObsFn W "Fixed::relu" [v451] m1079 v949 m1099 cs1107
   ev1129 : ObsFn W "Fixed::relu" [v489] m1099 v950 m1119 cs1127
   ev1149 : ObsFn W "Fixed::relu" [v527] m1119 v951 m1139 cs1147
   ev1169 : ObsFn W "Fixed::relu" [v565] m1139 v952 m1159 cs1167
   ev1189 : ObsFn W "Fixed::relu" [v603] m1159 v953 m1179 cs1187
   ev1209 : ObsFn W "Fixed::relu" [v641] m1179 v954 m1199 cs1207
   ev1229 : ObsFn W "Fixed::relu" [v679] m1199 v955 m1219 cs1227
   ev1249 : ObsFn W "Fixed::relu" [v717] m1219 v956 m1239 cs1247
   ev1269 : ObsFn W "Fixed::relu" [v755] m1239 v957 m1259 cs1267
   he1278 : h' = m1259  (unused)
   hc1279 : calls = ...  (unused) -/
/-- **`Fixed::hidden` is `Model.hidden`** on lists: the pre-activations and their `relu`. -/
theorem hidden_core {w1 : List (List IxAICore.Fx)} {b1 x : List IxAICore.Fx}
    (hw : w1.length = 16) (hrows : ∀ row ∈ w1, row.length = 8) (hb : b1.length = 16)
    (hx : x.length = 8) (hdot : ∀ row ∈ w1, Small (IxAICore.Fx.dotRaw row x))
    (hz : ∀ z ∈ hiddenZ w1 b1 x, Small z.raw) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::hidden" [encMat w1, encVec b1, encVec x] h r h' calls) :
    r = .tuple [encVec (hiddenZ w1 b1 x), encVec ((hiddenZ w1 b1 x).map IxAICore.Fx.relu)] := by
  obtain ⟨w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15,
      rfl⟩ := list_eq16 hw
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15,
      rfl⟩ := list_eq16 hb
  have hz' : ∀ z ∈ [IxAICore.Fx.add (IxAICore.Fx.dot w_0 x) b_0,
      IxAICore.Fx.add (IxAICore.Fx.dot w_1 x) b_1, IxAICore.Fx.add (IxAICore.Fx.dot w_2 x) b_2,
      IxAICore.Fx.add (IxAICore.Fx.dot w_3 x) b_3, IxAICore.Fx.add (IxAICore.Fx.dot w_4 x) b_4,
      IxAICore.Fx.add (IxAICore.Fx.dot w_5 x) b_5, IxAICore.Fx.add (IxAICore.Fx.dot w_6 x) b_6,
      IxAICore.Fx.add (IxAICore.Fx.dot w_7 x) b_7, IxAICore.Fx.add (IxAICore.Fx.dot w_8 x) b_8,
      IxAICore.Fx.add (IxAICore.Fx.dot w_9 x) b_9, IxAICore.Fx.add (IxAICore.Fx.dot w_10 x) b_10,
      IxAICore.Fx.add (IxAICore.Fx.dot w_11 x) b_11, IxAICore.Fx.add (IxAICore.Fx.dot w_12 x) b_12,
      IxAICore.Fx.add (IxAICore.Fx.dot w_13 x) b_13, IxAICore.Fx.add (IxAICore.Fx.dot w_14 x) b_14,
      IxAICore.Fx.add (IxAICore.Fx.dot w_15 x) b_15],
      Small z.raw := hz
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13,
      x_r14, x_r15, x_c0, x_c1, x_c2, x_c3, x_c4, x_c5, x_c6, x_c7, x_c8, x_c9, x_c10, x_c11, x_c12,
      x_c13, x_c14, x_c15, v185, m186, cs196, v223, m224, cs234, v261, m262, cs272, v299, m300,
      cs310, v337, m338, cs348, v375, m376, cs386, v413, m414, cs424, v451, m452, cs462, v489, m490,
      cs500, v527, m528, cs538, v565, m566, cs576, v603, m604, cs614, v641, m642, cs652, v679, m680,
      cs690, v717, m718, cs728, v755, m756, cs766, v942, v943, v944, v945, v946, v947, v948, v949,
      v950, v951, v952, v953, v954, v955, v956, v957, m959, cs967, m979, cs987, m999, cs1007, m1019,
      cs1027, m1039, cs1047, m1059, cs1067, m1079, cs1087, m1099, cs1107, m1119, cs1127, m1139,
      cs1147, m1159, cs1167, m1179, cs1187, m1199, cs1207, m1219, cs1227, m1239, cs1247, m1259,
      cs1267, hv11, hv103, ev198, ev236, ev274, ev312, ev350, ev388, ev426, ev464, ev502, ev540,
      ev578, ev616, ev654, ev692, ev730, ev768, he797, ev969, ev989, ev1009, ev1029, ev1049, ev1069,
      ev1089, ev1109, ev1129, ev1149, ev1169, ev1189, ev1209, ev1229, ev1249, ev1269, -, -⟩ :=
    «Fixed::hidden».obs ev
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv103
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv103
  obtain rfl := hidden_unit_spec (hrows w_0 (by simp)) hx (hdot w_0 (by simp)) ev198
  obtain rfl := hidden_unit_spec (hrows w_1 (by simp)) hx (hdot w_1 (by simp)) ev236
  obtain rfl := hidden_unit_spec (hrows w_2 (by simp)) hx (hdot w_2 (by simp)) ev274
  obtain rfl := hidden_unit_spec (hrows w_3 (by simp)) hx (hdot w_3 (by simp)) ev312
  obtain rfl := hidden_unit_spec (hrows w_4 (by simp)) hx (hdot w_4 (by simp)) ev350
  obtain rfl := hidden_unit_spec (hrows w_5 (by simp)) hx (hdot w_5 (by simp)) ev388
  obtain rfl := hidden_unit_spec (hrows w_6 (by simp)) hx (hdot w_6 (by simp)) ev426
  obtain rfl := hidden_unit_spec (hrows w_7 (by simp)) hx (hdot w_7 (by simp)) ev464
  obtain rfl := hidden_unit_spec (hrows w_8 (by simp)) hx (hdot w_8 (by simp)) ev502
  obtain rfl := hidden_unit_spec (hrows w_9 (by simp)) hx (hdot w_9 (by simp)) ev540
  obtain rfl := hidden_unit_spec (hrows w_10 (by simp)) hx (hdot w_10 (by simp)) ev578
  obtain rfl := hidden_unit_spec (hrows w_11 (by simp)) hx (hdot w_11 (by simp)) ev616
  obtain rfl := hidden_unit_spec (hrows w_12 (by simp)) hx (hdot w_12 (by simp)) ev654
  obtain rfl := hidden_unit_spec (hrows w_13 (by simp)) hx (hdot w_13 (by simp)) ev692
  obtain rfl := hidden_unit_spec (hrows w_14 (by simp)) hx (hdot w_14 (by simp)) ev730
  obtain rfl := hidden_unit_spec (hrows w_15 (by simp)) hx (hdot w_15 (by simp)) ev768
  obtain rfl := relu_spec (hz' _ (by simp)) ev969
  obtain rfl := relu_spec (hz' _ (by simp)) ev989
  obtain rfl := relu_spec (hz' _ (by simp)) ev1009
  obtain rfl := relu_spec (hz' _ (by simp)) ev1029
  obtain rfl := relu_spec (hz' _ (by simp)) ev1049
  obtain rfl := relu_spec (hz' _ (by simp)) ev1069
  obtain rfl := relu_spec (hz' _ (by simp)) ev1089
  obtain rfl := relu_spec (hz' _ (by simp)) ev1109
  obtain rfl := relu_spec (hz' _ (by simp)) ev1129
  obtain rfl := relu_spec (hz' _ (by simp)) ev1149
  obtain rfl := relu_spec (hz' _ (by simp)) ev1169
  obtain rfl := relu_spec (hz' _ (by simp)) ev1189
  obtain rfl := relu_spec (hz' _ (by simp)) ev1209
  obtain rfl := relu_spec (hz' _ (by simp)) ev1229
  obtain rfl := relu_spec (hz' _ (by simp)) ev1249
  obtain rfl := relu_spec (hz' _ (by simp)) ev1269
  subst he797
  rfl

/-- **`Fixed::hidden` returns `Model.hidden m x`**, both components, as the function returns
them. -/
theorem hidden_spec {m : IxAICore.Model} {x : List IxAICore.Fx} (hw : m.w1.length = 16)
    (hrows : ∀ row ∈ m.w1, row.length = 8) (hb : m.b1.length = 16) (hx : x.length = 8)
    (hdot : ∀ row ∈ m.w1, Small (IxAICore.Fx.dotRaw row x))
    (hz : ∀ z ∈ (m.hidden x).1, Small z.raw) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::hidden" [encMat m.w1, encVec m.b1, encVec x] h r h' calls) :
    r = .tuple [encVec (m.hidden x).1, encVec (m.hidden x).2] := by
  rw [hidden_eq]
  exact hidden_core hw hrows hb hx hdot hz ev

/- Consumes `«Fixed::outputs».Path.run`: 55 binders (`x_r0` … `cs518`), then the facts
   hv11 : x_w2 = (.tuple [x_r0, x_r1, …, x_r10])
   hv78 : x_b2 = (.tuple [x_c0, x_c1, …, x_c10])
   he148 : r = (.tuple [v137, v138, …, v147])
   ev160 : ObsFn W "Fixed::output_unit" [x_r0, x_c0, x_h] h v137 m150 cs158
   ev196 : ObsFn W "Fixed::output_unit" [x_r1, x_c1, x_h] m150 v138 m186 cs194
   ev232 : ObsFn W "Fixed::output_unit" [x_r2, x_c2, x_h] m186 v139 m222 cs230
   ev268 : ObsFn W "Fixed::output_unit" [x_r3, x_c3, x_h] m222 v140 m258 cs266
   ev304 : ObsFn W "Fixed::output_unit" [x_r4, x_c4, x_h] m258 v141 m294 cs302
   ev340 : ObsFn W "Fixed::output_unit" [x_r5, x_c5, x_h] m294 v142 m330 cs338
   ev376 : ObsFn W "Fixed::output_unit" [x_r6, x_c6, x_h] m330 v143 m366 cs374
   ev412 : ObsFn W "Fixed::output_unit" [x_r7, x_c7, x_h] m366 v144 m402 cs410
   ev448 : ObsFn W "Fixed::output_unit" [x_r8, x_c8, x_h] m402 v145 m438 cs446
   ev484 : ObsFn W "Fixed::output_unit" [x_r9, x_c9, x_h] m438 v146 m474 cs482
   ev520 : ObsFn W "Fixed::output_unit" [x_r10, x_c10, x_h] m474 v147 m510 cs518
   he545 : h' = m510  (unused)
   hc546 : calls = ...  (unused) -/
/-- **`Fixed::outputs` is the output layer** from the hidden activations `hs`: `o` in
`Model.delta`, `Model.outputs` once `hs` is `(Model.hidden m x).2`. -/
theorem outputs_spec {w2 : List (List IxAICore.Fx)} {b2 hs : List IxAICore.Fx}
    (hw : w2.length = 11) (hrows : ∀ row ∈ w2, row.length = 16) (hb : b2.length = 11)
    (hh : hs.length = 16) (hdot : ∀ row ∈ w2, Small (IxAICore.Fx.dotRaw row hs))
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::outputs" [encMat w2, encVec b2, encVec hs] h r h' calls) :
    r = encVec (outputsOf w2 b2 hs) := by
  obtain ⟨w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, w_8, w_9, w_10, rfl⟩ := list_eq11 hw
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, rfl⟩ := list_eq11 hb
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_c0, x_c1, x_c2, x_c3,
      x_c4, x_c5, x_c6, x_c7, x_c8, x_c9, x_c10, v137, v138, v139, v140, v141, v142, v143, v144,
      v145, v146, v147, m150, cs158, m186, cs194, m222, cs230, m258, cs266, m294, cs302, m330,
      cs338, m366, cs374, m402, cs410, m438, cs446, m474, cs482, m510, cs518, hv11, hv78, he148,
      ev160, ev196, ev232, ev268, ev304, ev340, ev376, ev412, ev448, ev484, ev520, -, -⟩ :=
    «Fixed::outputs».obs ev
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv78
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv78
  obtain rfl := output_unit_spec (hrows w_0 (by simp)) hh (hdot w_0 (by simp)) ev160
  obtain rfl := output_unit_spec (hrows w_1 (by simp)) hh (hdot w_1 (by simp)) ev196
  obtain rfl := output_unit_spec (hrows w_2 (by simp)) hh (hdot w_2 (by simp)) ev232
  obtain rfl := output_unit_spec (hrows w_3 (by simp)) hh (hdot w_3 (by simp)) ev268
  obtain rfl := output_unit_spec (hrows w_4 (by simp)) hh (hdot w_4 (by simp)) ev304
  obtain rfl := output_unit_spec (hrows w_5 (by simp)) hh (hdot w_5 (by simp)) ev340
  obtain rfl := output_unit_spec (hrows w_6 (by simp)) hh (hdot w_6 (by simp)) ev376
  obtain rfl := output_unit_spec (hrows w_7 (by simp)) hh (hdot w_7 (by simp)) ev412
  obtain rfl := output_unit_spec (hrows w_8 (by simp)) hh (hdot w_8 (by simp)) ev448
  obtain rfl := output_unit_spec (hrows w_9 (by simp)) hh (hdot w_9 (by simp)) ev484
  obtain rfl := output_unit_spec (hrows w_10 (by simp)) hh (hdot w_10 (by simp)) ev520
  subst he148
  rfl

/- Consumes `«Fixed::sub11».Path.run`: 33 binders (`x_a0` … `v147`), then the facts
   hv11 : x_a = (.tuple [x_a0, x_a1, …, x_a10])
   hv78 : x_b = (.tuple [x_b0, x_b1, …, x_b10])
   he148 : r = (.tuple [v137, v138, …, v147])
   op162 : evalBinOp .sub (x_a0 : SourceValue F) (x_b0 : SourceValue F) = .ok v137
   op178 : evalBinOp .sub (x_a1 : SourceValue F) (x_b1 : SourceValue F) = .ok v138
   op194 : evalBinOp .sub (x_a2 : SourceValue F) (x_b2 : SourceValue F) = .ok v139
   op210 : evalBinOp .sub (x_a3 : SourceValue F) (x_b3 : SourceValue F) = .ok v140
   op226 : evalBinOp .sub (x_a4 : SourceValue F) (x_b4 : SourceValue F) = .ok v141
   op242 : evalBinOp .sub (x_a5 : SourceValue F) (x_b5 : SourceValue F) = .ok v142
   op258 : evalBinOp .sub (x_a6 : SourceValue F) (x_b6 : SourceValue F) = .ok v143
   op274 : evalBinOp .sub (x_a7 : SourceValue F) (x_b7 : SourceValue F) = .ok v144
   op290 : evalBinOp .sub (x_a8 : SourceValue F) (x_b8 : SourceValue F) = .ok v145
   op306 : evalBinOp .sub (x_a9 : SourceValue F) (x_b9 : SourceValue F) = .ok v146
   op322 : evalBinOp .sub (x_a10 : SourceValue F) (x_b10 : SourceValue F) = .ok v147
   he325 : h' = h  (unused)
   hc326 : calls = ...  (unused) -/
/-- **`Fixed::sub11` is `List.zipWith Fx.sub`** (`dout` from `o` and `t`). -/
theorem sub11_spec {a b : List IxAICore.Fx} (ha : a.length = 11) (hb : b.length = 11)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::sub11" [encVec a, encVec b] h r h' calls) :
    r = encVec (List.zipWith IxAICore.Fx.sub a b) := by
  obtain ⟨a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, rfl⟩ := list_eq11 ha
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, rfl⟩ := list_eq11 hb
  obtain ⟨x_a0, x_a1, x_a2, x_a3, x_a4, x_a5, x_a6, x_a7, x_a8, x_a9, x_a10, x_b0, x_b1, x_b2, x_b3,
      x_b4, x_b5, x_b6, x_b7, x_b8, x_b9, x_b10, v137, v138, v139, v140, v141, v142, v143, v144,
      v145, v146, v147, hv11, hv78, he148, op162, op178, op194, op210, op226, op242, op258, op274,
      op290, op306, op322, -, -⟩ :=
    «Fixed::sub11».obs ev
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv78
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv78
  obtain rfl := sub_fx op162
  obtain rfl := sub_fx op178
  obtain rfl := sub_fx op194
  obtain rfl := sub_fx op210
  obtain rfl := sub_fx op226
  obtain rfl := sub_fx op242
  obtain rfl := sub_fx op258
  obtain rfl := sub_fx op274
  obtain rfl := sub_fx op290
  obtain rfl := sub_fx op306
  obtain rfl := sub_fx op322
  subst he148
  rfl

/-! ## Backward pass -/

/- Consumes `«Fixed::delta».Path.run`: 89 binders (`m2` … `cs881`), then the facts
   ev14 : ObsFn W "Fixed::hidden" [x_w1, x_b1, x_x] h (.tuple [(.tuple [x_z0, x_z1, …, x_z15]),…
   ev79 : ObsFn W "Fixed::outputs" [x_w2, x_b2, x_h] m2 v66 m69 cs77
   ev65 : ObsFn W "Fixed::sub11" [v66, x_t] m69 v52 m53 cs63
   hv213 : x_w2t = (.tuple [x_c0, x_c1, …, x_c15])
   he300 : r = (.tuple [x_h, (.tuple [v316, v317, …, v331]), v52])
   ev343 : ObsFn W "Fixed::back_unit" [x_z0, x_c0, v52] m53 v316 m333 cs341
   ev379 : ObsFn W "Fixed::back_unit" [x_z1, x_c1, v52] m333 v317 m369 cs377
   ev415 : ObsFn W "Fixed::back_unit" [x_z2, x_c2, v52] m369 v318 m405 cs413
   ev451 : ObsFn W "Fixed::back_unit" [x_z3, x_c3, v52] m405 v319 m441 cs449
   ev487 : ObsFn W "Fixed::back_unit" [x_z4, x_c4, v52] m441 v320 m477 cs485
   ev523 : ObsFn W "Fixed::back_unit" [x_z5, x_c5, v52] m477 v321 m513 cs521
   ev559 : ObsFn W "Fixed::back_unit" [x_z6, x_c6, v52] m513 v322 m549 cs557
   ev595 : ObsFn W "Fixed::back_unit" [x_z7, x_c7, v52] m549 v323 m585 cs593
   ev631 : ObsFn W "Fixed::back_unit" [x_z8, x_c8, v52] m585 v324 m621 cs629
   ev667 : ObsFn W "Fixed::back_unit" [x_z9, x_c9, v52] m621 v325 m657 cs665
   ev703 : ObsFn W "Fixed::back_unit" [x_z10, x_c10, v52] m657 v326 m693 cs701
   ev739 : ObsFn W "Fixed::back_unit" [x_z11, x_c11, v52] m693 v327 m729 cs737
   ev775 : ObsFn W "Fixed::back_unit" [x_z12, x_c12, v52] m729 v328 m765 cs773
   ev811 : ObsFn W "Fixed::back_unit" [x_z13, x_c13, v52] m765 v329 m801 cs809
   ev847 : ObsFn W "Fixed::back_unit" [x_z14, x_c14, v52] m801 v330 m837 cs845
   ev883 : ObsFn W "Fixed::back_unit" [x_z15, x_c15, v52] m837 v331 m873 cs881
   he915 : h' = m873  (unused)
   hc916 : calls = ...  (unused) -/
/-- **`Fixed::delta` is `Model.delta`** on lists, as the triple `(h, dz, dout)`. -/
theorem delta_core {w1 w2 w2T : List (List IxAICore.Fx)} {b1 b2 x t : List IxAICore.Fx}
    (hw1 : w1.length = 16) (hw1r : ∀ row ∈ w1, row.length = 8) (hb1 : b1.length = 16)
    (hw2 : w2.length = 11) (hw2r : ∀ row ∈ w2, row.length = 16) (hb2 : b2.length = 11)
    (hT : w2T.length = 16) (hTr : ∀ c ∈ w2T, c.length = 11) (hx : x.length = 8)
    (ht : t.length = 11) (hb : DeltaBounds (IxAICore.Model.mk w1 b1 w2 b2) w2T x t)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::delta"
      [encMat w1, encVec b1, encMat w2, encVec b2, encMat w2T, encVec x, encVec t] h r h' calls) :
    r = .tuple [encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).h,
      encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).dz,
      encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).dout] := by
  have hdot1 := hb.dot1
  have hz := hb.pre
  have hdot2 := hb.dot2
  have hdot3 := hb.dot3
  obtain ⟨w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15,
      rfl⟩ := list_eq16 hw1
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15,
      rfl⟩ := list_eq16 hb1
  obtain ⟨k_0, k_1, k_2, k_3, k_4, k_5, k_6, k_7, k_8, k_9, k_10, k_11, k_12, k_13, k_14, k_15,
      rfl⟩ := list_eq16 hT
  have hzL : hiddenZ [w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7,
       w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15]
      [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7,
       b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15] x =
      [IxAICore.Fx.add (IxAICore.Fx.dot w_0 x) b_0, IxAICore.Fx.add (IxAICore.Fx.dot w_1 x) b_1,
      IxAICore.Fx.add (IxAICore.Fx.dot w_2 x) b_2, IxAICore.Fx.add (IxAICore.Fx.dot w_3 x) b_3,
      IxAICore.Fx.add (IxAICore.Fx.dot w_4 x) b_4, IxAICore.Fx.add (IxAICore.Fx.dot w_5 x) b_5,
      IxAICore.Fx.add (IxAICore.Fx.dot w_6 x) b_6, IxAICore.Fx.add (IxAICore.Fx.dot w_7 x) b_7,
      IxAICore.Fx.add (IxAICore.Fx.dot w_8 x) b_8, IxAICore.Fx.add (IxAICore.Fx.dot w_9 x) b_9,
      IxAICore.Fx.add (IxAICore.Fx.dot w_10 x) b_10, IxAICore.Fx.add (IxAICore.Fx.dot w_11 x) b_11,
      IxAICore.Fx.add (IxAICore.Fx.dot w_12 x) b_12, IxAICore.Fx.add (IxAICore.Fx.dot w_13 x) b_13,
      IxAICore.Fx.add (IxAICore.Fx.dot w_14 x) b_14,
      IxAICore.Fx.add (IxAICore.Fx.dot w_15 x) b_15] := rfl
  have hz' : ∀ z ∈ [IxAICore.Fx.add (IxAICore.Fx.dot w_0 x) b_0,
      IxAICore.Fx.add (IxAICore.Fx.dot w_1 x) b_1, IxAICore.Fx.add (IxAICore.Fx.dot w_2 x) b_2,
      IxAICore.Fx.add (IxAICore.Fx.dot w_3 x) b_3, IxAICore.Fx.add (IxAICore.Fx.dot w_4 x) b_4,
      IxAICore.Fx.add (IxAICore.Fx.dot w_5 x) b_5, IxAICore.Fx.add (IxAICore.Fx.dot w_6 x) b_6,
      IxAICore.Fx.add (IxAICore.Fx.dot w_7 x) b_7, IxAICore.Fx.add (IxAICore.Fx.dot w_8 x) b_8,
      IxAICore.Fx.add (IxAICore.Fx.dot w_9 x) b_9, IxAICore.Fx.add (IxAICore.Fx.dot w_10 x) b_10,
      IxAICore.Fx.add (IxAICore.Fx.dot w_11 x) b_11, IxAICore.Fx.add (IxAICore.Fx.dot w_12 x) b_12,
      IxAICore.Fx.add (IxAICore.Fx.dot w_13 x) b_13, IxAICore.Fx.add (IxAICore.Fx.dot w_14 x) b_14,
      IxAICore.Fx.add (IxAICore.Fx.dot w_15 x) b_15],
      Small z.raw := hz
  have hhl : ((hiddenZ [w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7,
       w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15]
      [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7,
       b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15] x).map IxAICore.Fx.relu).length = 16 := by
    first | rfl | simp [hiddenZ]
  have hdl : (List.zipWith IxAICore.Fx.sub (outputsOf w2 b2 ((hiddenZ [w_0, w_1, w_2, w_3, w_4,
      w_5, w_6, w_7,
       w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15]
      [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7,
       b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15] x).map IxAICore.Fx.relu)) t).length = 11 := by
    simp [outputsOf, hw2, hb2, ht]
  obtain ⟨m2, cs12, x_h, v52, m53, cs63, v66, m69, cs77, x_z0, x_z1, x_z2, x_z3, x_z4, x_z5, x_z6,
      x_z7, x_z8, x_z9, x_z10, x_z11, x_z12, x_z13, x_z14, x_z15, x_c0, x_c1, x_c2, x_c3, x_c4,
      x_c5, x_c6, x_c7, x_c8, x_c9, x_c10, x_c11, x_c12, x_c13, x_c14, x_c15, v316, v317, v318,
      v319, v320, v321, v322, v323, v324, v325, v326, v327, v328, v329, v330, v331, m333, cs341,
      m369, cs377, m405, cs413, m441, cs449, m477, cs485, m513, cs521, m549, cs557, m585, cs593,
      m621, cs629, m657, cs665, m693, cs701, m729, cs737, m765, cs773, m801, cs809, m837, cs845,
      m873, cs881, ev14, ev79, ev65, hv213, he300, ev343, ev379, ev415, ev451, ev487, ev523, ev559,
      ev595, ev631, ev667, ev703, ev739, ev775, ev811, ev847, ev883, -, -⟩ :=
    «Fixed::delta».obs ev
  have e := hidden_core (w1 := [w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7,
       w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15])
    (b1 := [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7,
       b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15])
    (by first | rfl | simp) hw1r (by first | rfl | simp) hx hdot1 hz ev14
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e
  obtain ⟨ez, rfl⟩ := e
  rw [hzL] at ez
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at ez
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ez
  obtain rfl := outputs_spec hw2 hw2r hb2 hhl hdot2 ev79
  obtain rfl := sub11_spec (by simp [outputsOf, hw2, hb2]) ht ev65
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv213
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv213
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_0 (by simp)) hdl (hdot3 k_0 (by simp)) ev343
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_1 (by simp)) hdl (hdot3 k_1 (by simp)) ev379
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_2 (by simp)) hdl (hdot3 k_2 (by simp)) ev415
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_3 (by simp)) hdl (hdot3 k_3 (by simp)) ev451
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_4 (by simp)) hdl (hdot3 k_4 (by simp)) ev487
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_5 (by simp)) hdl (hdot3 k_5 (by simp)) ev523
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_6 (by simp)) hdl (hdot3 k_6 (by simp)) ev559
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_7 (by simp)) hdl (hdot3 k_7 (by simp)) ev595
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_8 (by simp)) hdl (hdot3 k_8 (by simp)) ev631
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_9 (by simp)) hdl (hdot3 k_9 (by simp)) ev667
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_10 (by simp)) hdl (hdot3 k_10 (by simp))
      ev703
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_11 (by simp)) hdl (hdot3 k_11 (by simp))
      ev739
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_12 (by simp)) hdl (hdot3 k_12 (by simp))
      ev775
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_13 (by simp)) hdl (hdot3 k_13 (by simp))
      ev811
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_14 (by simp)) hdl (hdot3 k_14 (by simp))
      ev847
  obtain rfl := back_unit_spec (hz' _ (by simp)) (hTr k_15 (by simp)) hdl (hdot3 k_15 (by simp))
      ev883
  subst he300
  rfl

/-- **`Fixed::delta` returns `Model.delta m w2T x t`** as `(h, dz, dout)`. -/
theorem delta_spec {m : IxAICore.Model} {w2T : List (List IxAICore.Fx)} {x t : List IxAICore.Fx}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hT : w2T.length = 16) (hTr : ∀ c ∈ w2T, c.length = 11) (hx : x.length = 8)
    (ht : t.length = 11) (hb : DeltaBounds m w2T x t) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::delta"
      [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2, encMat w2T, encVec x, encVec t]
      h r h' calls) :
    r = .tuple [encVec (m.delta w2T x t).h, encVec (m.delta w2T x t).dz,
      encVec (m.delta w2T x t).dout] := by
  obtain ⟨w1, b1, w2, b2⟩ := m
  exact delta_core (w1 := w1) (b1 := b1) (w2 := w2) (b2 := b2) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    hx ht hb ev

/- Consumes `«Fixed::deltas».Path.run`: 140 binders (`x_x0` … `x_dout19`), then the facts
   hv11 : x_xs = (.tuple [x_x0, x_x1, …, x_x19])
   hv123 : x_ts = (.tuple [x_t0, x_t1, …, x_t19])
   ev238 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t0] h (.tuple [x_h0, x_dz0, x_dout0]) m226 c…
   ev326 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t1] m226 (.tuple [x_h1, x_dz1, x_dout1]) m31…
   ev414 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t2] m314 (.tuple [x_h2, x_dz2, x_dout2]) m40…
   ev502 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t3] m402 (.tuple [x_h3, x_dz3, x_dout3]) m49…
   ev590 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t4] m490 (.tuple [x_h4, x_dz4, x_dout4]) m57…
   ev678 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t5] m578 (.tuple [x_h5, x_dz5, x_dout5]) m66…
   ev766 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t6] m666 (.tuple [x_h6, x_dz6, x_dout6]) m75…
   ev854 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t7] m754 (.tuple [x_h7, x_dz7, x_dout7]) m84…
   ev942 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t8] m842 (.tuple [x_h8, x_dz8, x_dout8]) m93…
   ev1030 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t9] m930 (.tuple [x_h9, x_dz9, x_dout9]) m10…
   ev1118 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t10] m1018 (.tuple [x_h10, x_dz10, x_dout10]…
   ev1206 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t11] m1106 (.tuple [x_h11, x_dz11, x_dout11]…
   ev1294 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t12] m1194 (.tuple [x_h12, x_dz12, x_dout12]…
   ev1382 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t13] m1282 (.tuple [x_h13, x_dz13, x_dout13]…
   ev1470 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t14] m1370 (.tuple [x_h14, x_dz14, x_dout14]…
   ev1558 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t15] m1458 (.tuple [x_h15, x_dz15, x_dout15]…
   ev1646 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t16] m1546 (.tuple [x_h16, x_dz16, x_dout16]…
   ev1734 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t17] m1634 (.tuple [x_h17, x_dz17, x_dout17]…
   ev1822 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t18] m1722 (.tuple [x_h18, x_dz18, x_dout18]…
   ev1910 : ObsFn W "Fixed::delta" [x_w1, x_b1, …, x_t19] m1810 (.tuple [x_h19, x_dz19, x_dout19]…
   he1990 : r = (.tuple [(.tuple [x_h0, x_h1, …, x_h19]), (.tuple [x_dz0, x_dz1, …, x_dz19]), (.t…
   he2495 : h' = m1898  (unused)
   hc2496 : calls = ...  (unused) -/
/-- **`Fixed::deltas` is `ds` in `Model.step`**, as the matrices of its `h`, `dz` and `dout`
fields. -/
theorem deltas_spec {m : IxAICore.Model} {w2T : List (List IxAICore.Fx)}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hT : w2T.length = 16) (hTr : ∀ c ∈ w2T, c.length = 11) (hn : batch.length = 20)
    (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hb : ∀ p ∈ batch, DeltaBounds m w2T p.1 p.2) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::deltas"
      [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2, encMat w2T,
        encMat (batch.map (·.1)), encMat (batch.map (·.2))] h r h' calls) :
    r = .tuple [encMat ((deltasOf m w2T batch).map (·.h)),
      encMat ((deltasOf m w2T batch).map (·.dz)),
      encMat ((deltasOf m w2T batch).map (·.dout))] := by
  obtain ⟨⟨x_0, t_0⟩, ⟨x_1, t_1⟩, ⟨x_2, t_2⟩, ⟨x_3, t_3⟩, ⟨x_4, t_4⟩, ⟨x_5, t_5⟩, ⟨x_6, t_6⟩,
      ⟨x_7, t_7⟩, ⟨x_8, t_8⟩, ⟨x_9, t_9⟩, ⟨x_10, t_10⟩, ⟨x_11, t_11⟩, ⟨x_12, t_12⟩, ⟨x_13, t_13⟩,
      ⟨x_14, t_14⟩, ⟨x_15, t_15⟩, ⟨x_16, t_16⟩, ⟨x_17, t_17⟩, ⟨x_18, t_18⟩, ⟨x_19, t_19⟩,
      rfl⟩ := list_eq20 hn
  obtain ⟨x_x0, x_x1, x_x2, x_x3, x_x4, x_x5, x_x6, x_x7, x_x8, x_x9, x_x10, x_x11, x_x12, x_x13,
      x_x14, x_x15, x_x16, x_x17, x_x18, x_x19, x_t0, x_t1, x_t2, x_t3, x_t4, x_t5, x_t6, x_t7,
      x_t8, x_t9, x_t10, x_t11, x_t12, x_t13, x_t14, x_t15, x_t16, x_t17, x_t18, x_t19, m226, cs236,
      x_h0, x_dz0, x_dout0, m314, cs324, x_h1, x_dz1, x_dout1, m402, cs412, x_h2, x_dz2, x_dout2,
      m490, cs500, x_h3, x_dz3, x_dout3, m578, cs588, x_h4, x_dz4, x_dout4, m666, cs676, x_h5,
      x_dz5, x_dout5, m754, cs764, x_h6, x_dz6, x_dout6, m842, cs852, x_h7, x_dz7, x_dout7, m930,
      cs940, x_h8, x_dz8, x_dout8, m1018, cs1028, x_h9, x_dz9, x_dout9, m1106, cs1116, x_h10,
      x_dz10, x_dout10, m1194, cs1204, x_h11, x_dz11, x_dout11, m1282, cs1292, x_h12, x_dz12,
      x_dout12, m1370, cs1380, x_h13, x_dz13, x_dout13, m1458, cs1468, x_h14, x_dz14, x_dout14,
      m1546, cs1556, x_h15, x_dz15, x_dout15, m1634, cs1644, x_h16, x_dz16, x_dout16, m1722, cs1732,
      x_h17, x_dz17, x_dout17, m1810, cs1820, x_h18, x_dz18, x_dout18, m1898, cs1908, x_h19, x_dz19,
      x_dout19, hv11, hv123, ev238, ev326, ev414, ev502, ev590, ev678, ev766, ev854, ev942, ev1030,
      ev1118, ev1206, ev1294, ev1382, ev1470, ev1558, ev1646, ev1734, ev1822, ev1910, he1990, -,
      -⟩ :=
    «Fixed::deltas».obs ev
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv123
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩ := hv123
  have e0 := delta_spec (x := x_0) (t := t_0) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_0, t_0) (by simp)).1 (hex (x_0, t_0) (by simp)).2 (hb (x_0, t_0) (by simp)) ev238
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e0
  obtain ⟨rfl, rfl, rfl⟩ := e0
  have e1 := delta_spec (x := x_1) (t := t_1) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_1, t_1) (by simp)).1 (hex (x_1, t_1) (by simp)).2 (hb (x_1, t_1) (by simp)) ev326
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  have e2 := delta_spec (x := x_2) (t := t_2) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_2, t_2) (by simp)).1 (hex (x_2, t_2) (by simp)).2 (hb (x_2, t_2) (by simp)) ev414
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e2
  obtain ⟨rfl, rfl, rfl⟩ := e2
  have e3 := delta_spec (x := x_3) (t := t_3) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_3, t_3) (by simp)).1 (hex (x_3, t_3) (by simp)).2 (hb (x_3, t_3) (by simp)) ev502
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e3
  obtain ⟨rfl, rfl, rfl⟩ := e3
  have e4 := delta_spec (x := x_4) (t := t_4) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_4, t_4) (by simp)).1 (hex (x_4, t_4) (by simp)).2 (hb (x_4, t_4) (by simp)) ev590
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e4
  obtain ⟨rfl, rfl, rfl⟩ := e4
  have e5 := delta_spec (x := x_5) (t := t_5) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_5, t_5) (by simp)).1 (hex (x_5, t_5) (by simp)).2 (hb (x_5, t_5) (by simp)) ev678
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e5
  obtain ⟨rfl, rfl, rfl⟩ := e5
  have e6 := delta_spec (x := x_6) (t := t_6) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_6, t_6) (by simp)).1 (hex (x_6, t_6) (by simp)).2 (hb (x_6, t_6) (by simp)) ev766
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e6
  obtain ⟨rfl, rfl, rfl⟩ := e6
  have e7 := delta_spec (x := x_7) (t := t_7) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_7, t_7) (by simp)).1 (hex (x_7, t_7) (by simp)).2 (hb (x_7, t_7) (by simp)) ev854
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e7
  obtain ⟨rfl, rfl, rfl⟩ := e7
  have e8 := delta_spec (x := x_8) (t := t_8) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_8, t_8) (by simp)).1 (hex (x_8, t_8) (by simp)).2 (hb (x_8, t_8) (by simp)) ev942
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e8
  obtain ⟨rfl, rfl, rfl⟩ := e8
  have e9 := delta_spec (x := x_9) (t := t_9) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_9, t_9) (by simp)).1 (hex (x_9, t_9) (by simp)).2 (hb (x_9, t_9) (by simp)) ev1030
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e9
  obtain ⟨rfl, rfl, rfl⟩ := e9
  have e10 := delta_spec (x := x_10) (t := t_10) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_10, t_10) (by simp)).1 (hex (x_10, t_10) (by simp)).2 (hb (x_10, t_10) (by simp)) ev1118
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e10
  obtain ⟨rfl, rfl, rfl⟩ := e10
  have e11 := delta_spec (x := x_11) (t := t_11) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_11, t_11) (by simp)).1 (hex (x_11, t_11) (by simp)).2 (hb (x_11, t_11) (by simp)) ev1206
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e11
  obtain ⟨rfl, rfl, rfl⟩ := e11
  have e12 := delta_spec (x := x_12) (t := t_12) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_12, t_12) (by simp)).1 (hex (x_12, t_12) (by simp)).2 (hb (x_12, t_12) (by simp)) ev1294
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e12
  obtain ⟨rfl, rfl, rfl⟩ := e12
  have e13 := delta_spec (x := x_13) (t := t_13) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_13, t_13) (by simp)).1 (hex (x_13, t_13) (by simp)).2 (hb (x_13, t_13) (by simp)) ev1382
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e13
  obtain ⟨rfl, rfl, rfl⟩ := e13
  have e14 := delta_spec (x := x_14) (t := t_14) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_14, t_14) (by simp)).1 (hex (x_14, t_14) (by simp)).2 (hb (x_14, t_14) (by simp)) ev1470
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e14
  obtain ⟨rfl, rfl, rfl⟩ := e14
  have e15 := delta_spec (x := x_15) (t := t_15) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_15, t_15) (by simp)).1 (hex (x_15, t_15) (by simp)).2 (hb (x_15, t_15) (by simp)) ev1558
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e15
  obtain ⟨rfl, rfl, rfl⟩ := e15
  have e16 := delta_spec (x := x_16) (t := t_16) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_16, t_16) (by simp)).1 (hex (x_16, t_16) (by simp)).2 (hb (x_16, t_16) (by simp)) ev1646
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e16
  obtain ⟨rfl, rfl, rfl⟩ := e16
  have e17 := delta_spec (x := x_17) (t := t_17) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_17, t_17) (by simp)).1 (hex (x_17, t_17) (by simp)).2 (hb (x_17, t_17) (by simp)) ev1734
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e17
  obtain ⟨rfl, rfl, rfl⟩ := e17
  have e18 := delta_spec (x := x_18) (t := t_18) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_18, t_18) (by simp)).1 (hex (x_18, t_18) (by simp)).2 (hb (x_18, t_18) (by simp)) ev1822
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e18
  obtain ⟨rfl, rfl, rfl⟩ := e18
  have e19 := delta_spec (x := x_19) (t := t_19) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr
    (hex (x_19, t_19) (by simp)).1 (hex (x_19, t_19) (by simp)).2 (hb (x_19, t_19) (by simp)) ev1910
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e19
  obtain ⟨rfl, rfl, rfl⟩ := e19
  subst he1990
  rfl

/-! ## Transposes -/

/-- **`Fixed::transpose11x16` is `transposeN 16`** on a 11-row matrix. The path binds the rows and
projects every entry; a projection that succeeds reads the row's entry. -/
theorem transpose11x16_spec {n : ℕ} (hn : n = 16) {rows : List (List IxAICore.Fx)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::transpose11x16" [encMat rows] h r h' calls) :
    r = encMat (IxAICore.transposeN n rows) := by
  subst hn
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, v95, v96, v97, v98,
      v99, v100, v101, v102, v103, v104, v105, v224, v225, v226, v227, v228, v229, v230, v231,
      v232, v233, v234, v353, v354, v355, v356, v357, v358, v359, v360, v361, v362, v363, v482,
      v483, v484, v485, v486, v487, v488, v489, v490, v491, v492, v611, v612, v613, v614, v615,
      v616, v617, v618, v619, v620, v621, v740, v741, v742, v743, v744, v745, v746, v747, v748,
      v749, v750, v869, v870, v871, v872, v873, v874, v875, v876, v877, v878, v879, v998, v999,
      v1000, v1001, v1002, v1003, v1004, v1005, v1006, v1007, v1008, v1127, v1128, v1129, v1130,
      v1131, v1132, v1133, v1134, v1135, v1136, v1137, v1256, v1257, v1258, v1259, v1260, v1261,
      v1262, v1263, v1264, v1265, v1266, v1385, v1386, v1387, v1388, v1389, v1390, v1391, v1392,
      v1393, v1394, v1395, v1514, v1515, v1516, v1517, v1518, v1519, v1520, v1521, v1522, v1523,
      v1524, v1643, v1644, v1645, v1646, v1647, v1648, v1649, v1650, v1651, v1652, v1653, v1772,
      v1773, v1774, v1775, v1776, v1777, v1778, v1779, v1780, v1781, v1782, v1901, v1902, v1903,
      v1904, v1905, v1906, v1907, v1908, v1909, v1910, v1911, v2030, v2031, v2032, v2033, v2034,
      v2035, v2036, v2037, v2038, v2039, v2040, hv11, he86, pr114, pr124, pr134, pr144, pr154,
      pr164, pr174, pr184, pr194, pr204, pr214, pr243, pr253, pr263, pr273, pr283, pr293, pr303,
      pr313, pr323, pr333, pr343, pr372, pr382, pr392, pr402, pr412, pr422, pr432, pr442, pr452,
      pr462, pr472, pr501, pr511, pr521, pr531, pr541, pr551, pr561, pr571, pr581, pr591, pr601,
      pr630, pr640, pr650, pr660, pr670, pr680, pr690, pr700, pr710, pr720, pr730, pr759, pr769,
      pr779, pr789, pr799, pr809, pr819, pr829, pr839, pr849, pr859, pr888, pr898, pr908, pr918,
      pr928, pr938, pr948, pr958, pr968, pr978, pr988, pr1017, pr1027, pr1037, pr1047, pr1057,
      pr1067, pr1077, pr1087, pr1097, pr1107, pr1117, pr1146, pr1156, pr1166, pr1176, pr1186,
      pr1196, pr1206, pr1216, pr1226, pr1236, pr1246, pr1275, pr1285, pr1295, pr1305, pr1315,
      pr1325, pr1335, pr1345, pr1355, pr1365, pr1375, pr1404, pr1414, pr1424, pr1434, pr1444,
      pr1454, pr1464, pr1474, pr1484, pr1494, pr1504, pr1533, pr1543, pr1553, pr1563, pr1573,
      pr1583, pr1593, pr1603, pr1613, pr1623, pr1633, pr1662, pr1672, pr1682, pr1692, pr1702,
      pr1712, pr1722, pr1732, pr1742, pr1752, pr1762, pr1791, pr1801, pr1811, pr1821, pr1831,
      pr1841, pr1851, pr1861, pr1871, pr1881, pr1891, pr1920, pr1930, pr1940, pr1950, pr1960,
      pr1970, pr1980, pr1990, pr2000, pr2010, pr2020, pr2049, pr2059, pr2069, pr2079, pr2089,
      pr2099, pr2109, pr2119, pr2129, pr2139, pr2149, -, -⟩ :=
    «Fixed::transpose11x16».obs ev
  have hv : rows.map encVec = [x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10] :=
    Aiur.Value.tuple.inj hv11
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, rfl⟩ := list_eq11 (by simpa using congrArg List.length hv)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv
  obtain rfl := proj_encVec pr114
  obtain rfl := proj_encVec pr124
  obtain rfl := proj_encVec pr134
  obtain rfl := proj_encVec pr144
  obtain rfl := proj_encVec pr154
  obtain rfl := proj_encVec pr164
  obtain rfl := proj_encVec pr174
  obtain rfl := proj_encVec pr184
  obtain rfl := proj_encVec pr194
  obtain rfl := proj_encVec pr204
  obtain rfl := proj_encVec pr214
  obtain rfl := proj_encVec pr243
  obtain rfl := proj_encVec pr253
  obtain rfl := proj_encVec pr263
  obtain rfl := proj_encVec pr273
  obtain rfl := proj_encVec pr283
  obtain rfl := proj_encVec pr293
  obtain rfl := proj_encVec pr303
  obtain rfl := proj_encVec pr313
  obtain rfl := proj_encVec pr323
  obtain rfl := proj_encVec pr333
  obtain rfl := proj_encVec pr343
  obtain rfl := proj_encVec pr372
  obtain rfl := proj_encVec pr382
  obtain rfl := proj_encVec pr392
  obtain rfl := proj_encVec pr402
  obtain rfl := proj_encVec pr412
  obtain rfl := proj_encVec pr422
  obtain rfl := proj_encVec pr432
  obtain rfl := proj_encVec pr442
  obtain rfl := proj_encVec pr452
  obtain rfl := proj_encVec pr462
  obtain rfl := proj_encVec pr472
  obtain rfl := proj_encVec pr501
  obtain rfl := proj_encVec pr511
  obtain rfl := proj_encVec pr521
  obtain rfl := proj_encVec pr531
  obtain rfl := proj_encVec pr541
  obtain rfl := proj_encVec pr551
  obtain rfl := proj_encVec pr561
  obtain rfl := proj_encVec pr571
  obtain rfl := proj_encVec pr581
  obtain rfl := proj_encVec pr591
  obtain rfl := proj_encVec pr601
  obtain rfl := proj_encVec pr630
  obtain rfl := proj_encVec pr640
  obtain rfl := proj_encVec pr650
  obtain rfl := proj_encVec pr660
  obtain rfl := proj_encVec pr670
  obtain rfl := proj_encVec pr680
  obtain rfl := proj_encVec pr690
  obtain rfl := proj_encVec pr700
  obtain rfl := proj_encVec pr710
  obtain rfl := proj_encVec pr720
  obtain rfl := proj_encVec pr730
  obtain rfl := proj_encVec pr759
  obtain rfl := proj_encVec pr769
  obtain rfl := proj_encVec pr779
  obtain rfl := proj_encVec pr789
  obtain rfl := proj_encVec pr799
  obtain rfl := proj_encVec pr809
  obtain rfl := proj_encVec pr819
  obtain rfl := proj_encVec pr829
  obtain rfl := proj_encVec pr839
  obtain rfl := proj_encVec pr849
  obtain rfl := proj_encVec pr859
  obtain rfl := proj_encVec pr888
  obtain rfl := proj_encVec pr898
  obtain rfl := proj_encVec pr908
  obtain rfl := proj_encVec pr918
  obtain rfl := proj_encVec pr928
  obtain rfl := proj_encVec pr938
  obtain rfl := proj_encVec pr948
  obtain rfl := proj_encVec pr958
  obtain rfl := proj_encVec pr968
  obtain rfl := proj_encVec pr978
  obtain rfl := proj_encVec pr988
  obtain rfl := proj_encVec pr1017
  obtain rfl := proj_encVec pr1027
  obtain rfl := proj_encVec pr1037
  obtain rfl := proj_encVec pr1047
  obtain rfl := proj_encVec pr1057
  obtain rfl := proj_encVec pr1067
  obtain rfl := proj_encVec pr1077
  obtain rfl := proj_encVec pr1087
  obtain rfl := proj_encVec pr1097
  obtain rfl := proj_encVec pr1107
  obtain rfl := proj_encVec pr1117
  obtain rfl := proj_encVec pr1146
  obtain rfl := proj_encVec pr1156
  obtain rfl := proj_encVec pr1166
  obtain rfl := proj_encVec pr1176
  obtain rfl := proj_encVec pr1186
  obtain rfl := proj_encVec pr1196
  obtain rfl := proj_encVec pr1206
  obtain rfl := proj_encVec pr1216
  obtain rfl := proj_encVec pr1226
  obtain rfl := proj_encVec pr1236
  obtain rfl := proj_encVec pr1246
  obtain rfl := proj_encVec pr1275
  obtain rfl := proj_encVec pr1285
  obtain rfl := proj_encVec pr1295
  obtain rfl := proj_encVec pr1305
  obtain rfl := proj_encVec pr1315
  obtain rfl := proj_encVec pr1325
  obtain rfl := proj_encVec pr1335
  obtain rfl := proj_encVec pr1345
  obtain rfl := proj_encVec pr1355
  obtain rfl := proj_encVec pr1365
  obtain rfl := proj_encVec pr1375
  obtain rfl := proj_encVec pr1404
  obtain rfl := proj_encVec pr1414
  obtain rfl := proj_encVec pr1424
  obtain rfl := proj_encVec pr1434
  obtain rfl := proj_encVec pr1444
  obtain rfl := proj_encVec pr1454
  obtain rfl := proj_encVec pr1464
  obtain rfl := proj_encVec pr1474
  obtain rfl := proj_encVec pr1484
  obtain rfl := proj_encVec pr1494
  obtain rfl := proj_encVec pr1504
  obtain rfl := proj_encVec pr1533
  obtain rfl := proj_encVec pr1543
  obtain rfl := proj_encVec pr1553
  obtain rfl := proj_encVec pr1563
  obtain rfl := proj_encVec pr1573
  obtain rfl := proj_encVec pr1583
  obtain rfl := proj_encVec pr1593
  obtain rfl := proj_encVec pr1603
  obtain rfl := proj_encVec pr1613
  obtain rfl := proj_encVec pr1623
  obtain rfl := proj_encVec pr1633
  obtain rfl := proj_encVec pr1662
  obtain rfl := proj_encVec pr1672
  obtain rfl := proj_encVec pr1682
  obtain rfl := proj_encVec pr1692
  obtain rfl := proj_encVec pr1702
  obtain rfl := proj_encVec pr1712
  obtain rfl := proj_encVec pr1722
  obtain rfl := proj_encVec pr1732
  obtain rfl := proj_encVec pr1742
  obtain rfl := proj_encVec pr1752
  obtain rfl := proj_encVec pr1762
  obtain rfl := proj_encVec pr1791
  obtain rfl := proj_encVec pr1801
  obtain rfl := proj_encVec pr1811
  obtain rfl := proj_encVec pr1821
  obtain rfl := proj_encVec pr1831
  obtain rfl := proj_encVec pr1841
  obtain rfl := proj_encVec pr1851
  obtain rfl := proj_encVec pr1861
  obtain rfl := proj_encVec pr1871
  obtain rfl := proj_encVec pr1881
  obtain rfl := proj_encVec pr1891
  obtain rfl := proj_encVec pr1920
  obtain rfl := proj_encVec pr1930
  obtain rfl := proj_encVec pr1940
  obtain rfl := proj_encVec pr1950
  obtain rfl := proj_encVec pr1960
  obtain rfl := proj_encVec pr1970
  obtain rfl := proj_encVec pr1980
  obtain rfl := proj_encVec pr1990
  obtain rfl := proj_encVec pr2000
  obtain rfl := proj_encVec pr2010
  obtain rfl := proj_encVec pr2020
  obtain rfl := proj_encVec pr2049
  obtain rfl := proj_encVec pr2059
  obtain rfl := proj_encVec pr2069
  obtain rfl := proj_encVec pr2079
  obtain rfl := proj_encVec pr2089
  obtain rfl := proj_encVec pr2099
  obtain rfl := proj_encVec pr2109
  obtain rfl := proj_encVec pr2119
  obtain rfl := proj_encVec pr2129
  obtain rfl := proj_encVec pr2139
  obtain rfl := proj_encVec pr2149
  subst he86
  rw [transposeN_eq_cols]
  rfl

/-- **`Fixed::transpose20x16` is `transposeN 16`** on a 20-row matrix. The path binds the rows and
projects every entry; a projection that succeeds reads the row's entry. -/
theorem transpose20x16_spec {n : ℕ} (hn : n = 16) {rows : List (List IxAICore.Fx)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::transpose20x16" [encMat rows] h r h' calls) :
    r = encMat (IxAICore.transposeN n rows) := by
  subst hn
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13,
      x_r14, x_r15, x_r16, x_r17, x_r18, x_r19, v140, v141, v142, v143, v144, v145, v146, v147,
      v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v368, v369, v370,
      v371, v372, v373, v374, v375, v376, v377, v378, v379, v380, v381, v382, v383, v384, v385,
      v386, v387, v596, v597, v598, v599, v600, v601, v602, v603, v604, v605, v606, v607, v608,
      v609, v610, v611, v612, v613, v614, v615, v824, v825, v826, v827, v828, v829, v830, v831,
      v832, v833, v834, v835, v836, v837, v838, v839, v840, v841, v842, v843, v1052, v1053,
      v1054, v1055, v1056, v1057, v1058, v1059, v1060, v1061, v1062, v1063, v1064, v1065, v1066,
      v1067, v1068, v1069, v1070, v1071, v1280, v1281, v1282, v1283, v1284, v1285, v1286, v1287,
      v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1508,
      v1509, v1510, v1511, v1512, v1513, v1514, v1515, v1516, v1517, v1518, v1519, v1520, v1521,
      v1522, v1523, v1524, v1525, v1526, v1527, v1736, v1737, v1738, v1739, v1740, v1741, v1742,
      v1743, v1744, v1745, v1746, v1747, v1748, v1749, v1750, v1751, v1752, v1753, v1754, v1755,
      v1964, v1965, v1966, v1967, v1968, v1969, v1970, v1971, v1972, v1973, v1974, v1975, v1976,
      v1977, v1978, v1979, v1980, v1981, v1982, v1983, v2192, v2193, v2194, v2195, v2196, v2197,
      v2198, v2199, v2200, v2201, v2202, v2203, v2204, v2205, v2206, v2207, v2208, v2209, v2210,
      v2211, v2420, v2421, v2422, v2423, v2424, v2425, v2426, v2427, v2428, v2429, v2430, v2431,
      v2432, v2433, v2434, v2435, v2436, v2437, v2438, v2439, v2648, v2649, v2650, v2651, v2652,
      v2653, v2654, v2655, v2656, v2657, v2658, v2659, v2660, v2661, v2662, v2663, v2664, v2665,
      v2666, v2667, v2876, v2877, v2878, v2879, v2880, v2881, v2882, v2883, v2884, v2885, v2886,
      v2887, v2888, v2889, v2890, v2891, v2892, v2893, v2894, v2895, v3104, v3105, v3106, v3107,
      v3108, v3109, v3110, v3111, v3112, v3113, v3114, v3115, v3116, v3117, v3118, v3119, v3120,
      v3121, v3122, v3123, v3332, v3333, v3334, v3335, v3336, v3337, v3338, v3339, v3340, v3341,
      v3342, v3343, v3344, v3345, v3346, v3347, v3348, v3349, v3350, v3351, v3560, v3561, v3562,
      v3563, v3564, v3565, v3566, v3567, v3568, v3569, v3570, v3571, v3572, v3573, v3574, v3575,
      v3576, v3577, v3578, v3579, hv11, he131, pr168, pr178, pr188, pr198, pr208, pr218, pr228,
      pr238, pr248, pr258, pr268, pr278, pr288, pr298, pr308, pr318, pr328, pr338, pr348, pr358,
      pr396, pr406, pr416, pr426, pr436, pr446, pr456, pr466, pr476, pr486, pr496, pr506, pr516,
      pr526, pr536, pr546, pr556, pr566, pr576, pr586, pr624, pr634, pr644, pr654, pr664, pr674,
      pr684, pr694, pr704, pr714, pr724, pr734, pr744, pr754, pr764, pr774, pr784, pr794, pr804,
      pr814, pr852, pr862, pr872, pr882, pr892, pr902, pr912, pr922, pr932, pr942, pr952, pr962,
      pr972, pr982, pr992, pr1002, pr1012, pr1022, pr1032, pr1042, pr1080, pr1090, pr1100,
      pr1110, pr1120, pr1130, pr1140, pr1150, pr1160, pr1170, pr1180, pr1190, pr1200, pr1210,
      pr1220, pr1230, pr1240, pr1250, pr1260, pr1270, pr1308, pr1318, pr1328, pr1338, pr1348,
      pr1358, pr1368, pr1378, pr1388, pr1398, pr1408, pr1418, pr1428, pr1438, pr1448, pr1458,
      pr1468, pr1478, pr1488, pr1498, pr1536, pr1546, pr1556, pr1566, pr1576, pr1586, pr1596,
      pr1606, pr1616, pr1626, pr1636, pr1646, pr1656, pr1666, pr1676, pr1686, pr1696, pr1706,
      pr1716, pr1726, pr1764, pr1774, pr1784, pr1794, pr1804, pr1814, pr1824, pr1834, pr1844,
      pr1854, pr1864, pr1874, pr1884, pr1894, pr1904, pr1914, pr1924, pr1934, pr1944, pr1954,
      pr1992, pr2002, pr2012, pr2022, pr2032, pr2042, pr2052, pr2062, pr2072, pr2082, pr2092,
      pr2102, pr2112, pr2122, pr2132, pr2142, pr2152, pr2162, pr2172, pr2182, pr2220, pr2230,
      pr2240, pr2250, pr2260, pr2270, pr2280, pr2290, pr2300, pr2310, pr2320, pr2330, pr2340,
      pr2350, pr2360, pr2370, pr2380, pr2390, pr2400, pr2410, pr2448, pr2458, pr2468, pr2478,
      pr2488, pr2498, pr2508, pr2518, pr2528, pr2538, pr2548, pr2558, pr2568, pr2578, pr2588,
      pr2598, pr2608, pr2618, pr2628, pr2638, pr2676, pr2686, pr2696, pr2706, pr2716, pr2726,
      pr2736, pr2746, pr2756, pr2766, pr2776, pr2786, pr2796, pr2806, pr2816, pr2826, pr2836,
      pr2846, pr2856, pr2866, pr2904, pr2914, pr2924, pr2934, pr2944, pr2954, pr2964, pr2974,
      pr2984, pr2994, pr3004, pr3014, pr3024, pr3034, pr3044, pr3054, pr3064, pr3074, pr3084,
      pr3094, pr3132, pr3142, pr3152, pr3162, pr3172, pr3182, pr3192, pr3202, pr3212, pr3222,
      pr3232, pr3242, pr3252, pr3262, pr3272, pr3282, pr3292, pr3302, pr3312, pr3322, pr3360,
      pr3370, pr3380, pr3390, pr3400, pr3410, pr3420, pr3430, pr3440, pr3450, pr3460, pr3470,
      pr3480, pr3490, pr3500, pr3510, pr3520, pr3530, pr3540, pr3550, pr3588, pr3598, pr3608,
      pr3618, pr3628, pr3638, pr3648, pr3658, pr3668, pr3678, pr3688, pr3698, pr3708, pr3718,
      pr3728, pr3738, pr3748, pr3758, pr3768, pr3778, -, -⟩ :=
    «Fixed::transpose20x16».obs ev
  have hv : rows.map encVec = [x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13, x_r14, x_r15, x_r16, x_r17, x_r18, x_r19] :=
    Aiur.Value.tuple.inj hv11
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, rfl⟩ := list_eq20 (by simpa using congrArg List.length hv)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv
  obtain rfl := proj_encVec pr168
  obtain rfl := proj_encVec pr178
  obtain rfl := proj_encVec pr188
  obtain rfl := proj_encVec pr198
  obtain rfl := proj_encVec pr208
  obtain rfl := proj_encVec pr218
  obtain rfl := proj_encVec pr228
  obtain rfl := proj_encVec pr238
  obtain rfl := proj_encVec pr248
  obtain rfl := proj_encVec pr258
  obtain rfl := proj_encVec pr268
  obtain rfl := proj_encVec pr278
  obtain rfl := proj_encVec pr288
  obtain rfl := proj_encVec pr298
  obtain rfl := proj_encVec pr308
  obtain rfl := proj_encVec pr318
  obtain rfl := proj_encVec pr328
  obtain rfl := proj_encVec pr338
  obtain rfl := proj_encVec pr348
  obtain rfl := proj_encVec pr358
  obtain rfl := proj_encVec pr396
  obtain rfl := proj_encVec pr406
  obtain rfl := proj_encVec pr416
  obtain rfl := proj_encVec pr426
  obtain rfl := proj_encVec pr436
  obtain rfl := proj_encVec pr446
  obtain rfl := proj_encVec pr456
  obtain rfl := proj_encVec pr466
  obtain rfl := proj_encVec pr476
  obtain rfl := proj_encVec pr486
  obtain rfl := proj_encVec pr496
  obtain rfl := proj_encVec pr506
  obtain rfl := proj_encVec pr516
  obtain rfl := proj_encVec pr526
  obtain rfl := proj_encVec pr536
  obtain rfl := proj_encVec pr546
  obtain rfl := proj_encVec pr556
  obtain rfl := proj_encVec pr566
  obtain rfl := proj_encVec pr576
  obtain rfl := proj_encVec pr586
  obtain rfl := proj_encVec pr624
  obtain rfl := proj_encVec pr634
  obtain rfl := proj_encVec pr644
  obtain rfl := proj_encVec pr654
  obtain rfl := proj_encVec pr664
  obtain rfl := proj_encVec pr674
  obtain rfl := proj_encVec pr684
  obtain rfl := proj_encVec pr694
  obtain rfl := proj_encVec pr704
  obtain rfl := proj_encVec pr714
  obtain rfl := proj_encVec pr724
  obtain rfl := proj_encVec pr734
  obtain rfl := proj_encVec pr744
  obtain rfl := proj_encVec pr754
  obtain rfl := proj_encVec pr764
  obtain rfl := proj_encVec pr774
  obtain rfl := proj_encVec pr784
  obtain rfl := proj_encVec pr794
  obtain rfl := proj_encVec pr804
  obtain rfl := proj_encVec pr814
  obtain rfl := proj_encVec pr852
  obtain rfl := proj_encVec pr862
  obtain rfl := proj_encVec pr872
  obtain rfl := proj_encVec pr882
  obtain rfl := proj_encVec pr892
  obtain rfl := proj_encVec pr902
  obtain rfl := proj_encVec pr912
  obtain rfl := proj_encVec pr922
  obtain rfl := proj_encVec pr932
  obtain rfl := proj_encVec pr942
  obtain rfl := proj_encVec pr952
  obtain rfl := proj_encVec pr962
  obtain rfl := proj_encVec pr972
  obtain rfl := proj_encVec pr982
  obtain rfl := proj_encVec pr992
  obtain rfl := proj_encVec pr1002
  obtain rfl := proj_encVec pr1012
  obtain rfl := proj_encVec pr1022
  obtain rfl := proj_encVec pr1032
  obtain rfl := proj_encVec pr1042
  obtain rfl := proj_encVec pr1080
  obtain rfl := proj_encVec pr1090
  obtain rfl := proj_encVec pr1100
  obtain rfl := proj_encVec pr1110
  obtain rfl := proj_encVec pr1120
  obtain rfl := proj_encVec pr1130
  obtain rfl := proj_encVec pr1140
  obtain rfl := proj_encVec pr1150
  obtain rfl := proj_encVec pr1160
  obtain rfl := proj_encVec pr1170
  obtain rfl := proj_encVec pr1180
  obtain rfl := proj_encVec pr1190
  obtain rfl := proj_encVec pr1200
  obtain rfl := proj_encVec pr1210
  obtain rfl := proj_encVec pr1220
  obtain rfl := proj_encVec pr1230
  obtain rfl := proj_encVec pr1240
  obtain rfl := proj_encVec pr1250
  obtain rfl := proj_encVec pr1260
  obtain rfl := proj_encVec pr1270
  obtain rfl := proj_encVec pr1308
  obtain rfl := proj_encVec pr1318
  obtain rfl := proj_encVec pr1328
  obtain rfl := proj_encVec pr1338
  obtain rfl := proj_encVec pr1348
  obtain rfl := proj_encVec pr1358
  obtain rfl := proj_encVec pr1368
  obtain rfl := proj_encVec pr1378
  obtain rfl := proj_encVec pr1388
  obtain rfl := proj_encVec pr1398
  obtain rfl := proj_encVec pr1408
  obtain rfl := proj_encVec pr1418
  obtain rfl := proj_encVec pr1428
  obtain rfl := proj_encVec pr1438
  obtain rfl := proj_encVec pr1448
  obtain rfl := proj_encVec pr1458
  obtain rfl := proj_encVec pr1468
  obtain rfl := proj_encVec pr1478
  obtain rfl := proj_encVec pr1488
  obtain rfl := proj_encVec pr1498
  obtain rfl := proj_encVec pr1536
  obtain rfl := proj_encVec pr1546
  obtain rfl := proj_encVec pr1556
  obtain rfl := proj_encVec pr1566
  obtain rfl := proj_encVec pr1576
  obtain rfl := proj_encVec pr1586
  obtain rfl := proj_encVec pr1596
  obtain rfl := proj_encVec pr1606
  obtain rfl := proj_encVec pr1616
  obtain rfl := proj_encVec pr1626
  obtain rfl := proj_encVec pr1636
  obtain rfl := proj_encVec pr1646
  obtain rfl := proj_encVec pr1656
  obtain rfl := proj_encVec pr1666
  obtain rfl := proj_encVec pr1676
  obtain rfl := proj_encVec pr1686
  obtain rfl := proj_encVec pr1696
  obtain rfl := proj_encVec pr1706
  obtain rfl := proj_encVec pr1716
  obtain rfl := proj_encVec pr1726
  obtain rfl := proj_encVec pr1764
  obtain rfl := proj_encVec pr1774
  obtain rfl := proj_encVec pr1784
  obtain rfl := proj_encVec pr1794
  obtain rfl := proj_encVec pr1804
  obtain rfl := proj_encVec pr1814
  obtain rfl := proj_encVec pr1824
  obtain rfl := proj_encVec pr1834
  obtain rfl := proj_encVec pr1844
  obtain rfl := proj_encVec pr1854
  obtain rfl := proj_encVec pr1864
  obtain rfl := proj_encVec pr1874
  obtain rfl := proj_encVec pr1884
  obtain rfl := proj_encVec pr1894
  obtain rfl := proj_encVec pr1904
  obtain rfl := proj_encVec pr1914
  obtain rfl := proj_encVec pr1924
  obtain rfl := proj_encVec pr1934
  obtain rfl := proj_encVec pr1944
  obtain rfl := proj_encVec pr1954
  obtain rfl := proj_encVec pr1992
  obtain rfl := proj_encVec pr2002
  obtain rfl := proj_encVec pr2012
  obtain rfl := proj_encVec pr2022
  obtain rfl := proj_encVec pr2032
  obtain rfl := proj_encVec pr2042
  obtain rfl := proj_encVec pr2052
  obtain rfl := proj_encVec pr2062
  obtain rfl := proj_encVec pr2072
  obtain rfl := proj_encVec pr2082
  obtain rfl := proj_encVec pr2092
  obtain rfl := proj_encVec pr2102
  obtain rfl := proj_encVec pr2112
  obtain rfl := proj_encVec pr2122
  obtain rfl := proj_encVec pr2132
  obtain rfl := proj_encVec pr2142
  obtain rfl := proj_encVec pr2152
  obtain rfl := proj_encVec pr2162
  obtain rfl := proj_encVec pr2172
  obtain rfl := proj_encVec pr2182
  obtain rfl := proj_encVec pr2220
  obtain rfl := proj_encVec pr2230
  obtain rfl := proj_encVec pr2240
  obtain rfl := proj_encVec pr2250
  obtain rfl := proj_encVec pr2260
  obtain rfl := proj_encVec pr2270
  obtain rfl := proj_encVec pr2280
  obtain rfl := proj_encVec pr2290
  obtain rfl := proj_encVec pr2300
  obtain rfl := proj_encVec pr2310
  obtain rfl := proj_encVec pr2320
  obtain rfl := proj_encVec pr2330
  obtain rfl := proj_encVec pr2340
  obtain rfl := proj_encVec pr2350
  obtain rfl := proj_encVec pr2360
  obtain rfl := proj_encVec pr2370
  obtain rfl := proj_encVec pr2380
  obtain rfl := proj_encVec pr2390
  obtain rfl := proj_encVec pr2400
  obtain rfl := proj_encVec pr2410
  obtain rfl := proj_encVec pr2448
  obtain rfl := proj_encVec pr2458
  obtain rfl := proj_encVec pr2468
  obtain rfl := proj_encVec pr2478
  obtain rfl := proj_encVec pr2488
  obtain rfl := proj_encVec pr2498
  obtain rfl := proj_encVec pr2508
  obtain rfl := proj_encVec pr2518
  obtain rfl := proj_encVec pr2528
  obtain rfl := proj_encVec pr2538
  obtain rfl := proj_encVec pr2548
  obtain rfl := proj_encVec pr2558
  obtain rfl := proj_encVec pr2568
  obtain rfl := proj_encVec pr2578
  obtain rfl := proj_encVec pr2588
  obtain rfl := proj_encVec pr2598
  obtain rfl := proj_encVec pr2608
  obtain rfl := proj_encVec pr2618
  obtain rfl := proj_encVec pr2628
  obtain rfl := proj_encVec pr2638
  obtain rfl := proj_encVec pr2676
  obtain rfl := proj_encVec pr2686
  obtain rfl := proj_encVec pr2696
  obtain rfl := proj_encVec pr2706
  obtain rfl := proj_encVec pr2716
  obtain rfl := proj_encVec pr2726
  obtain rfl := proj_encVec pr2736
  obtain rfl := proj_encVec pr2746
  obtain rfl := proj_encVec pr2756
  obtain rfl := proj_encVec pr2766
  obtain rfl := proj_encVec pr2776
  obtain rfl := proj_encVec pr2786
  obtain rfl := proj_encVec pr2796
  obtain rfl := proj_encVec pr2806
  obtain rfl := proj_encVec pr2816
  obtain rfl := proj_encVec pr2826
  obtain rfl := proj_encVec pr2836
  obtain rfl := proj_encVec pr2846
  obtain rfl := proj_encVec pr2856
  obtain rfl := proj_encVec pr2866
  obtain rfl := proj_encVec pr2904
  obtain rfl := proj_encVec pr2914
  obtain rfl := proj_encVec pr2924
  obtain rfl := proj_encVec pr2934
  obtain rfl := proj_encVec pr2944
  obtain rfl := proj_encVec pr2954
  obtain rfl := proj_encVec pr2964
  obtain rfl := proj_encVec pr2974
  obtain rfl := proj_encVec pr2984
  obtain rfl := proj_encVec pr2994
  obtain rfl := proj_encVec pr3004
  obtain rfl := proj_encVec pr3014
  obtain rfl := proj_encVec pr3024
  obtain rfl := proj_encVec pr3034
  obtain rfl := proj_encVec pr3044
  obtain rfl := proj_encVec pr3054
  obtain rfl := proj_encVec pr3064
  obtain rfl := proj_encVec pr3074
  obtain rfl := proj_encVec pr3084
  obtain rfl := proj_encVec pr3094
  obtain rfl := proj_encVec pr3132
  obtain rfl := proj_encVec pr3142
  obtain rfl := proj_encVec pr3152
  obtain rfl := proj_encVec pr3162
  obtain rfl := proj_encVec pr3172
  obtain rfl := proj_encVec pr3182
  obtain rfl := proj_encVec pr3192
  obtain rfl := proj_encVec pr3202
  obtain rfl := proj_encVec pr3212
  obtain rfl := proj_encVec pr3222
  obtain rfl := proj_encVec pr3232
  obtain rfl := proj_encVec pr3242
  obtain rfl := proj_encVec pr3252
  obtain rfl := proj_encVec pr3262
  obtain rfl := proj_encVec pr3272
  obtain rfl := proj_encVec pr3282
  obtain rfl := proj_encVec pr3292
  obtain rfl := proj_encVec pr3302
  obtain rfl := proj_encVec pr3312
  obtain rfl := proj_encVec pr3322
  obtain rfl := proj_encVec pr3360
  obtain rfl := proj_encVec pr3370
  obtain rfl := proj_encVec pr3380
  obtain rfl := proj_encVec pr3390
  obtain rfl := proj_encVec pr3400
  obtain rfl := proj_encVec pr3410
  obtain rfl := proj_encVec pr3420
  obtain rfl := proj_encVec pr3430
  obtain rfl := proj_encVec pr3440
  obtain rfl := proj_encVec pr3450
  obtain rfl := proj_encVec pr3460
  obtain rfl := proj_encVec pr3470
  obtain rfl := proj_encVec pr3480
  obtain rfl := proj_encVec pr3490
  obtain rfl := proj_encVec pr3500
  obtain rfl := proj_encVec pr3510
  obtain rfl := proj_encVec pr3520
  obtain rfl := proj_encVec pr3530
  obtain rfl := proj_encVec pr3540
  obtain rfl := proj_encVec pr3550
  obtain rfl := proj_encVec pr3588
  obtain rfl := proj_encVec pr3598
  obtain rfl := proj_encVec pr3608
  obtain rfl := proj_encVec pr3618
  obtain rfl := proj_encVec pr3628
  obtain rfl := proj_encVec pr3638
  obtain rfl := proj_encVec pr3648
  obtain rfl := proj_encVec pr3658
  obtain rfl := proj_encVec pr3668
  obtain rfl := proj_encVec pr3678
  obtain rfl := proj_encVec pr3688
  obtain rfl := proj_encVec pr3698
  obtain rfl := proj_encVec pr3708
  obtain rfl := proj_encVec pr3718
  obtain rfl := proj_encVec pr3728
  obtain rfl := proj_encVec pr3738
  obtain rfl := proj_encVec pr3748
  obtain rfl := proj_encVec pr3758
  obtain rfl := proj_encVec pr3768
  obtain rfl := proj_encVec pr3778
  subst he131
  rw [transposeN_eq_cols]
  rfl

/-- **`Fixed::transpose20x8` is `transposeN 8`** on a 20-row matrix. The path binds the rows and
projects every entry; a projection that succeeds reads the row's entry. -/
theorem transpose20x8_spec {n : ℕ} (hn : n = 8) {rows : List (List IxAICore.Fx)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::transpose20x8" [encMat rows] h r h' calls) :
    r = encMat (IxAICore.transposeN n rows) := by
  subst hn
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13,
      x_r14, x_r15, x_r16, x_r17, x_r18, x_r19, v132, v133, v134, v135, v136, v137, v138, v139,
      v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v360, v361, v362,
      v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377,
      v378, v379, v588, v589, v590, v591, v592, v593, v594, v595, v596, v597, v598, v599, v600,
      v601, v602, v603, v604, v605, v606, v607, v816, v817, v818, v819, v820, v821, v822, v823,
      v824, v825, v826, v827, v828, v829, v830, v831, v832, v833, v834, v835, v1044, v1045,
      v1046, v1047, v1048, v1049, v1050, v1051, v1052, v1053, v1054, v1055, v1056, v1057, v1058,
      v1059, v1060, v1061, v1062, v1063, v1272, v1273, v1274, v1275, v1276, v1277, v1278, v1279,
      v1280, v1281, v1282, v1283, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1500,
      v1501, v1502, v1503, v1504, v1505, v1506, v1507, v1508, v1509, v1510, v1511, v1512, v1513,
      v1514, v1515, v1516, v1517, v1518, v1519, v1728, v1729, v1730, v1731, v1732, v1733, v1734,
      v1735, v1736, v1737, v1738, v1739, v1740, v1741, v1742, v1743, v1744, v1745, v1746, v1747,
      hv11, he123, pr160, pr170, pr180, pr190, pr200, pr210, pr220, pr230, pr240, pr250, pr260,
      pr270, pr280, pr290, pr300, pr310, pr320, pr330, pr340, pr350, pr388, pr398, pr408, pr418,
      pr428, pr438, pr448, pr458, pr468, pr478, pr488, pr498, pr508, pr518, pr528, pr538, pr548,
      pr558, pr568, pr578, pr616, pr626, pr636, pr646, pr656, pr666, pr676, pr686, pr696, pr706,
      pr716, pr726, pr736, pr746, pr756, pr766, pr776, pr786, pr796, pr806, pr844, pr854, pr864,
      pr874, pr884, pr894, pr904, pr914, pr924, pr934, pr944, pr954, pr964, pr974, pr984, pr994,
      pr1004, pr1014, pr1024, pr1034, pr1072, pr1082, pr1092, pr1102, pr1112, pr1122, pr1132,
      pr1142, pr1152, pr1162, pr1172, pr1182, pr1192, pr1202, pr1212, pr1222, pr1232, pr1242,
      pr1252, pr1262, pr1300, pr1310, pr1320, pr1330, pr1340, pr1350, pr1360, pr1370, pr1380,
      pr1390, pr1400, pr1410, pr1420, pr1430, pr1440, pr1450, pr1460, pr1470, pr1480, pr1490,
      pr1528, pr1538, pr1548, pr1558, pr1568, pr1578, pr1588, pr1598, pr1608, pr1618, pr1628,
      pr1638, pr1648, pr1658, pr1668, pr1678, pr1688, pr1698, pr1708, pr1718, pr1756, pr1766,
      pr1776, pr1786, pr1796, pr1806, pr1816, pr1826, pr1836, pr1846, pr1856, pr1866, pr1876,
      pr1886, pr1896, pr1906, pr1916, pr1926, pr1936, pr1946, -, -⟩ :=
    «Fixed::transpose20x8».obs ev
  have hv : rows.map encVec = [x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13, x_r14, x_r15, x_r16, x_r17, x_r18, x_r19] :=
    Aiur.Value.tuple.inj hv11
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, rfl⟩ := list_eq20 (by simpa using congrArg List.length hv)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv
  obtain rfl := proj_encVec pr160
  obtain rfl := proj_encVec pr170
  obtain rfl := proj_encVec pr180
  obtain rfl := proj_encVec pr190
  obtain rfl := proj_encVec pr200
  obtain rfl := proj_encVec pr210
  obtain rfl := proj_encVec pr220
  obtain rfl := proj_encVec pr230
  obtain rfl := proj_encVec pr240
  obtain rfl := proj_encVec pr250
  obtain rfl := proj_encVec pr260
  obtain rfl := proj_encVec pr270
  obtain rfl := proj_encVec pr280
  obtain rfl := proj_encVec pr290
  obtain rfl := proj_encVec pr300
  obtain rfl := proj_encVec pr310
  obtain rfl := proj_encVec pr320
  obtain rfl := proj_encVec pr330
  obtain rfl := proj_encVec pr340
  obtain rfl := proj_encVec pr350
  obtain rfl := proj_encVec pr388
  obtain rfl := proj_encVec pr398
  obtain rfl := proj_encVec pr408
  obtain rfl := proj_encVec pr418
  obtain rfl := proj_encVec pr428
  obtain rfl := proj_encVec pr438
  obtain rfl := proj_encVec pr448
  obtain rfl := proj_encVec pr458
  obtain rfl := proj_encVec pr468
  obtain rfl := proj_encVec pr478
  obtain rfl := proj_encVec pr488
  obtain rfl := proj_encVec pr498
  obtain rfl := proj_encVec pr508
  obtain rfl := proj_encVec pr518
  obtain rfl := proj_encVec pr528
  obtain rfl := proj_encVec pr538
  obtain rfl := proj_encVec pr548
  obtain rfl := proj_encVec pr558
  obtain rfl := proj_encVec pr568
  obtain rfl := proj_encVec pr578
  obtain rfl := proj_encVec pr616
  obtain rfl := proj_encVec pr626
  obtain rfl := proj_encVec pr636
  obtain rfl := proj_encVec pr646
  obtain rfl := proj_encVec pr656
  obtain rfl := proj_encVec pr666
  obtain rfl := proj_encVec pr676
  obtain rfl := proj_encVec pr686
  obtain rfl := proj_encVec pr696
  obtain rfl := proj_encVec pr706
  obtain rfl := proj_encVec pr716
  obtain rfl := proj_encVec pr726
  obtain rfl := proj_encVec pr736
  obtain rfl := proj_encVec pr746
  obtain rfl := proj_encVec pr756
  obtain rfl := proj_encVec pr766
  obtain rfl := proj_encVec pr776
  obtain rfl := proj_encVec pr786
  obtain rfl := proj_encVec pr796
  obtain rfl := proj_encVec pr806
  obtain rfl := proj_encVec pr844
  obtain rfl := proj_encVec pr854
  obtain rfl := proj_encVec pr864
  obtain rfl := proj_encVec pr874
  obtain rfl := proj_encVec pr884
  obtain rfl := proj_encVec pr894
  obtain rfl := proj_encVec pr904
  obtain rfl := proj_encVec pr914
  obtain rfl := proj_encVec pr924
  obtain rfl := proj_encVec pr934
  obtain rfl := proj_encVec pr944
  obtain rfl := proj_encVec pr954
  obtain rfl := proj_encVec pr964
  obtain rfl := proj_encVec pr974
  obtain rfl := proj_encVec pr984
  obtain rfl := proj_encVec pr994
  obtain rfl := proj_encVec pr1004
  obtain rfl := proj_encVec pr1014
  obtain rfl := proj_encVec pr1024
  obtain rfl := proj_encVec pr1034
  obtain rfl := proj_encVec pr1072
  obtain rfl := proj_encVec pr1082
  obtain rfl := proj_encVec pr1092
  obtain rfl := proj_encVec pr1102
  obtain rfl := proj_encVec pr1112
  obtain rfl := proj_encVec pr1122
  obtain rfl := proj_encVec pr1132
  obtain rfl := proj_encVec pr1142
  obtain rfl := proj_encVec pr1152
  obtain rfl := proj_encVec pr1162
  obtain rfl := proj_encVec pr1172
  obtain rfl := proj_encVec pr1182
  obtain rfl := proj_encVec pr1192
  obtain rfl := proj_encVec pr1202
  obtain rfl := proj_encVec pr1212
  obtain rfl := proj_encVec pr1222
  obtain rfl := proj_encVec pr1232
  obtain rfl := proj_encVec pr1242
  obtain rfl := proj_encVec pr1252
  obtain rfl := proj_encVec pr1262
  obtain rfl := proj_encVec pr1300
  obtain rfl := proj_encVec pr1310
  obtain rfl := proj_encVec pr1320
  obtain rfl := proj_encVec pr1330
  obtain rfl := proj_encVec pr1340
  obtain rfl := proj_encVec pr1350
  obtain rfl := proj_encVec pr1360
  obtain rfl := proj_encVec pr1370
  obtain rfl := proj_encVec pr1380
  obtain rfl := proj_encVec pr1390
  obtain rfl := proj_encVec pr1400
  obtain rfl := proj_encVec pr1410
  obtain rfl := proj_encVec pr1420
  obtain rfl := proj_encVec pr1430
  obtain rfl := proj_encVec pr1440
  obtain rfl := proj_encVec pr1450
  obtain rfl := proj_encVec pr1460
  obtain rfl := proj_encVec pr1470
  obtain rfl := proj_encVec pr1480
  obtain rfl := proj_encVec pr1490
  obtain rfl := proj_encVec pr1528
  obtain rfl := proj_encVec pr1538
  obtain rfl := proj_encVec pr1548
  obtain rfl := proj_encVec pr1558
  obtain rfl := proj_encVec pr1568
  obtain rfl := proj_encVec pr1578
  obtain rfl := proj_encVec pr1588
  obtain rfl := proj_encVec pr1598
  obtain rfl := proj_encVec pr1608
  obtain rfl := proj_encVec pr1618
  obtain rfl := proj_encVec pr1628
  obtain rfl := proj_encVec pr1638
  obtain rfl := proj_encVec pr1648
  obtain rfl := proj_encVec pr1658
  obtain rfl := proj_encVec pr1668
  obtain rfl := proj_encVec pr1678
  obtain rfl := proj_encVec pr1688
  obtain rfl := proj_encVec pr1698
  obtain rfl := proj_encVec pr1708
  obtain rfl := proj_encVec pr1718
  obtain rfl := proj_encVec pr1756
  obtain rfl := proj_encVec pr1766
  obtain rfl := proj_encVec pr1776
  obtain rfl := proj_encVec pr1786
  obtain rfl := proj_encVec pr1796
  obtain rfl := proj_encVec pr1806
  obtain rfl := proj_encVec pr1816
  obtain rfl := proj_encVec pr1826
  obtain rfl := proj_encVec pr1836
  obtain rfl := proj_encVec pr1846
  obtain rfl := proj_encVec pr1856
  obtain rfl := proj_encVec pr1866
  obtain rfl := proj_encVec pr1876
  obtain rfl := proj_encVec pr1886
  obtain rfl := proj_encVec pr1896
  obtain rfl := proj_encVec pr1906
  obtain rfl := proj_encVec pr1916
  obtain rfl := proj_encVec pr1926
  obtain rfl := proj_encVec pr1936
  obtain rfl := proj_encVec pr1946
  subst he123
  rw [transposeN_eq_cols]
  rfl

/-- **`Fixed::transpose20x11` is `transposeN 11`** on a 20-row matrix. The path binds the rows and
projects every entry; a projection that succeeds reads the row's entry. -/
theorem transpose20x11_spec {n : ℕ} (hn : n = 11) {rows : List (List IxAICore.Fx)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::transpose20x11" [encMat rows] h r h' calls) :
    r = encMat (IxAICore.transposeN n rows) := by
  subst hn
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13,
      x_r14, x_r15, x_r16, x_r17, x_r18, x_r19, v135, v136, v137, v138, v139, v140, v141, v142,
      v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v363, v364, v365,
      v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, v379, v380,
      v381, v382, v591, v592, v593, v594, v595, v596, v597, v598, v599, v600, v601, v602, v603,
      v604, v605, v606, v607, v608, v609, v610, v819, v820, v821, v822, v823, v824, v825, v826,
      v827, v828, v829, v830, v831, v832, v833, v834, v835, v836, v837, v838, v1047, v1048,
      v1049, v1050, v1051, v1052, v1053, v1054, v1055, v1056, v1057, v1058, v1059, v1060, v1061,
      v1062, v1063, v1064, v1065, v1066, v1275, v1276, v1277, v1278, v1279, v1280, v1281, v1282,
      v1283, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1503,
      v1504, v1505, v1506, v1507, v1508, v1509, v1510, v1511, v1512, v1513, v1514, v1515, v1516,
      v1517, v1518, v1519, v1520, v1521, v1522, v1731, v1732, v1733, v1734, v1735, v1736, v1737,
      v1738, v1739, v1740, v1741, v1742, v1743, v1744, v1745, v1746, v1747, v1748, v1749, v1750,
      v1959, v1960, v1961, v1962, v1963, v1964, v1965, v1966, v1967, v1968, v1969, v1970, v1971,
      v1972, v1973, v1974, v1975, v1976, v1977, v1978, v2187, v2188, v2189, v2190, v2191, v2192,
      v2193, v2194, v2195, v2196, v2197, v2198, v2199, v2200, v2201, v2202, v2203, v2204, v2205,
      v2206, v2415, v2416, v2417, v2418, v2419, v2420, v2421, v2422, v2423, v2424, v2425, v2426,
      v2427, v2428, v2429, v2430, v2431, v2432, v2433, v2434, hv11, he126, pr163, pr173, pr183,
      pr193, pr203, pr213, pr223, pr233, pr243, pr253, pr263, pr273, pr283, pr293, pr303, pr313,
      pr323, pr333, pr343, pr353, pr391, pr401, pr411, pr421, pr431, pr441, pr451, pr461, pr471,
      pr481, pr491, pr501, pr511, pr521, pr531, pr541, pr551, pr561, pr571, pr581, pr619, pr629,
      pr639, pr649, pr659, pr669, pr679, pr689, pr699, pr709, pr719, pr729, pr739, pr749, pr759,
      pr769, pr779, pr789, pr799, pr809, pr847, pr857, pr867, pr877, pr887, pr897, pr907, pr917,
      pr927, pr937, pr947, pr957, pr967, pr977, pr987, pr997, pr1007, pr1017, pr1027, pr1037,
      pr1075, pr1085, pr1095, pr1105, pr1115, pr1125, pr1135, pr1145, pr1155, pr1165, pr1175,
      pr1185, pr1195, pr1205, pr1215, pr1225, pr1235, pr1245, pr1255, pr1265, pr1303, pr1313,
      pr1323, pr1333, pr1343, pr1353, pr1363, pr1373, pr1383, pr1393, pr1403, pr1413, pr1423,
      pr1433, pr1443, pr1453, pr1463, pr1473, pr1483, pr1493, pr1531, pr1541, pr1551, pr1561,
      pr1571, pr1581, pr1591, pr1601, pr1611, pr1621, pr1631, pr1641, pr1651, pr1661, pr1671,
      pr1681, pr1691, pr1701, pr1711, pr1721, pr1759, pr1769, pr1779, pr1789, pr1799, pr1809,
      pr1819, pr1829, pr1839, pr1849, pr1859, pr1869, pr1879, pr1889, pr1899, pr1909, pr1919,
      pr1929, pr1939, pr1949, pr1987, pr1997, pr2007, pr2017, pr2027, pr2037, pr2047, pr2057,
      pr2067, pr2077, pr2087, pr2097, pr2107, pr2117, pr2127, pr2137, pr2147, pr2157, pr2167,
      pr2177, pr2215, pr2225, pr2235, pr2245, pr2255, pr2265, pr2275, pr2285, pr2295, pr2305,
      pr2315, pr2325, pr2335, pr2345, pr2355, pr2365, pr2375, pr2385, pr2395, pr2405, pr2443,
      pr2453, pr2463, pr2473, pr2483, pr2493, pr2503, pr2513, pr2523, pr2533, pr2543, pr2553,
      pr2563, pr2573, pr2583, pr2593, pr2603, pr2613, pr2623, pr2633, -, -⟩ :=
    «Fixed::transpose20x11».obs ev
  have hv : rows.map encVec = [x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13, x_r14, x_r15, x_r16, x_r17, x_r18, x_r19] :=
    Aiur.Value.tuple.inj hv11
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, rfl⟩ := list_eq20 (by simpa using congrArg List.length hv)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv
  obtain rfl := proj_encVec pr163
  obtain rfl := proj_encVec pr173
  obtain rfl := proj_encVec pr183
  obtain rfl := proj_encVec pr193
  obtain rfl := proj_encVec pr203
  obtain rfl := proj_encVec pr213
  obtain rfl := proj_encVec pr223
  obtain rfl := proj_encVec pr233
  obtain rfl := proj_encVec pr243
  obtain rfl := proj_encVec pr253
  obtain rfl := proj_encVec pr263
  obtain rfl := proj_encVec pr273
  obtain rfl := proj_encVec pr283
  obtain rfl := proj_encVec pr293
  obtain rfl := proj_encVec pr303
  obtain rfl := proj_encVec pr313
  obtain rfl := proj_encVec pr323
  obtain rfl := proj_encVec pr333
  obtain rfl := proj_encVec pr343
  obtain rfl := proj_encVec pr353
  obtain rfl := proj_encVec pr391
  obtain rfl := proj_encVec pr401
  obtain rfl := proj_encVec pr411
  obtain rfl := proj_encVec pr421
  obtain rfl := proj_encVec pr431
  obtain rfl := proj_encVec pr441
  obtain rfl := proj_encVec pr451
  obtain rfl := proj_encVec pr461
  obtain rfl := proj_encVec pr471
  obtain rfl := proj_encVec pr481
  obtain rfl := proj_encVec pr491
  obtain rfl := proj_encVec pr501
  obtain rfl := proj_encVec pr511
  obtain rfl := proj_encVec pr521
  obtain rfl := proj_encVec pr531
  obtain rfl := proj_encVec pr541
  obtain rfl := proj_encVec pr551
  obtain rfl := proj_encVec pr561
  obtain rfl := proj_encVec pr571
  obtain rfl := proj_encVec pr581
  obtain rfl := proj_encVec pr619
  obtain rfl := proj_encVec pr629
  obtain rfl := proj_encVec pr639
  obtain rfl := proj_encVec pr649
  obtain rfl := proj_encVec pr659
  obtain rfl := proj_encVec pr669
  obtain rfl := proj_encVec pr679
  obtain rfl := proj_encVec pr689
  obtain rfl := proj_encVec pr699
  obtain rfl := proj_encVec pr709
  obtain rfl := proj_encVec pr719
  obtain rfl := proj_encVec pr729
  obtain rfl := proj_encVec pr739
  obtain rfl := proj_encVec pr749
  obtain rfl := proj_encVec pr759
  obtain rfl := proj_encVec pr769
  obtain rfl := proj_encVec pr779
  obtain rfl := proj_encVec pr789
  obtain rfl := proj_encVec pr799
  obtain rfl := proj_encVec pr809
  obtain rfl := proj_encVec pr847
  obtain rfl := proj_encVec pr857
  obtain rfl := proj_encVec pr867
  obtain rfl := proj_encVec pr877
  obtain rfl := proj_encVec pr887
  obtain rfl := proj_encVec pr897
  obtain rfl := proj_encVec pr907
  obtain rfl := proj_encVec pr917
  obtain rfl := proj_encVec pr927
  obtain rfl := proj_encVec pr937
  obtain rfl := proj_encVec pr947
  obtain rfl := proj_encVec pr957
  obtain rfl := proj_encVec pr967
  obtain rfl := proj_encVec pr977
  obtain rfl := proj_encVec pr987
  obtain rfl := proj_encVec pr997
  obtain rfl := proj_encVec pr1007
  obtain rfl := proj_encVec pr1017
  obtain rfl := proj_encVec pr1027
  obtain rfl := proj_encVec pr1037
  obtain rfl := proj_encVec pr1075
  obtain rfl := proj_encVec pr1085
  obtain rfl := proj_encVec pr1095
  obtain rfl := proj_encVec pr1105
  obtain rfl := proj_encVec pr1115
  obtain rfl := proj_encVec pr1125
  obtain rfl := proj_encVec pr1135
  obtain rfl := proj_encVec pr1145
  obtain rfl := proj_encVec pr1155
  obtain rfl := proj_encVec pr1165
  obtain rfl := proj_encVec pr1175
  obtain rfl := proj_encVec pr1185
  obtain rfl := proj_encVec pr1195
  obtain rfl := proj_encVec pr1205
  obtain rfl := proj_encVec pr1215
  obtain rfl := proj_encVec pr1225
  obtain rfl := proj_encVec pr1235
  obtain rfl := proj_encVec pr1245
  obtain rfl := proj_encVec pr1255
  obtain rfl := proj_encVec pr1265
  obtain rfl := proj_encVec pr1303
  obtain rfl := proj_encVec pr1313
  obtain rfl := proj_encVec pr1323
  obtain rfl := proj_encVec pr1333
  obtain rfl := proj_encVec pr1343
  obtain rfl := proj_encVec pr1353
  obtain rfl := proj_encVec pr1363
  obtain rfl := proj_encVec pr1373
  obtain rfl := proj_encVec pr1383
  obtain rfl := proj_encVec pr1393
  obtain rfl := proj_encVec pr1403
  obtain rfl := proj_encVec pr1413
  obtain rfl := proj_encVec pr1423
  obtain rfl := proj_encVec pr1433
  obtain rfl := proj_encVec pr1443
  obtain rfl := proj_encVec pr1453
  obtain rfl := proj_encVec pr1463
  obtain rfl := proj_encVec pr1473
  obtain rfl := proj_encVec pr1483
  obtain rfl := proj_encVec pr1493
  obtain rfl := proj_encVec pr1531
  obtain rfl := proj_encVec pr1541
  obtain rfl := proj_encVec pr1551
  obtain rfl := proj_encVec pr1561
  obtain rfl := proj_encVec pr1571
  obtain rfl := proj_encVec pr1581
  obtain rfl := proj_encVec pr1591
  obtain rfl := proj_encVec pr1601
  obtain rfl := proj_encVec pr1611
  obtain rfl := proj_encVec pr1621
  obtain rfl := proj_encVec pr1631
  obtain rfl := proj_encVec pr1641
  obtain rfl := proj_encVec pr1651
  obtain rfl := proj_encVec pr1661
  obtain rfl := proj_encVec pr1671
  obtain rfl := proj_encVec pr1681
  obtain rfl := proj_encVec pr1691
  obtain rfl := proj_encVec pr1701
  obtain rfl := proj_encVec pr1711
  obtain rfl := proj_encVec pr1721
  obtain rfl := proj_encVec pr1759
  obtain rfl := proj_encVec pr1769
  obtain rfl := proj_encVec pr1779
  obtain rfl := proj_encVec pr1789
  obtain rfl := proj_encVec pr1799
  obtain rfl := proj_encVec pr1809
  obtain rfl := proj_encVec pr1819
  obtain rfl := proj_encVec pr1829
  obtain rfl := proj_encVec pr1839
  obtain rfl := proj_encVec pr1849
  obtain rfl := proj_encVec pr1859
  obtain rfl := proj_encVec pr1869
  obtain rfl := proj_encVec pr1879
  obtain rfl := proj_encVec pr1889
  obtain rfl := proj_encVec pr1899
  obtain rfl := proj_encVec pr1909
  obtain rfl := proj_encVec pr1919
  obtain rfl := proj_encVec pr1929
  obtain rfl := proj_encVec pr1939
  obtain rfl := proj_encVec pr1949
  obtain rfl := proj_encVec pr1987
  obtain rfl := proj_encVec pr1997
  obtain rfl := proj_encVec pr2007
  obtain rfl := proj_encVec pr2017
  obtain rfl := proj_encVec pr2027
  obtain rfl := proj_encVec pr2037
  obtain rfl := proj_encVec pr2047
  obtain rfl := proj_encVec pr2057
  obtain rfl := proj_encVec pr2067
  obtain rfl := proj_encVec pr2077
  obtain rfl := proj_encVec pr2087
  obtain rfl := proj_encVec pr2097
  obtain rfl := proj_encVec pr2107
  obtain rfl := proj_encVec pr2117
  obtain rfl := proj_encVec pr2127
  obtain rfl := proj_encVec pr2137
  obtain rfl := proj_encVec pr2147
  obtain rfl := proj_encVec pr2157
  obtain rfl := proj_encVec pr2167
  obtain rfl := proj_encVec pr2177
  obtain rfl := proj_encVec pr2215
  obtain rfl := proj_encVec pr2225
  obtain rfl := proj_encVec pr2235
  obtain rfl := proj_encVec pr2245
  obtain rfl := proj_encVec pr2255
  obtain rfl := proj_encVec pr2265
  obtain rfl := proj_encVec pr2275
  obtain rfl := proj_encVec pr2285
  obtain rfl := proj_encVec pr2295
  obtain rfl := proj_encVec pr2305
  obtain rfl := proj_encVec pr2315
  obtain rfl := proj_encVec pr2325
  obtain rfl := proj_encVec pr2335
  obtain rfl := proj_encVec pr2345
  obtain rfl := proj_encVec pr2355
  obtain rfl := proj_encVec pr2365
  obtain rfl := proj_encVec pr2375
  obtain rfl := proj_encVec pr2385
  obtain rfl := proj_encVec pr2395
  obtain rfl := proj_encVec pr2405
  obtain rfl := proj_encVec pr2443
  obtain rfl := proj_encVec pr2453
  obtain rfl := proj_encVec pr2463
  obtain rfl := proj_encVec pr2473
  obtain rfl := proj_encVec pr2483
  obtain rfl := proj_encVec pr2493
  obtain rfl := proj_encVec pr2503
  obtain rfl := proj_encVec pr2513
  obtain rfl := proj_encVec pr2523
  obtain rfl := proj_encVec pr2533
  obtain rfl := proj_encVec pr2543
  obtain rfl := proj_encVec pr2553
  obtain rfl := proj_encVec pr2563
  obtain rfl := proj_encVec pr2573
  obtain rfl := proj_encVec pr2583
  obtain rfl := proj_encVec pr2593
  obtain rfl := proj_encVec pr2603
  obtain rfl := proj_encVec pr2613
  obtain rfl := proj_encVec pr2623
  obtain rfl := proj_encVec pr2633
  subst he126
  rw [transposeN_eq_cols]
  rfl

/-! ## Updates -/

/- Consumes `«Fixed::update_row8».Path.run`: 64 binders (`x_w0` … `cs553`), then the facts
   hv11 : x_row = (.tuple [x_w0, x_w1, …, x_w7])
   hv63 : x_cols = (.tuple [x_c0, x_c1, …, x_c7])
   he115 : r = (.tuple [v107, v108, …, v114])
   ev156 : ObsFn W "Fixed::dot20" [x_d, x_c0] h v130 m146 cs154
   ev127 : ObsFn W "Fixed::upd" [x_w0, x_lr, v130] m146 v107 m117 cs125
   ev213 : ObsFn W "Fixed::dot20" [x_d, x_c1] m117 v187 m203 cs211
   ev184 : ObsFn W "Fixed::upd" [x_w1, x_lr, v187] m203 v108 m174 cs182
   ev270 : ObsFn W "Fixed::dot20" [x_d, x_c2] m174 v244 m260 cs268
   ev241 : ObsFn W "Fixed::upd" [x_w2, x_lr, v244] m260 v109 m231 cs239
   ev327 : ObsFn W "Fixed::dot20" [x_d, x_c3] m231 v301 m317 cs325
   ev298 : ObsFn W "Fixed::upd" [x_w3, x_lr, v301] m317 v110 m288 cs296
   ev384 : ObsFn W "Fixed::dot20" [x_d, x_c4] m288 v358 m374 cs382
   ev355 : ObsFn W "Fixed::upd" [x_w4, x_lr, v358] m374 v111 m345 cs353
   ev441 : ObsFn W "Fixed::dot20" [x_d, x_c5] m345 v415 m431 cs439
   ev412 : ObsFn W "Fixed::upd" [x_w5, x_lr, v415] m431 v112 m402 cs410
   ev498 : ObsFn W "Fixed::dot20" [x_d, x_c6] m402 v472 m488 cs496
   ev469 : ObsFn W "Fixed::upd" [x_w6, x_lr, v472] m488 v113 m459 cs467
   ev555 : ObsFn W "Fixed::dot20" [x_d, x_c7] m459 v529 m545 cs553
   ev526 : ObsFn W "Fixed::upd" [x_w7, x_lr, v529] m545 v114 m516 cs524
   he572 : h' = m516  (unused)
   hc573 : calls = ...  (unused) -/
/-- **`Fixed::update_row8` updates one row**: `upd w (Fx.dot d col)` for each weight and column,
the row function of `Model.step`. -/
theorem update_row8_spec {row d : List IxAICore.Fx} {cols : List (List IxAICore.Fx)} {lr :
    IxAICore.Fx}
    (hrow : row.length = 8) (hd : d.length = 20) (hcols : cols.length = 8)
    (hc : ∀ c ∈ cols, c.length = 20) (hrw : VecW row) (hb : RowBounds lr d cols) {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_row8" [encVec row, encVec d, encMat cols, fxVal lr] h r h' calls) :
    r = encVec (updRow lr row d cols) ∧ VecW (updRow lr row d cols) := by
  obtain ⟨w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, rfl⟩ := list_eq8 hrow
  obtain ⟨c_0, c_1, c_2, c_3, c_4, c_5, c_6, c_7, rfl⟩ := list_eq8 hcols
  obtain ⟨x_w0, x_w1, x_w2, x_w3, x_w4, x_w5, x_w6, x_w7, x_c0, x_c1, x_c2, x_c3, x_c4, x_c5, x_c6,
      x_c7, v107, v108, v109, v110, v111, v112, v113, v114, m117, cs125, v130, m146, cs154, m174,
      cs182, v187, m203, cs211, m231, cs239, v244, m260, cs268, m288, cs296, v301, m317, cs325,
      m345, cs353, v358, m374, cs382, m402, cs410, v415, m431, cs439, m459, cs467, v472, m488,
      cs496, m516, cs524, v529, m545, cs553, hv11, hv63, he115, ev156, ev127, ev213, ev184, ev270,
      ev241, ev327, ev298, ev384, ev355, ev441, ev412, ev498, ev469, ev555, ev526, -, -⟩ :=
    «Fixed::update_row8».obs ev
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv63
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv63
  obtain rfl := dot20_spec hd (hc c_0 (by simp)) (hb c_0 (by simp)).1 ev156
  obtain ⟨rfl, k_0⟩ := upd_spec (hrw w_0 (by simp)) (hb c_0 (by simp)).2 ev127
  obtain rfl := dot20_spec hd (hc c_1 (by simp)) (hb c_1 (by simp)).1 ev213
  obtain ⟨rfl, k_1⟩ := upd_spec (hrw w_1 (by simp)) (hb c_1 (by simp)).2 ev184
  obtain rfl := dot20_spec hd (hc c_2 (by simp)) (hb c_2 (by simp)).1 ev270
  obtain ⟨rfl, k_2⟩ := upd_spec (hrw w_2 (by simp)) (hb c_2 (by simp)).2 ev241
  obtain rfl := dot20_spec hd (hc c_3 (by simp)) (hb c_3 (by simp)).1 ev327
  obtain ⟨rfl, k_3⟩ := upd_spec (hrw w_3 (by simp)) (hb c_3 (by simp)).2 ev298
  obtain rfl := dot20_spec hd (hc c_4 (by simp)) (hb c_4 (by simp)).1 ev384
  obtain ⟨rfl, k_4⟩ := upd_spec (hrw w_4 (by simp)) (hb c_4 (by simp)).2 ev355
  obtain rfl := dot20_spec hd (hc c_5 (by simp)) (hb c_5 (by simp)).1 ev441
  obtain ⟨rfl, k_5⟩ := upd_spec (hrw w_5 (by simp)) (hb c_5 (by simp)).2 ev412
  obtain rfl := dot20_spec hd (hc c_6 (by simp)) (hb c_6 (by simp)).1 ev498
  obtain ⟨rfl, k_6⟩ := upd_spec (hrw w_6 (by simp)) (hb c_6 (by simp)).2 ev469
  obtain rfl := dot20_spec hd (hc c_7 (by simp)) (hb c_7 (by simp)).1 ev555
  obtain ⟨rfl, k_7⟩ := upd_spec (hrw w_7 (by simp)) (hb c_7 (by simp)).2 ev526
  subst he115
  refine ⟨rfl, ?_⟩
  unfold VecW
  intro a ha
  simp only [updRow, List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/- Consumes `«Fixed::update_row16».Path.run`: 128 binders (`x_w0` … `cs1097`), then the facts
   hv11 : x_row = (.tuple [x_w0, x_w1, …, x_w15])
   hv103 : x_cols = (.tuple [x_c0, x_c1, …, x_c15])
   he203 : r = (.tuple [v187, v188, …, v202])
   ev244 : ObsFn W "Fixed::dot20" [x_d, x_c0] h v218 m234 cs242
   ev215 : ObsFn W "Fixed::upd" [x_w0, x_lr, v218] m234 v187 m205 cs213
   ev301 : ObsFn W "Fixed::dot20" [x_d, x_c1] m205 v275 m291 cs299
   ev272 : ObsFn W "Fixed::upd" [x_w1, x_lr, v275] m291 v188 m262 cs270
   ev358 : ObsFn W "Fixed::dot20" [x_d, x_c2] m262 v332 m348 cs356
   ev329 : ObsFn W "Fixed::upd" [x_w2, x_lr, v332] m348 v189 m319 cs327
   ev415 : ObsFn W "Fixed::dot20" [x_d, x_c3] m319 v389 m405 cs413
   ev386 : ObsFn W "Fixed::upd" [x_w3, x_lr, v389] m405 v190 m376 cs384
   ev472 : ObsFn W "Fixed::dot20" [x_d, x_c4] m376 v446 m462 cs470
   ev443 : ObsFn W "Fixed::upd" [x_w4, x_lr, v446] m462 v191 m433 cs441
   ev529 : ObsFn W "Fixed::dot20" [x_d, x_c5] m433 v503 m519 cs527
   ev500 : ObsFn W "Fixed::upd" [x_w5, x_lr, v503] m519 v192 m490 cs498
   ev586 : ObsFn W "Fixed::dot20" [x_d, x_c6] m490 v560 m576 cs584
   ev557 : ObsFn W "Fixed::upd" [x_w6, x_lr, v560] m576 v193 m547 cs555
   ev643 : ObsFn W "Fixed::dot20" [x_d, x_c7] m547 v617 m633 cs641
   ev614 : ObsFn W "Fixed::upd" [x_w7, x_lr, v617] m633 v194 m604 cs612
   ev700 : ObsFn W "Fixed::dot20" [x_d, x_c8] m604 v674 m690 cs698
   ev671 : ObsFn W "Fixed::upd" [x_w8, x_lr, v674] m690 v195 m661 cs669
   ev757 : ObsFn W "Fixed::dot20" [x_d, x_c9] m661 v731 m747 cs755
   ev728 : ObsFn W "Fixed::upd" [x_w9, x_lr, v731] m747 v196 m718 cs726
   ev814 : ObsFn W "Fixed::dot20" [x_d, x_c10] m718 v788 m804 cs812
   ev785 : ObsFn W "Fixed::upd" [x_w10, x_lr, v788] m804 v197 m775 cs783
   ev871 : ObsFn W "Fixed::dot20" [x_d, x_c11] m775 v845 m861 cs869
   ev842 : ObsFn W "Fixed::upd" [x_w11, x_lr, v845] m861 v198 m832 cs840
   ev928 : ObsFn W "Fixed::dot20" [x_d, x_c12] m832 v902 m918 cs926
   ev899 : ObsFn W "Fixed::upd" [x_w12, x_lr, v902] m918 v199 m889 cs897
   ev985 : ObsFn W "Fixed::dot20" [x_d, x_c13] m889 v959 m975 cs983
   ev956 : ObsFn W "Fixed::upd" [x_w13, x_lr, v959] m975 v200 m946 cs954
   ev1042 : ObsFn W "Fixed::dot20" [x_d, x_c14] m946 v1016 m1032 cs1040
   ev1013 : ObsFn W "Fixed::upd" [x_w14, x_lr, v1016] m1032 v201 m1003 cs1011
   ev1099 : ObsFn W "Fixed::dot20" [x_d, x_c15] m1003 v1073 m1089 cs1097
   ev1070 : ObsFn W "Fixed::upd" [x_w15, x_lr, v1073] m1089 v202 m1060 cs1068
   he1116 : h' = m1060  (unused)
   hc1117 : calls = ...  (unused) -/
/-- **`Fixed::update_row16` updates one row**: `upd w (Fx.dot d col)` for each weight and column,
the row function of `Model.step`. -/
theorem update_row16_spec {row d : List IxAICore.Fx} {cols : List (List IxAICore.Fx)} {lr :
    IxAICore.Fx}
    (hrow : row.length = 16) (hd : d.length = 20) (hcols : cols.length = 16)
    (hc : ∀ c ∈ cols, c.length = 20) (hrw : VecW row) (hb : RowBounds lr d cols) {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_row16" [encVec row, encVec d, encMat cols, fxVal lr] h r h' calls)
        :
    r = encVec (updRow lr row d cols) ∧ VecW (updRow lr row d cols) := by
  obtain ⟨w_0, w_1, w_2, w_3, w_4, w_5, w_6, w_7, w_8, w_9, w_10, w_11, w_12, w_13, w_14, w_15,
      rfl⟩ := list_eq16 hrow
  obtain ⟨c_0, c_1, c_2, c_3, c_4, c_5, c_6, c_7, c_8, c_9, c_10, c_11, c_12, c_13, c_14, c_15,
      rfl⟩ := list_eq16 hcols
  obtain ⟨x_w0, x_w1, x_w2, x_w3, x_w4, x_w5, x_w6, x_w7, x_w8, x_w9, x_w10, x_w11, x_w12, x_w13,
      x_w14, x_w15, x_c0, x_c1, x_c2, x_c3, x_c4, x_c5, x_c6, x_c7, x_c8, x_c9, x_c10, x_c11, x_c12,
      x_c13, x_c14, x_c15, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198,
      v199, v200, v201, v202, m205, cs213, v218, m234, cs242, m262, cs270, v275, m291, cs299, m319,
      cs327, v332, m348, cs356, m376, cs384, v389, m405, cs413, m433, cs441, v446, m462, cs470,
      m490, cs498, v503, m519, cs527, m547, cs555, v560, m576, cs584, m604, cs612, v617, m633,
      cs641, m661, cs669, v674, m690, cs698, m718, cs726, v731, m747, cs755, m775, cs783, v788,
      m804, cs812, m832, cs840, v845, m861, cs869, m889, cs897, v902, m918, cs926, m946, cs954,
      v959, m975, cs983, m1003, cs1011, v1016, m1032, cs1040, m1060, cs1068, v1073, m1089, cs1097,
      hv11, hv103, he203, ev244, ev215, ev301, ev272, ev358, ev329, ev415, ev386, ev472, ev443,
      ev529, ev500, ev586, ev557, ev643, ev614, ev700, ev671, ev757, ev728, ev814, ev785, ev871,
      ev842, ev928, ev899, ev985, ev956, ev1042, ev1013, ev1099, ev1070, -, -⟩ :=
    «Fixed::update_row16».obs ev
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv103
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv103
  obtain rfl := dot20_spec hd (hc c_0 (by simp)) (hb c_0 (by simp)).1 ev244
  obtain ⟨rfl, k_0⟩ := upd_spec (hrw w_0 (by simp)) (hb c_0 (by simp)).2 ev215
  obtain rfl := dot20_spec hd (hc c_1 (by simp)) (hb c_1 (by simp)).1 ev301
  obtain ⟨rfl, k_1⟩ := upd_spec (hrw w_1 (by simp)) (hb c_1 (by simp)).2 ev272
  obtain rfl := dot20_spec hd (hc c_2 (by simp)) (hb c_2 (by simp)).1 ev358
  obtain ⟨rfl, k_2⟩ := upd_spec (hrw w_2 (by simp)) (hb c_2 (by simp)).2 ev329
  obtain rfl := dot20_spec hd (hc c_3 (by simp)) (hb c_3 (by simp)).1 ev415
  obtain ⟨rfl, k_3⟩ := upd_spec (hrw w_3 (by simp)) (hb c_3 (by simp)).2 ev386
  obtain rfl := dot20_spec hd (hc c_4 (by simp)) (hb c_4 (by simp)).1 ev472
  obtain ⟨rfl, k_4⟩ := upd_spec (hrw w_4 (by simp)) (hb c_4 (by simp)).2 ev443
  obtain rfl := dot20_spec hd (hc c_5 (by simp)) (hb c_5 (by simp)).1 ev529
  obtain ⟨rfl, k_5⟩ := upd_spec (hrw w_5 (by simp)) (hb c_5 (by simp)).2 ev500
  obtain rfl := dot20_spec hd (hc c_6 (by simp)) (hb c_6 (by simp)).1 ev586
  obtain ⟨rfl, k_6⟩ := upd_spec (hrw w_6 (by simp)) (hb c_6 (by simp)).2 ev557
  obtain rfl := dot20_spec hd (hc c_7 (by simp)) (hb c_7 (by simp)).1 ev643
  obtain ⟨rfl, k_7⟩ := upd_spec (hrw w_7 (by simp)) (hb c_7 (by simp)).2 ev614
  obtain rfl := dot20_spec hd (hc c_8 (by simp)) (hb c_8 (by simp)).1 ev700
  obtain ⟨rfl, k_8⟩ := upd_spec (hrw w_8 (by simp)) (hb c_8 (by simp)).2 ev671
  obtain rfl := dot20_spec hd (hc c_9 (by simp)) (hb c_9 (by simp)).1 ev757
  obtain ⟨rfl, k_9⟩ := upd_spec (hrw w_9 (by simp)) (hb c_9 (by simp)).2 ev728
  obtain rfl := dot20_spec hd (hc c_10 (by simp)) (hb c_10 (by simp)).1 ev814
  obtain ⟨rfl, k_10⟩ := upd_spec (hrw w_10 (by simp)) (hb c_10 (by simp)).2 ev785
  obtain rfl := dot20_spec hd (hc c_11 (by simp)) (hb c_11 (by simp)).1 ev871
  obtain ⟨rfl, k_11⟩ := upd_spec (hrw w_11 (by simp)) (hb c_11 (by simp)).2 ev842
  obtain rfl := dot20_spec hd (hc c_12 (by simp)) (hb c_12 (by simp)).1 ev928
  obtain ⟨rfl, k_12⟩ := upd_spec (hrw w_12 (by simp)) (hb c_12 (by simp)).2 ev899
  obtain rfl := dot20_spec hd (hc c_13 (by simp)) (hb c_13 (by simp)).1 ev985
  obtain ⟨rfl, k_13⟩ := upd_spec (hrw w_13 (by simp)) (hb c_13 (by simp)).2 ev956
  obtain rfl := dot20_spec hd (hc c_14 (by simp)) (hb c_14 (by simp)).1 ev1042
  obtain ⟨rfl, k_14⟩ := upd_spec (hrw w_14 (by simp)) (hb c_14 (by simp)).2 ev1013
  obtain rfl := dot20_spec hd (hc c_15 (by simp)) (hb c_15 (by simp)).1 ev1099
  obtain ⟨rfl, k_15⟩ := upd_spec (hrw w_15 (by simp)) (hb c_15 (by simp)).2 ev1070
  subst he203
  refine ⟨rfl, ?_⟩
  unfold VecW
  intro a ha
  simp only [updRow, List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/- Consumes `«Fixed::update_w1».Path.run`: 80 binders (`x_r0` … `cs873`), then the facts
   hv11 : x_w1 = (.tuple [x_r0, x_r1, …, x_r15])
   hv103 : x_dzt = (.tuple [x_d0, x_d1, …, x_d15])
   he203 : r = (.tuple [v187, v188, …, v202])
   ev215 : ObsFn W "Fixed::update_row8" [x_r0, x_d0, x_xt, x_lr] h v187 m205 cs213
   ev259 : ObsFn W "Fixed::update_row8" [x_r1, x_d1, x_xt, x_lr] m205 v188 m249 cs257
   ev303 : ObsFn W "Fixed::update_row8" [x_r2, x_d2, x_xt, x_lr] m249 v189 m293 cs301
   ev347 : ObsFn W "Fixed::update_row8" [x_r3, x_d3, x_xt, x_lr] m293 v190 m337 cs345
   ev391 : ObsFn W "Fixed::update_row8" [x_r4, x_d4, x_xt, x_lr] m337 v191 m381 cs389
   ev435 : ObsFn W "Fixed::update_row8" [x_r5, x_d5, x_xt, x_lr] m381 v192 m425 cs433
   ev479 : ObsFn W "Fixed::update_row8" [x_r6, x_d6, x_xt, x_lr] m425 v193 m469 cs477
   ev523 : ObsFn W "Fixed::update_row8" [x_r7, x_d7, x_xt, x_lr] m469 v194 m513 cs521
   ev567 : ObsFn W "Fixed::update_row8" [x_r8, x_d8, x_xt, x_lr] m513 v195 m557 cs565
   ev611 : ObsFn W "Fixed::update_row8" [x_r9, x_d9, x_xt, x_lr] m557 v196 m601 cs609
   ev655 : ObsFn W "Fixed::update_row8" [x_r10, x_d10, x_xt, x_lr] m601 v197 m645 cs653
   ev699 : ObsFn W "Fixed::update_row8" [x_r11, x_d11, x_xt, x_lr] m645 v198 m689 cs697
   ev743 : ObsFn W "Fixed::update_row8" [x_r12, x_d12, x_xt, x_lr] m689 v199 m733 cs741
   ev787 : ObsFn W "Fixed::update_row8" [x_r13, x_d13, x_xt, x_lr] m733 v200 m777 cs785
   ev831 : ObsFn W "Fixed::update_row8" [x_r14, x_d14, x_xt, x_lr] m777 v201 m821 cs829
   ev875 : ObsFn W "Fixed::update_row8" [x_r15, x_d15, x_xt, x_lr] m821 v202 m865 cs873
   he908 : h' = m865  (unused)
   hc909 : calls = ...  (unused) -/
/-- **`Fixed::update_w1` is the field `w1` of `Model.step`**, from `dzT` and `xT`. -/
theorem update_w1_spec {w dzT xT : List (List IxAICore.Fx)} {lr : IxAICore.Fx}
    (hw : w.length = 16) (hrows : ∀ row ∈ w, row.length = 8) (hd : dzT.length = 16)
    (hdr : ∀ d ∈ dzT, d.length = 20) (hc : xT.length = 8)
    (hcr : ∀ c ∈ xT, c.length = 20) (hwb : MatW w) (hb : ∀ d ∈ dzT, RowBounds lr d xT)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_w1" [encMat w, encMat dzT, encMat xT, fxVal lr] h r h' calls) :
    r = encMat (List.zipWith (fun row d => updRow lr row d xT) w dzT) ∧
      MatW (List.zipWith (fun row d => updRow lr row d xT) w dzT) := by
  obtain ⟨r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7, r_8, r_9, r_10, r_11, r_12, r_13, r_14, r_15,
      rfl⟩ := list_eq16 hw
  obtain ⟨d_0, d_1, d_2, d_3, d_4, d_5, d_6, d_7, d_8, d_9, d_10, d_11, d_12, d_13, d_14, d_15,
      rfl⟩ := list_eq16 hd
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_r11, x_r12, x_r13,
      x_r14, x_r15, x_d0, x_d1, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7, x_d8, x_d9, x_d10, x_d11, x_d12,
      x_d13, x_d14, x_d15, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198,
      v199, v200, v201, v202, m205, cs213, m249, cs257, m293, cs301, m337, cs345, m381, cs389, m425,
      cs433, m469, cs477, m513, cs521, m557, cs565, m601, cs609, m645, cs653, m689, cs697, m733,
      cs741, m777, cs785, m821, cs829, m865, cs873, hv11, hv103, he203, ev215, ev259, ev303, ev347,
      ev391, ev435, ev479, ev523, ev567, ev611, ev655, ev699, ev743, ev787, ev831, ev875, -, -⟩ :=
    «Fixed::update_w1».obs ev
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv103
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv103
  obtain ⟨rfl, k_0⟩ := update_row8_spec (hrows r_0 (by simp)) (hdr d_0 (by simp)) hc hcr
    (hwb r_0 (by simp)) (hb d_0 (by simp)) ev215
  obtain ⟨rfl, k_1⟩ := update_row8_spec (hrows r_1 (by simp)) (hdr d_1 (by simp)) hc hcr
    (hwb r_1 (by simp)) (hb d_1 (by simp)) ev259
  obtain ⟨rfl, k_2⟩ := update_row8_spec (hrows r_2 (by simp)) (hdr d_2 (by simp)) hc hcr
    (hwb r_2 (by simp)) (hb d_2 (by simp)) ev303
  obtain ⟨rfl, k_3⟩ := update_row8_spec (hrows r_3 (by simp)) (hdr d_3 (by simp)) hc hcr
    (hwb r_3 (by simp)) (hb d_3 (by simp)) ev347
  obtain ⟨rfl, k_4⟩ := update_row8_spec (hrows r_4 (by simp)) (hdr d_4 (by simp)) hc hcr
    (hwb r_4 (by simp)) (hb d_4 (by simp)) ev391
  obtain ⟨rfl, k_5⟩ := update_row8_spec (hrows r_5 (by simp)) (hdr d_5 (by simp)) hc hcr
    (hwb r_5 (by simp)) (hb d_5 (by simp)) ev435
  obtain ⟨rfl, k_6⟩ := update_row8_spec (hrows r_6 (by simp)) (hdr d_6 (by simp)) hc hcr
    (hwb r_6 (by simp)) (hb d_6 (by simp)) ev479
  obtain ⟨rfl, k_7⟩ := update_row8_spec (hrows r_7 (by simp)) (hdr d_7 (by simp)) hc hcr
    (hwb r_7 (by simp)) (hb d_7 (by simp)) ev523
  obtain ⟨rfl, k_8⟩ := update_row8_spec (hrows r_8 (by simp)) (hdr d_8 (by simp)) hc hcr
    (hwb r_8 (by simp)) (hb d_8 (by simp)) ev567
  obtain ⟨rfl, k_9⟩ := update_row8_spec (hrows r_9 (by simp)) (hdr d_9 (by simp)) hc hcr
    (hwb r_9 (by simp)) (hb d_9 (by simp)) ev611
  obtain ⟨rfl, k_10⟩ := update_row8_spec (hrows r_10 (by simp)) (hdr d_10 (by simp)) hc hcr
    (hwb r_10 (by simp)) (hb d_10 (by simp)) ev655
  obtain ⟨rfl, k_11⟩ := update_row8_spec (hrows r_11 (by simp)) (hdr d_11 (by simp)) hc hcr
    (hwb r_11 (by simp)) (hb d_11 (by simp)) ev699
  obtain ⟨rfl, k_12⟩ := update_row8_spec (hrows r_12 (by simp)) (hdr d_12 (by simp)) hc hcr
    (hwb r_12 (by simp)) (hb d_12 (by simp)) ev743
  obtain ⟨rfl, k_13⟩ := update_row8_spec (hrows r_13 (by simp)) (hdr d_13 (by simp)) hc hcr
    (hwb r_13 (by simp)) (hb d_13 (by simp)) ev787
  obtain ⟨rfl, k_14⟩ := update_row8_spec (hrows r_14 (by simp)) (hdr d_14 (by simp)) hc hcr
    (hwb r_14 (by simp)) (hb d_14 (by simp)) ev831
  obtain ⟨rfl, k_15⟩ := update_row8_spec (hrows r_15 (by simp)) (hdr d_15 (by simp)) hc hcr
    (hwb r_15 (by simp)) (hb d_15 (by simp)) ev875
  subst he203
  refine ⟨rfl, ?_⟩
  unfold MatW
  intro a ha
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/- Consumes `«Fixed::update_w2».Path.run`: 55 binders (`x_r0` … `cs598`), then the facts
   hv11 : x_w2 = (.tuple [x_r0, x_r1, …, x_r10])
   hv78 : x_doutt = (.tuple [x_d0, x_d1, …, x_d10])
   he148 : r = (.tuple [v137, v138, …, v147])
   ev160 : ObsFn W "Fixed::update_row16" [x_r0, x_d0, x_ht, x_lr] h v137 m150 cs158
   ev204 : ObsFn W "Fixed::update_row16" [x_r1, x_d1, x_ht, x_lr] m150 v138 m194 cs202
   ev248 : ObsFn W "Fixed::update_row16" [x_r2, x_d2, x_ht, x_lr] m194 v139 m238 cs246
   ev292 : ObsFn W "Fixed::update_row16" [x_r3, x_d3, x_ht, x_lr] m238 v140 m282 cs290
   ev336 : ObsFn W "Fixed::update_row16" [x_r4, x_d4, x_ht, x_lr] m282 v141 m326 cs334
   ev380 : ObsFn W "Fixed::update_row16" [x_r5, x_d5, x_ht, x_lr] m326 v142 m370 cs378
   ev424 : ObsFn W "Fixed::update_row16" [x_r6, x_d6, x_ht, x_lr] m370 v143 m414 cs422
   ev468 : ObsFn W "Fixed::update_row16" [x_r7, x_d7, x_ht, x_lr] m414 v144 m458 cs466
   ev512 : ObsFn W "Fixed::update_row16" [x_r8, x_d8, x_ht, x_lr] m458 v145 m502 cs510
   ev556 : ObsFn W "Fixed::update_row16" [x_r9, x_d9, x_ht, x_lr] m502 v146 m546 cs554
   ev600 : ObsFn W "Fixed::update_row16" [x_r10, x_d10, x_ht, x_lr] m546 v147 m590 cs598
   he633 : h' = m590  (unused)
   hc634 : calls = ...  (unused) -/
/-- **`Fixed::update_w2` is the field `w2` of `Model.step`**, from `doutT` and `hT`. -/
theorem update_w2_spec {w doutT hT : List (List IxAICore.Fx)} {lr : IxAICore.Fx}
    (hw : w.length = 11) (hrows : ∀ row ∈ w, row.length = 16) (hd : doutT.length = 11)
    (hdr : ∀ d ∈ doutT, d.length = 20) (hc : hT.length = 16)
    (hcr : ∀ c ∈ hT, c.length = 20) (hwb : MatW w) (hb : ∀ d ∈ doutT, RowBounds lr d hT)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_w2" [encMat w, encMat doutT, encMat hT, fxVal lr] h r h' calls) :
    r = encMat (List.zipWith (fun row d => updRow lr row d hT) w doutT) ∧
      MatW (List.zipWith (fun row d => updRow lr row d hT) w doutT) := by
  obtain ⟨r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7, r_8, r_9, r_10, rfl⟩ := list_eq11 hw
  obtain ⟨d_0, d_1, d_2, d_3, d_4, d_5, d_6, d_7, d_8, d_9, d_10, rfl⟩ := list_eq11 hd
  obtain ⟨x_r0, x_r1, x_r2, x_r3, x_r4, x_r5, x_r6, x_r7, x_r8, x_r9, x_r10, x_d0, x_d1, x_d2, x_d3,
      x_d4, x_d5, x_d6, x_d7, x_d8, x_d9, x_d10, v137, v138, v139, v140, v141, v142, v143, v144,
      v145, v146, v147, m150, cs158, m194, cs202, m238, cs246, m282, cs290, m326, cs334, m370,
      cs378, m414, cs422, m458, cs466, m502, cs510, m546, cs554, m590, cs598, hv11, hv78, he148,
      ev160, ev204, ev248, ev292, ev336, ev380, ev424, ev468, ev512, ev556, ev600, -, -⟩ :=
    «Fixed::update_w2».obs ev
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv78
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv78
  obtain ⟨rfl, k_0⟩ := update_row16_spec (hrows r_0 (by simp)) (hdr d_0 (by simp)) hc hcr
    (hwb r_0 (by simp)) (hb d_0 (by simp)) ev160
  obtain ⟨rfl, k_1⟩ := update_row16_spec (hrows r_1 (by simp)) (hdr d_1 (by simp)) hc hcr
    (hwb r_1 (by simp)) (hb d_1 (by simp)) ev204
  obtain ⟨rfl, k_2⟩ := update_row16_spec (hrows r_2 (by simp)) (hdr d_2 (by simp)) hc hcr
    (hwb r_2 (by simp)) (hb d_2 (by simp)) ev248
  obtain ⟨rfl, k_3⟩ := update_row16_spec (hrows r_3 (by simp)) (hdr d_3 (by simp)) hc hcr
    (hwb r_3 (by simp)) (hb d_3 (by simp)) ev292
  obtain ⟨rfl, k_4⟩ := update_row16_spec (hrows r_4 (by simp)) (hdr d_4 (by simp)) hc hcr
    (hwb r_4 (by simp)) (hb d_4 (by simp)) ev336
  obtain ⟨rfl, k_5⟩ := update_row16_spec (hrows r_5 (by simp)) (hdr d_5 (by simp)) hc hcr
    (hwb r_5 (by simp)) (hb d_5 (by simp)) ev380
  obtain ⟨rfl, k_6⟩ := update_row16_spec (hrows r_6 (by simp)) (hdr d_6 (by simp)) hc hcr
    (hwb r_6 (by simp)) (hb d_6 (by simp)) ev424
  obtain ⟨rfl, k_7⟩ := update_row16_spec (hrows r_7 (by simp)) (hdr d_7 (by simp)) hc hcr
    (hwb r_7 (by simp)) (hb d_7 (by simp)) ev468
  obtain ⟨rfl, k_8⟩ := update_row16_spec (hrows r_8 (by simp)) (hdr d_8 (by simp)) hc hcr
    (hwb r_8 (by simp)) (hb d_8 (by simp)) ev512
  obtain ⟨rfl, k_9⟩ := update_row16_spec (hrows r_9 (by simp)) (hdr d_9 (by simp)) hc hcr
    (hwb r_9 (by simp)) (hb d_9 (by simp)) ev556
  obtain ⟨rfl, k_10⟩ := update_row16_spec (hrows r_10 (by simp)) (hdr d_10 (by simp)) hc hcr
    (hwb r_10 (by simp)) (hb d_10 (by simp)) ev600
  subst he148
  refine ⟨rfl, ?_⟩
  unfold MatW
  intro a ha
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/- Consumes `«Fixed::update_bias16».Path.run`: 128 binders (`x_b0` … `cs977`), then the facts
   hv11 : x_b = (.tuple [x_b0, x_b1, …, x_b15])
   hv103 : x_dt = (.tuple [x_d0, x_d1, …, x_d15])
   he203 : r = (.tuple [v187, v188, …, v202])
   ev244 : ObsFn W "Fixed::sum20" [x_d0] h v218 m234 cs242
   ev215 : ObsFn W "Fixed::upd" [x_b0, x_lr, v218] m234 v187 m205 cs213
   ev293 : ObsFn W "Fixed::sum20" [x_d1] m205 v267 m283 cs291
   ev264 : ObsFn W "Fixed::upd" [x_b1, x_lr, v267] m283 v188 m254 cs262
   ev342 : ObsFn W "Fixed::sum20" [x_d2] m254 v316 m332 cs340
   ev313 : ObsFn W "Fixed::upd" [x_b2, x_lr, v316] m332 v189 m303 cs311
   ev391 : ObsFn W "Fixed::sum20" [x_d3] m303 v365 m381 cs389
   ev362 : ObsFn W "Fixed::upd" [x_b3, x_lr, v365] m381 v190 m352 cs360
   ev440 : ObsFn W "Fixed::sum20" [x_d4] m352 v414 m430 cs438
   ev411 : ObsFn W "Fixed::upd" [x_b4, x_lr, v414] m430 v191 m401 cs409
   ev489 : ObsFn W "Fixed::sum20" [x_d5] m401 v463 m479 cs487
   ev460 : ObsFn W "Fixed::upd" [x_b5, x_lr, v463] m479 v192 m450 cs458
   ev538 : ObsFn W "Fixed::sum20" [x_d6] m450 v512 m528 cs536
   ev509 : ObsFn W "Fixed::upd" [x_b6, x_lr, v512] m528 v193 m499 cs507
   ev587 : ObsFn W "Fixed::sum20" [x_d7] m499 v561 m577 cs585
   ev558 : ObsFn W "Fixed::upd" [x_b7, x_lr, v561] m577 v194 m548 cs556
   ev636 : ObsFn W "Fixed::sum20" [x_d8] m548 v610 m626 cs634
   ev607 : ObsFn W "Fixed::upd" [x_b8, x_lr, v610] m626 v195 m597 cs605
   ev685 : ObsFn W "Fixed::sum20" [x_d9] m597 v659 m675 cs683
   ev656 : ObsFn W "Fixed::upd" [x_b9, x_lr, v659] m675 v196 m646 cs654
   ev734 : ObsFn W "Fixed::sum20" [x_d10] m646 v708 m724 cs732
   ev705 : ObsFn W "Fixed::upd" [x_b10, x_lr, v708] m724 v197 m695 cs703
   ev783 : ObsFn W "Fixed::sum20" [x_d11] m695 v757 m773 cs781
   ev754 : ObsFn W "Fixed::upd" [x_b11, x_lr, v757] m773 v198 m744 cs752
   ev832 : ObsFn W "Fixed::sum20" [x_d12] m744 v806 m822 cs830
   ev803 : ObsFn W "Fixed::upd" [x_b12, x_lr, v806] m822 v199 m793 cs801
   ev881 : ObsFn W "Fixed::sum20" [x_d13] m793 v855 m871 cs879
   ev852 : ObsFn W "Fixed::upd" [x_b13, x_lr, v855] m871 v200 m842 cs850
   ev930 : ObsFn W "Fixed::sum20" [x_d14] m842 v904 m920 cs928
   ev901 : ObsFn W "Fixed::upd" [x_b14, x_lr, v904] m920 v201 m891 cs899
   ev979 : ObsFn W "Fixed::sum20" [x_d15] m891 v953 m969 cs977
   ev950 : ObsFn W "Fixed::upd" [x_b15, x_lr, v953] m969 v202 m940 cs948
   he988 : h' = m940  (unused)
   hc989 : calls = ...  (unused) -/
/-- **`Fixed::update_bias16` is the field `b1` of `Model.step`**: `upd b (Fx.sum d)`. -/
theorem update_bias16_spec {b : List IxAICore.Fx} {dT : List (List IxAICore.Fx)} {lr : IxAICore.Fx}
    (hb : b.length = 16) (hd : dT.length = 16) (hdr : ∀ d ∈ dT, d.length = 20)
    (hbw : VecW b) (hbd : BiasBounds lr dT) {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_bias16" [encVec b, encMat dT, fxVal lr] h r h' calls) :
    r = encVec (updBias lr b dT) ∧ VecW (updBias lr b dT) := by
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15,
      rfl⟩ := list_eq16 hb
  obtain ⟨d_0, d_1, d_2, d_3, d_4, d_5, d_6, d_7, d_8, d_9, d_10, d_11, d_12, d_13, d_14, d_15,
      rfl⟩ := list_eq16 hd
  obtain ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, x_b8, x_b9, x_b10, x_b11, x_b12, x_b13,
      x_b14, x_b15, x_d0, x_d1, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7, x_d8, x_d9, x_d10, x_d11, x_d12,
      x_d13, x_d14, x_d15, v187, v188, v189, v190, v191, v192, v193, v194, v195, v196, v197, v198,
      v199, v200, v201, v202, m205, cs213, v218, m234, cs242, m254, cs262, v267, m283, cs291, m303,
      cs311, v316, m332, cs340, m352, cs360, v365, m381, cs389, m401, cs409, v414, m430, cs438,
      m450, cs458, v463, m479, cs487, m499, cs507, v512, m528, cs536, m548, cs556, v561, m577,
      cs585, m597, cs605, v610, m626, cs634, m646, cs654, v659, m675, cs683, m695, cs703, v708,
      m724, cs732, m744, cs752, v757, m773, cs781, m793, cs801, v806, m822, cs830, m842, cs850,
      v855, m871, cs879, m891, cs899, v904, m920, cs928, m940, cs948, v953, m969, cs977, hv11,
      hv103, he203, ev244, ev215, ev293, ev264, ev342, ev313, ev391, ev362, ev440, ev411, ev489,
      ev460, ev538, ev509, ev587, ev558, ev636, ev607, ev685, ev656, ev734, ev705, ev783, ev754,
      ev832, ev803, ev881, ev852, ev930, ev901, ev979, ev950, -, -⟩ :=
    «Fixed::update_bias16».obs ev
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv103
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv103
  obtain rfl := sum20_spec (hdr d_0 (by simp)) ev244
  obtain ⟨rfl, k_0⟩ := upd_spec (hbw b_0 (by simp)) (hbd d_0 (by simp)) ev215
  obtain rfl := sum20_spec (hdr d_1 (by simp)) ev293
  obtain ⟨rfl, k_1⟩ := upd_spec (hbw b_1 (by simp)) (hbd d_1 (by simp)) ev264
  obtain rfl := sum20_spec (hdr d_2 (by simp)) ev342
  obtain ⟨rfl, k_2⟩ := upd_spec (hbw b_2 (by simp)) (hbd d_2 (by simp)) ev313
  obtain rfl := sum20_spec (hdr d_3 (by simp)) ev391
  obtain ⟨rfl, k_3⟩ := upd_spec (hbw b_3 (by simp)) (hbd d_3 (by simp)) ev362
  obtain rfl := sum20_spec (hdr d_4 (by simp)) ev440
  obtain ⟨rfl, k_4⟩ := upd_spec (hbw b_4 (by simp)) (hbd d_4 (by simp)) ev411
  obtain rfl := sum20_spec (hdr d_5 (by simp)) ev489
  obtain ⟨rfl, k_5⟩ := upd_spec (hbw b_5 (by simp)) (hbd d_5 (by simp)) ev460
  obtain rfl := sum20_spec (hdr d_6 (by simp)) ev538
  obtain ⟨rfl, k_6⟩ := upd_spec (hbw b_6 (by simp)) (hbd d_6 (by simp)) ev509
  obtain rfl := sum20_spec (hdr d_7 (by simp)) ev587
  obtain ⟨rfl, k_7⟩ := upd_spec (hbw b_7 (by simp)) (hbd d_7 (by simp)) ev558
  obtain rfl := sum20_spec (hdr d_8 (by simp)) ev636
  obtain ⟨rfl, k_8⟩ := upd_spec (hbw b_8 (by simp)) (hbd d_8 (by simp)) ev607
  obtain rfl := sum20_spec (hdr d_9 (by simp)) ev685
  obtain ⟨rfl, k_9⟩ := upd_spec (hbw b_9 (by simp)) (hbd d_9 (by simp)) ev656
  obtain rfl := sum20_spec (hdr d_10 (by simp)) ev734
  obtain ⟨rfl, k_10⟩ := upd_spec (hbw b_10 (by simp)) (hbd d_10 (by simp)) ev705
  obtain rfl := sum20_spec (hdr d_11 (by simp)) ev783
  obtain ⟨rfl, k_11⟩ := upd_spec (hbw b_11 (by simp)) (hbd d_11 (by simp)) ev754
  obtain rfl := sum20_spec (hdr d_12 (by simp)) ev832
  obtain ⟨rfl, k_12⟩ := upd_spec (hbw b_12 (by simp)) (hbd d_12 (by simp)) ev803
  obtain rfl := sum20_spec (hdr d_13 (by simp)) ev881
  obtain ⟨rfl, k_13⟩ := upd_spec (hbw b_13 (by simp)) (hbd d_13 (by simp)) ev852
  obtain rfl := sum20_spec (hdr d_14 (by simp)) ev930
  obtain ⟨rfl, k_14⟩ := upd_spec (hbw b_14 (by simp)) (hbd d_14 (by simp)) ev901
  obtain rfl := sum20_spec (hdr d_15 (by simp)) ev979
  obtain ⟨rfl, k_15⟩ := upd_spec (hbw b_15 (by simp)) (hbd d_15 (by simp)) ev950
  subst he203
  refine ⟨rfl, ?_⟩
  unfold VecW
  intro a ha
  simp only [updBias, List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/- Consumes `«Fixed::update_bias11».Path.run`: 88 binders (`x_b0` … `cs677`), then the facts
   hv11 : x_b = (.tuple [x_b0, x_b1, …, x_b10])
   hv78 : x_dt = (.tuple [x_d0, x_d1, …, x_d10])
   he148 : r = (.tuple [v137, v138, …, v147])
   ev189 : ObsFn W "Fixed::sum20" [x_d0] h v163 m179 cs187
   ev160 : ObsFn W "Fixed::upd" [x_b0, x_lr, v163] m179 v137 m150 cs158
   ev238 : ObsFn W "Fixed::sum20" [x_d1] m150 v212 m228 cs236
   ev209 : ObsFn W "Fixed::upd" [x_b1, x_lr, v212] m228 v138 m199 cs207
   ev287 : ObsFn W "Fixed::sum20" [x_d2] m199 v261 m277 cs285
   ev258 : ObsFn W "Fixed::upd" [x_b2, x_lr, v261] m277 v139 m248 cs256
   ev336 : ObsFn W "Fixed::sum20" [x_d3] m248 v310 m326 cs334
   ev307 : ObsFn W "Fixed::upd" [x_b3, x_lr, v310] m326 v140 m297 cs305
   ev385 : ObsFn W "Fixed::sum20" [x_d4] m297 v359 m375 cs383
   ev356 : ObsFn W "Fixed::upd" [x_b4, x_lr, v359] m375 v141 m346 cs354
   ev434 : ObsFn W "Fixed::sum20" [x_d5] m346 v408 m424 cs432
   ev405 : ObsFn W "Fixed::upd" [x_b5, x_lr, v408] m424 v142 m395 cs403
   ev483 : ObsFn W "Fixed::sum20" [x_d6] m395 v457 m473 cs481
   ev454 : ObsFn W "Fixed::upd" [x_b6, x_lr, v457] m473 v143 m444 cs452
   ev532 : ObsFn W "Fixed::sum20" [x_d7] m444 v506 m522 cs530
   ev503 : ObsFn W "Fixed::upd" [x_b7, x_lr, v506] m522 v144 m493 cs501
   ev581 : ObsFn W "Fixed::sum20" [x_d8] m493 v555 m571 cs579
   ev552 : ObsFn W "Fixed::upd" [x_b8, x_lr, v555] m571 v145 m542 cs550
   ev630 : ObsFn W "Fixed::sum20" [x_d9] m542 v604 m620 cs628
   ev601 : ObsFn W "Fixed::upd" [x_b9, x_lr, v604] m620 v146 m591 cs599
   ev679 : ObsFn W "Fixed::sum20" [x_d10] m591 v653 m669 cs677
   ev650 : ObsFn W "Fixed::upd" [x_b10, x_lr, v653] m669 v147 m640 cs648
   he688 : h' = m640  (unused)
   hc689 : calls = ...  (unused) -/
/-- **`Fixed::update_bias11` is the field `b2` of `Model.step`**: `upd b (Fx.sum d)`. -/
theorem update_bias11_spec {b : List IxAICore.Fx} {dT : List (List IxAICore.Fx)} {lr : IxAICore.Fx}
    (hb : b.length = 11) (hd : dT.length = 11) (hdr : ∀ d ∈ dT, d.length = 20)
    (hbw : VecW b) (hbd : BiasBounds lr dT) {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::update_bias11" [encVec b, encMat dT, fxVal lr] h r h' calls) :
    r = encVec (updBias lr b dT) ∧ VecW (updBias lr b dT) := by
  obtain ⟨b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, rfl⟩ := list_eq11 hb
  obtain ⟨d_0, d_1, d_2, d_3, d_4, d_5, d_6, d_7, d_8, d_9, d_10, rfl⟩ := list_eq11 hd
  obtain ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, x_b8, x_b9, x_b10, x_d0, x_d1, x_d2, x_d3,
      x_d4, x_d5, x_d6, x_d7, x_d8, x_d9, x_d10, v137, v138, v139, v140, v141, v142, v143, v144,
      v145, v146, v147, m150, cs158, v163, m179, cs187, m199, cs207, v212, m228, cs236, m248, cs256,
      v261, m277, cs285, m297, cs305, v310, m326, cs334, m346, cs354, v359, m375, cs383, m395,
      cs403, v408, m424, cs432, m444, cs452, v457, m473, cs481, m493, cs501, v506, m522, cs530,
      m542, cs550, v555, m571, cs579, m591, cs599, v604, m620, cs628, m640, cs648, v653, m669,
      cs677, hv11, hv78, he148, ev189, ev160, ev238, ev209, ev287, ev258, ev336, ev307, ev385,
      ev356, ev434, ev405, ev483, ev454, ev532, ev503, ev581, ev552, ev630, ev601, ev679, ev650, -,
      -⟩ :=
    «Fixed::update_bias11».obs ev
  simp only [encVec, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv11
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
  simp only [encMat, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true, eq_self_iff_true] at hv78
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv78
  obtain rfl := sum20_spec (hdr d_0 (by simp)) ev189
  obtain ⟨rfl, k_0⟩ := upd_spec (hbw b_0 (by simp)) (hbd d_0 (by simp)) ev160
  obtain rfl := sum20_spec (hdr d_1 (by simp)) ev238
  obtain ⟨rfl, k_1⟩ := upd_spec (hbw b_1 (by simp)) (hbd d_1 (by simp)) ev209
  obtain rfl := sum20_spec (hdr d_2 (by simp)) ev287
  obtain ⟨rfl, k_2⟩ := upd_spec (hbw b_2 (by simp)) (hbd d_2 (by simp)) ev258
  obtain rfl := sum20_spec (hdr d_3 (by simp)) ev336
  obtain ⟨rfl, k_3⟩ := upd_spec (hbw b_3 (by simp)) (hbd d_3 (by simp)) ev307
  obtain rfl := sum20_spec (hdr d_4 (by simp)) ev385
  obtain ⟨rfl, k_4⟩ := upd_spec (hbw b_4 (by simp)) (hbd d_4 (by simp)) ev356
  obtain rfl := sum20_spec (hdr d_5 (by simp)) ev434
  obtain ⟨rfl, k_5⟩ := upd_spec (hbw b_5 (by simp)) (hbd d_5 (by simp)) ev405
  obtain rfl := sum20_spec (hdr d_6 (by simp)) ev483
  obtain ⟨rfl, k_6⟩ := upd_spec (hbw b_6 (by simp)) (hbd d_6 (by simp)) ev454
  obtain rfl := sum20_spec (hdr d_7 (by simp)) ev532
  obtain ⟨rfl, k_7⟩ := upd_spec (hbw b_7 (by simp)) (hbd d_7 (by simp)) ev503
  obtain rfl := sum20_spec (hdr d_8 (by simp)) ev581
  obtain ⟨rfl, k_8⟩ := upd_spec (hbw b_8 (by simp)) (hbd d_8 (by simp)) ev552
  obtain rfl := sum20_spec (hdr d_9 (by simp)) ev630
  obtain ⟨rfl, k_9⟩ := upd_spec (hbw b_9 (by simp)) (hbd d_9 (by simp)) ev601
  obtain rfl := sum20_spec (hdr d_10 (by simp)) ev679
  obtain ⟨rfl, k_10⟩ := upd_spec (hbw b_10 (by simp)) (hbd d_10 (by simp)) ev650
  subst he148
  refine ⟨rfl, ?_⟩
  unfold VecW
  intro a ha
  simp only [updBias, List.zipWith_cons_cons, List.zipWith_nil_left, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ## One SGD step -/

/- Consumes `«Fixed::step».Path.run`: 32 binders (`v1` … `cs339`), then the facts
   ev14 : ObsFn W "Fixed::transpose11x16" [x_w2] h v1 m2 cs12
   ev36 : ObsFn W "Fixed::deltas" [x_w1, x_b1, …, x_ts] m2 (.tuple [x_hs, x_dzs, x_douts]) m24 …
   ev124 : ObsFn W "Fixed::transpose20x16" [x_dzs] m24 v111 m112 cs122
   ev146 : ObsFn W "Fixed::transpose20x8" [x_xs] m112 v133 m134 cs144
   ev168 : ObsFn W "Fixed::transpose20x16" [x_hs] m134 v155 m156 cs166
   ev190 : ObsFn W "Fixed::transpose20x11" [x_douts] m156 v177 m178 cs188
   he205 : r = (.tuple [v201, v202, v203, v204])
   ev217 : ObsFn W "Fixed::update_w1" [x_w1, v111, v133, x_lr] m178 v201 m207 cs215
   ev261 : ObsFn W "Fixed::update_bias16" [x_b1, v111, x_lr] m207 v202 m251 cs259
   ev297 : ObsFn W "Fixed::update_w2" [x_w2, v177, v155, x_lr] m251 v203 m287 cs295
   ev341 : ObsFn W "Fixed::update_bias11" [x_b2, v177, x_lr] m287 v204 m331 cs339
   he366 : h' = m331  (unused)
   hc367 : calls = ...  (unused) -/
/-- **`Fixed::step` is `Model.step`.** On the encoded model, batch and learning rate, every
observed derivation of `Fixed::step` returns the encoding of `Model.step lr m batch`, provided
the model and the batch have the fixed shapes, the parameters are below `2^13` (`ModelW`), and
every value the step rounds or sign-tests is below `2^55` in magnitude (`StepBounds`). The
returned parameters are again below `2^13`: `Fixed::upd` checks each one. -/
theorem step_spec {lr : IxAICore.Fx} {m : IxAICore.Model}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hn : batch.length = 20) (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hm : ModelW m) (hb : StepBounds lr m batch) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::step"
      [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2, encMat (batch.map (·.1)),
        encMat (batch.map (·.2)), fxVal lr] h r h' calls) :
    r = encModel (IxAICore.Model.step lr m batch) ∧ ModelW (IxAICore.Model.step lr m batch) := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hm
  have hne : batch.isEmpty = false := by
    cases batch with
    | nil => simp at hn
    | cons _ _ => rfl
  have hI : (IxAICore.getD m.w1 0 []).length = 8 := by
    cases hm : m.w1 with
    | nil => rw [hm] at hw1; simp at hw1
    | cons row rows => exact hw1r row (by rw [hm]; simp)
  have hT : (IxAICore.transposeN m.b1.length m.w2).length = 16 := by
    rw [length_transposeN]; exact hb1
  have hTr : ∀ c ∈ IxAICore.transposeN m.b1.length m.w2, c.length = 11 :=
    fun c hc => (col_length_transposeN _ _ c hc).trans hw2
  have hlen : (deltasOf m (IxAICore.transposeN m.b1.length m.w2) batch).length = 20 := by
    simp [deltasOf, hn]
  have hdz : (IxAICore.transposeN m.b1.length ((deltasOf m (IxAICore.transposeN m.b1.length m.w2)
      batch).map (·.dz))).length = 16 := by
    rw [length_transposeN]; exact hb1
  have hdzr : ∀ d ∈ IxAICore.transposeN m.b1.length ((deltasOf m (IxAICore.transposeN m.b1.length
      m.w2) batch).map (·.dz)), d.length = 20 :=
    fun d hd => by rw [col_length_transposeN _ _ d hd, List.length_map, hlen]
  have hxT : (IxAICore.transposeN (IxAICore.getD m.w1 0 []).length
      ((deltasOf m (IxAICore.transposeN m.b1.length m.w2) batch).map (·.x))).length = 8 := by
    rw [length_transposeN]; exact hI
  have hxTr : ∀ c ∈ IxAICore.transposeN (IxAICore.getD m.w1 0 []).length
      ((deltasOf m (IxAICore.transposeN m.b1.length m.w2) batch).map (·.x)), c.length = 20 :=
    fun c hc => by rw [col_length_transposeN _ _ c hc, List.length_map, hlen]
  have hhT : (IxAICore.transposeN m.b1.length ((deltasOf m (IxAICore.transposeN m.b1.length m.w2)
      batch).map (·.h))).length = 16 := by
    rw [length_transposeN]; exact hb1
  have hhTr : ∀ c ∈ IxAICore.transposeN m.b1.length ((deltasOf m (IxAICore.transposeN m.b1.length
      m.w2) batch).map (·.h)), c.length = 20 :=
    fun c hc => by rw [col_length_transposeN _ _ c hc, List.length_map, hlen]
  have hoT : (IxAICore.transposeN m.b2.length ((deltasOf m (IxAICore.transposeN m.b1.length m.w2)
      batch).map (·.dout))).length = 11 := by
    rw [length_transposeN]; exact hb2
  have hoTr : ∀ d ∈ IxAICore.transposeN m.b2.length ((deltasOf m (IxAICore.transposeN m.b1.length
      m.w2) batch).map (·.dout)), d.length = 20 :=
    fun d hd => by rw [col_length_transposeN _ _ d hd, List.length_map, hlen]
  obtain ⟨v1, m2, cs12, m24, cs34, x_hs, x_dzs, x_douts, v111, m112, cs122, v133, m134, cs144, v155,
      m156, cs166, v177, m178, cs188, v201, v202, v203, v204, m207, cs215, m251, cs259, m287, cs295,
      m331, cs339, ev14, ev36, ev124, ev146, ev168, ev190, he205, ev217, ev261, ev297, ev341, -,
      -⟩ :=
    «Fixed::step».obs ev
  obtain rfl := transpose11x16_spec hb1 ev14
  have e := deltas_spec hw1 hw1r hb1 hw2 hw2r hb2 hT hTr hn hex hb.deltas ev36
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain rfl := transpose20x16_spec hb1 ev124
  rw [← deltasOf_x m (IxAICore.transposeN m.b1.length m.w2) batch] at ev146
  obtain rfl := transpose20x8_spec hI ev146
  obtain rfl := transpose20x16_spec hb1 ev168
  obtain rfl := transpose20x11_spec hb2 ev190
  obtain ⟨rfl, k1⟩ := update_w1_spec hw1 hw1r hdz hdzr hxT hxTr hm1 hb.w1 ev217
  obtain ⟨rfl, k2⟩ := update_bias16_spec hb1 hdz hdzr hm2 hb.b1 ev261
  obtain ⟨rfl, k3⟩ := update_w2_spec hw2 hw2r hoT hoTr hhT hhTr hm3 hb.w2 ev297
  obtain ⟨rfl, k4⟩ := update_bias11_spec hb2 hoT hoTr hm4 hb.b2 ev341
  subst he205
  rw [step_of_ne hne]
  exact ⟨rfl, k1, k2, k3, k4⟩

/-- **`step_spec` with the host's encodings**: `Fixed::step` on `IxAIAiur.stepArgs m batch lr`
returns `IxAIAiur.modelValue (Model.step lr m batch)`, the value the host's test compares. -/
theorem step_spec_host {lr : IxAICore.Fx} {m : IxAICore.Model}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hn : batch.length = 20) (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hm : ModelW m) (hb : StepBounds lr m batch) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::step" (IxAIAiur.stepArgs m batch lr) h r h' calls) :
    r = IxAIAiur.modelValue (IxAICore.Model.step lr m batch) :=
  (step_spec hw1 hw1r hb1 hw2 hw2r hb2 hn hex hm hb ev).1

end IxAIStep.Fixed.Specs
