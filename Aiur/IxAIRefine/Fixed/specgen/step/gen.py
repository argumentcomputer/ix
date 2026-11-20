import sys, re
sys.setrecursionlimit(100000)
import sim

C = 'IxAICore.'
FX = C + 'Fx'
OUT = []
def emit(s=''): OUT.append(s)

def wrap(prefix, items, suffix, indent='      ', width=100):
    head, _, rest = suffix.partition('\n')
    items = items[:-1] + [items[-1] + head]
    suffix = ('\n' + rest) if _ else ''
    lines = []; cur = prefix
    for i, it in enumerate(items):
        piece = it + (', ' if i < len(items) - 1 else '')
        if len(cur) + len(piece.rstrip()) > width:
            lines.append(cur.rstrip()); cur = indent
        cur += piece
    first_suffix = suffix.split('\n')[0]
    if len(cur) + len(first_suffix) > width and cur.strip():
        lines.append(cur.rstrip()); cur = indent
    cur += suffix
    lines.append(cur)
    return '\n'.join(lines)

def abbrev(text):
    # shorten long tuple literals in comments
    def sh(m):
        items = m.group(1).split(', ')
        if len(items) <= 6: return m.group(0)
        return '[' + ', '.join(items[:2]) + ', …, ' + items[-1] + ']'
    prev = None
    while prev != text:
        prev = text
        text = re.sub(r'\[([^\[\]]*)\]', sh, text)
    return text.replace('(.tuple', '(.tuple').replace('[', '⟦').replace(']', '⟧')

def path_comment(fname, used):
    bs, fs, _ = sim.path(fname)
    lines = [f'/- Consumes `«Fixed::{fname}».Path.run`: {len(bs)} binders (`{bs[0]}` … `{bs[-1]}`), then the facts']
    for n, t in fs:
        mark = '' if n in used else '  (unused)'
        t2 = abbrev(t).replace('⟦', '[').replace('⟧', ']')
        if len(t2) > 88: t2 = t2[:85] + '…'
        lines.append(f'   {n} : {t2}{mark}')
    lines[-1] += ' -/'
    if any(n.startswith('hv') for n, _ in fs) and not fname.startswith('transpose'):
        lines.append('-- unverified: `simp only [enc…, List.map_cons, …, List.cons.injEq, and_true]` turns each')
        lines.append('-- array-pattern fact `hv…` into one equation `enc… = x_…` per element, in order, and')
        lines.append('-- the closing `rfl` unfolds `List.zipWith`/`List.map` on the literal lists.')
    return '\n'.join(lines)

def obtain_path(fname, used, ind='  '):
    bs, fs, _ = sim.path(fname)
    names = bs + [n if n in used else '-' for n, _ in fs]
    return wrap(ind + 'obtain ⟨', names, f'⟩ :=\n{ind}  «Fixed::{fname}».obs ev', indent=ind + '    ')

def facts(fname): return sim.path(fname)[1]

def rfls(k): return '⟨' + ', '.join(['rfl'] * k) + '⟩'

SIMP_TAIL = 'List.map_cons, List.map_nil, Aiur.Value.tuple.injEq, List.cons.injEq,\n    and_true, eq_self_iff_true]'
def simp_vec(h): return f'  simp only [encVec, {SIMP_TAIL} at {h}'
def simp_mat(h): return f'  simp only [encMat, {SIMP_TAIL} at {h}'
SIMP_TUP = 'simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true, eq_self_iff_true] at'

def vars_(p, n): return [f'{p}_{i}' for i in range(n)]
def destr(vs, hyp, n):
    return wrap('  obtain ⟨', vs + ['rfl'], f'⟩ := list_eq{n} {hyp}', indent='      ')
def lit(xs, ind='      ', per=8):
    rows = [', '.join(xs[i:i+per]) for i in range(0, len(xs), per)]
    return '[' + (',\n' + ind + ' ').join(rows) + ']'

HEADER = r'''import IxAIRefine.Fixed.Specs

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
  `transposeN`. These need no shape hypotheses: the path's array patterns fix the shape, and
  `map_transposeN` moves the encoding through `transposeN` once, by induction.
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
`StepBounds …`, so a concrete step's bounds can be discharged by evaluation. Additions and
subtractions are field operations and need no bound: the field value is the cast of the
integer result, which is what `fxVal` encodes.

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

-- unverified: the `if` on `batch.isEmpty` reduces by `rfl` once `batch.isEmpty` is rewritten
-- to `false`, and the matcher of `fun (x, t) => …` in `Model.step` is definitionally the one in
-- `deltasOf` (shared by Lean's matcher cache, or equal by structure eta).
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

-- unverified (the four soundness lemmas): `simp only [Bool.and_eq_true, List.all_eq_true]`
-- splits the conjunction into the shape the anonymous constructors expect.
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

/-- `transposeN` on encoded entries: the same recursion over `SourceValue F`, with the encoded
default. -/
def trV : ℕ → List (List (SourceValue F)) → List (List (SourceValue F))
  | 0, _ => []
  | n + 1, rows => rows.map (·.headD (fxVal IxAICore.Fx.zero)) :: trV n (rows.map (·.tail))

theorem map_heads (rows : List (List IxAICore.Fx)) :
    (rows.map (·.headD IxAICore.Fx.zero)).map fxVal =
      (rows.map (·.map fxVal)).map (·.headD (fxVal IxAICore.Fx.zero)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have h1 : fxVal (r.headD IxAICore.Fx.zero) = (r.map fxVal).headD (fxVal IxAICore.Fx.zero) := by
      cases r <;> rfl
    show fxVal (r.headD IxAICore.Fx.zero) :: (rs.map (·.headD IxAICore.Fx.zero)).map fxVal =
      (r.map fxVal).headD (fxVal IxAICore.Fx.zero) ::
        (rs.map (·.map fxVal)).map (·.headD (fxVal IxAICore.Fx.zero))
    rw [h1, ih]

theorem map_tails (rows : List (List IxAICore.Fx)) :
    (rows.map (·.tail)).map (·.map fxVal) = (rows.map (·.map fxVal)).map (·.tail) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have h1 : r.tail.map fxVal = (r.map fxVal).tail := by cases r <;> rfl
    show r.tail.map fxVal :: (rs.map (·.tail)).map (·.map fxVal) =
      (r.map fxVal).tail :: (rs.map (·.map fxVal)).map (·.tail)
    rw [h1, ih]

-- unverified: `simp only [List.map_cons]` leaves the two heads beta-reduced, as `map_heads`
-- and `map_tails` state them.
/-- **Encoding commutes with `transposeN`.** -/
theorem map_transposeN (n : ℕ) (rows : List (List IxAICore.Fx)) :
    (IxAICore.transposeN n rows).map (·.map fxVal) = trV n (rows.map (·.map fxVal)) := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    show (rows.map (·.headD IxAICore.Fx.zero) ::
        IxAICore.transposeN n (rows.map (·.tail))).map (·.map fxVal) =
      (rows.map (·.map fxVal)).map (·.headD (fxVal IxAICore.Fx.zero)) ::
        trV n ((rows.map (·.map fxVal)).map (·.tail))
    simp only [List.map_cons]
    rw [ih, map_heads, map_tails]

-- unverified: after `List.map_map`, `encVec` and `Value.tuple ∘ (·.map fxVal)` agree by `rfl`.
theorem encMat_eq (rows : List (List IxAICore.Fx)) :
    encMat rows = .tuple ((rows.map (·.map fxVal)).map Aiur.Value.tuple) := by
  rw [List.map_map]
  rfl

-- unverified: `simp at h` refutes `[] = _ :: _` after `List.map_nil`/`List.map_cons`.
theorem map_tuple_inj {A B : List (List (SourceValue F))}
    (h : A.map Aiur.Value.tuple = B.map Aiur.Value.tuple) : A = B := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a as ih =>
    cases B with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Aiur.Value.tuple.inj h.1, ih h.2]

/-- An encoded matrix determines its encoded rows. -/
theorem rows_of_encMat {rows : List (List IxAICore.Fx)} {X : List (List (SourceValue F))}
    (h : encMat rows = .tuple (X.map Aiur.Value.tuple)) : rows.map (·.map fxVal) = X := by
  rw [encMat_eq] at h
  exact map_tuple_inj (Aiur.Value.tuple.inj h)

-- unverified: the `show` unfolds `Model.delta` to read its `x` field.
theorem deltasOf_x (m : IxAICore.Model) (w2T : List (List IxAICore.Fx))
    (batch : List (List IxAICore.Fx × List IxAICore.Fx)) :
    (deltasOf m w2T batch).map (·.x) = batch.map (·.1) := by
  induction batch with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨x, t⟩ := p
    show x :: (deltasOf m w2T ps).map (·.x) = x :: ps.map (·.1)
    rw [ih]
'''

emit(HEADER)

# ---------------------------------------------------------------- units
emit('/-! ## One entry -/\n')

def unit_spec(name, dotn, n, rowname, vecname):
    used = {'ev14', 'op8'}
    emit(path_comment(f'{name}', used))
    emit(f'''/-- **`Fixed::{name}` is `Fx.add (Fx.dot {rowname} {vecname}) b`.** -/
theorem {name}_spec {{{rowname} {vecname} : List IxAICore.Fx}} {{b : IxAICore.Fx}} (hr : {rowname}.length = {n})
    (hv : {vecname}.length = {n}) (hb : Small (IxAICore.Fx.dotRaw {rowname} {vecname})) {{h h' : Heap F}}
    {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::{name}" [encVec {rowname}, fxVal b, encVec {vecname}] h r h' calls) :
    r = fxVal (IxAICore.Fx.add (IxAICore.Fx.dot {rowname} {vecname}) b) := by
{obtain_path(name, used)}
  obtain rfl := dot{dotn}_spec hr hv hb ev14
  exact add_fx op8
''')

unit_spec('hidden_unit', 8, 8, 'row', 'x')
unit_spec('output_unit', 16, 16, 'row', 'hs')

used = {'ev14', 'ev28', 'op8'}
emit(path_comment('back_unit', used))
emit(f'''/-- **`Fixed::back_unit` is one entry of `dz`**: `Fx.dot col dout` where `Fx.pos z`, else
zero. The dot product is computed either way, so its bound is needed either way. -/
theorem back_unit_spec {{z : IxAICore.Fx}} {{col dout : List IxAICore.Fx}} (hz : Small z.raw)
    (hcol : col.length = 11) (hd : dout.length = 11) (hb : Small (IxAICore.Fx.dotRaw col dout))
    {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::back_unit" [fxVal z, encVec col, encVec dout] h r h' calls) :
    r = fxVal (if IxAICore.Fx.pos z then IxAICore.Fx.dot col dout else IxAICore.Fx.zero) := by
{obtain_path('back_unit', used)}
  obtain rfl := pos_spec hz ev14
  obtain rfl := dot11_spec hcol hd hb ev28
  exact mul_pos_fx op8
''')

used = {'ev15', 'op8'}
emit(path_comment('upd', used))
emit(f'''/-- **`Fixed::upd` is the SGD update** `Fx.sub w (Fx.mul lr g)` (`upd` in `Model.step`). -/
theorem upd_spec {{w lr g : IxAICore.Fx}} (hb : Small (lr.raw * g.raw)) {{h h' : Heap F}}
    {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::upd" [fxVal w, fxVal lr, fxVal g] h r h' calls) :
    r = fxVal (IxAICore.Fx.sub w (IxAICore.Fx.mul lr g)) := by
{obtain_path('upd', used)}
  obtain rfl := mul_spec hb ev15
  exact sub_fx op8
''')

# ---------------------------------------------------------------- hidden
emit('/-! ## Forward pass -/\n')

def fx_add_dot(row, vec, b): return f'IxAICore.Fx.add (IxAICore.Fx.dot {row} {vec}) {b}'

fs = facts('hidden')
hv = [n for n, t in fs if n.startswith('hv')]
hu = [n for n, t in fs if '"Fixed::hidden_unit"' in t]
re_ = [n for n, t in fs if '"Fixed::relu"' in t]
res = [n for n, t in fs if t.startswith('r = ')][0]
used = set(hv + hu + re_ + [res])
W = vars_('w', 16); B = vars_('b', 16)
lines = [path_comment('hidden', used)]
lines.append(f'''-- unverified: membership in a 16-element literal list closes by `simp`.
/-- **`Fixed::hidden` is `Model.hidden`** on lists: the pre-activations and their `relu`. -/
theorem hidden_core {{w1 : List (List IxAICore.Fx)}} {{b1 x : List IxAICore.Fx}}
    (hw : w1.length = 16) (hrows : ∀ row ∈ w1, row.length = 8) (hb : b1.length = 16)
    (hx : x.length = 8) (hdot : ∀ row ∈ w1, Small (IxAICore.Fx.dotRaw row x))
    (hz : ∀ z ∈ hiddenZ w1 b1 x, Small z.raw) {{h h' : Heap F}} {{r : SourceValue F}}
    {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::hidden" [encMat w1, encVec b1, encVec x] h r h' calls) :
    r = .tuple [encVec (hiddenZ w1 b1 x), encVec ((hiddenZ w1 b1 x).map IxAICore.Fx.relu)] := by''')
lines.append(destr(W, 'hw', 16))
lines.append(destr(B, 'hb', 16))
lines.append(wrap('  have hz\' : ∀ z ∈ [', [fx_add_dot(W[i], 'x', B[i]) for i in range(16)], '],\n      Small z.raw := hz', indent='      '))
lines.append(obtain_path('hidden', used))
lines.append(simp_mat(hv[0])); lines.append(f'  obtain {rfls(16)} := {hv[0]}')
lines.append(simp_vec(hv[1])); lines.append(f'  obtain {rfls(16)} := {hv[1]}')
for i, e in enumerate(hu):
    lines.append(f'  obtain rfl := hidden_unit_spec (hrows {W[i]} (by simp)) hx (hdot {W[i]} (by simp)) {e}')
for i, e in enumerate(re_):
    lines.append(f'  obtain rfl := relu_spec (hz\' _ (by simp)) {e}')
lines.append(f'  subst {res}')
lines.append('  rfl\n')
emit('\n'.join(lines))

emit('''-- unverified: `(m.hidden x).1` and `hiddenZ m.w1 m.b1 x` agree by unfolding (`hidden_eq`).
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
''')

# outputs
fs = facts('outputs')
hv = [n for n, t in fs if n.startswith('hv')]
ou = [n for n, t in fs if '"Fixed::output_unit"' in t]
res = [n for n, t in fs if t.startswith('r = ')][0]
used = set(hv + ou + [res])
W = vars_('w', 11); B = vars_('b', 11)
lines = [path_comment('outputs', used)]
lines.append(f'''/-- **`Fixed::outputs` is the output layer** from the hidden activations `hs`: `o` in
`Model.delta`, `Model.outputs` once `hs` is `(Model.hidden m x).2`. -/
theorem outputs_spec {{w2 : List (List IxAICore.Fx)}} {{b2 hs : List IxAICore.Fx}}
    (hw : w2.length = 11) (hrows : ∀ row ∈ w2, row.length = 16) (hb : b2.length = 11)
    (hh : hs.length = 16) (hdot : ∀ row ∈ w2, Small (IxAICore.Fx.dotRaw row hs))
    {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::outputs" [encMat w2, encVec b2, encVec hs] h r h' calls) :
    r = encVec (outputsOf w2 b2 hs) := by''')
lines.append(destr(W, 'hw', 11))
lines.append(destr(B, 'hb', 11))
lines.append(obtain_path('outputs', used))
lines.append(simp_mat(hv[0])); lines.append(f'  obtain {rfls(11)} := {hv[0]}')
lines.append(simp_vec(hv[1])); lines.append(f'  obtain {rfls(11)} := {hv[1]}')
for i, e in enumerate(ou):
    lines.append(f'  obtain rfl := output_unit_spec (hrows {W[i]} (by simp)) hh (hdot {W[i]} (by simp)) {e}')
lines.append(f'  subst {res}')
lines.append('  rfl\n')
emit('\n'.join(lines))

# sub11
fs = facts('sub11')
hv = [n for n, t in fs if n.startswith('hv')]
ops = [n for n, t in fs if n.startswith('op')]
res = [n for n, t in fs if t.startswith('r = ')][0]
used = set(hv + ops + [res])
A = vars_('a', 11); B = vars_('b', 11)
lines = [path_comment('sub11', used)]
lines.append(f'''/-- **`Fixed::sub11` is `List.zipWith Fx.sub`** (`dout` from `o` and `t`). -/
theorem sub11_spec {{a b : List IxAICore.Fx}} (ha : a.length = 11) (hb : b.length = 11)
    {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::sub11" [encVec a, encVec b] h r h' calls) :
    r = encVec (List.zipWith IxAICore.Fx.sub a b) := by''')
lines.append(destr(A, 'ha', 11))
lines.append(destr(B, 'hb', 11))
lines.append(obtain_path('sub11', used))
lines.append(simp_vec(hv[0])); lines.append(f'  obtain {rfls(11)} := {hv[0]}')
lines.append(simp_vec(hv[1])); lines.append(f'  obtain {rfls(11)} := {hv[1]}')
for e in ops:
    lines.append(f'  obtain rfl := sub_fx {e}')
lines.append(f'  subst {res}')
lines.append('  rfl\n')
emit('\n'.join(lines))

# ---------------------------------------------------------------- delta
emit('/-! ## Backward pass -/\n')
fs = facts('delta')
ev_h = [n for n, t in fs if '"Fixed::hidden"' in t][0]
ev_o = [n for n, t in fs if '"Fixed::outputs"' in t][0]
ev_s = [n for n, t in fs if '"Fixed::sub11"' in t][0]
hv = [n for n, t in fs if n.startswith('hv')][0]
res = [n for n, t in fs if t.startswith('r = ')][0]
bu = [n for n, t in fs if '"Fixed::back_unit"' in t]
used = {ev_h, ev_o, ev_s, hv, res} | set(bu)
W = vars_('w', 16); B = vars_('b', 16); K = vars_('k', 16)
Zs = [fx_add_dot(W[i], 'x', B[i]) for i in range(16)]
hsT = f'(hiddenZ {lit(W)}\n      {lit(B)} x).map IxAICore.Fx.relu'
lines = [path_comment('delta', used)]
lines.append(f'''-- unverified: the final `rfl` unfolds `Model.delta`, whose `let (z, h) := m.hidden x` reduces
-- because `Model.hidden` returns a pair literal.
/-- **`Fixed::delta` is `Model.delta`** on lists, as the triple `(h, dz, dout)`. -/
theorem delta_core {{w1 w2 w2T : List (List IxAICore.Fx)}} {{b1 b2 x t : List IxAICore.Fx}}
    (hw1 : w1.length = 16) (hw1r : ∀ row ∈ w1, row.length = 8) (hb1 : b1.length = 16)
    (hw2 : w2.length = 11) (hw2r : ∀ row ∈ w2, row.length = 16) (hb2 : b2.length = 11)
    (hT : w2T.length = 16) (hTr : ∀ c ∈ w2T, c.length = 11) (hx : x.length = 8)
    (ht : t.length = 11) (hb : DeltaBounds (IxAICore.Model.mk w1 b1 w2 b2) w2T x t)
    {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::delta"
      [encMat w1, encVec b1, encMat w2, encVec b2, encMat w2T, encVec x, encVec t] h r h' calls) :
    r = .tuple [encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).h,
      encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).dz,
      encVec (IxAICore.Model.delta (IxAICore.Model.mk w1 b1 w2 b2) w2T x t).dout] := by
  have hdot1 := hb.dot1
  have hz := hb.pre
  have hdot2 := hb.dot2
  have hdot3 := hb.dot3''')
lines.append(destr(W, 'hw1', 16))
lines.append(destr(B, 'hb1', 16))
lines.append(destr(K, 'hT', 16))
lines.append('  have hzL : hiddenZ ' + lit(W) + '\n      ' + lit(B) + ' x =\n' + wrap('      [', Zs, '] := rfl', indent='      '))
lines.append(wrap('  have hz\' : ∀ z ∈ [', Zs, '],\n      Small z.raw := hz', indent='      '))
lines.append(f'''  have hhl : ({hsT}).length = 16 := by
    first | rfl | simp [hiddenZ]
  have hdl : (List.zipWith IxAICore.Fx.sub (outputsOf w2 b2 ({hsT})) t).length = 11 := by
    simp [outputsOf, hw2, hb2, ht]''')
lines.append(obtain_path('delta', used))
lines.append(f'''  have e := hidden_core (w1 := {lit(W)})
    (b1 := {lit(B)})
    (by first | rfl | simp) hw1r (by first | rfl | simp) hx hdot1 hz {ev_h}
  {SIMP_TUP} e
  obtain ⟨ez, rfl⟩ := e
  rw [hzL] at ez''')
lines.append(simp_vec('ez'))
lines.append(f'  obtain {rfls(16)} := ez')
lines.append(f'''  obtain rfl := outputs_spec hw2 hw2r hb2 hhl hdot2 {ev_o}
  obtain rfl := sub11_spec (by simp [outputsOf, hw2, hb2]) ht {ev_s}''')
lines.append(simp_mat(hv)); lines.append(f'  obtain {rfls(16)} := {hv}')
for i, e in enumerate(bu):
    lines.append(f'  obtain rfl := back_unit_spec (hz\' _ (by simp)) (hTr {K[i]} (by simp)) hdl (hdot3 {K[i]} (by simp)) {e}')
lines.append(f'  subst {res}')
lines.append('  rfl\n')
emit('\n'.join(lines))

emit('''/-- **`Fixed::delta` returns `Model.delta m w2T x t`** as `(h, dz, dout)`. -/
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
''')

# deltas
fs = facts('deltas')
hv = [n for n, t in fs if n.startswith('hv')]
dl = [n for n, t in fs if '"Fixed::delta"' in t]
res = [n for n, t in fs if t.startswith('r = ')][0]
used = set(hv + dl + [res])
X = vars_('x', 20); T = vars_('t', 20)
lines = [path_comment('deltas', used)]
lines.append(f'''/-- **`Fixed::deltas` is `ds` in `Model.step`**, as the matrices of its `h`, `dz` and `dout`
fields. -/
theorem deltas_spec {{m : IxAICore.Model}} {{w2T : List (List IxAICore.Fx)}}
    {{batch : List (List IxAICore.Fx × List IxAICore.Fx)}}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hT : w2T.length = 16) (hTr : ∀ c ∈ w2T, c.length = 11) (hn : batch.length = 20)
    (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hb : ∀ p ∈ batch, DeltaBounds m w2T p.1 p.2) {{h h' : Heap F}} {{r : SourceValue F}}
    {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::deltas"
      [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2, encMat w2T,
        encMat (batch.map (·.1)), encMat (batch.map (·.2))] h r h' calls) :
    r = .tuple [encMat ((deltasOf m w2T batch).map (·.h)),
      encMat ((deltasOf m w2T batch).map (·.dz)),
      encMat ((deltasOf m w2T batch).map (·.dout))] := by''')
lines.append(wrap('  obtain ⟨', [f'⟨{X[i]}, {T[i]}⟩' for i in range(20)] + ['rfl'], '⟩ := list_eq20 hn', indent='      '))
lines.append(obtain_path('deltas', used))
lines.append(simp_mat(hv[0])); lines.append(f'  obtain {rfls(20)} := {hv[0]}')
lines.append(simp_mat(hv[1])); lines.append(f'  obtain {rfls(20)} := {hv[1]}')
for i, e in enumerate(dl):
    p = f'({X[i]}, {T[i]})'
    lines.append(f'  have e{i} := delta_spec (x := {X[i]}) (t := {T[i]}) hw1 hw1r hb1 hw2 hw2r hb2 hT hTr')
    lines.append(f'    (hex {p} (by simp)).1 (hex {p} (by simp)).2 (hb {p} (by simp)) {e}')
    lines.append(f'  {SIMP_TUP} e{i}')
    lines.append(f'  obtain ⟨rfl, rfl, rfl⟩ := e{i}')
lines.append(f'  subst {res}')
lines.append('  rfl\n')
emit('\n'.join(lines))

# ---------------------------------------------------------------- transposes
emit('/-! ## Transposes -/\n')
for name, R, Cn in [('transpose11x16', 11, 16), ('transpose20x16', 20, 16), ('transpose20x8', 20, 8), ('transpose20x11', 20, 11)]:
    fs = facts(name)
    hv = [n for n, t in fs if n.startswith('hv')][0]
    res = [n for n, t in fs if t.startswith('r = ')][0]
    used = {hv, res}
    Xl = '[' + ', '.join('[' + ', '.join(f'x_a{i}_{j}' for j in range(Cn)) + ']' for i in range(R)) + ']'
    Xrows = ['[' + ', '.join(f'x_a{i}_{j}' for j in range(Cn)) + ']' for i in range(R)]
    lines = [path_comment(name, used)]
    lines.append(f'''/-- **`Fixed::{name}` is `transposeN {Cn}`** on a {R}-row matrix. -/
theorem {name}_spec {{n : ℕ}} (hn : n = {Cn}) {{rows : List (List IxAICore.Fx)}} {{h h' : Heap F}}
    {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::{name}" [encMat rows] h r h' calls) :
    r = encMat (IxAICore.transposeN n rows) := by
  subst hn''')
    lines.append(obtain_path(name, used))
    lines.append(wrap('  have hX := rows_of_encMat (X := [', Xrows, f']) {hv}', indent='      '))
    lines.append(f'  subst {res}')
    lines.append('  -- unverified: the closing `rfl` evaluates `trV` on the literal matrix of path variables.')
    lines.append('  rw [encMat_eq, map_transposeN, hX]')
    lines.append('  rfl\n')
    emit('\n'.join(lines))

# ---------------------------------------------------------------- updates
emit('/-! ## Updates -/\n')
for name, n in [('update_row8', 8), ('update_row16', 16)]:
    fs = facts(name)
    hv = [nm for nm, t in fs if nm.startswith('hv')]
    dots = [nm for nm, t in fs if '"Fixed::dot20"' in t]
    upds = [nm for nm, t in fs if '"Fixed::upd"' in t]
    res = [nm for nm, t in fs if t.startswith('r = ')][0]
    used = set(hv + dots + upds + [res])
    Wv = vars_('w', n); Cv = vars_('c', n)
    lines = [path_comment(name, used)]
    lines.append(f'''/-- **`Fixed::{name}` updates one row**: `upd w (Fx.dot d col)` for each weight and column,
the row function of `Model.step`. -/
theorem {name}_spec {{row d : List IxAICore.Fx}} {{cols : List (List IxAICore.Fx)}} {{lr : IxAICore.Fx}}
    (hrow : row.length = {n}) (hd : d.length = 20) (hcols : cols.length = {n})
    (hc : ∀ c ∈ cols, c.length = 20) (hb : RowBounds lr d cols) {{h h' : Heap F}}
    {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::{name}" [encVec row, encVec d, encMat cols, fxVal lr] h r h' calls) :
    r = encVec (updRow lr row d cols) := by''')
    lines.append(destr(Wv, 'hrow', n))
    lines.append(destr(Cv, 'hcols', n))
    lines.append(obtain_path(name, used))
    lines.append(simp_vec(hv[0])); lines.append(f'  obtain {rfls(n)} := {hv[0]}')
    lines.append(simp_mat(hv[1])); lines.append(f'  obtain {rfls(n)} := {hv[1]}')
    for i in range(n):
        lines.append(f'  obtain rfl := dot20_spec hd (hc {Cv[i]} (by simp)) (hb {Cv[i]} (by simp)).1 {dots[i]}')
        lines.append(f'  obtain rfl := upd_spec (hb {Cv[i]} (by simp)).2 {upds[i]}')
    lines.append(f'  subst {res}')
    lines.append('  rfl\n')
    emit('\n'.join(lines))

for name, rowfn, n, rl, cl, dname, cname in [('update_w1', 'update_row8', 16, 8, 8, 'dzT', 'xT'), ('update_w2', 'update_row16', 11, 16, 16, 'doutT', 'hT')]:
    fs = facts(name)
    hv = [nm for nm, t in fs if nm.startswith('hv')]
    ups = [nm for nm, t in fs if f'"Fixed::{rowfn}"' in t]
    res = [nm for nm, t in fs if t.startswith('r = ')][0]
    used = set(hv + ups + [res])
    Rv = vars_('r', n); Dv = vars_('d', n)
    field = 'w1' if name == 'update_w1' else 'w2'
    lines = [path_comment(name, used)]
    lines.append(f'''/-- **`Fixed::{name}` is the field `{field}` of `Model.step`**, from `{dname}` and `{cname}`. -/
theorem {name}_spec {{w {dname} {cname} : List (List IxAICore.Fx)}} {{lr : IxAICore.Fx}}
    (hw : w.length = {n}) (hrows : ∀ row ∈ w, row.length = {rl}) (hd : {dname}.length = {n})
    (hdr : ∀ d ∈ {dname}, d.length = 20) (hc : {cname}.length = {cl})
    (hcr : ∀ c ∈ {cname}, c.length = 20) (hb : ∀ d ∈ {dname}, RowBounds lr d {cname})
    {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::{name}" [encMat w, encMat {dname}, encMat {cname}, fxVal lr] h r h' calls) :
    r = encMat (List.zipWith (fun row d => updRow lr row d {cname}) w {dname}) := by''')
    lines.append(destr(Rv, 'hw', n))
    lines.append(destr(Dv, 'hd', n))
    lines.append(obtain_path(name, used))
    lines.append(simp_mat(hv[0])); lines.append(f'  obtain {rfls(n)} := {hv[0]}')
    lines.append(simp_mat(hv[1])); lines.append(f'  obtain {rfls(n)} := {hv[1]}')
    for i in range(n):
        lines.append(f'  obtain rfl := {rowfn}_spec (hrows {Rv[i]} (by simp)) (hdr {Dv[i]} (by simp)) hc hcr')
        lines.append(f'    (hb {Dv[i]} (by simp)) {ups[i]}')
    lines.append(f'  subst {res}')
    lines.append('  rfl\n')
    emit('\n'.join(lines))

for name, n, field in [('update_bias16', 16, 'b1'), ('update_bias11', 11, 'b2')]:
    fs = facts(name)
    hv = [nm for nm, t in fs if nm.startswith('hv')]
    sums = [nm for nm, t in fs if '"Fixed::sum20"' in t]
    upds = [nm for nm, t in fs if '"Fixed::upd"' in t]
    res = [nm for nm, t in fs if t.startswith('r = ')][0]
    used = set(hv + sums + upds + [res])
    Bv = vars_('b', n); Dv = vars_('d', n)
    lines = [path_comment(name, used)]
    lines.append(f'''/-- **`Fixed::{name}` is the field `{field}` of `Model.step`**: `upd b (Fx.sum d)`. -/
theorem {name}_spec {{b : List IxAICore.Fx}} {{dT : List (List IxAICore.Fx)}} {{lr : IxAICore.Fx}}
    (hb : b.length = {n}) (hd : dT.length = {n}) (hdr : ∀ d ∈ dT, d.length = 20)
    (hbd : BiasBounds lr dT) {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::{name}" [encVec b, encMat dT, fxVal lr] h r h' calls) :
    r = encVec (updBias lr b dT) := by''')
    lines.append(destr(Bv, 'hb', n))
    lines.append(destr(Dv, 'hd', n))
    lines.append(obtain_path(name, used))
    lines.append(simp_vec(hv[0])); lines.append(f'  obtain {rfls(n)} := {hv[0]}')
    lines.append(simp_mat(hv[1])); lines.append(f'  obtain {rfls(n)} := {hv[1]}')
    for i in range(n):
        lines.append(f'  obtain rfl := sum20_spec (hdr {Dv[i]} (by simp)) {sums[i]}')
        lines.append(f'  obtain rfl := upd_spec (hbd {Dv[i]} (by simp)) {upds[i]}')
    lines.append(f'  subst {res}')
    lines.append('  rfl\n')
    emit('\n'.join(lines))

# ---------------------------------------------------------------- step
fs = facts('step')
def f_(s): return [n for n, t in fs if s in t]
ev_t1 = f_('"Fixed::transpose11x16"')[0]
ev_ds = f_('"Fixed::deltas"')[0]
ev_t16 = f_('"Fixed::transpose20x16"')
ev_t8 = f_('"Fixed::transpose20x8"')[0]
ev_t11 = f_('"Fixed::transpose20x11"')[0]
res = [n for n, t in fs if t.startswith('r = ')][0]
ev_uw1 = f_('"Fixed::update_w1"')[0]; ev_ub1 = f_('"Fixed::update_bias16"')[0]
ev_uw2 = f_('"Fixed::update_w2"')[0]; ev_ub2 = f_('"Fixed::update_bias11"')[0]
used = {ev_t1, ev_ds, ev_t8, ev_t11, res, ev_uw1, ev_ub1, ev_uw2, ev_ub2} | set(ev_t16)
# which transpose20x16 is dzs vs hs
dz16 = [n for n in ev_t16 if '[x_dzs]' in dict(fs)[n]][0]
hs16 = [n for n in ev_t16 if '[x_hs]' in dict(fs)[n]][0]
DS = 'deltasOf m (IxAICore.transposeN m.b1.length m.w2) batch'
lines = ['/-! ## One SGD step -/\n', path_comment('step', used)]
lines.append(f'''/-- **`Fixed::step` is `Model.step`.** On the encoded model, batch and learning rate, every
observed derivation of `Fixed::step` returns the encoding of `Model.step lr m batch`, provided
the model and the batch have the fixed shapes and every value the step rounds or sign-tests is
below `2^55` in magnitude (`StepBounds`, decided by `stepBoundsB`). -/
theorem step_spec {{lr : IxAICore.Fx}} {{m : IxAICore.Model}}
    {{batch : List (List IxAICore.Fx × List IxAICore.Fx)}}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hn : batch.length = 20) (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hb : StepBounds lr m batch) {{h h' : Heap F}} {{r : SourceValue F}} {{calls : List (Call F)}}
    (ev : ObsFn W "Fixed::step"
      [encMat m.w1, encVec m.b1, encMat m.w2, encVec m.b2, encMat (batch.map (·.1)),
        encMat (batch.map (·.2)), fxVal lr] h r h' calls) :
    r = encModel (IxAICore.Model.step lr m batch) := by
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
  have hlen : ({DS}).length = 20 := by
    simp [deltasOf, hn]
  have hdz : (IxAICore.transposeN m.b1.length (({DS}).map (·.dz))).length = 16 := by
    rw [length_transposeN]; exact hb1
  have hdzr : ∀ d ∈ IxAICore.transposeN m.b1.length (({DS}).map (·.dz)), d.length = 20 :=
    fun d hd => by rw [col_length_transposeN _ _ d hd, List.length_map, hlen]
  have hxT : (IxAICore.transposeN (IxAICore.getD m.w1 0 []).length
      (({DS}).map (·.x))).length = 8 := by
    rw [length_transposeN]; exact hI
  have hxTr : ∀ c ∈ IxAICore.transposeN (IxAICore.getD m.w1 0 []).length
      (({DS}).map (·.x)), c.length = 20 :=
    fun c hc => by rw [col_length_transposeN _ _ c hc, List.length_map, hlen]
  have hhT : (IxAICore.transposeN m.b1.length (({DS}).map (·.h))).length = 16 := by
    rw [length_transposeN]; exact hb1
  have hhTr : ∀ c ∈ IxAICore.transposeN m.b1.length (({DS}).map (·.h)), c.length = 20 :=
    fun c hc => by rw [col_length_transposeN _ _ c hc, List.length_map, hlen]
  have hoT : (IxAICore.transposeN m.b2.length (({DS}).map (·.dout))).length = 11 := by
    rw [length_transposeN]; exact hb2
  have hoTr : ∀ d ∈ IxAICore.transposeN m.b2.length (({DS}).map (·.dout)), d.length = 20 :=
    fun d hd => by rw [col_length_transposeN _ _ d hd, List.length_map, hlen]''')
lines.append(obtain_path('step', used))
lines.append(f'''  obtain rfl := transpose11x16_spec hb1 {ev_t1}
  have e := deltas_spec hw1 hw1r hb1 hw2 hw2r hb2 hT hTr hn hex hb.deltas {ev_ds}
  {SIMP_TUP} e
  obtain ⟨rfl, rfl, rfl⟩ := e
  obtain rfl := transpose20x16_spec hb1 {dz16}
  rw [← deltasOf_x m (IxAICore.transposeN m.b1.length m.w2) batch] at {ev_t8}
  obtain rfl := transpose20x8_spec hI {ev_t8}
  obtain rfl := transpose20x16_spec hb1 {hs16}
  obtain rfl := transpose20x11_spec hb2 {ev_t11}
  obtain rfl := update_w1_spec hw1 hw1r hdz hdzr hxT hxTr hb.w1 {ev_uw1}
  obtain rfl := update_bias16_spec hb1 hdz hdzr hb.b1 {ev_ub1}
  obtain rfl := update_w2_spec hw2 hw2r hoT hoTr hhT hhTr hb.w2 {ev_uw2}
  obtain rfl := update_bias11_spec hb2 hoT hoTr hb.b2 {ev_ub2}
  subst {res}
  -- unverified: the closing `rfl` unfolds `encModel`, `xTOf`, `dzTOf`, `hTOf`, `doutTOf` and
  -- `w2TOf` to the terms the update specs return.
  rw [step_of_ne hne]
  rfl
''')
emit('\n'.join(lines))

emit('''/-- **`step_spec` with the host's encodings**: `Fixed::step` on `IxAIAiur.stepArgs m batch lr`
returns `IxAIAiur.modelValue (Model.step lr m batch)`, the value the host's test compares. -/
theorem step_spec_host {lr : IxAICore.Fx} {m : IxAICore.Model}
    {batch : List (List IxAICore.Fx × List IxAICore.Fx)}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hn : batch.length = 20) (hex : ∀ p ∈ batch, p.1.length = 8 ∧ p.2.length = 11)
    (hb : StepBounds lr m batch) {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::step" (IxAIAiur.stepArgs m batch lr) h r h' calls) :
    r = IxAIAiur.modelValue (IxAICore.Model.step lr m batch) :=
  step_spec hw1 hw1r hb1 hw2 hw2r hb2 hn hex hb ev

end IxAIStep.Fixed.Specs''')

def split_long(text, width=100):
    out = []; depth = 0
    for line in text.split('\n'):
        in_comment = depth > 0 or line.lstrip().startswith('--') or line.lstrip().startswith('/-')
        depth += line.count('/-') - line.count('-/')
        if len(line) <= width or in_comment:
            out.append(line); continue
        ind = len(line) - len(line.lstrip())
        cont = ' ' * (ind + 4)
        cur = line
        while len(cur) > width:
            cut = cur.rfind(' ', len(cont) + 1, width)
            if cut <= len(cont): break
            out.append(cur[:cut]); cur = cont + cur[cut + 1:]
        out.append(cur)
    return '\n'.join(out)

open(sys.argv[1], 'w').write(split_long('\n'.join(OUT)) + '\n')
