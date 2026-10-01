module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.SetModel.TupleTower

@[expose] public section

/-!
# The telescope introduction: `TeleS` from an interpreted binder chain
(task #175, stage 1)

The tuple tier (`ConLeche/SetBase/TupleTower.lean`) states its laws over
an abstract dependent telescope `TeleS V n`.  A checked
direct-structure block does not hand the install a `TeleS` — it hands
a list of **annotated field domains** (`Fs : List AnnotTerm`, the
constructor type reading's pi-domains after the parameters, each
scoped under its predecessors).  This module is the bridge:

    teleOfFields ρ Fs : TeleS V Fs.length

interprets the chain under successively consed environments — the
dependency of field `i` on fields `0..i−1` is carried by the
*environment*, exactly as `interp` carries every binder dependency,
so the length-indexed fully-dependent tail of `TeleS`
(`cons (A : V) (B : V → TeleS V n)`) is populated with no new
machinery: `B a` is the tail's telescope at `cons a ρ`.

The tier's premise/conclusion currencies transpose:

| tier | AnnotTerm currency (this file) |
|---|---|
| `FitsS T as` | `SpineFit ρ Fs as` (`fitsS_teleOfFields`) |
| `teleNth T i pre` | `⟦Fs[i]⟧` at `consList pre ρ` (`teleNth_teleOfFields`) |
| `BoundS w T` | `FieldsBound w ρ Fs` (`boundS_teleOfFields`) |
| `PropS T` | `FieldsBound 0 ρ Fs` (`propS_teleOfFields`; `univ_zero`) |

`FieldsGraded` carries the **per-field** sort data `(uᵢ, Fᵢ)` the O5
check (`checkStructFieldUniv`, field sort `≤` result sort) produces:
`fieldsBound_of_graded` is O5's semantic discharge (cumulativity,
`univ_mono`), and at a squash instantiation (`w = 0`) the same bound
forces every field sort to `0`, which is the O4/R1 branch —
`propS_of_graded` gives `PropS`, so the squash projection laws hold
with no extra check for the O5-covered class.  R2 (recursive fields)
never reaches this file: O2 excludes the class syntactically, and the
`teleOfFields` walk interprets every domain in the pre-block alphabet.

The four capstone corollaries (`mkTower_mem_teleOfFields`,
`towerSet_elim_teleOfFields`, `projS_mem_teleOfFields`,
`towerSet_univ_teleOfFields`) are the tier's intro/eta/projection/
formation laws restated in the AnnotTerm currency — the shapes the
stage-4 install battery consumes.  `projS_mem_teleOfFields`'s premise
`(w = 0 → FieldsBound 0 ρ Fs)` IS the per-use O4/R1 branch: vacuous at
graph instantiations, the proof-field legality (`infer_proj`'s Prop
restriction, semantically) at squash ones.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The environment a value spine ends in: the values consed in order,
outermost (earliest binder) first — `consList [a₀, …, aₖ] ρ` is the
frame under binders `a₀ … aₖ`, innermost last.  (The Model tier's
`consN` (`IndTeleP.lean`) is the same fold; this copy exists because
that module is a lane module and this one is lane-neutral base.) -/
def consList : List V → (Nat → V) → Nat → V
  | [], ρ => ρ
  | a :: as, ρ => consList as (cons a ρ)

omit [SetTheory V] in
@[simp] theorem consList_nil (ρ : Nat → V) : consList [] ρ = ρ := rfl

omit [SetTheory V] in
@[simp] theorem consList_cons (a : V) (as : List V) (ρ : Nat → V) :
    consList (a :: as) ρ = consList as (cons a ρ) := rfl

/-- **The telescope introduction**: the semantic `TeleS` over the
interpreted binder chain.  Field `i`'s set is `⟦Fs[i]⟧` at the
environment binding the earlier fields' values — the dependent tail is
the interpretation environment itself. -/
noncomputable def teleOfFields (ρ : Nat → V) :
    (Fs : List AnnotTerm) → TeleS V Fs.length
  | [] => .nil
  | F :: Fs => .cons (interp V ρ F) fun a => teleOfFields (cons a ρ) Fs

@[simp] theorem teleOfFields_nil (ρ : Nat → V) :
    teleOfFields ρ ([] : List AnnotTerm) = .nil := rfl

@[simp] theorem teleOfFields_cons (ρ : Nat → V) (F : AnnotTerm)
    (Fs : List AnnotTerm) :
    teleOfFields ρ (F :: Fs)
      = .cons (interp V ρ F) (fun a => teleOfFields (cons a ρ) Fs) := rfl

/-- `SpineFit ρ Fs as`: the values fit the interpreted chain — right
length, each value in its domain's interpretation at the earlier
values.  The AnnotTerm currency of the tier's `FitsS`. -/
def SpineFit (ρ : Nat → V) : List AnnotTerm → List V → Prop
  | [], [] => True
  | F :: Fs, a :: as => a ∈ˢ interp V ρ F ∧ SpineFit (cons a ρ) Fs as
  | _, _ => False

/-- `FieldsBound w ρ Fs`: every field's interpretation lives in
`univ w`, hereditarily — O5's semantic form, the tier's `BoundS`. -/
def FieldsBound (w : Nat) (ρ : Nat → V) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => interp V ρ F ∈ˢ (univ w : V) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBound w (cons a ρ) Fs

/-- `FieldsGraded ρ Ds`: the per-field grading — field `i`'s
interpretation lives in `univ uᵢ` at its own sort numeral `uᵢ`,
hereditarily.  `Ds` is the `(sort, domain)` zip the O5/O4 checks
produce. -/
def FieldsGraded (ρ : Nat → V) : List (Nat × AnnotTerm) → Prop
  | [] => True
  | d :: Ds => interp V ρ d.2 ∈ˢ (univ d.1 : V) ∧
      ∀ a, a ∈ˢ interp V ρ d.2 → FieldsGraded (cons a ρ) Ds

omit [SetTheory V] in
theorem consList_append (xs ys : List V) (ρ : Nat → V) :
    consList (xs ++ ys) ρ = consList ys (consList xs ρ) := by
  induction xs generalizing ρ with
  | nil => rfl
  | cons x xs ih => rw [List.cons_append, consList_cons, consList_cons, ih]

/-- Fits concatenate: a fit of the first chain and a fit of the second
at the extended environment give a fit of the concatenation. -/
theorem SpineFit.append :
    ∀ {Fs₁ : List AnnotTerm} {as₁ : List V} {Fs₂ : List AnnotTerm}
      {as₂ : List V} {ρ : Nat → V},
      SpineFit ρ Fs₁ as₁ → SpineFit (consList as₁ ρ) Fs₂ as₂ →
      SpineFit ρ (Fs₁ ++ Fs₂) (as₁ ++ as₂)
  | [], [], _, _, _, _, h₂ => h₂
  | [], _ :: _, _, _, _, h₁, _ => h₁.elim
  | _ :: _, [], _, _, _, h₁, _ => h₁.elim
  | _ :: Fs₁, _a :: as₁, _, _, _, h₁, h₂ =>
    ⟨h₁.1, SpineFit.append (Fs₁ := Fs₁) (as₁ := as₁) h₁.2 h₂⟩

theorem SpineFit.length_eq :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V},
      SpineFit ρ Fs as → as.length = Fs.length
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | _ :: Fs, _, _ :: as, h =>
    congrArg Nat.succ (SpineFit.length_eq (Fs := Fs) (as := as) h.2)

/-- The fit currencies coincide: the tier's `FitsS` at `teleOfFields`
is `SpineFit`. -/
theorem fitsS_teleOfFields :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V},
      FitsS (teleOfFields ρ Fs) as ↔ SpineFit ρ Fs as
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | _ :: Fs, _, _ :: as =>
    and_congr Iff.rfl (fitsS_teleOfFields (Fs := Fs) (as := as))

/-- The `i`-th field set at a prefix valuation is the `i`-th domain's
interpretation at the prefix environment. -/
theorem teleNth_teleOfFields :
    ∀ {Fs : List AnnotTerm} (ρ : Nat → V) (i : Nat) (h : i < Fs.length)
      (pre : List V), pre.length = i →
      teleNth (teleOfFields ρ Fs) i pre = interp V (consList pre ρ) Fs[i]
  | F :: Fs, ρ, 0, _, [], _ => rfl
  | F :: Fs, ρ, i + 1, h, a :: pre, hlen => by
    rw [List.getElem_cons_succ, consList_cons]
    exact teleNth_teleOfFields (cons a ρ) i (Nat.lt_of_succ_lt_succ h) pre
      (Nat.succ.inj hlen)

/-- The bound currencies coincide: the tier's `BoundS` at
`teleOfFields` is `FieldsBound`. -/
theorem boundS_teleOfFields :
    ∀ {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V},
      BoundS w (teleOfFields ρ Fs) ↔ FieldsBound w ρ Fs
  | _, [], _ => Iff.rfl
  | _, _ :: Fs, _ =>
    and_congr Iff.rfl (forall_congr' fun _a => imp_congr Iff.rfl
      (boundS_teleOfFields (Fs := Fs)))

/-- The squash currency: the tier's `PropS` at `teleOfFields` is
`FieldsBound 0` (`univ 0 = univZero` definitionally). -/
theorem propS_teleOfFields :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V},
      PropS (teleOfFields ρ Fs) ↔ FieldsBound 0 ρ Fs
  | [], _ => Iff.rfl
  | _ :: Fs, _ =>
    and_congr (by rw [univ_zero]) (forall_congr' fun _a => imp_congr Iff.rfl
      (propS_teleOfFields (Fs := Fs)))

/-- **O5's semantic discharge**: per-field grading plus the per-field
sort bound gives the hereditary `univ w` bound, by cumulativity. -/
theorem fieldsBound_of_graded {w : Nat} :
    ∀ {Ds : List (Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsGraded ρ Ds → (∀ d ∈ Ds, d.1 ≤ w) →
      FieldsBound w ρ (Ds.map (·.2))
  | [], _, _, _ => trivial
  | d :: Ds, _, hg, hle =>
    ⟨univ_mono (hle d (.head _)) _ hg.1,
     fun a ha => fieldsBound_of_graded (Ds := Ds) (hg.2 a ha)
       (fun d' hd' => hle d' (.tail _ hd'))⟩

/-- **The O4/R1 squash branch**: all field sorts `0` gives `PropS` —
the proof-field legality premise of the squash projection laws.  In
the O5-covered class this is derivable at every squash instantiation
(each `uᵢ ≤ 0`). -/
theorem propS_of_graded {Ds : List (Nat × AnnotTerm)} {ρ : Nat → V}
    (hg : FieldsGraded ρ Ds) (h0 : ∀ d ∈ Ds, d.1 = 0) :
    PropS (teleOfFields ρ (Ds.map (·.2))) :=
  propS_teleOfFields.mpr
    (fieldsBound_of_graded hg fun d hd => Nat.le_of_eq (h0 d hd))

/-! ## The tier's laws at the interpreted telescope

The four capstone corollaries, in the currencies the install battery
consumes.  Iota needs no bridge at all (`projS_mkTower` mentions no
telescope), and coherence (`mkTower_inj`) likewise. -/

/-- **Introduction** (graph regime): a fitting spine's tower inhabits
the interpreted carrier. -/
theorem mkTower_mem_teleOfFields {w : Nat} (hw : w ≠ 0)
    {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ Fs as) :
    mkTower as ∈ˢ towerSet w (teleOfFields ρ Fs) :=
  mkTower_mem hw (fitsS_teleOfFields.mpr hsp)

/-- **Introduction** (squash regime): a fitting spine puts `pt` in the
interpreted carrier. -/
theorem pt_mem_tower_teleOfFields {Fs : List AnnotTerm} {ρ : Nat → V}
    {as : List V} (hsp : SpineFit ρ Fs as) :
    (pt : V) ∈ˢ towerSet 0 (teleOfFields ρ Fs) :=
  pt_mem_tower (fitsS_teleOfFields.mpr hsp)

/-- **Eta + elimination** (graph regime): a member of the interpreted
carrier is the tower of its own projections, and those projections fit
the interpreted chain. -/
theorem towerSet_elim_teleOfFields {w : Nat} (hw : w ≠ 0)
    {Fs : List AnnotTerm} {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ towerSet w (teleOfFields ρ Fs)) :
    SpineFit ρ Fs (projList Fs.length x)
      ∧ x = mkTower (projList Fs.length x) := by
  obtain ⟨hf, heta⟩ := towerSet_elim hw (teleOfFields ρ Fs) hx
  exact ⟨fitsS_teleOfFields.mp hf, heta⟩

/-- **Projection membership**, two regimes in one statement: the
`i`-th projection lands in the `i`-th domain's interpretation at the
earlier projections.  The premise is the O4/R1 per-use branch —
vacuous at a graph instantiation, the proof-field legality (`PropS`
via `propS_teleOfFields`) at a squash one. -/
theorem projS_mem_teleOfFields {w : Nat} {Fs : List AnnotTerm}
    {ρ : Nat → V} {x : V} (hreg : w = 0 → FieldsBound 0 ρ Fs)
    (hx : x ∈ˢ towerSet w (teleOfFields ρ Fs)) {i : Nat}
    (h : i < Fs.length) :
    projS i x ∈ˢ interp V (consList (projList i x) ρ) Fs[i] := by
  have hnth := teleNth_teleOfFields ρ i h (projList i x)
    (projList_length i x)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hm := projS_mem_zero (propS_teleOfFields.mpr (hreg rfl)) hx i h
    rwa [hnth] at hm
  · have hm := projS_mem (Nat.pos_iff_ne_zero.mp hw) hx i h
    rwa [hnth] at hm

/-- **Formation** (graph regime): the interpreted carrier lives at the
structure's own level, from the hereditary bound. -/
theorem towerSet_univ_teleOfFields {w : Nat} {Fs : List AnnotTerm}
    {ρ : Nat → V} (hb : FieldsBound w ρ Fs) :
    towerSet w (teleOfFields ρ Fs) ∈ˢ (univ w : V) :=
  towerSet_mem_univ _ (boundS_teleOfFields.mpr hb)

/-- **Formation** (squash regime) needs nothing: restated for the
consumer's symmetry. -/
theorem towerSet_zero_univZero_teleOfFields {Fs : List AnnotTerm}
    {ρ : Nat → V} :
    towerSet 0 (teleOfFields ρ Fs) ∈ˢ (univZero : V) :=
  towerSet_zero_mem_univZero _

end ConLeche.Semantics
