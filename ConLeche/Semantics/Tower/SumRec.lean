module

public import ConLeche.Semantics.Tower.SumRecCase

@[expose] public section

/-!
# The sum recursor leaf (task #175 sum-types, stage S4b; indexed)

`sumRecAV ℓ w rds Fss Ess srcs nIdx = mkLamsC ℓ rds (sumRecBodyAV …)` —
the constant-bit λ-tower (bit `ℓ`) over the recursor type reading's
binder data (parameters, motive, one minor per constructor, the
`nIdx` index binders, major), whose body sits one binder below the
K-frame `(p⃗, motive, minors, ı⃗)` and is, in the **graph regime**, the
case recursor (`caseRecAV`, stage `0`, depth `1`) on the major's tag
applied to the major's payload:

    sumRecBodyAV = (caseRec 0 (t.0)) (t.1)        t = bvar 0

and at a **squash instantiation** (`w = 0`, task #175 indexed) the
first minor applied to the fields' SOURCES — an index variable for a
field that is one of the constructor's index expressions, the point
for a proof field (`srcAV`): the squashed value carries no field, so
the recursor reads the data fields off the index arguments, which is
official's subsingleton elimination (`Eq`'s large eliminator).  A
squash body with no constructor is the point.

`sumRecBody_facts` gives the body's grading and its membership in
`M ı⃗ t` at every carrier member (the graph regime through the case
recursor's stage-`0` motive; the squash regime through the minors'
inhabitation at a zero elimination level, and through the sources'
fit when the elimination level is nonzero — then there is exactly one
constructor and the sources ARE the witness's fields, `SqHypS.hsrc`),
and `sumRecBody_iota` the iota: at `t = inj j (mkTower (f⃗ ++ [pt]))`
the body is minor `j` folded along `f⃗`.  The leaf's ONE hereditary
premise is `RecPreS` — the parameter walk ending in `RecBaseS`: the
motive entry graded, and under every motive, minor and index the
major entry reads to the carrier and the K-frame satisfies `RecHypS`
and `SqHypS` — and `underTowerOk_of_recPreS` turns it into the
tower's premise.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The sources -/

/-- A field's source at depth `D'` below the K-frame: the index
variable it occurs as, or the point. -/
def srcAV (nIdx D' : Nat) : Option Nat → AnnotTerm
  | some l => .bvar (D' + nIdx - 1 - l)
  | none => .prf

/-- The sources' values at an index tuple. -/
noncomputable def srcVals (is : List V) (src : List (Option Nat)) : List V :=
  src.map fun s => match s with
    | some l => is.getD l pt
    | none => pt

theorem srcAV_wellDenoted (nIdx D' : Nat) (s : Option Nat) (σ : Nat → V) : WellDenoted V σ (srcAV nIdx D' s) := by
  cases s <;> trivial

/-- The sources read to their values at the frame. -/
theorem map_srcAV_interp {nIdx D' : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D' ρ₀ σ)
    (src : List (Option Nat)) (hsrc : ∀ s ∈ src, ∀ l, s = some l → l < nIdx) :
    (src.map (srcAV nIdx D')).map (interp V σ) = srcVals (frameIdx nIdx ρ₀) src := by
  unfold srcVals
  rw [List.map_map]
  apply List.map_congr_left
  intro s hs
  cases s with
  | none => rfl
  | some l =>
    simp only [Function.comp_def, srcAV, interp_bvar]
    exact h.idx (hsrc _ hs l rfl)

/-! ## The major's projections -/

/-- The major's own `sigmaSet` package — the payload both projection
nodes' gradings ask for (task #225: one fact, two clause equations). -/
theorem major_sigma {w : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss' : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ₀ Fss') (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρ₀ Fss')) :
    ∃ u v A Bf, interp V σ (.bvar 0) ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V) := by
  refine ⟨w, w, omega, natFibre (sumFibre w ρ₀ Fss'), ?_, omega_mem_univ_pos hw, ?_⟩
  · rw [interp_bvar, show Nat.max w w = w from Nat.max_self w]
    exact ht
  · intro k hk
    obtain ⟨i', rfl, hfib⟩ := natFibre_of_mem (sumFibre w ρ₀ Fss') hk
    rw [hfib]
    unfold sumFibre
    cases hi' : Fss'[i']? with
    | none => exact empty_mem_univ w
    | some Fs =>
      exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? hi')).toBound hw)

/-- The major's tag node is graded (graph regime) through the
carrier's own `sigmaSet`. -/
theorem major_fst_wellDenoted {w : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V}
    {Fss' : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ₀ Fss') (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρ₀ Fss')) :
    WellDenoted V σ (.fst (.bvar 0)) := by
  rw [WellDenoted_fst]
  exact ⟨trivial, major_sigma hw hok ht⟩

/-- The major's payload node, the same way. -/
theorem major_snd_wellDenoted {w : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V}
    {Fss' : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ₀ Fss') (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρ₀ Fss')) :
    WellDenoted V σ (.snd (.bvar 0)) := by
  rw [WellDenoted_snd]
  exact ⟨trivial, major_sigma hw hok ht⟩

/-! ## The body -/

theorem foldl_app_pt_sum : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt_sum ts

/-! ## The hereditary premise -/

/-- The conclusion `motive ı⃗ t` spelled at the body frame. -/
def recConcAV (n nIdx : Nat) : AnnotTerm := .app (motAppAV n nIdx 1) (.bvar 0)

end ConLeche.Semantics
