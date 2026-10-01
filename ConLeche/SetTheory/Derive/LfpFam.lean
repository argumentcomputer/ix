module

public import ConLeche.SetTheory.Derive.Lfp
import ConLeche.SetTheory.Derive.Graphs
@[expose] public section

/-!
# Least pre-fixed points of family functors (task #188, indexed)

The carrier of a directly installed recursive **family** `T : I → Sort w`
is the least pre-fixed point of its constructor-tower functor acting on
FAMILIES — graphs over the index-tuple set `I` with values in `univ w`
(`famSpace`), ordered pointwise (`FamLe`).  This is `Lfp.lean` fibrewise:

    lfpFamSet w I F = i ↦ {x ∈ L₀ i | ∀ closed X, x ∈ X i}

over a classically chosen closed family `L₀` (the empty family when
there is none — TOTAL, so the basis constant `lfpFam` needs no
certificate: `lfpFamSet_mem`).  Under a closed member and monotonicity
the least pre-fixed family is a fixed point (`lfpFamSet_eq`) and
supports fibrewise structural induction (`lfpFamSet_induction`); the
closed member is exhibited by the semantics (the ω-iterate family, per
fibre — `ConLeche/SetModel/Iter.lean`'s `natUnion`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The family space over `I`: graphs into `univ w`. -/
noncomputable def famSpace (w : Nat) (I : V) : V := piSet I fun _ => univ w

/-- The pointwise order on families over `I`. -/
def FamLe (I X Y : V) : Prop := ∀ i, i ∈ˢ I → app X i ⊆ˢ app Y i

theorem FamLe.refl (I X : V) : FamLe I X X := fun _ _ => Subset.refl _

theorem FamLe.trans {I X Y Z : V} (h₁ : FamLe I X Y) (h₂ : FamLe I Y Z) : FamLe I X Z :=
  fun i hi => Subset.trans (h₁ i hi) (h₂ i hi)

/-- An `F`-closed family: a pre-fixed point of `app F` in the family
space. -/
def IsClosedFam (w : Nat) (I F X : V) : Prop :=
  X ∈ˢ famSpace w I ∧ FamLe I (app F X) X

theorem famSpace_app {w : Nat} {I X i : V} (hX : X ∈ˢ famSpace w I) (hi : i ∈ˢ I) :
    app X i ∈ˢ (univ w : V) :=
  app_mem_of_mem_piSet hX hi

/-- Members of the family space agreeing pointwise are equal. -/
theorem famSpace_ext {w : Nat} {I X Y : V} (hX : X ∈ˢ famSpace w I) (hY : Y ∈ˢ famSpace w I)
    (h : ∀ i, i ∈ˢ I → app X i = app Y i) : X = Y :=
  eq_of_mem_piSet_app_eq hX hY h

/-- A graph with fibres in `univ w` is in the family space. -/
theorem graph_mem_famSpace {w : Nat} {I : V} {G : V → V} (h : ∀ i, i ∈ˢ I → G i ∈ˢ (univ w : V)) :
    graph G I ∈ˢ famSpace w I :=
  graph_mem_piSet h

open Classical in
/-- **The least pre-fixed family of `F` over `I`** — fibrewise the
intersection of the closed families when there is one (separated from
a chosen closed family), the empty family otherwise. -/
noncomputable def lfpFamSet (w : Nat) (I F : V) : V :=
  if h : ∃ L, IsClosedFam w I F L then
    graph (fun i => sep (app (Classical.choose h) i)
      (fun x => ∀ X, IsClosedFam w I F X → x ∈ˢ app X i)) I
  else graph (fun _ => empty) I

theorem lfpFamSet_of_not {w : Nat} {I F : V} (h : ¬ ∃ L, IsClosedFam w I F L) :
    lfpFamSet w I F = graph (fun _ => empty) I := by
  unfold lfpFamSet; exact dif_neg h

theorem mem_app_lfpFamSet {w : Nat} {I F i x : V} (h : ∃ L, IsClosedFam w I F L) (hi : i ∈ˢ I) :
    x ∈ˢ app (lfpFamSet w I F) i ↔ ∀ X, IsClosedFam w I F X → x ∈ˢ app X i := by
  unfold lfpFamSet
  rw [dif_pos h, app_graph hi, mem_sep]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩

/-- **Leastness**: the least pre-fixed family lies in every closed
family. -/
theorem lfpFamSet_le {w : Nat} {I F X : V} (hX : IsClosedFam w I F X) :
    FamLe I (lfpFamSet w I F) X :=
  fun _ hi _x hx => (mem_app_lfpFamSet ⟨X, hX⟩ hi).mp hx X hX

/-- **Formation, unconditional**: the least pre-fixed family is in the
family space. -/
theorem lfpFamSet_mem (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ famSpace w I := by
  by_cases h : ∃ L, IsClosedFam w I F L
  · unfold lfpFamSet
    rw [dif_pos h]
    exact graph_mem_famSpace fun _ hi =>
      univ_sep_mem (famSpace_app (Classical.choose_spec h).1 hi)
  · rw [lfpFamSet_of_not h]
    exact graph_mem_famSpace fun _ _ => empty_mem_univ w

/-- Monotonicity of a family functor on the family space. -/
def MonoFam (w : Nat) (I F : V) : Prop :=
  ∀ X Y, X ∈ˢ famSpace w I → Y ∈ˢ famSpace w I → FamLe I X Y → FamLe I (app F X) (app F Y)

/-- The functor maps the family space into itself. -/
def MapsFam (w : Nat) (I F : V) : Prop :=
  ∀ X, X ∈ˢ famSpace w I → app F X ∈ˢ famSpace w I

/-- **Closure**: the least pre-fixed family is a pre-fixed point. -/
theorem lfpFamSet_closed {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) : FamLe I (app F (lfpFamSet w I F)) (lfpFamSet w I F) := by
  intro i hi x hx
  rw [mem_app_lfpFamSet h hi]
  intro X hX
  exact hX.2 i hi x (hmono _ _ (lfpFamSet_mem w I F) hX.1 (lfpFamSet_le hX) i hi x hx)

/-- The least pre-fixed family is a post-fixed point. -/
theorem lfpFamSet_fixed {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) :
    FamLe I (lfpFamSet w I F) (app F (lfpFamSet w I F)) := by
  refine lfpFamSet_le ⟨hmaps _ (lfpFamSet_mem w I F), ?_⟩
  exact hmono _ _ (hmaps _ (lfpFamSet_mem w I F)) (lfpFamSet_mem w I F)
    (lfpFamSet_closed h hmono)

/-- The fixed-point equation, fibrewise. -/
theorem app_lfpFamSet_eq {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) {i : V} (hi : i ∈ˢ I) :
    app (app F (lfpFamSet w I F)) i = app (lfpFamSet w I F) i :=
  Subset.antisymm (lfpFamSet_closed h hmono i hi) (lfpFamSet_fixed h hmono hmaps i hi)

/-- The fixed-point equation. -/
theorem lfpFamSet_eq {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (hmaps : MapsFam w I F) :
    app F (lfpFamSet w I F) = lfpFamSet w I F :=
  famSpace_ext (hmaps _ (lfpFamSet_mem w I F)) (lfpFamSet_mem w I F)
    fun _ hi => app_lfpFamSet_eq h hmono hmaps hi

/-- **Structural induction**, fibrewise: a property closed under the
functor on the carrier holds on the whole carrier. -/
theorem lfpFamSet_induction {w : Nat} {I F : V} (h : ∃ L, IsClosedFam w I F L)
    (hmono : MonoFam w I F) (P : V → V → Prop)
    (hP : ∀ i, i ∈ˢ I → ∀ x,
      x ∈ˢ app (app F (graph (fun i => sep (app (lfpFamSet w I F) i) (P i)) I)) i → P i x) :
    ∀ i, i ∈ˢ I → ∀ x, x ∈ˢ app (lfpFamSet w I F) i → P i x := by
  intro i hi x hx
  have hSmem : graph (fun i => sep (app (lfpFamSet w I F) i) (P i)) I ∈ˢ famSpace w I :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem w I F) hi)
  have hSle : FamLe I (graph (fun i => sep (app (lfpFamSet w I F) i) (P i)) I) (lfpFamSet w I F) := by
    intro i hi y hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
  have hS : IsClosedFam w I F (graph (fun i => sep (app (lfpFamSet w I F) i) (P i)) I) := by
    refine ⟨hSmem, fun i hi y hy => ?_⟩
    rw [app_graph hi, mem_sep]
    refine ⟨?_, hP i hi y hy⟩
    exact lfpFamSet_closed h hmono i hi y
      (hmono _ _ hSmem (lfpFamSet_mem w I F) hSle i hi y hy)
  have := lfpFamSet_le hS i hi x hx
  rw [app_graph hi] at this
  exact (mem_sep.mp this).2

end ConLeche.SetTheory
