module

public import ConLeche.SetTheory.Derive.LfpFam
import ConLeche.SetTheory.Derive.Pt
@[expose] public section

/-!
# The recursion theorem by lfp induction (task #202, Stage A2)

The recursive squash regime's large eliminator: the family lives at
`Prop` (its fibres are truth values, the sole proof the point) and the
recursor eliminates into `Sort ℓ`, `ℓ ≠ 0`.  The recursor's value at an
index `i` is determined by the recursion equation `R i = st i (R on the
predecessors of i)` — well-founded along the family's least fixed
point, which is why it exists and is unique.

This module states that abstractly, `Expr`-free: over an index set `I`
with predecessor sets `pred i ⊆ I`, a bound `B i ∈ univ ℓ` and a step
`st i g` (`g` a choice function of predecessor values), the GRAPH
functor `recGraphStep` sends a family `S` to the family of values
`st i g` for `g ∈ Π_{j ∈ pred i} S j` (within `B i`); it is monotone
and `B` is a closed family, so its least fixed point `recGraph` exists,
and at every index whose `Acc`-family fibre (`accFam`: inhabited iff
`Cond i` and every predecessor's fibre is) is inhabited, `recGraph`'s
fibre is a SINGLETON (`recGraph_exists_unique`) — by
`lfpFamSet_induction` on the `Acc` family: the predecessors' fibres
are singletons, the graph of their elements witnesses existence
(`app_lfpFamSet_eq`), and any element is the step at that same choice
function, by function extensionality on `piSet`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section RecGraph

variable (ℓ : Nat) (I : V) (pred : V → V) (B : V → V) (st : V → V → V)

/-- The graph functor's fibre at `i` over the family `S`. -/
noncomputable def recGraphFibre (S i : V) : V :=
  sep (B i) fun v => ∃ g, g ∈ˢ piSet (pred i) (fun j => app S j) ∧ v = st i g

/-- The graph functor on families over `I`, as a set-function on the
family space. -/
noncomputable def recGraphStep : V :=
  graph (fun S => graph (fun i => recGraphFibre pred B st S i) I) (famSpace ℓ I)

/-- **The recursor's graph**: the least fixed point of the graph
functor. -/
noncomputable def recGraph : V := lfpFamSet ℓ I (recGraphStep ℓ I pred B st)

variable {ℓ I pred B st}

theorem app_recGraphStep {S : V} (hS : S ∈ˢ famSpace ℓ I) :
    app (recGraphStep ℓ I pred B st) S = graph (fun i => recGraphFibre pred B st S i) I :=
  app_graph hS

theorem app_app_recGraphStep {S i : V} (hS : S ∈ˢ famSpace ℓ I) (hi : i ∈ˢ I) :
    app (app (recGraphStep ℓ I pred B st) S) i = recGraphFibre pred B st S i := by
  rw [app_recGraphStep hS, app_graph hi]

theorem mem_recGraphFibre {S i v : V} :
    v ∈ˢ recGraphFibre pred B st S i ↔
      v ∈ˢ B i ∧ ∃ g, g ∈ˢ piSet (pred i) (fun j => app S j) ∧ v = st i g :=
  mem_sep

/-- The functor maps the family space into itself. -/
theorem recGraphStep_maps (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V)) :
    MapsFam ℓ I (recGraphStep ℓ I pred B st) := by
  intro S hS
  rw [app_recGraphStep hS]
  exact graph_mem_famSpace fun i hi => univ_sep_mem (hB i hi)

/-- The functor is monotone: more predecessor values, more steps. -/
theorem recGraphStep_mono (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I) :
    MonoFam ℓ I (recGraphStep ℓ I pred B st) := by
  intro X Y hX hY hle i hi v hv
  rw [app_app_recGraphStep hX hi] at hv
  rw [app_app_recGraphStep hY hi]
  obtain ⟨hvB, g, hg, rfl⟩ := mem_recGraphFibre.mp hv
  refine mem_recGraphFibre.mpr ⟨hvB, g, ?_, rfl⟩
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hg
  refine mem_piSet.mpr ⟨fun p hp => ?_, htot⟩
  obtain ⟨j, hj, y, hy, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
  exact mem_sigmaPairs.mpr ⟨j, hj, y, hle j (hpred i hi j hj) y hy, rfl⟩

/-- The bound is a closed family. -/
theorem recGraphStep_closed (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V)) :
    IsClosedFam ℓ I (recGraphStep ℓ I pred B st) (graph B I) := by
  refine ⟨graph_mem_famSpace hB, fun i hi v hv => ?_⟩
  rw [app_app_recGraphStep (graph_mem_famSpace hB) hi] at hv
  rw [app_graph hi]
  exact (mem_recGraphFibre.mp hv).1

/-- **The fixed-point equation**, fibrewise. -/
theorem app_recGraph_eq (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V))
    (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I) {i : V} (hi : i ∈ˢ I) :
    app (recGraph ℓ I pred B st) i = recGraphFibre pred B st (recGraph ℓ I pred B st) i := by
  unfold recGraph
  rw [← app_lfpFamSet_eq ⟨_, recGraphStep_closed hB⟩ (recGraphStep_mono hpred)
    (recGraphStep_maps hB) hi, app_app_recGraphStep (lfpFamSet_mem _ _ _) hi]

end RecGraph

/-! ## The `Acc` family -/

section AccFam

variable (I : V) (pred : V → V) (Cond : V → Prop)

/-- The `Acc` functor's fibre: inhabited iff the side condition holds
and every predecessor's fibre is inhabited. -/
noncomputable def accFibre (X i : V) : V :=
  truthVal (Cond i ∧ ∀ j, j ∈ˢ pred i → ∃ y, y ∈ˢ app X j)

noncomputable def accStep : V :=
  graph (fun X => graph (fun i => accFibre pred Cond X i) I) (famSpace 0 I)

/-- **The `Acc` family**: the least fixed point of the `Acc` functor at
`Prop`. -/
noncomputable def accFam : V := lfpFamSet 0 I (accStep I pred Cond)

variable {I pred Cond}

theorem app_app_accStep {X i : V} (hX : X ∈ˢ famSpace 0 I) (hi : i ∈ˢ I) :
    app (app (accStep I pred Cond) X) i = accFibre pred Cond X i := by
  unfold accStep
  rw [app_graph hX, app_graph hi]

theorem accStep_maps : MapsFam 0 I (accStep I pred Cond) := by
  intro X hX
  unfold accStep
  rw [app_graph hX]
  refine graph_mem_famSpace fun i _ => ?_
  rw [univ_zero]
  exact truthVal_mem_univZero _

theorem accStep_mono (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I) : MonoFam 0 I (accStep I pred Cond) := by
  intro X Y hX hY hle i hi x hx
  rw [app_app_accStep hX hi] at hx
  rw [app_app_accStep hY hi]
  obtain ⟨⟨hc, hall⟩, rfl⟩ := mem_truthVal.mp hx
  refine mem_truthVal.mpr ⟨⟨hc, fun j hj => ?_⟩, rfl⟩
  obtain ⟨y, hy⟩ := hall j hj
  exact ⟨y, hle j (hpred i hi j hj) y hy⟩

theorem accStep_closed : IsClosedFam 0 I (accStep I pred Cond) (graph (fun _ => unitSet) I) := by
  refine ⟨graph_mem_famSpace fun _ _ => by rw [univ_zero]; exact mem_univZero.mpr (Subset.refl _),
    fun i hi x hx => ?_⟩
  rw [app_app_accStep (graph_mem_famSpace fun _ _ => by
    rw [univ_zero]; exact mem_univZero.mpr (Subset.refl _)) hi] at hx
  rw [app_graph hi]
  obtain ⟨-, rfl⟩ := mem_truthVal.mp hx
  exact pt_mem_unitSet

end AccFam

/-! ## The recursion theorem -/

section RecTheorem

variable {ℓ : Nat} {I : V} {pred : V → V} {B : V → V} {st : V → V → V} {Cond : V → Prop}

/-- **The local step**: at an index whose predecessors' fibres are all
singletons, the recursor's graph has exactly one value. -/
theorem recGraph_singleton_of_preds (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V))
    (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I)
    {i : V} (hi : i ∈ˢ I)
    (hst : ∀ g, g ∈ˢ piSet (pred i) (fun j => app (recGraph ℓ I pred B st) j) → st i g ∈ˢ B i)
    (hP : ∀ j, j ∈ˢ pred i → (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) j) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) j → v' ∈ˢ app (recGraph ℓ I pred B st) j →
        v = v') :
    (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) i) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) i → v' ∈ˢ app (recGraph ℓ I pred B st) i →
        v = v' := by
  -- the choice function of the predecessors' values
  have hchoice : ∀ j, ∃ v, j ∈ˢ pred i → v ∈ˢ app (recGraph ℓ I pred B st) j := fun j =>
    Classical.byCases (fun h : j ∈ˢ pred i => ⟨_, fun _ => Classical.choose_spec (hP j h).1⟩)
      (fun h => ⟨pt, fun h' => absurd h' h⟩)
  have hu : ∀ j, j ∈ˢ pred i →
      Classical.choose (hchoice j) ∈ˢ app (recGraph ℓ I pred B st) j :=
    fun j hj => Classical.choose_spec (hchoice j) hj
  have hg : graph (fun j => Classical.choose (hchoice j)) (pred i)
      ∈ˢ piSet (pred i) (fun j => app (recGraph ℓ I pred B st) j) := graph_mem_piSet hu
  -- any value at `i` is the step at that choice function
  have key : ∀ v, v ∈ˢ app (recGraph ℓ I pred B st) i →
      v = st i (graph (fun j => Classical.choose (hchoice j)) (pred i)) := by
    intro v hv
    rw [app_recGraph_eq hB hpred hi] at hv
    obtain ⟨-, g', hg', rfl⟩ := mem_recGraphFibre.mp hv
    congr 1
    rw [← eq_graph_app_of_mem_piSet hg']
    exact graph_congr fun j hj => (hP j hj).2 _ _ (app_mem_of_mem_piSet hg' hj) (hu j hj)
  refine ⟨⟨st i (graph (fun j => Classical.choose (hchoice j)) (pred i)), ?_⟩,
    fun v v' hv hv' => by rw [key v hv, key v' hv']⟩
  rw [app_recGraph_eq hB hpred hi]
  exact mem_recGraphFibre.mpr ⟨hst _ hg, _, hg, rfl⟩

/-- The graph's selector: the fibre's element (the point off the graph). -/
noncomputable def recSel (G : V) (i : V) : V :=
  open Classical in
  if h : ∃ v, v ∈ˢ app G i then Classical.choose h else pt

theorem recSel_mem {G i : V} (h : ∃ v, v ∈ˢ app G i) : recSel G i ∈ˢ app G i := by
  unfold recSel
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **The recursion equation** at an index whose fibre and whose
predecessors' fibres are singletons: the selector's value is the step
at the selector's graph over the predecessors. -/
theorem recSel_eq (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V))
    (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I) {i : V} (hi : i ∈ˢ I)
    (hPi : ∃ v, v ∈ˢ app (recGraph ℓ I pred B st) i)
    (hP : ∀ j, j ∈ˢ pred i → (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) j) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) j → v' ∈ˢ app (recGraph ℓ I pred B st) j →
        v = v') :
    recSel (recGraph ℓ I pred B st) i
      = st i (graph (fun j => recSel (recGraph ℓ I pred B st) j) (pred i)) := by
  have hv := recSel_mem hPi
  rw [app_recGraph_eq hB hpred hi] at hv
  obtain ⟨-, g', hg', hst⟩ := mem_recGraphFibre.mp hv
  rw [hst]
  congr 1
  rw [← eq_graph_app_of_mem_piSet hg']
  exact graph_congr fun j hj =>
    (hP j hj).2 _ _ (app_mem_of_mem_piSet hg' hj) (recSel_mem (hP j hj).1)

/-- **The recursion theorem by lfp induction**: at every index whose
`Acc`-family fibre is inhabited, the recursor's graph has exactly one
value. -/
theorem recGraph_exists_unique (hB : ∀ i, i ∈ˢ I → B i ∈ˢ (univ ℓ : V))
    (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I)
    (hst : ∀ i, i ∈ˢ I → ∀ g, g ∈ˢ piSet (pred i) (fun j => app (recGraph ℓ I pred B st) j) →
      st i g ∈ˢ B i) :
    ∀ i, i ∈ˢ I → ∀ x, x ∈ˢ app (accFam I pred Cond) i →
      (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) i) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) i → v' ∈ˢ app (recGraph ℓ I pred B st) i →
        v = v' := by
  refine lfpFamSet_induction ⟨_, accStep_closed (pred := pred) (Cond := Cond)⟩ (accStep_mono hpred)
    (fun i _ => (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) i) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) i → v' ∈ˢ app (recGraph ℓ I pred B st) i →
        v = v') ?_
  intro i hi x hx
  have hsubmem : graph (fun i => sep (app (lfpFamSet 0 I (accStep I pred Cond)) i)
      (fun _ => (∃ v, v ∈ˢ app (recGraph ℓ I pred B st) i) ∧
        ∀ v v', v ∈ˢ app (recGraph ℓ I pred B st) i → v' ∈ˢ app (recGraph ℓ I pred B st) i →
          v = v')) I ∈ˢ famSpace 0 I :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  rw [app_app_accStep hsubmem hi] at hx
  obtain ⟨⟨-, hall⟩, -⟩ := mem_truthVal.mp hx
  refine recGraph_singleton_of_preds hB hpred hi (hst i hi) fun j hj => ?_
  obtain ⟨y, hy⟩ := hall j hj
  rw [app_graph (hpred i hi j hj)] at hy
  exact (mem_sep.mp hy).2

end RecTheorem

end ConLeche.SetTheory
