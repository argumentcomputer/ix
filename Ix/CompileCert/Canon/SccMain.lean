import Ix.CompileCert.Canon.SccStep

/-!
# M7 L1, components: the components are the strongly connected components

`Ix.Compile.Canon.condensation adj` runs Tarjan's loop from every node in index order over
the graph with out-of-range successors dropped (`filt adj`). When it returns (`some C`):

* `condensation_cover`, `condensation_range`, `condensation_unique`: every node is in exactly
  one component, and components hold only nodes;
* `condensation_scc`: two nodes are in one component exactly when each reaches the other (the
  components are the strongly connected components, design document §2.1, Def 2.1);
* `condensation_topo`: every edge goes from a component to the same or an earlier one, so
  reachability between components follows the reverse order of `C.comps` and the
  condensation is acyclic (`condensation_acyclic`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-! ## The loop -/

theorem popComponent_exhausted' (st : TarjanState) (v : Nat) :
    (st.popComponent v).exhausted = st.exhausted := by
  cases st; simp only [TarjanState.popComponent]

theorem finishSt_index (st : TarjanState) (v : Nat) (rest : List (Nat × Nat)) :
    (finishSt st v rest).index = st.index := by
  unfold finishSt
  split <;> (try split) <;> simp [setLow_index, popComponent_index'] <;>
    first | rfl | simp [popComponent_index']

theorem finishSt_exhausted (st : TarjanState) (v : Nat) (rest : List (Nat × Nat)) :
    (finishSt st v rest).exhausted = st.exhausted := by
  unfold finishSt
  split <;> (try split) <;> simp [setLow_exhausted, popComponent_exhausted'] <;>
    first | rfl | simp [popComponent_exhausted']

/-- `tarjanLoop` keeps the invariant; when it does not run out of fuel it ends with an empty
call stack; visited nodes stay visited; exhaustion is never undone. -/
theorem tarjanLoop_spec {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (fuel : Nat) (st : TarjanState), Inv G st →
      Inv G (tarjanLoop G fuel st) ∧
      ((tarjanLoop G fuel st).exhausted = false → (tarjanLoop G fuel st).calls = []) ∧
      (∀ r, ix st r ≠ 0 → ix (tarjanLoop G fuel st) r ≠ 0) ∧
      (st.exhausted = true → (tarjanLoop G fuel st).exhausted = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st I
    rw [tarjanLoop_zero]
    split
    · rename_i h
      exact ⟨I, fun _ => by simpa using h, fun _ h => h, id⟩
    · refine ⟨I.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, (fun h => by simp at h), (fun _ h => h),
        (fun _ => rfl)⟩
  | succ fuel ih =>
    intro st I
    cases hc : st.calls with
    | nil =>
      rw [tarjanLoop_nil G fuel st hc]
      exact ⟨I, fun _ => hc, fun _ h => h, id⟩
    | cons p rest =>
      obtain ⟨v, i⟩ := p
      by_cases hi : i < (succs G v).size
      · by_cases h0 : ix st (succs G v)[i] = 0
        · rw [tarjanLoop_new G fuel st v i rest hc hi h0]
          obtain ⟨A, B, C, D⟩ := ih _ (inv_new I hG hc hi h0)
          refine ⟨A, B, fun r hr => C r ?_, fun h => D (by rw [visit_exhausted]; exact h)⟩
          have hsz : (succs G v)[i] < st.index.size := by
            rw [I.szI]; exact hG _ _ (mem_succs_of_getElem hi)
          rw [ix_visit (st := ({ st with calls := (v, i + 1) :: rest } : TarjanState)) hsz]
          have : r ≠ (succs G v)[i] := fun e => hr (e ▸ h0)
          simp only [this, ↓reduceIte]; exact hr
        · by_cases hon : os st (succs G v)[i] = true
          · rw [tarjanLoop_on G fuel st v i rest hc hi h0 hon]
            obtain ⟨A, B, C, D⟩ := ih _ (inv_on I hc hi h0 hon)
            exact ⟨A, B, fun r hr => C r (by simpa [ix, setLow_index] using hr),
              fun h => D (by rw [setLow_exhausted]; exact h)⟩
          · have hon' : os st (succs G v)[i] = false := by simpa using hon
            rw [tarjanLoop_done G fuel st v i rest hc hi h0 hon']
            obtain ⟨A, B, C, D⟩ := ih _ (inv_done I hc hi h0 hon')
            exact ⟨A, B, fun r hr => C r hr, fun h => D h⟩
      · rw [tarjanLoop_finish G fuel st v i rest hc hi]
        obtain ⟨A, B, C, D⟩ := ih _ (inv_finish I hc hi)
        exact ⟨A, B, fun r hr => C r (by simpa [ix, finishSt_index] using hr),
          fun h => D (by rw [finishSt_exhausted]; exact h)⟩

/-! ## The roots -/

/-- One step of `condensation`'s fold over the roots. -/
def rootStep (G : Array (Array Nat)) (s : TarjanState × Nat) (r : Nat) : TarjanState × Nat :=
  match s with
  | (st, fuel) =>
    if st.exhausted || st.index[r]?.getD 0 != 0 then (st, fuel)
    else (tarjanLoop G fuel (st.visit r), fuel)

/-- What the fold over the roots keeps. -/
def RootInv (G : Array (Array Nat)) (st : TarjanState) : Prop :=
  Inv G st ∧ (st.exhausted = false → st.calls = [] ∧ st.stack = [])

theorem empty_stack_of_calls {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st)
    (h : st.calls = []) : st.stack = [] := by
  cases hs : st.stack with
  | nil => rfl
  | cons x xs =>
    obtain ⟨g, hg, -⟩ := I.stack_gray x (by rw [hs]; simp)
    simp [grays, h] at hg

theorem rootStep_spec {G : Array (Array Nat)} (hG : Bounded G) (s : TarjanState × Nat) (r : Nat)
    (hr : r < G.size) (h : RootInv G s.1) :
    RootInv G (rootStep G s r).1 ∧ (∀ u, ix s.1 u ≠ 0 → ix (rootStep G s r).1 u ≠ 0) ∧
    (s.1.exhausted = true → (rootStep G s r).1.exhausted = true) ∧
    ((rootStep G s r).1.exhausted = false → ix (rootStep G s r).1 r ≠ 0) := by
  obtain ⟨st, fuel⟩ := s
  obtain ⟨I, hcs⟩ := h
  simp only [rootStep]
  split
  · rename_i hskip
    refine ⟨⟨I, hcs⟩, fun _ h => h, id, fun hex => ?_⟩
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hskip
    rcases hskip with hskip | hskip
    · simp only at hex; rw [hskip] at hex; cases hex
    · exact hskip
  · rename_i hgo
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hgo
    obtain ⟨hex, h0'⟩ := hgo
    have h0 : ix st r = 0 := h0'
    have hex' : st.exhausted = false := by simpa using hex
    obtain ⟨hc, hs⟩ := hcs hex'
    have I1 := inv_root I hc hs hr h0
    obtain ⟨A, B, C, D⟩ := tarjanLoop_spec hG fuel _ I1
    have hsz : r < st.index.size := by rw [I.szI]; exact hr
    refine ⟨⟨A, fun h => ⟨B h, empty_stack_of_calls A (B h)⟩⟩, fun u hu => C u ?_, fun h => ?_,
      fun _ => C r ?_⟩
    · rw [ix_visit hsz]
      have : u ≠ r := fun e => hu (e ▸ h0)
      simp only [this, ↓reduceIte]; exact hu
    · simp [hex'] at h
    · rw [ix_visit hsz]; simp; exact Nat.ne_of_gt I.next_pos

theorem fold_spec {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (l : List Nat), (∀ r ∈ l, r < G.size) → ∀ (s : TarjanState × Nat), RootInv G s.1 →
      RootInv G (l.foldl (rootStep G) s).1 ∧
      (∀ u, ix s.1 u ≠ 0 → ix (l.foldl (rootStep G) s).1 u ≠ 0) ∧
      (s.1.exhausted = true → (l.foldl (rootStep G) s).1.exhausted = true) ∧
      ((l.foldl (rootStep G) s).1.exhausted = false → ∀ r ∈ l, ix (l.foldl (rootStep G) s).1 r ≠ 0) := by
  intro l
  induction l with
  | nil => intro _ s h; exact ⟨h, fun _ h => h, id, fun _ r hr => by simp at hr⟩
  | cons r rs ih =>
    intro hl s h
    obtain ⟨A, B, C, D⟩ := rootStep_spec hG s r (hl r (by simp)) h
    obtain ⟨A', B', C', D'⟩ := ih (fun r' hr' => hl r' (by simp [hr'])) (rootStep G s r) A
    simp only [List.foldl_cons]
    refine ⟨A', fun u hu => B' u (B u hu), fun h => C' (C h), fun hex r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with hr' | hr'
    · subst hr'
      by_cases he : (rootStep G s r').1.exhausted = true
      · rw [C' he] at hex; cases hex
      · exact B' r' (D (by simpa using he))
    · exact D' hex r' hr'

/-! ## `condensation` -/

/-- The graph `condensation` runs on: successors outside the node range dropped. -/
def filt (adj : Array (Array Nat)) : Array (Array Nat) := adj.map (·.filter (· < adj.size))

theorem filt_size (adj : Array (Array Nat)) : (filt adj).size = adj.size := by simp [filt]

theorem succs_filt (adj : Array (Array Nat)) (v : Nat) :
    succs (filt adj) v = (adj[v]?.getD #[]).filter (· < adj.size) := by
  simp only [succs, filt, Array.getElem?_map]
  cases adj[v]? <;> rfl

theorem edge_filt {adj : Array (Array Nat)} {u w : Nat} :
    Edge (filt adj) u w ↔ w ∈ adj[u]?.getD #[] ∧ w < adj.size := by
  simp only [Edge, succs_filt, Array.mem_filter, decide_eq_true_eq]

theorem filt_bounded (adj : Array (Array Nat)) : Bounded (filt adj) := fun _ _ e => by
  rw [filt_size]; exact (edge_filt.1 e).2

/-- The fuel `condensation` gives every root. -/
def fuel0 (adj : Array (Array Nat)) : Nat := (filt adj).foldl (init := 0) (· + ·.size) + adj.size + 1

theorem condensation_eq (adj : Array (Array Nat)) : condensation adj =
    let st := ((List.range adj.size).foldl (rootStep (filt adj)) (initSt adj.size, fuel0 adj)).1
    if st.exhausted then none else some { comps := st.comps, roots := st.roots, order := st.order } := by
  rfl

/-- `condensation`'s final state satisfies the invariant with empty stacks, every node visited. -/
theorem condensation_state {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) :
    ∃ st, Inv (filt adj) st ∧ st.calls = [] ∧ st.stack = [] ∧
      (∀ r < adj.size, ix st r ≠ 0) ∧ C.comps = st.comps := by
  rw [condensation_eq] at h
  simp only at h
  have I0 : RootInv (filt adj) (initSt adj.size, fuel0 adj).1 := by
    refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
    have := inv_init (filt adj); rw [filt_size] at this; exact this
  obtain ⟨⟨A, B⟩, -, -, D⟩ := fold_spec (filt_bounded adj) (List.range adj.size)
    (fun r hr => by rw [filt_size]; simpa using hr) _ I0
  generalize ((List.range adj.size).foldl (rootStep (filt adj)) (initSt adj.size, fuel0 adj)) = s
    at h A B D
  split at h
  · cases h
  · rename_i hex
    have hex' : s.1.exhausted = false := by simpa using hex
    cases h
    exact ⟨s.1, A, (B hex').1, (B hex').2, fun r hr => D hex' r (by simpa using hr), rfl⟩

/-! ## The components are the strongly connected components -/

section
variable {adj : Array (Array Nat)} {C : Condensation} (h : condensation adj = some C)
include h

/-- Every node is in a component. -/
theorem condensation_cover : ∀ v < adj.size, ∃ c ∈ C.comps, v ∈ c := by
  obtain ⟨st, I, -, hs, hv, hc⟩ := condensation_state h
  intro v hvn
  rw [hc]; exact (I.comp_iff v).2 ⟨hv v hvn, by rw [hs]; simp⟩

/-- Components hold only nodes. -/
theorem condensation_range : ∀ c ∈ C.comps, ∀ v ∈ c, v < adj.size := by
  obtain ⟨st, I, -, -, -, hc⟩ := condensation_state h
  intro c hcm v hvc
  rw [hc] at hcm
  have := ((I.comp_iff v).1 ⟨c, hcm, hvc⟩).1
  have := I.lt_of_ix this; rwa [filt_size] at this

/-- No node is in two components. -/
theorem condensation_unique : ∀ (k k' : Nat) (c c' : Array Nat) (v : Nat),
    C.comps[k]? = some c → C.comps[k']? = some c' → v ∈ c → v ∈ c' → k = k' := by
  obtain ⟨st, I, -, -, -, hc⟩ := condensation_state h
  rw [hc]; exact I.comp_uniq

/-- Every edge goes from a component to the same or an earlier one (`C.comps` is in reverse
topological order of the condensation). -/
theorem condensation_topo : ∀ (k : Nat) (c : Array Nat) (u w : Nat), C.comps[k]? = some c →
    u ∈ c → Edge (filt adj) u w → ∃ k' c', k' ≤ k ∧ C.comps[k']? = some c' ∧ w ∈ c' := by
  obtain ⟨st, I, -, -, -, hc⟩ := condensation_state h
  rw [hc]; exact I.comp_down

/-- Nodes reachable from a component lie in the same or an earlier component. -/
theorem condensation_reach {k : Nat} {c : Array Nat} {u w : Nat} (hk : C.comps[k]? = some c)
    (hu : u ∈ c) (r : Reach (filt adj) u w) : ∃ k' c', k' ≤ k ∧ C.comps[k']? = some c' ∧ w ∈ c' := by
  induction r with
  | refl => exact ⟨k, c, Nat.le_refl _, hk, hu⟩
  | tail _ e ih =>
    obtain ⟨k1, c1, hle1, hk1, hv1⟩ := ih
    obtain ⟨k2, c2, hle2, hk2, hw2⟩ := condensation_topo h k1 c1 _ _ hk1 hv1 e
    exact ⟨k2, c2, Nat.le_trans hle2 hle1, hk2, hw2⟩

/-- **Components are strongly connected components** (Def 2.1): two nodes are in one component
exactly when each reaches the other. -/
theorem condensation_scc (u v : Nat) :
    (∃ c ∈ C.comps, u ∈ c ∧ v ∈ c) ↔
      u < adj.size ∧ v < adj.size ∧ Reach (filt adj) u v ∧ Reach (filt adj) v u := by
  obtain ⟨st, I, -, -, -, hc⟩ := condensation_state h
  constructor
  · rintro ⟨c, hcm, hu, hv⟩
    refine ⟨condensation_range h c hcm u hu, condensation_range h c hcm v hv, ?_, ?_⟩
    · rw [hc] at hcm; exact I.comp_conn c hcm u hu v hv
    · rw [hc] at hcm; exact I.comp_conn c hcm v hv u hu
  · rintro ⟨hu, hv, ruv, rvu⟩
    obtain ⟨cu, hcu, huc⟩ := condensation_cover h u hu
    obtain ⟨cv, hcv, hvc⟩ := condensation_cover h v hv
    obtain ⟨ku, hku⟩ := Array.getElem?_of_mem hcu
    obtain ⟨kv, hkv⟩ := Array.getElem?_of_mem hcv
    obtain ⟨k1, c1, hle1, hk1, hv1⟩ := condensation_reach h hku huc ruv
    obtain ⟨k2, c2, hle2, hk2, hu2⟩ := condensation_reach h hkv hvc rvu
    have e1 := condensation_unique h k1 kv c1 cv v hk1 hkv hv1 hvc
    have e2 := condensation_unique h k2 ku c2 cu u hk2 hku hu2 huc
    have : ku = kv := by omega
    subst this
    rw [hku] at hkv; cases hkv
    exact ⟨cu, hcu, huc, hvc⟩

/-- **The condensation is acyclic**: if a node of component `k` reaches a node of component
`k'` and back, then `k = k'`. -/
theorem condensation_acyclic {k k' : Nat} {c c' : Array Nat} (hk : C.comps[k]? = some c)
    (hk' : C.comps[k']? = some c') {u u' w w' : Nat} (hu : u ∈ c) (hw : w ∈ c') (hu' : u' ∈ c)
    (hw' : w' ∈ c') (r : Reach (filt adj) u w) (r' : Reach (filt adj) w' u') : k = k' := by
  obtain ⟨k1, c1, hle1, hk1, hw1⟩ := condensation_reach h hk hu r
  obtain ⟨k2, c2, hle2, hk2, hu2⟩ := condensation_reach h hk' hw' r'
  have := condensation_unique h k1 k' c1 c' w hk1 hk' hw1 hw
  have := condensation_unique h k2 k c2 c u' hk2 hk hu2 hu'
  omega

end

end Ix.CompileCert.Canon
