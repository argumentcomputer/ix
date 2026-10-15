module

public import Ix.CompileCert.Canon.SccFuel

/-!
# Components: the roots and the discovery order are nodes

`Ix.CondenseM.run` reads `condensation`'s roots and discovery order back as names, by position
in its array of nodes. `condensation_order_lt`, `condensation_roots_lt`: both hold only nodes
`0 … n-1`, so every such read is in range. The invariant (`Nodes`) is separate from `Inv`
(`Scc.lean`): it only records that `visit`, `popComponent` and the call stack touch nodes of
the graph.
-/

@[expose] public section

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-- The discovery order, the roots and the call stack hold only nodes below `n`. -/
structure Nodes (n : Nat) (st : TarjanState) : Prop where
  order : ∀ v ∈ st.order, v < n
  roots : ∀ r ∈ st.roots, r < n
  calls : ∀ p ∈ st.calls, p.1 < n

theorem visit_order (st : TarjanState) (w : Nat) : (st.visit w).order = st.order.push w := by
  cases st; rfl

theorem setLow_order (st : TarjanState) (u x : Nat) : (st.setLow u x).order = st.order := by
  cases st; rfl

theorem popComponent_order (st : TarjanState) (v : Nat) :
    (st.popComponent v).order = st.order := by
  cases st; simp only [TarjanState.popComponent]

theorem popComponent_roots (st : TarjanState) (v : Nat) :
    (st.popComponent v).roots = st.roots.push v := by
  cases st; simp only [TarjanState.popComponent]

theorem nodes_initSt (n m : Nat) : Nodes n (initSt m) where
  order v hv := by simp [initSt] at hv
  roots r hr := by simp [initSt] at hr
  calls p hp := by simp [initSt] at hp

namespace Nodes

variable {n : Nat} {st : TarjanState}

theorem visit (N : Nodes n st) {w : Nat} (hw : w < n) : Nodes n (st.visit w) where
  order v hv := by
    rw [visit_order, Array.mem_push] at hv
    rcases hv with hv | rfl
    · exact N.order v hv
    · exact hw
  roots r hr := by rw [visit_roots] at hr; exact N.roots r hr
  calls p hp := by
    rw [visit_calls, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hw
    · exact N.calls p hp

theorem setLow (N : Nodes n st) (u x : Nat) : Nodes n (st.setLow u x) where
  order v hv := by rw [setLow_order] at hv; exact N.order v hv
  roots r hr := by rw [setLow_roots] at hr; exact N.roots r hr
  calls p hp := by rw [setLow_calls] at hp; exact N.calls p hp

theorem withCalls (N : Nodes n st) {cs : List (Nat × Nat)} (hcs : ∀ p ∈ cs, p.1 < n) :
    Nodes n { st with calls := cs } where
  order := N.order
  roots := N.roots
  calls := hcs

theorem pop (N : Nodes n st) {v : Nat} (hv : v < n) : Nodes n (st.popComponent v) where
  order u hu := by rw [popComponent_order] at hu; exact N.order u hu
  roots r hr := by
    rw [popComponent_roots, Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact N.roots r hr
    · exact hv
  calls p hp := by rw [popComponent_calls] at hp; exact N.calls p hp

theorem finish (N : Nodes n st) {v i : Nat} {rest : List (Nat × Nat)}
    (hc : st.calls = (v, i) :: rest) : Nodes n (finishSt st v rest) := by
  have hv : v < n := N.calls (v, i) (by rw [hc]; exact List.mem_cons_self ..)
  have N1 : Nodes n ({ st with calls := rest } : TarjanState) :=
    N.withCalls fun p hp => N.calls p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
  have N2 : Nodes n (if lw st v == ix st v then
      ({ st with calls := rest } : TarjanState).popComponent v
      else ({ st with calls := rest } : TarjanState)) := by
    split
    · exact N1.pop hv
    · exact N1
  unfold finishSt
  cases rest with
  | nil => exact N2
  | cons p rest' => exact N2.setLow _ _

end Nodes

/-- `tarjanLoop` touches only nodes. -/
theorem tarjanLoop_nodes {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (fuel : Nat) (st : TarjanState), Nodes G.size st → Nodes G.size (tarjanLoop G fuel st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st N
    rw [tarjanLoop_zero]
    split
    · exact N
    · exact ⟨N.order, N.roots, N.calls⟩
  | succ fuel ih =>
    intro st N
    cases hc : st.calls with
    | nil => rw [tarjanLoop_nil G fuel st hc]; exact N
    | cons p rest =>
      obtain ⟨v, i⟩ := p
      have N1 : Nodes G.size ({ st with calls := (v, i + 1) :: rest } : TarjanState) := by
        refine N.withCalls fun p hp => ?_
        rcases List.mem_cons.1 hp with rfl | hp
        · exact N.calls (v, i) (by rw [hc]; exact List.mem_cons_self ..)
        · exact N.calls p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
      by_cases hi : i < (succs G v).size
      · by_cases h0 : ix st (succs G v)[i] = 0
        · rw [tarjanLoop_new G fuel st v i rest hc hi h0]
          exact ih _ (N1.visit (hG _ _ (mem_succs_of_getElem hi)))
        · by_cases hon : os st (succs G v)[i] = true
          · rw [tarjanLoop_on G fuel st v i rest hc hi h0 hon]
            exact ih _ (N1.setLow _ _)
          · have hon' : os st (succs G v)[i] = false := by simpa using hon
            rw [tarjanLoop_done G fuel st v i rest hc hi h0 hon']
            exact ih _ N1
      · rw [tarjanLoop_finish G fuel st v i rest hc hi]
        exact ih _ (N.finish hc)

theorem rootStep_nodes {G : Array (Array Nat)} (hG : Bounded G) (s : TarjanState × Nat) (r : Nat)
    (hr : r < G.size) (N : Nodes G.size s.1) : Nodes G.size (rootStep G s r).1 := by
  obtain ⟨st, fuel⟩ := s
  simp only [rootStep]
  split
  · exact N
  · exact tarjanLoop_nodes hG fuel _ (N.visit hr)

theorem fold_nodes {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (l : List Nat), (∀ r ∈ l, r < G.size) → ∀ (s : TarjanState × Nat), Nodes G.size s.1 →
      Nodes G.size (l.foldl (rootStep G) s).1 := by
  intro l
  induction l with
  | nil => intro _ s N; exact N
  | cons r rs ih =>
    intro hl s N
    simp only [List.foldl_cons]
    exact ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) _
      (rootStep_nodes hG s r (hl r (List.mem_cons_self ..)) N)

/-- The discovery order and the roots of `condensation adj` hold only nodes of `adj`. -/
theorem condensation_nodes {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) :
    (∀ v ∈ C.order, v < adj.size) ∧ (∀ r ∈ C.roots, r < adj.size) := by
  rw [condensation_eq] at h
  simp only at h
  have N := fold_nodes (filt_bounded adj) (List.range adj.size)
    (fun r hr => by rw [filt_size]; simpa using hr) (initSt adj.size, fuel0 adj)
    (nodes_initSt _ _)
  rw [filt_size] at N
  generalize ((List.range adj.size).foldl (rootStep (filt adj)) (initSt adj.size, fuel0 adj)) = s
    at h N
  split at h
  · cases h
  · cases h
    exact ⟨N.order, N.roots⟩

/-- Every node in the discovery order is a node of `adj`. -/
theorem condensation_order_lt {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) {v : Nat} (hv : v ∈ C.order) : v < adj.size :=
  (condensation_nodes h).1 v hv

/-- Every root is a node of `adj`. -/
theorem condensation_roots_lt {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) {r : Nat} (hr : r ∈ C.roots) : r < adj.size :=
  (condensation_nodes h).2 r hr

end Ix.CompileCert.Canon

end
