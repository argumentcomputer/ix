import Ix.CompileCert.Canon.SccMain

/-!
# M7 L1, components: Tarjan's fuel suffices

`condensation` gives each root the fuel `|E| + |V| + 1` (`fuel0`) and reports exhaustion as
`none`. `condensation_isSome`: it never does. The work left (`pot`: each unvisited node with
its edges, and each gray node's unexplored edges) drops by exactly one at every iteration of
the loop and is at most `|E| + |V|` when a root is visited.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-- The work for the unvisited nodes. -/
def potV (G : Array (Array Nat)) (st : TarjanState) : Nat :=
  ((List.range G.size).map fun v => if ix st v = 0 then (succs G v).size + 1 else 0).sum

/-- The work for the gray nodes' unexplored edges. -/
def potC (G : Array (Array Nat)) (calls : List (Nat × Nat)) : Nat :=
  (calls.map fun p => (succs G p.1).size + 1 - p.2).sum

/-- The work left. -/
def pot (G : Array (Array Nat)) (st : TarjanState) : Nat := potV G st + potC G st.calls

theorem sum_range_update (g g' : Nat → Nat) (w : Nat) (h : ∀ v, v ≠ w → g' v = g v) :
    ∀ n, w < n → ((List.range n).map g').sum + g w = ((List.range n).map g).sum + g' w := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases e : w = n
    · subst e
      have : (List.range w).map g' = (List.range w).map g :=
        List.map_congr_left fun v hv => h v (by simp at hv; omega)
      rw [this]; omega
    · have := ih (by omega)
      have hn' : g' n = g n := h n (Ne.symm e)
      omega

theorem sum_map_le {f g : Nat → Nat} : ∀ (l : List Nat), (∀ v ∈ l, f v ≤ g v) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_map_le l (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have := h a (List.mem_cons_self ..)
    omega

theorem potV_congr {G : Array (Array Nat)} {st st' : TarjanState} (h : st'.index = st.index) :
    potV G st' = potV G st := by
  unfold potV ix; rw [h]

theorem potV_visit {G : Array (Array Nat)} {st : TarjanState} {w : Nat} (hw : w < G.size)
    (hsz : w < st.index.size) (h0 : ix st w = 0) (hn : st.next ≠ 0) :
    potV G (st.visit w) + ((succs G w).size + 1) = potV G st := by
  unfold potV
  have := sum_range_update (fun v => if ix st v = 0 then (succs G v).size + 1 else 0)
    (fun v => if ix (st.visit w) v = 0 then (succs G v).size + 1 else 0) w
    (fun v hv => by simp only [ix_visit hsz, hv, ↓reduceIte]) G.size hw
  simp only [ix_visit hsz, ↓reduceIte, hn, h0] at this ⊢
  omega

theorem potV_le (G : Array (Array Nat)) (st : TarjanState) :
    potV G st ≤ ((List.range G.size).map fun v => (succs G v).size + 1).sum :=
  sum_map_le _ fun v _ => by split <;> omega

theorem potC_pos {G : Array (Array Nat)} {p : Nat × Nat} {rest : List (Nat × Nat)}
    (hp : p.2 ≤ (succs G p.1).size) : 1 ≤ potC G (p :: rest) := by
  simp only [potC, List.map_cons, List.sum_cons]; omega

/-! ## One iteration -/

theorem popComponent_calls (st : TarjanState) (v : Nat) : (st.popComponent v).calls = st.calls := by
  cases st; simp only [TarjanState.popComponent]

theorem finishSt_calls (st : TarjanState) (v : Nat) (rest : List (Nat × Nat)) :
    (finishSt st v rest).calls = rest := by
  unfold finishSt
  split <;> (try split) <;> simp [setLow_calls, popComponent_calls] <;>
    first | rfl | simp [popComponent_calls]

/-- **Tarjan's loop does not run out of fuel** when the fuel covers the work left. -/
theorem tarjanLoop_fuel {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (fuel : Nat) (st : TarjanState), Inv G st → pot G st ≤ fuel → st.exhausted = false →
      (tarjanLoop G fuel st).exhausted = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro st I hp hex
    rw [tarjanLoop_zero]
    cases hc : st.calls with
    | nil => simp only [List.isEmpty_nil, ↓reduceIte]; exact hex
    | cons p rest =>
      have := potC_pos (G := G) (rest := rest) (I.calls_le p (by rw [hc]; exact List.mem_cons_self ..))
      unfold pot at hp; rw [hc] at hp; omega
  | succ fuel ih =>
    intro st I hp hex
    cases hc : st.calls with
    | nil => rw [tarjanLoop_nil G fuel st hc]; exact hex
    | cons p rest =>
      obtain ⟨v, i⟩ := p
      have hpC : potC G st.calls = (succs G v).size + 1 - i + potC G rest := by
        rw [hc]; simp only [potC, List.map_cons, List.sum_cons]
      have hle : i ≤ (succs G v).size := I.calls_le (v, i) (by rw [hc]; exact List.mem_cons_self ..)
      by_cases hi : i < (succs G v).size
      · have hstep : potC G ((v, i + 1) :: rest) + 1 = potC G st.calls := by
          rw [hpC]; simp only [potC, List.map_cons, List.sum_cons]; omega
        by_cases h0 : ix st (succs G v)[i] = 0
        · rw [tarjanLoop_new G fuel st v i rest hc hi h0]
          apply ih _ (inv_new I hG hc hi h0) _ (by rw [visit_exhausted]; exact hex)
          have hw : (succs G v)[i] < G.size := hG _ _ (mem_succs_of_getElem hi)
          have hsz : (succs G v)[i] < st.index.size := by rw [I.szI]; exact hw
          have hV := potV_visit (G := G) (st := ({ st with calls := (v, i + 1) :: rest } : TarjanState))
            hw hsz h0 (Nat.ne_of_gt I.next_pos)
          have hV' : potV G ({ st with calls := (v, i + 1) :: rest } : TarjanState) = potV G st :=
            potV_congr rfl
          have hcv : (({ st with calls := (v, i + 1) :: rest } : TarjanState).visit (succs G v)[i]).calls =
              ((succs G v)[i], 0) :: (v, i + 1) :: rest := by
            cases st; rfl
          unfold pot at hp ⊢
          rw [hcv]
          have : potC G (((succs G v)[i], 0) :: (v, i + 1) :: rest) =
              (succs G (succs G v)[i]).size + 1 + potC G ((v, i + 1) :: rest) := by
            simp only [potC, List.map_cons, List.sum_cons]; omega
          rw [this]; omega
        · by_cases hon : os st (succs G v)[i] = true
          · rw [tarjanLoop_on G fuel st v i rest hc hi h0 hon]
            apply ih _ (inv_on I hc hi h0 hon) _ (by rw [setLow_exhausted]; exact hex)
            unfold pot at hp ⊢
            have e1 : potV G (({ st with calls := (v, i + 1) :: rest } : TarjanState).setLow v
                (min (lw st v) (ix st (succs G v)[i]))) = potV G st := potV_congr (by rw [setLow_index])
            have e2 : potC G (({ st with calls := (v, i + 1) :: rest } : TarjanState).setLow v
                (min (lw st v) (ix st (succs G v)[i]))).calls = potC G ((v, i + 1) :: rest) := by
              rw [setLow_calls]
            rw [e1, e2]
            omega
          · have hon' : os st (succs G v)[i] = false := by simpa using hon
            rw [tarjanLoop_done G fuel st v i rest hc hi h0 hon']
            apply ih _ (inv_done I hc hi h0 hon') _ hex
            unfold pot at hp ⊢
            rw [potV_congr rfl]
            show potV G st + potC G ((v, i + 1) :: rest) ≤ fuel
            omega
      · rw [tarjanLoop_finish G fuel st v i rest hc hi]
        apply ih _ (inv_finish I hc hi) _ (by rw [finishSt_exhausted]; exact hex)
        unfold pot at hp ⊢
        rw [potV_congr (finishSt_index st v rest), finishSt_calls]
        have : i = (succs G v).size := by omega
        rw [hpC] at hp
        omega

/-! ## The roots -/

theorem foldl_add_size (G : Array (Array Nat)) :
    G.foldl (init := 0) (· + ·.size) = ((List.range G.size).map fun v => (succs G v).size).sum := by
  rw [← Array.foldl_toList]
  have e : (List.range G.size).map (fun v => (succs G v).size) = G.toList.map Array.size := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range, succs]
      rw [Array.getElem?_eq_getElem (by simpa using h1)]
      simp
  rw [e]
  suffices h : ∀ (l : List (Array Nat)) (a : Nat), l.foldl (· + ·.size) a = a + (l.map Array.size).sum by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih => intro a; simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem sum_succ_add (G : Array (Array Nat)) :
    ((List.range G.size).map fun v => (succs G v).size + 1).sum =
      ((List.range G.size).map fun v => (succs G v).size).sum + G.size := by
  generalize G.size = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem rootStep_fuel {adj : Array (Array Nat)} (s : TarjanState × Nat) (r : Nat) (hr : r < adj.size)
    (h : RootInv (filt adj) s.1) (hf : s.2 = fuel0 adj) (hex : s.1.exhausted = false) :
    (rootStep (filt adj) s r).1.exhausted = false ∧ (rootStep (filt adj) s r).2 = fuel0 adj := by
  obtain ⟨st, fuel⟩ := s
  simp only at hf hex; subst hf
  obtain ⟨I, hcs⟩ := h
  simp only [rootStep]
  split
  · exact ⟨hex, rfl⟩
  · rename_i hgo
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hgo
    obtain ⟨-, h0'⟩ := hgo
    have h0 : ix st r = 0 := h0'
    obtain ⟨hc, hs⟩ := hcs hex
    have hr' : r < (filt adj).size := by rw [filt_size]; exact hr
    have I1 := inv_root I hc hs hr' h0
    refine ⟨tarjanLoop_fuel (filt_bounded adj) _ _ I1 ?_ (by rw [visit_exhausted]; exact hex), rfl⟩
    have hsz : r < st.index.size := by rw [I.szI]; exact hr'
    have hV := potV_visit (G := filt adj) hr' hsz h0 (Nat.ne_of_gt I.next_pos)
    have hcv : (st.visit r).calls = [(r, 0)] := by
      have : (st.visit r).calls = (r, 0) :: st.calls := by cases st; rfl
      rw [this, hc]
    unfold pot fuel0
    rw [hcv]
    have hC : potC (filt adj) [(r, 0)] = (succs (filt adj) r).size + 1 := by
      simp only [potC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    rw [hC]
    have h1 := potV_le (filt adj) st
    rw [sum_succ_add, ← foldl_add_size] at h1
    have hs := filt_size adj
    omega

theorem fold_fuel {adj : Array (Array Nat)} :
    ∀ (l : List Nat), (∀ r ∈ l, r < adj.size) → ∀ (s : TarjanState × Nat), RootInv (filt adj) s.1 →
      s.2 = fuel0 adj → s.1.exhausted = false →
      (l.foldl (rootStep (filt adj)) s).1.exhausted = false := by
  intro l
  induction l with
  | nil => intro _ s _ _ hex; exact hex
  | cons r rs ih =>
    intro hl s h hf hex
    obtain ⟨A, -, -, -⟩ := rootStep_spec (filt_bounded adj) s r
      (by rw [filt_size]; exact hl r (List.mem_cons_self ..)) h
    obtain ⟨E, F⟩ := rootStep_fuel s r (hl r (List.mem_cons_self ..)) h hf hex
    simp only [List.foldl_cons]
    exact ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) _ A F E

/-- **`condensation` always returns**: the fuel `|E| + |V| + 1` per root is never exhausted. -/
theorem condensation_isSome (adj : Array (Array Nat)) : (condensation adj).isSome = true := by
  rw [condensation_eq]
  simp only
  have I0 : RootInv (filt adj) (initSt adj.size, fuel0 adj).1 := by
    refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
    have := inv_init (filt adj); rw [filt_size] at this; exact this
  have := fold_fuel (List.range adj.size) (fun r hr => by simpa using hr) _ I0 rfl rfl
  rw [this]
  rfl

theorem condensation_some (adj : Array (Array Nat)) : ∃ C, condensation adj = some C := by
  have := condensation_isSome adj
  cases h : condensation adj with
  | none => rw [h] at this; cases this
  | some C => exact ⟨C, rfl⟩

end Ix.CompileCert.Canon
