import Ix.CompileCert.Canon.Scc

/-!
# M7 L1, components: every iteration of Tarjan's loop keeps the invariant

`inv_root` (a new DFS root), `inv_new` (an edge to an unvisited node), `inv_on` (an edge to a
node on the stack), `inv_done` (an edge to a popped node), and `inv_finish` (a finished node:
pop its component if it is a root, else pass its low link to its parent).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-! ## Consequences of the invariant -/

theorem grays_cons {st : TarjanState} {v i : Nat} {rest : List (Nat × Nat)}
    (hc : st.calls = (v, i) :: rest) : grays st = v :: rest.map (·.1) := by simp [grays, hc]

/-- Counters of entries other than `x`'s do not constrain `x`'s edges. -/
theorem expl_iff_of_calls {G : Array (Array Nat)} {st st' : TarjanState} {x w : Nat}
    (hc : ∀ p : Nat × Nat, p.1 = x → (p ∈ st'.calls ↔ p ∈ st.calls)) :
    Expl G st' x w ↔ Expl G st x w := by
  constructor <;> rintro ⟨j, hj, hlt⟩ <;> refine ⟨j, hj, fun p hp hpx => hlt p ?_ hpx⟩
  · exact (hc p hpx).2 hp
  · exact (hc p hpx).1 hp

namespace Inv

variable {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st)
include I

theorem eq_of_ix {a b : Nat} (ha : a ∈ st.stack) (h : ix st a = ix st b) : a = b :=
  I.ix_inj a b h (I.st_vis a ha)

theorem not_stack_of_ix_zero {w : Nat} (h : ix st w = 0) : w ∉ st.stack :=
  fun hw => I.st_vis w hw h

theorem gray_stack {g : Nat} (h : g ∈ grays st) : g ∈ st.stack := I.calls_on g h

/-- The top gray node has the largest number among the gray nodes. -/
theorem top_gray {v i : Nat} {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) :
    ∀ g ∈ rest.map (·.1), ix st g < ix st v := by
  have := I.calls_sorted
  simp only [grays, hc, List.map_cons, List.pairwise_cons] at this
  exact this.1

theorem le_top {v i : Nat} {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) :
    ∀ g ∈ grays st, ix st g ≤ ix st v := by
  intro g hg
  rw [grays_cons hc] at hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (I.top_gray hc g hg)

theorem not_rest {v i : Nat} {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) :
    v ∉ rest.map (·.1) := fun h => Nat.lt_irrefl _ (I.top_gray hc v h)

theorem v_stack {v i : Nat} {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) :
    v ∈ st.stack := I.gray_stack (by rw [grays_cons hc]; simp)

end Inv

theorem mem_succs_of_getElem {G : Array (Array Nat)} {v i : Nat} (hi : i < (succs G v).size) :
    Edge G v (succs G v)[i] := Array.getElem_mem hi

theorem exists_index_of_edge {G : Array (Array Nat)} {u w : Nat} (h : Edge G u w) :
    ∃ j : Nat, (succs G u)[j]? = some w := by
  obtain ⟨j, hj, e⟩ := Array.getElem_of_mem h
  exact ⟨j, by rw [Array.getElem?_eq_getElem hj, e]⟩

/-! ## A new DFS root -/

theorem inv_root {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st)
    (hc : st.calls = []) (hs : st.stack = []) {r : Nat} (hr : r < G.size) (h0 : ix st r = 0) :
    Inv G (st.visit r) := by
  have hI : r < st.index.size := by rw [I.szI]; exact hr
  have hL : r < st.low.size := by rw [I.szL]; exact hr
  have hO : r < st.onStack.size := by rw [I.szO]; exact hr
  have gr : grays (st.visit r) = [r] := by simp [grays, visit_calls, hc]
  have sk : (st.visit r).stack = [r] := by simp [visit_stack, hs]
  refine
    { szI := by simp [visit_index, Array.set!, I.szI]
      szL := by simp [visit_low, Array.set!, I.szL]
      szO := by simp [visit_onStack, Array.set!, I.szO]
      next_pos := by simp [visit_next]
      ix_lt := ?_, ix_inj := ?_, on_iff := ?_, st_vis := ?_, st_sorted := ?_
      calls_on := ?_, calls_le := ?_, calls_sorted := ?_, stack_gray := ?_, gray_reach := ?_
      low_le := ?_, low_wit := ?_, low_fin := ?_, low_gray := ?_, explored := ?_
      comp_iff := ?_, comp_uniq := ?_, comp_conn := ?_, comp_down := ?_ }
  · intro u; rw [ix_visit hI, visit_next]; split
    · omega
    · have := I.ix_lt u; omega
  · intro a b h hne
    simp only [ix_visit hI] at h hne
    by_cases ha : a = r <;> by_cases hb : b = r <;> simp only [ha, hb, ↓reduceIte] at h hne
    · rw [ha, hb]
    · have := I.ix_lt b; omega
    · have := I.ix_lt a; omega
    · exact I.ix_inj a b h hne
  · intro u; rw [os_visit hO, sk]
    by_cases hu : u = r
    · simp [hu]
    · simp only [hu, ↓reduceIte, List.mem_singleton, iff_false]
      rw [I.on_iff, hs]; simp
  · intro u hu; rw [sk, List.mem_singleton] at hu; subst hu
    rw [ix_visit hI]; simp; exact Nat.ne_of_gt I.next_pos
  · rw [sk]; simp
  · intro g hg; rw [gr] at hg; rw [sk]; exact hg
  · intro p hp; simp only [visit_calls, hc, List.mem_singleton] at hp; subst hp; simp
  · rw [gr]; simp
  · intro x hx; rw [sk, List.mem_singleton] at hx; subst hx
    exact ⟨x, by rw [gr]; simp, Nat.le_refl _⟩
  · intro g hg x hx _
    rw [gr, List.mem_singleton] at hg; rw [sk, List.mem_singleton] at hx
    subst hg; subst hx; exact .refl _
  · intro x hx; rw [sk, List.mem_singleton] at hx; subst hx
    rw [ix_visit hI, lw_visit hL]; simp
  · intro x hx; rw [sk, List.mem_singleton] at hx; subst hx
    refine ⟨x, by rw [sk]; simp, ?_, .refl _⟩
    rw [ix_visit hI, lw_visit hL]; simp
  · intro x hx hng; rw [sk, List.mem_singleton] at hx; subst hx
    exact absurd (by rw [gr]; simp) hng
  · intro x hx g hg _ _
    rw [sk, List.mem_singleton] at hx; rw [gr, List.mem_singleton] at hg
    subst hx; subst hg; exact Nat.le_refl _
  · intro x hx w hw
    rw [sk, List.mem_singleton] at hx; subst hx
    obtain ⟨j, -, hj⟩ := hw
    exact absurd (hj (x, 0) (by simp [visit_calls]) rfl) (Nat.not_lt_zero _)
  · intro u
    rw [visit_comps, ix_visit hI, sk]
    by_cases hu : u = r
    · subst hu
      simp only [↓reduceIte, List.mem_singleton, not_true_eq_false, and_false, iff_false]
      rintro ⟨c, hc', huc⟩
      exact (I.comp_iff u |>.1 ⟨c, hc', huc⟩).1 h0
    · simp only [hu, ↓reduceIte, List.mem_singleton]
      rw [I.comp_iff u, hs]; simp
  · intro k k' c c' u; rw [visit_comps]; exact I.comp_uniq k k' c c' u
  · intro c; rw [visit_comps]; exact I.comp_conn c
  · intro k c u w; rw [visit_comps]; exact I.comp_down k c u w

/-! ## Exploring an edge -/

/-- Exploring edge `i` of the top gray node `v`, once its target satisfies the explored-edge
condition. -/
theorem inv_bump {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (hw : ix st (succs G v)[i] ≠ 0 ∧ ((succs G v)[i] ∈ st.stack → lw st v ≤ ix st (succs G v)[i])) :
    Inv G ({ st with calls := (v, i + 1) :: rest } : TarjanState) := by
  have hg : grays ({ st with calls := (v, i + 1) :: rest } : TarjanState) = grays st := by
    simp [grays, hc]
  have hnr := I.not_rest hc
  refine
    { szI := I.szI, szL := I.szL, szO := I.szO, next_pos := I.next_pos, ix_lt := I.ix_lt
      ix_inj := I.ix_inj, on_iff := I.on_iff, st_vis := I.st_vis, st_sorted := I.st_sorted
      calls_on := by rw [hg]; exact I.calls_on
      calls_le := ?_
      calls_sorted := by rw [hg]; exact I.calls_sorted
      stack_gray := by rw [hg]; exact I.stack_gray
      gray_reach := by rw [hg]; exact I.gray_reach
      low_le := I.low_le, low_wit := I.low_wit
      low_fin := by rw [hg]; exact I.low_fin
      low_gray := by rw [hg]; exact I.low_gray
      explored := ?_
      comp_iff := I.comp_iff, comp_uniq := I.comp_uniq, comp_conn := I.comp_conn
      comp_down := I.comp_down }
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hi
    · exact I.calls_le p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
  · intro x hx u hu
    obtain ⟨j, hj, hlt⟩ := hu
    by_cases hxj : x = v ∧ j = i
    · obtain ⟨rfl, rfl⟩ := hxj
      rw [Array.getElem?_eq_getElem hi] at hj
      cases hj
      exact hw
    · refine I.explored x hx u ⟨j, hj, fun p hp hpx => ?_⟩
      rw [hc] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only at hpx; subst hpx
        have h1 := hlt (v, i + 1) (by simp) rfl
        have h2 : j ≠ i := fun h => hxj ⟨rfl, h⟩
        simp only at h1 ⊢; omega
      · exact hlt p (List.mem_cons_of_mem _ hp) hpx

/-- An edge to a node already popped. -/
theorem inv_done {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (h0 : ix st (succs G v)[i] ≠ 0) (hon : os st (succs G v)[i] = false) :
    Inv G ({ st with calls := (v, i + 1) :: rest } : TarjanState) :=
  inv_bump I hc hi ⟨h0, fun hs => by rw [(I.on_iff _).2 hs] at hon; cases hon⟩

/-- Lowering the low link of the top gray node `v` to the number of a stack node `w` it has an
edge to. -/
theorem inv_lower {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) {w : Nat} (hvw : Edge G v w)
    (hw : w ∈ st.stack) : Inv G (st.setLow v (min (lw st v) (ix st w))) := by
  have hv := I.v_stack hc
  have hL : v < st.low.size := by rw [I.szL]; exact I.lt_of_stack hv
  have lw' : ∀ u, lw (st.setLow v (min (lw st v) (ix st w))) u =
      if u = v then min (lw st v) (ix st w) else lw st u := lw_setLow hL
  have ix' : ix (st.setLow v (min (lw st v) (ix st w))) = ix st := by
    funext u; simp [ix, setLow_index]
  have os' : os (st.setLow v (min (lw st v) (ix st w))) = os st := by
    funext u; simp [os, setLow_onStack]
  have gr' : grays (st.setLow v (min (lw st v) (ix st w))) = grays st := by
    simp [grays, setLow_calls]
  have hvg : v ∈ grays st := by rw [grays_cons hc]; simp
  refine
    { szI := by rw [setLow_index]; exact I.szI
      szL := by rw [setLow_low]; simp [Array.set!, I.szL]
      szO := by rw [setLow_onStack]; exact I.szO
      next_pos := by rw [setLow_next]; exact I.next_pos
      ix_lt := by rw [ix', setLow_next]; exact I.ix_lt
      ix_inj := by rw [ix']; exact I.ix_inj
      on_iff := by rw [os', setLow_stack]; exact I.on_iff
      st_vis := by rw [ix', setLow_stack]; exact I.st_vis
      st_sorted := by rw [ix', setLow_stack]; exact I.st_sorted
      calls_on := by rw [gr', setLow_stack]; exact I.calls_on
      calls_le := by rw [setLow_calls]; exact I.calls_le
      calls_sorted := by rw [gr', ix']; exact I.calls_sorted
      stack_gray := by rw [gr', ix', setLow_stack]; exact I.stack_gray
      gray_reach := by rw [gr', ix', setLow_stack]; exact I.gray_reach
      low_le := ?_, low_wit := ?_, low_fin := ?_, low_gray := ?_, explored := ?_
      comp_iff := by rw [setLow_comps, ix', setLow_stack]; exact I.comp_iff
      comp_uniq := by rw [setLow_comps]; exact I.comp_uniq
      comp_conn := by rw [setLow_comps]; exact I.comp_conn
      comp_down := by rw [setLow_comps]; exact I.comp_down }
  · intro x hx; rw [setLow_stack] at hx; rw [lw', ix']
    split
    · subst x; exact Nat.le_trans (Nat.min_le_left _ _) (I.low_le _ hv)
    · exact I.low_le x hx
  · intro x hx; rw [setLow_stack] at hx; rw [lw', ix', setLow_stack]
    split
    · subst x
      by_cases hm : ix st w < lw st v
      · exact ⟨w, hw, by omega, .single hvw⟩
      · obtain ⟨y, hy, e, r⟩ := I.low_wit _ hv
        exact ⟨y, hy, by omega, r⟩
    · exact I.low_wit x hx
  · intro x hx hng; rw [setLow_stack] at hx; rw [gr'] at hng; rw [lw', ix']
    have : x ≠ v := fun h => hng (h ▸ hvg)
    simp only [this, ↓reduceIte]
    exact I.low_fin x hx hng
  · intro x hx g hg hgx hmax
    rw [setLow_stack] at hx; rw [gr'] at hg hmax; rw [ix'] at hgx hmax; rw [lw', lw']
    by_cases hgv : g = v
    · subst hgv
      by_cases hxv : x = g
      · subst hxv; simp
      · simp only [↓reduceIte, hxv]
        exact Nat.le_trans (Nat.min_le_left _ _) (I.low_gray x hx _ hg hgx hmax)
    · by_cases hxv : x = v
      · subst hxv
        have h1 := hmax x hvg (Nat.le_refl _)
        exact absurd (I.eq_of_ix (I.gray_stack hg) (by omega : ix st g = ix st x)) hgv
      · simp only [hgv, hxv, ↓reduceIte]
        exact I.low_gray x hx g hg hgx hmax
  · intro x hx u hu
    rw [setLow_stack] at hx
    have hu' : Expl G st x u := (expl_iff_of_calls (fun p _ => by rw [setLow_calls])).1 hu
    obtain ⟨h1, h2⟩ := I.explored x hx u hu'
    refine ⟨by rw [ix']; exact h1, fun hus => ?_⟩
    rw [setLow_stack] at hus
    rw [lw', ix']
    split
    · subst x; exact Nat.le_trans (Nat.min_le_left _ _) (h2 hus)
    · exact h2 hus

/-- An edge to a node on the stack. -/
theorem inv_on {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) (hi : i < (succs G v).size)
    (h0 : ix st (succs G v)[i] ≠ 0) (hon : os st (succs G v)[i] = true) :
    Inv G (({ st with calls := (v, i + 1) :: rest } : TarjanState).setLow v
      (min (lw st v) (ix st (succs G v)[i]))) := by
  have hw : (succs G v)[i] ∈ st.stack := (I.on_iff _).1 hon
  have I2 := inv_lower I hc (mem_succs_of_getElem hi) hw
  have hc2 : (st.setLow v (min (lw st v) (ix st (succs G v)[i]))).calls = (v, i) :: rest := by
    rw [setLow_calls, hc]
  have hv := I.v_stack hc
  have hL : v < st.low.size := by rw [I.szL]; exact I.lt_of_stack hv
  have I3 := inv_bump I2 hc2 hi ⟨by simpa [ix, setLow_index] using h0, fun _ => by
    rw [lw_setLow hL]; simp only [ix, setLow_index, ↓reduceIte]; exact Nat.min_le_right _ _⟩
  have e : ({ st.setLow v (min (lw st v) (ix st (succs G v)[i])) with
      calls := (v, i + 1) :: rest } : TarjanState) =
      ({ st with calls := (v, i + 1) :: rest } : TarjanState).setLow v
        (min (lw st v) (ix st (succs G v)[i])) := by
    cases st; rfl
  rw [← e]; exact I3

/-- An edge to an unvisited node: visit it. -/
theorem inv_new {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) (hG : Bounded G)
    {v i : Nat} {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest)
    (hi : i < (succs G v).size) (h0 : ix st (succs G v)[i] = 0) :
    Inv G (({ st with calls := (v, i + 1) :: rest } : TarjanState).visit (succs G v)[i]) := by
  have hedge : Edge G v (succs G v)[i] := mem_succs_of_getElem hi
  have hwn : (succs G v)[i] < G.size := hG _ _ hedge
  have hjw : ∀ j, (succs G v)[j]? = some (succs G v)[i] → j = i → True := fun _ _ _ => trivial
  have hget : (succs G v)[i]? = some (succs G v)[i] := Array.getElem?_eq_getElem hi
  generalize (succs G v)[i] = w at h0 hedge hwn hget ⊢
  clear hjw
  have hsz : w < st.index.size := by rw [I.szI]; exact hwn
  have hszL : w < st.low.size := by rw [I.szL]; exact hwn
  have hszO : w < st.onStack.size := by rw [I.szO]; exact hwn
  let st1 : TarjanState := { st with calls := (v, i + 1) :: rest }
  have ixs : ∀ u, ix (st1.visit w) u = if u = w then st.next else ix st u :=
    fun u => ix_visit (st := st1) hsz u
  have lws : ∀ u, lw (st1.visit w) u = if u = w then st.next else lw st u :=
    fun u => lw_visit (st := st1) hszL u
  have oss : ∀ u, os (st1.visit w) u = if u = w then true else os st u :=
    fun u => os_visit (st := st1) hszO u
  have sk : (st1.visit w).stack = w :: st.stack := visit_stack st1 w
  have cl : (st1.visit w).calls = (w, 0) :: (v, i + 1) :: rest := visit_calls st1 w
  have gr : grays (st1.visit w) = w :: grays st := by
    simp only [grays, cl, hc, List.map_cons]
  have nx : (st1.visit w).next = st.next + 1 := visit_next st1 w
  have cp : (st1.visit w).comps = st.comps := visit_comps st1 w
  have wns : w ∉ st.stack := I.not_stack_of_ix_zero h0
  have ne_w : ∀ u ∈ st.stack, u ≠ w := fun u hu h => wns (h ▸ hu)
  have gne_w : ∀ g ∈ grays st, g ≠ w := fun g hg => ne_w g (I.calls_on g hg)
  have hv := I.v_stack hc
  have npos := I.next_pos
  have ixlt := I.ix_lt
  -- every old visited node has a number below `next`, the new node's
  have ixs_ne : ∀ u, u ≠ w → ix (st1.visit w) u = ix st u := fun u hu => by
    rw [ixs]; simp [hu]
  have lws_ne : ∀ u, u ≠ w → lw (st1.visit w) u = lw st u := fun u hu => by
    rw [lws]; simp [hu]
  have ixs_w : ix (st1.visit w) w = st.next := by rw [ixs]; simp
  have lws_w : lw (st1.visit w) w = st.next := by rw [lws]; simp
  show Inv G (st1.visit w)
  refine
    { szI := by simp [visit_index, Array.set!, st1, I.szI]
      szL := by simp [visit_low, Array.set!, st1, I.szL]
      szO := by simp [visit_onStack, Array.set!, st1, I.szO]
      next_pos := by rw [nx]; omega
      ix_lt := ?_, ix_inj := ?_, on_iff := ?_, st_vis := ?_, st_sorted := ?_
      calls_on := ?_, calls_le := ?_, calls_sorted := ?_, stack_gray := ?_, gray_reach := ?_
      low_le := ?_, low_wit := ?_, low_fin := ?_, low_gray := ?_, explored := ?_
      comp_iff := ?_, comp_uniq := ?_, comp_conn := ?_, comp_down := ?_ }
  · intro u; rw [nx]
    by_cases hu : u = w
    · subst u; rw [ixs_w]; omega
    · rw [ixs_ne u hu]; have := ixlt u; omega
  · intro a b h hne
    by_cases ha : a = w <;> by_cases hb : b = w
    · rw [ha, hb]
    · subst a; rw [ixs_w, ixs_ne b hb] at h; have := ixlt b; omega
    · subst b; rw [ixs_w, ixs_ne a ha] at h; have := ixlt a; omega
    · rw [ixs_ne a ha, ixs_ne b hb] at h; rw [ixs_ne a ha] at hne; exact I.ix_inj a b h hne
  · intro u; rw [oss, sk]
    by_cases hu : u = w
    · simp [hu]
    · simp only [hu, ↓reduceIte, List.mem_cons, false_or]; exact I.on_iff u
  · intro u hu; rw [sk] at hu
    rcases List.mem_cons.1 hu with hu | hu
    · subst u; rw [ixs_w]; omega
    · rw [ixs_ne u (ne_w u hu)]; exact I.st_vis u hu
  · rw [sk, List.pairwise_cons]
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [ixs_w, ixs_ne b (ne_w b hb)]; exact ixlt b
    · refine I.st_sorted.imp_of_mem fun {a b} ha hb h => ?_
      rw [ixs_ne a (ne_w a ha), ixs_ne b (ne_w b hb)]; exact h
  · intro g hg; rw [gr] at hg; rw [sk]
    rcases List.mem_cons.1 hg with hg | hg
    · subst g; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (I.calls_on g hg)
  · intro p hp; rw [cl] at hp
    simp only [List.mem_cons] at hp
    rcases hp with hp | hp | hp
    · subst p; simp
    · subst p; exact hi
    · exact I.calls_le p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
  · rw [gr, List.pairwise_cons]
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [ixs_w, ixs_ne b (gne_w b hb)]; exact ixlt b
    · refine I.calls_sorted.imp_of_mem fun {a b} ha hb h => ?_
      rw [ixs_ne a (gne_w a ha), ixs_ne b (gne_w b hb)]; exact h
  · intro x hx; rw [sk] at hx; rw [gr]
    rcases List.mem_cons.1 hx with hx | hx
    · subst x; exact ⟨w, List.mem_cons_self .., Nat.le_refl _⟩
    · obtain ⟨g, hg, hle⟩ := I.stack_gray x hx
      refine ⟨g, List.mem_cons_of_mem _ hg, ?_⟩
      rw [ixs_ne g (gne_w g hg), ixs_ne x (ne_w x hx)]; exact hle
  · intro g hg x hx hle; rw [gr] at hg; rw [sk] at hx
    rcases List.mem_cons.1 hg with hg | hg
    · subst g
      rcases List.mem_cons.1 hx with hx | hx
      · subst x; exact .refl _
      · rw [ixs_w, ixs_ne x (ne_w x hx)] at hle; have := ixlt x; omega
    · rcases List.mem_cons.1 hx with hx | hx
      · -- the new node is reached from every old gray node through `v`
        subst x
        exact (I.gray_reach g hg v hv (I.le_top hc g hg)).tail hedge
      · rw [ixs_ne g (gne_w g hg), ixs_ne x (ne_w x hx)] at hle
        exact I.gray_reach g hg x hx hle
  · intro x hx; rw [sk] at hx
    rcases List.mem_cons.1 hx with hx | hx
    · subst x; rw [lws_w, ixs_w]; exact Nat.le_refl _
    · rw [lws_ne x (ne_w x hx), ixs_ne x (ne_w x hx)]; exact I.low_le x hx
  · intro x hx; rw [sk] at hx; rw [sk]
    rcases List.mem_cons.1 hx with hx | hx
    · subst x; exact ⟨w, List.mem_cons_self .., by rw [ixs_w, lws_w], .refl _⟩
    · obtain ⟨y, hy, e, r⟩ := I.low_wit x hx
      refine ⟨y, List.mem_cons_of_mem _ hy, ?_, r⟩
      rw [ixs_ne y (ne_w y hy), lws_ne x (ne_w x hx)]; exact e
  · intro x hx hng; rw [sk] at hx; rw [gr] at hng
    rcases List.mem_cons.1 hx with hx | hx
    · subst x; exact absurd (List.mem_cons_self ..) hng
    · rw [lws_ne x (ne_w x hx), ixs_ne x (ne_w x hx)]
      exact I.low_fin x hx (fun h => hng (List.mem_cons_of_mem _ h))
  · intro x hx g hg hgx hmax
    rw [sk] at hx; rw [gr] at hg hmax
    rcases List.mem_cons.1 hx with hx | hx
    · -- the new node is its own nearest gray node
      subst x
      have h1 := hmax w (List.mem_cons_self ..) (Nat.le_refl _)
      rcases List.mem_cons.1 hg with hg | hg
      · subst g; exact Nat.le_refl _
      · rw [ixs_w, ixs_ne g (gne_w g hg)] at h1
        have := ixlt g; omega
    · rcases List.mem_cons.1 hg with hg | hg
      · subst g; rw [ixs_w, ixs_ne x (ne_w x hx)] at hgx
        have := ixlt x; omega
      · rw [lws_ne g (gne_w g hg), lws_ne x (ne_w x hx)]
        rw [ixs_ne g (gne_w g hg), ixs_ne x (ne_w x hx)] at hgx
        refine I.low_gray x hx g hg hgx fun h hh hhx => ?_
        have := hmax h (List.mem_cons_of_mem _ hh)
        rw [ixs_ne h (gne_w h hh), ixs_ne x (ne_w x hx), ixs_ne g (gne_w g hg)] at this
        exact this hhx
  · intro x hx u hu
    rw [sk] at hx
    obtain ⟨j, hj, hlt⟩ := hu
    rcases List.mem_cons.1 hx with hx | hx
    · subst x; exact absurd (hlt (w, 0) (by rw [cl]; simp) rfl) (Nat.not_lt_zero _)
    · have hxw := ne_w x hx
      by_cases hxj : x = v ∧ j = i
      · obtain ⟨hxv, hji⟩ := hxj
        subst x; subst j
        rw [hget] at hj
        cases hj
        refine ⟨by rw [ixs_w]; omega, fun _ => ?_⟩
        rw [lws_ne v hxw, ixs_w]
        exact Nat.le_of_lt (Nat.lt_of_le_of_lt (I.low_le v hx) (ixlt v))
      · have hu : Expl G st x u := ⟨j, hj, fun p hp hpx => by
          rw [hc] at hp
          rcases List.mem_cons.1 hp with hp | hp
          · subst p; simp only at hpx; subst x
            have h1 := hlt (v, i + 1) (by rw [cl]; simp) rfl
            have h2 : j ≠ i := fun h => hxj ⟨rfl, h⟩
            simp only at h1 ⊢; omega
          · exact hlt p (by rw [cl]; simp [hp]) hpx⟩
        obtain ⟨h1, h2⟩ := I.explored x hx u hu
        have huw : u ≠ w := fun h => h1 (h ▸ h0)
        refine ⟨by rw [ixs_ne u huw]; exact h1, fun hus => ?_⟩
        rw [sk] at hus
        rcases List.mem_cons.1 hus with h | hus
        · exact absurd h huw
        · rw [lws_ne x hxw, ixs_ne u huw]; exact h2 hus
  · intro u; rw [cp, sk]
    by_cases hu : u = w
    · subst u
      rw [ixs_w]
      simp only [List.mem_cons_self, not_true_eq_false, and_false, iff_false]
      rintro ⟨c, hc', huc⟩
      exact (I.comp_iff w |>.1 ⟨c, hc', huc⟩).1 h0
    · rw [ixs_ne u hu]
      simp only [List.mem_cons, hu, false_or]
      exact I.comp_iff u
  · intro k k' c c' u; rw [cp]; exact I.comp_uniq k k' c c' u
  · intro c; rw [cp]; exact I.comp_conn c
  · intro k c u w'; rw [cp]; exact I.comp_down k c u w'

/-! ## Finishing a node -/

theorem mem_popped {pre : List Nat} {v u : Nat} :
    u ∈ (#[] ++ (pre ++ [v]).toArray).qsort (· < ·) ↔ u ∈ pre ∨ u = v := by
  rw [mem_qsort]; simp

/-- Finishing a root `v` (`lw v = ix v`): its component is the stack down to `v`, strongly
connected, with every edge to itself or to an earlier component. -/
theorem inv_pop {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) (hi : ¬ i < (succs G v).size)
    (hroot : lw st v = ix st v) :
    Inv G (({ st with calls := rest } : TarjanState).popComponent v) := by
  have hv := I.v_stack hc
  have hvg : v ∈ grays st := by rw [grays_cons hc]; simp
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hv
  have sorted := I.st_sorted
  rw [hs, List.pairwise_append, List.pairwise_cons] at sorted
  obtain ⟨_, ⟨hvpost, spost⟩, hpre⟩ := sorted
  -- every node above `v` has a larger number, every node below a smaller one
  have hpre' : ∀ a ∈ pre, ix st v < ix st a := fun a ha => hpre a ha v (by simp)
  have hpost' : ∀ b ∈ post, ix st b < ix st v := hvpost
  have vnpre : v ∉ pre := fun h => Nat.lt_irrefl _ (hpre' v h)
  have vnpost : v ∉ post := fun h => Nat.lt_irrefl _ (hpost' v h)
  have hstk : ∀ x, x ∈ st.stack ↔ x ∈ pre ∨ x = v ∨ x ∈ post := by
    intro x; rw [hs]; simp
  have above : ∀ x ∈ st.stack, ix st v ≤ ix st x → x ∈ pre ∨ x = v := by
    intro x hx hle
    rcases (hstk x).1 hx with h | h | h
    · exact .inl h
    · exact .inr h
    · have := hpost' x h; omega
  have below : ∀ x ∈ st.stack, ix st x < ix st v → x ∈ post := by
    intro x hx hlt
    rcases (hstk x).1 hx with h | h | h
    · have := hpre' x h; omega
    · subst h; omega
    · exact h
  have pre_stk : ∀ a ∈ pre, a ∈ st.stack := fun a ha => (hstk a).2 (.inl ha)
  have post_stk : ∀ b ∈ post, b ∈ st.stack := fun b hb => (hstk b).2 (.inr (.inr hb))
  have pre_npost : ∀ a ∈ pre, a ∉ post := fun a ha hb => by
    have := hpre' a ha; have := hpost' a hb; omega
  have rest_lt : ∀ g ∈ rest.map (·.1), ix st g < ix st v := I.top_gray hc
  have rest_post : ∀ g ∈ rest.map (·.1), g ∈ post := fun g hg =>
    below g (I.gray_stack (by rw [grays_cons hc]; exact List.mem_cons_of_mem _ hg)) (rest_lt g hg)
  have rest_g : ∀ g ∈ rest.map (·.1), g ∈ grays st := fun g hg => by
    rw [grays_cons hc]; exact List.mem_cons_of_mem _ hg
  -- nodes above `v` are finished, and the nearest gray node below them is `v`
  have pre_ng : ∀ a ∈ pre, a ∉ grays st := fun a ha hg => by
    have := I.le_top hc a hg; have := hpre' a ha; omega
  have pre_lowv : ∀ a ∈ pre, lw st v ≤ lw st a := fun a ha =>
    I.low_gray a (pre_stk a ha) v hvg (Nat.le_of_lt (hpre' a ha))
      (fun h hh _ => I.le_top hc h hh)
  -- every node of the component reaches `v`
  have reach_v : ∀ m, ∀ u ∈ st.stack, ix st u = m → ix st v ≤ m → Reach G u v := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro u hu hm hle
      rcases above u hu (hm ▸ hle) with hu' | hu'
      · have hlf := I.low_fin u hu (pre_ng u hu')
        obtain ⟨y, hy, e, r⟩ := I.low_wit u hu
        have h1 := pre_lowv u hu'
        exact r.trans (ih (ix st y) (by omega) y hy rfl (by omega))
      · subst hu'; exact .refl _
  obtain ⟨psk, pon, pcomps, -, pidx, plow, pcalls, pnext, -⟩ :=
    popComponent_spec ({ st with calls := rest } : TarjanState) v pre post hs vnpre
  generalize hst2 : ({ st with calls := rest } : TarjanState).popComponent v = st2 at psk pon pcomps pidx plow pcalls pnext
  have ix2 : ix st2 = ix st := by funext u; simp only [ix, pidx]
  have lw2 : lw st2 = lw st := by funext u; simp only [lw, plow]
  have hbound : ∀ w ∈ pre ++ [v], w < st.onStack.size := fun w hw => by
    rw [I.szO]; simp at hw
    rcases hw with hw | hw
    · exact I.lt_of_stack (pre_stk w hw)
    · subst hw; exact I.lt_of_stack hv
  have os2 : ∀ u, os st2 u = if u ∈ pre ++ [v] then false else os st u := fun u => by
    simp only [os, pon]; exact foldl_set_false_getD _ _ hbound u
  have gr2 : grays st2 = rest.map (·.1) := by simp [grays, pcalls]
  have hK : ∀ k, k < st.comps.size → st2.comps[k]? = st.comps[k]? := fun k hk => by
    rw [pcomps]; simp [Array.getElem?_push, Nat.ne_of_lt hk]
  have hKC : st2.comps[st.comps.size]? = some ((#[] ++ (pre ++ [v]).toArray).qsort (· < ·)) := by
    rw [pcomps]; simp
  have hKbig : ∀ k, st.comps.size < k → st2.comps[k]? = none := fun k hk => by
    rw [pcomps]; apply Array.getElem?_eq_none; rw [Array.size_push]
    show st.comps.size + 1 ≤ k; omega
  have oldk : ∀ k c, st.comps[k]? = some c → k < st.comps.size := fun k c h => by
    rcases Nat.lt_or_ge k st.comps.size with hk | hk
    · exact hk
    · rw [Array.getElem?_eq_none hk] at h; cases h
  -- membership in the new components
  have comps2 : ∀ c, c ∈ st2.comps ↔ c ∈ st.comps ∨
      c = (#[] ++ (pre ++ [v]).toArray).qsort (· < ·) := fun c => by
    rw [pcomps, Array.mem_push]
  -- the nodes of the new component are on the old stack
  have C_stk : ∀ u, u ∈ pre ∨ u = v → u ∈ st.stack := fun u hu => by
    rcases hu with hu | hu
    · exact pre_stk u hu
    · subst hu; exact hv
  have C_nold : ∀ u, u ∈ pre ∨ u = v → ∀ c ∈ st.comps, u ∉ c := fun u hu c hc' huc =>
    ((I.comp_iff u).1 ⟨c, hc', huc⟩).2 (C_stk u hu)
  have explored_C : ∀ u, u ∈ pre ∨ u = v → ∀ w, Edge G u w →
      ix st w ≠ 0 ∧ (w ∈ st.stack → lw st u ≤ ix st w) := by
    intro u hu w e
    obtain ⟨j, hj⟩ := exists_index_of_edge e
    refine I.explored u (C_stk u hu) w ⟨j, hj, fun p hp hpx => ?_⟩
    rw [hc] at hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst p; simp only at hpx ⊢
      have hjlt : j < (succs G u).size := by
        rcases Nat.lt_or_ge j (succs G u).size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hj; cases hj
      subst hpx; omega
    · exfalso
      have hg : p.1 ∈ rest.map (·.1) := List.mem_map_of_mem hp
      rw [hpx] at hg
      rcases hu with hu | hu
      · exact pre_npost u hu (rest_post u hg)
      · subst hu; exact I.not_rest hc hg
  refine
    { szI := by rw [pidx]; exact I.szI
      szL := by rw [plow]; exact I.szL
      szO := by rw [pon]; rw [foldl_set_false_size]; exact I.szO
      next_pos := by rw [pnext]; exact I.next_pos
      ix_lt := by rw [ix2, pnext]; exact I.ix_lt
      ix_inj := by rw [ix2]; exact I.ix_inj
      on_iff := ?_, st_vis := ?_, st_sorted := ?_
      calls_on := ?_, calls_le := ?_, calls_sorted := ?_, stack_gray := ?_, gray_reach := ?_
      low_le := ?_, low_wit := ?_, low_fin := ?_, low_gray := ?_, explored := ?_
      comp_iff := ?_, comp_uniq := ?_, comp_conn := ?_, comp_down := ?_ }
  · intro u; rw [os2, psk]
    by_cases hu : u ∈ pre ++ [v]
    · simp only [hu, ↓reduceIte, Bool.false_eq_true, false_iff]
      simp at hu
      rcases hu with hu | hu
      · exact pre_npost u hu
      · subst hu; exact vnpost
    · simp only [hu, ↓reduceIte]
      rw [I.on_iff, hstk]
      simp at hu
      constructor
      · rintro (h | h | h)
        · exact absurd h hu.1
        · exact absurd h hu.2
        · exact h
      · intro h; exact .inr (.inr h)
  · intro u hu; rw [psk] at hu; rw [ix2]; exact I.st_vis u (post_stk u hu)
  · rw [psk, ix2]; exact spost
  · intro g hg; rw [gr2] at hg; rw [psk]; exact rest_post g hg
  · intro p hp; rw [pcalls] at hp; exact I.calls_le p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
  · rw [gr2, ix2]
    have := I.calls_sorted
    rw [grays_cons hc, List.pairwise_cons] at this
    exact this.2
  · intro x hx; rw [psk] at hx; rw [gr2, ix2]
    obtain ⟨g, hg, hle⟩ := I.stack_gray x (post_stk x hx)
    refine ⟨g, ?_, hle⟩
    rw [grays_cons hc] at hg
    rcases List.mem_cons.1 hg with hg | hg
    · subst hg; have := hpost' x hx; omega
    · exact hg
  · intro g hg x hx hle; rw [gr2] at hg; rw [psk] at hx; rw [ix2] at hle
    exact I.gray_reach g (rest_g g hg) x (post_stk x hx) hle
  · intro x hx; rw [psk] at hx; rw [lw2, ix2]; exact I.low_le x (post_stk x hx)
  · intro x hx; rw [psk] at hx; rw [lw2, ix2, psk]
    obtain ⟨y, hy, e, r⟩ := I.low_wit x (post_stk x hx)
    have := I.low_le x (post_stk x hx)
    have := hpost' x hx
    exact ⟨y, below y hy (by omega), e, r⟩
  · intro x hx hng; rw [psk] at hx; rw [gr2] at hng; rw [lw2, ix2]
    refine I.low_fin x (post_stk x hx) fun hg => ?_
    rw [grays_cons hc] at hg
    rcases List.mem_cons.1 hg with hg | hg
    · subst hg; exact vnpost hx
    · exact hng hg
  · intro x hx g hg hgx hmax
    rw [psk] at hx; rw [gr2] at hg hmax; rw [ix2] at hgx hmax; rw [lw2]
    refine I.low_gray x (post_stk x hx) g (rest_g g hg) hgx fun h hh hhx => ?_
    rw [grays_cons hc] at hh
    rcases List.mem_cons.1 hh with hh | hh
    · subst hh; have := hpost' x hx; omega
    · exact hmax h hh hhx
  · intro x hx u hu
    rw [psk] at hx; rw [ix2, lw2, psk]
    have hu' : Expl G st x u := (expl_iff_of_calls (fun p hpx => by
      rw [pcalls, hc]
      simp only [List.mem_cons]
      constructor
      · exact .inr
      · rintro (h | h)
        · subst h; simp only at hpx; subst hpx; exact absurd hx vnpost
        · exact h)).1 hu
    obtain ⟨h1, h2⟩ := I.explored x (post_stk x hx) u hu'
    exact ⟨h1, fun hus => h2 (post_stk u hus)⟩
  · intro u; rw [ix2, psk]
    constructor
    · rintro ⟨c, hc', huc⟩
      rcases (comps2 c).1 hc' with hc' | hc'
      · obtain ⟨h1, h2⟩ := (I.comp_iff u).1 ⟨c, hc', huc⟩
        exact ⟨h1, fun h => h2 (post_stk u h)⟩
      · subst hc'
        have hu := mem_popped.1 huc
        refine ⟨I.st_vis u (C_stk u hu), ?_⟩
        rcases hu with hu | hu
        · exact pre_npost u hu
        · subst hu; exact vnpost
    · rintro ⟨h1, h2⟩
      by_cases hs' : u ∈ st.stack
      · rcases (hstk u).1 hs' with h | h | h
        · exact ⟨_, (comps2 _).2 (.inr rfl), mem_popped.2 (.inl h)⟩
        · exact ⟨_, (comps2 _).2 (.inr rfl), mem_popped.2 (.inr h)⟩
        · exact absurd h h2
      · obtain ⟨c, hc', huc⟩ := (I.comp_iff u).2 ⟨h1, hs'⟩
        exact ⟨c, (comps2 c).2 (.inl hc'), huc⟩
  · intro k k' c c' u hk hk' hu hu'
    rcases Nat.lt_trichotomy k st.comps.size with h1 | h1 | h1 <;>
      rcases Nat.lt_trichotomy k' st.comps.size with h2 | h2 | h2
    · rw [hK k h1] at hk; rw [hK k' h2] at hk'
      exact I.comp_uniq k k' c c' u hk hk' hu hu'
    · subst h2; rw [hK k h1] at hk; rw [hKC] at hk'; cases hk'
      exact absurd hu (C_nold u (mem_popped.1 hu') c (Array.mem_of_getElem? hk))
    · rw [hKbig k' h2] at hk'; cases hk'
    · subst h1; rw [hKC] at hk; cases hk; rw [hK k' h2] at hk'
      exact absurd hu' (C_nold u (mem_popped.1 hu) c' (Array.mem_of_getElem? hk'))
    · rw [h1, h2]
    · rw [hKbig k' h2] at hk'; cases hk'
    all_goals (rw [hKbig k h1] at hk; cases hk)
  · intro c hc' u hu w hw
    rcases (comps2 c).1 hc' with hc' | hc'
    · exact I.comp_conn c hc' u hu w hw
    · subst hc'
      have hu' := mem_popped.1 hu
      have hw' := mem_popped.1 hw
      refine (reach_v (ix st u) u (C_stk u hu') rfl ?_).trans ?_
      · rcases hu' with hu' | hu'
        · exact Nat.le_of_lt (hpre' u hu')
        · subst hu'; exact Nat.le_refl _
      · refine I.gray_reach v hvg w (C_stk w hw') ?_
        rcases hw' with hw' | hw'
        · exact Nat.le_of_lt (hpre' w hw')
        · subst hw'; exact Nat.le_refl _
  · intro k c u w hk hu e
    rcases Nat.lt_trichotomy k st.comps.size with h1 | h1 | h1
    · rw [hK k h1] at hk
      obtain ⟨k', c', hle, hk', hw⟩ := I.comp_down k c u w hk hu e
      exact ⟨k', c', hle, by rw [hK k' (Nat.lt_of_le_of_lt hle h1)]; exact hk', hw⟩
    · subst h1; rw [hKC] at hk; cases hk
      have hu' := mem_popped.1 hu
      obtain ⟨h1, h2⟩ := explored_C u hu' w e
      by_cases hws : w ∈ st.stack
      · -- the edge stays in the component
        have hlu : lw st v ≤ lw st u := by
          rcases hu' with hu' | hu'
          · exact pre_lowv u hu'
          · subst hu'; exact Nat.le_refl _
        have := h2 hws
        exact ⟨st.comps.size, _, Nat.le_refl _, hKC, mem_popped.2 (above w hws (by omega))⟩
      · -- the edge leaves for an earlier component
        obtain ⟨c', hc', hw⟩ := (I.comp_iff w).2 ⟨h1, hws⟩
        obtain ⟨k', hk'⟩ := Array.getElem?_of_mem hc'
        have hk'lt := oldk k' c' hk'
        exact ⟨k', c', Nat.le_of_lt hk'lt, by rw [hK k' hk'lt]; exact hk', hw⟩
    · rw [hKbig k h1] at hk; cases hk

/-- The invariant reads only the functions `ix`, `lw`, `os`, the stack, the calls, `next`, the
components and the array sizes. -/
theorem Inv.congr {G : Array (Array Nat)} {st st' : TarjanState} (I : Inv G st)
    (hI : st'.index.size = st.index.size) (hL : st'.low.size = st.low.size)
    (hO : st'.onStack.size = st.onStack.size) (hix : ix st' = ix st) (hlw : lw st' = lw st)
    (hos : os st' = os st) (hs : st'.stack = st.stack) (hc : st'.calls = st.calls)
    (hn : st'.next = st.next) (hk : st'.comps = st.comps) : Inv G st' := by
  have hg : grays st' = grays st := by simp [grays, hc]
  have hE : ∀ x w, Expl G st' x w ↔ Expl G st x w := fun x w =>
    expl_iff_of_calls fun p _ => by rw [hc]
  refine
    { szI := by rw [hI]; exact I.szI
      szL := by rw [hL]; exact I.szL
      szO := by rw [hO]; exact I.szO
      next_pos := by rw [hn]; exact I.next_pos
      ix_lt := by rw [hix, hn]; exact I.ix_lt
      ix_inj := by rw [hix]; exact I.ix_inj
      on_iff := by rw [hos, hs]; exact I.on_iff
      st_vis := by rw [hix, hs]; exact I.st_vis
      st_sorted := by rw [hix, hs]; exact I.st_sorted
      calls_on := by rw [hg, hs]; exact I.calls_on
      calls_le := by rw [hc]; exact I.calls_le
      calls_sorted := by rw [hg, hix]; exact I.calls_sorted
      stack_gray := by rw [hg, hix, hs]; exact I.stack_gray
      gray_reach := by rw [hg, hix, hs]; exact I.gray_reach
      low_le := by rw [hlw, hix, hs]; exact I.low_le
      low_wit := by rw [hlw, hix, hs]; exact I.low_wit
      low_fin := by rw [hlw, hix, hs, hg]; exact I.low_fin
      low_gray := by rw [hlw, hix, hs, hg]; exact I.low_gray
      explored := ?_
      comp_iff := by rw [hk, hix, hs]; exact I.comp_iff
      comp_uniq := by rw [hk]; exact I.comp_uniq
      comp_conn := by rw [hk]; exact I.comp_conn
      comp_down := by rw [hk]; exact I.comp_down }
  intro x hx w hw
  rw [hs] at hx; rw [hix, hlw, hs]
  exact I.explored x hx w ((hE x w).1 hw)

theorem popComponent_index' (st : TarjanState) (v : Nat) :
    (st.popComponent v).index = st.index := by
  cases st; simp only [TarjanState.popComponent]

theorem popComponent_low' (st : TarjanState) (v : Nat) : (st.popComponent v).low = st.low := by
  cases st; simp only [TarjanState.popComponent]

/-- Finishing a node that is not a root: it passes its low link to its parent. -/
theorem inv_lift {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {u k : Nat} {rest' : List (Nat × Nat)} (hc : st.calls = (v, i) :: (u, k) :: rest')
    (hi : ¬ i < (succs G v).size) (hnr : lw st v ≠ ix st v) :
    Inv G (({ st with calls := (u, k) :: rest' } : TarjanState).setLow u
      (min (lw st u) (lw st v))) := by
  have hv := I.v_stack hc
  have hvg : v ∈ grays st := by rw [grays_cons hc]; simp
  have hug : u ∈ grays st := by rw [grays_cons hc]; simp
  have hu := I.gray_stack hug
  have hlv : lw st v < ix st v := by have := I.low_le v hv; omega
  have huv : ix st u < ix st v := I.top_gray hc u (by simp)
  have hune : u ≠ v := fun h => by subst h; omega
  have rest_lt : ∀ g ∈ ((u, k) :: rest').map (·.1), ix st g < ix st v := I.top_gray hc
  have rest_le_u : ∀ g ∈ ((u, k) :: rest').map (·.1), ix st g ≤ ix st u := by
    have := I.calls_sorted
    rw [grays_cons hc, List.pairwise_cons, List.map_cons, List.pairwise_cons] at this
    intro g hg
    rcases List.mem_cons.1 hg with hg | hg
    · subst hg; exact Nat.le_refl _
    · exact Nat.le_of_lt (this.2.1 g hg)
  have rest_g : ∀ g ∈ ((u, k) :: rest').map (·.1), g ∈ grays st := fun g hg => by
    rw [grays_cons hc]; exact List.mem_cons_of_mem _ hg
  have hL : u < st.low.size := by rw [I.szL]; exact I.lt_of_stack hu
  let st1 : TarjanState := { st with calls := (u, k) :: rest' }
  have lw3 : ∀ x, lw (st1.setLow u (min (lw st u) (lw st v))) x =
      if x = u then min (lw st u) (lw st v) else lw st x := fun x => lw_setLow (st := st1) hL x
  have ix3 : ix (st1.setLow u (min (lw st u) (lw st v))) = ix st := by
    funext x; simp [ix, setLow_index, st1]
  have os3 : os (st1.setLow u (min (lw st u) (lw st v))) = os st := by
    funext x; simp [os, setLow_onStack, st1]
  have sk3 : (st1.setLow u (min (lw st u) (lw st v))).stack = st.stack := by
    rw [setLow_stack]
  have cl3 : (st1.setLow u (min (lw st u) (lw st v))).calls = (u, k) :: rest' := by
    rw [setLow_calls]
  have gr3 : grays (st1.setLow u (min (lw st u) (lw st v))) = ((u, k) :: rest').map (·.1) := by
    simp [grays, cl3]
  have cp3 : (st1.setLow u (min (lw st u) (lw st v))).comps = st.comps := by rw [setLow_comps]
  have lw3_ne : ∀ x, x ≠ u → lw (st1.setLow u (min (lw st u) (lw st v))) x = lw st x :=
    fun x hx => by rw [lw3]; simp [hx]
  have lw3_u : lw (st1.setLow u (min (lw st u) (lw st v))) u = min (lw st u) (lw st v) := by
    rw [lw3]; simp
  have lw3_le : ∀ x, lw (st1.setLow u (min (lw st u) (lw st v))) x ≤ lw st x := fun x => by
    rw [lw3]; split
    · subst x; exact Nat.min_le_left _ _
    · exact Nat.le_refl _
  show Inv G (st1.setLow u (min (lw st u) (lw st v)))
  refine
    { szI := by rw [setLow_index]; exact I.szI
      szL := by rw [setLow_low]; simp [Array.set!, st1, I.szL]
      szO := by rw [setLow_onStack]; exact I.szO
      next_pos := by rw [setLow_next]; exact I.next_pos
      ix_lt := by rw [ix3, setLow_next]; exact I.ix_lt
      ix_inj := by rw [ix3]; exact I.ix_inj
      on_iff := by rw [os3, sk3]; exact I.on_iff
      st_vis := by rw [ix3, sk3]; exact I.st_vis
      st_sorted := by rw [ix3, sk3]; exact I.st_sorted
      calls_on := by rw [gr3, sk3]; exact fun g hg => I.gray_stack (rest_g g hg)
      calls_le := by
        rw [cl3]; intro p hp; exact I.calls_le p (by rw [hc]; exact List.mem_cons_of_mem _ hp)
      calls_sorted := by
        rw [gr3, ix3]
        have := I.calls_sorted
        rw [grays_cons hc, List.pairwise_cons] at this
        exact this.2
      stack_gray := ?_, gray_reach := ?_
      low_le := ?_, low_wit := ?_, low_fin := ?_, low_gray := ?_, explored := ?_
      comp_iff := by rw [cp3, ix3, sk3]; exact I.comp_iff
      comp_uniq := by rw [cp3]; exact I.comp_uniq
      comp_conn := by rw [cp3]; exact I.comp_conn
      comp_down := by rw [cp3]; exact I.comp_down }
  · intro x hx; rw [sk3] at hx; rw [gr3, ix3]
    obtain ⟨g, hg, hle⟩ := I.stack_gray x hx
    rw [grays_cons hc] at hg
    rcases List.mem_cons.1 hg with hg | hg
    · subst hg; exact ⟨u, by simp, by omega⟩
    · exact ⟨g, hg, hle⟩
  · intro g hg x hx hle; rw [gr3] at hg; rw [sk3] at hx; rw [ix3] at hle
    exact I.gray_reach g (rest_g g hg) x hx hle
  · intro x hx; rw [sk3] at hx; rw [ix3]
    exact Nat.le_trans (lw3_le x) (I.low_le x hx)
  · intro x hx; rw [sk3] at hx; rw [ix3, sk3]
    by_cases hxu : x = u
    · subst hxu
      rw [lw3_u]
      by_cases hm : lw st v < lw st x
      · obtain ⟨y, hy, e, r⟩ := I.low_wit v hv
        exact ⟨y, hy, by omega, (I.gray_reach x hug v hv (Nat.le_of_lt huv)).trans r⟩
      · obtain ⟨y, hy, e, r⟩ := I.low_wit x hx
        exact ⟨y, hy, by omega, r⟩
    · rw [lw3_ne x hxu]; exact I.low_wit x hx
  · intro x hx hng; rw [sk3] at hx; rw [gr3] at hng; rw [ix3]
    have hxu : x ≠ u := fun h => hng (by subst h; simp)
    rw [lw3_ne x hxu]
    by_cases hxv : x = v
    · subst hxv; exact hlv
    · refine I.low_fin x hx fun hg => ?_
      rw [grays_cons hc] at hg
      rcases List.mem_cons.1 hg with hg | hg
      · exact hxv hg
      · exact hng hg
  · intro x hx g hg hgx hmax
    rw [sk3] at hx; rw [gr3] at hg hmax; rw [ix3] at hgx hmax
    have hgle := rest_le_u g hg
    by_cases hxv : ix st v ≤ ix st x
    · -- the nearest gray node below `x` is now `u`, and was `v`
      have hgu : g = u := by
        have := hmax u (by simp) (by omega)
        exact (I.eq_of_ix hu (by omega : ix st u = ix st g)).symm
      subst hgu
      have hxg : x ≠ g := fun h => by subst h; omega
      rw [lw3_u, lw3_ne x hxg]
      exact Nat.le_trans (Nat.min_le_right _ _)
        (I.low_gray x hx v hvg hxv fun h hh _ => I.le_top hc h hh)
    · have hold : lw st g ≤ lw st x := by
        refine I.low_gray x hx g (rest_g g hg) hgx fun h hh hhx => ?_
        rw [grays_cons hc] at hh
        rcases List.mem_cons.1 hh with hh | hh
        · subst hh; omega
        · exact hmax h hh hhx
      by_cases hxu : x = u
      · subst hxu
        have : g = x := by
          have := hmax x (by simp) (Nat.le_refl _)
          exact (I.eq_of_ix hu (by omega : ix st x = ix st g)).symm
        subst this; exact Nat.le_refl _
      · rw [lw3_ne x hxu]
        exact Nat.le_trans (lw3_le g) hold
  · intro x hx w hw
    rw [sk3] at hx; rw [ix3, sk3]
    by_cases hxv : x = v
    · subst hxv
      obtain ⟨j, hj, -⟩ := hw
      have hw' : Expl G st x w := ⟨j, hj, fun p hp hpx => by
        rw [hc] at hp
        rcases List.mem_cons.1 hp with hp | hp
        · subst hp
          have hjlt : j < (succs G x).size := by
            rcases Nat.lt_or_ge j (succs G x).size with h | h
            · exact h
            · rw [Array.getElem?_eq_none h] at hj; cases hj
          simp only; omega
        · exact absurd (hpx ▸ List.mem_map_of_mem hp) (I.not_rest hc)⟩
      obtain ⟨h1, h2⟩ := I.explored x hx w hw'
      exact ⟨h1, fun hws => by rw [lw3_ne x (Ne.symm hune)]; exact h2 hws⟩
    · have hw' : Expl G st x w := (expl_iff_of_calls (fun p hpx => by
        rw [cl3, hc]
        simp only [List.mem_cons]
        constructor
        · exact .inr
        · rintro (h | h)
          · subst h; exact absurd hpx.symm hxv
          · exact h)).1 hw
      obtain ⟨h1, h2⟩ := I.explored x hx w hw'
      exact ⟨h1, fun hws => Nat.le_trans (lw3_le x) (h2 hws)⟩

/-- Every finishing step keeps the invariant. -/
theorem inv_finish {G : Array (Array Nat)} {st : TarjanState} (I : Inv G st) {v i : Nat}
    {rest : List (Nat × Nat)} (hc : st.calls = (v, i) :: rest) (hi : ¬ i < (succs G v).size) :
    Inv G (finishSt st v rest) := by
  have hv := I.v_stack hc
  unfold finishSt
  by_cases hr : lw st v = ix st v
  · have I2 := inv_pop I hc hi hr
    have hb : (lw st v == ix st v) = true := by simp [hr]
    simp only [hb, ↓reduceIte]
    cases rest with
    | nil => exact I2
    | cons p rest' =>
      obtain ⟨u, k⟩ := p
      simp only
      have hu : u ∈ st.stack := I.gray_stack (by rw [grays_cons hc]; simp)
      have hlow : lw (({ st with calls := (u, k) :: rest' } : TarjanState).popComponent v) =
          lw st := by funext x; simp only [lw, popComponent_low']
      have hm : min (lw st u) (lw st v) = lw st u := by
        have := I.top_gray hc u (by simp); have := I.low_le u hu; omega
      rw [hlow, hm]
      generalize hst2 : ({ st with calls := (u, k) :: rest' } : TarjanState).popComponent v = st2 at I2 hlow
      have hL : u < st2.low.size := by rw [I2.szL]; exact I.lt_of_stack hu
      refine I2.congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [setLow_index]
      · rw [setLow_low]; simp [Array.set!]
      · rw [setLow_onStack]
      · funext x; simp [ix, setLow_index]
      · funext x; rw [lw_setLow hL]; split
        · subst x; rw [hlow]
        · rfl
      · funext x; simp [os, setLow_onStack]
      · rw [setLow_stack]
      · rw [setLow_calls]
      · rw [setLow_next]
      · rw [setLow_comps]
  · have hne : (lw st v == ix st v) = false := by simpa using hr
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    cases rest with
    | nil =>
      exfalso
      -- with no parent, `v` is the only gray node and nothing below it is on the stack
      obtain ⟨y, hy, e, -⟩ := I.low_wit v hv
      obtain ⟨g, hg, hle⟩ := I.stack_gray y hy
      rw [grays_cons hc] at hg
      have := I.low_le v hv
      simp at hg; subst hg; omega
    | cons p rest' =>
      obtain ⟨u, k⟩ := p
      exact inv_lift I hc hi hr

end Ix.CompileCert.Canon
