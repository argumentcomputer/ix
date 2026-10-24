import Ix.CompileCert.Canon.SccMain

/-! # The condensation's roots lie in their components

`Ix.CondenseM.run` names each block of the condensation by its component's root
(`Condensation.roots[k]` for `Condensation.comps[k]`), so the statements lane needs
every root to be a member of the component it names. `condensation_roots_mem`:
`condensation adj` records exactly one root per component, and that root lies in
the component (`condensation_root_mem` is the indexed form).

The invariant `RootsIn` is layered over `Ix.CompileCert.Canon.Inv` the way `Nodes`
is in `SccRange.lean`: `visit` and `setLow` leave `comps` and `roots` alone, and
`popComponent v` pushes the stack down to `v` together with `v`, which is on the
stack whenever the loop pops (`Inv.v_stack`). -/

namespace Ix.Cert.CondenseRoots

open Ix.Compile.Canon Ix.CompileCert.Canon

/-- One root per component, each inside its component. -/
def RootsIn (st : TarjanState) : Prop :=
  st.roots.size = st.comps.size ∧
    ∀ (k r : Nat) (c : Array Nat), st.roots[k]? = some r → st.comps[k]? = some c → r ∈ c

/-- Split a list at the first occurrence of `v`. -/
theorem split_first {v : Nat} : ∀ {l : List Nat}, v ∈ l → ∃ pre post, l = pre ++ v :: post ∧ v ∉ pre
  | x :: xs, h => by
    by_cases hx : x = v
    · exact ⟨[], xs, by simp [hx], by simp⟩
    · obtain ⟨pre, post, e, hn⟩ := split_first ((List.mem_cons.1 h).resolve_left (Ne.symm hx))
      exact ⟨x :: pre, post, by simp [e], by simp [hn, Ne.symm hx]⟩

namespace RootsIn

variable {st : TarjanState}

theorem congr (R : RootsIn st) {st' : TarjanState} (hr : st'.roots = st.roots)
    (hc : st'.comps = st.comps) : RootsIn st' := by
  unfold RootsIn; rw [hr, hc]; exact R

theorem pop (R : RootsIn st) {v : Nat} (hv : v ∈ st.stack) : RootsIn (st.popComponent v) := by
  obtain ⟨pre, post, hs, hn⟩ := split_first hv
  obtain ⟨-, -, hc, hr, -⟩ := popComponent_spec st v pre post hs hn
  refine ⟨by rw [hc, hr, Array.size_push, Array.size_push, R.1], fun k r c hk hck => ?_⟩
  rw [hr, Array.getElem?_push, R.1] at hk
  rw [hc, Array.getElem?_push] at hck
  by_cases e : k = st.comps.size
  · simp only [e, ↓reduceIte, Option.some.injEq] at hk hck
    subst hk hck
    exact mem_popped.2 (.inr rfl)
  · simp only [e, ↓reduceIte] at hk hck
    exact R.2 k r c hk hck

theorem finish (R : RootsIn st) {v : Nat} (hv : v ∈ st.stack) (rest : List (Nat × Nat)) :
    RootsIn (finishSt st v rest) := by
  have R1 : RootsIn ({ st with calls := rest } : TarjanState) := R.congr rfl rfl
  have R2 : RootsIn (if lw st v == ix st v then
      ({ st with calls := rest } : TarjanState).popComponent v
      else ({ st with calls := rest } : TarjanState)) := by
    split
    · exact R1.pop hv
    · exact R1
  unfold finishSt
  cases rest with
  | nil => exact R2
  | cons p rest' => exact R2.congr (setLow_roots ..) (setLow_comps ..)

end RootsIn

/-- `tarjanLoop` keeps `RootsIn` from any state satisfying Tarjan's invariant. -/
theorem tarjanLoop_roots {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (fuel : Nat) (st : TarjanState), Inv G st → RootsIn st → RootsIn (tarjanLoop G fuel st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st _ R
    rw [tarjanLoop_zero]
    split
    · exact R
    · exact R.congr rfl rfl
  | succ fuel ih =>
    intro st I R
    cases hc : st.calls with
    | nil => rw [tarjanLoop_nil G fuel st hc]; exact R
    | cons p rest =>
      obtain ⟨v, i⟩ := p
      have R1 : RootsIn ({ st with calls := (v, i + 1) :: rest } : TarjanState) := R.congr rfl rfl
      by_cases hi : i < (succs G v).size
      · by_cases h0 : ix st (succs G v)[i] = 0
        · rw [tarjanLoop_new G fuel st v i rest hc hi h0]
          exact ih _ (inv_new I hG hc hi h0) (R1.congr (visit_roots ..) (visit_comps ..))
        · by_cases hon : os st (succs G v)[i] = true
          · rw [tarjanLoop_on G fuel st v i rest hc hi h0 hon]
            exact ih _ (inv_on I hc hi h0 hon) (R1.congr (setLow_roots ..) (setLow_comps ..))
          · have hon' : os st (succs G v)[i] = false := by simpa using hon
            rw [tarjanLoop_done G fuel st v i rest hc hi h0 hon']
            exact ih _ (inv_done I hc hi h0 hon') R1
      · rw [tarjanLoop_finish G fuel st v i rest hc hi]
        exact ih _ (inv_finish I hc hi) (R.finish (I.v_stack hc) rest)

theorem rootStep_roots {G : Array (Array Nat)} (hG : Bounded G) (s : TarjanState × Nat) (r : Nat)
    (hr : r < G.size) (h : RootInv G s.1) (R : RootsIn s.1) : RootsIn (rootStep G s r).1 := by
  obtain ⟨st, fuel⟩ := s
  obtain ⟨I, hcs⟩ := h
  simp only [rootStep]
  split
  · exact R
  · rename_i hgo
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hgo
    obtain ⟨hex, h0⟩ := hgo
    obtain ⟨hc, hs⟩ := hcs (by simpa using hex)
    exact tarjanLoop_roots hG fuel _ (inv_root I hc hs hr h0)
      (R.congr (visit_roots ..) (visit_comps ..))

theorem fold_roots {G : Array (Array Nat)} (hG : Bounded G) :
    ∀ (l : List Nat), (∀ r ∈ l, r < G.size) → ∀ (s : TarjanState × Nat), RootInv G s.1 →
      RootsIn s.1 → RootsIn (l.foldl (rootStep G) s).1 := by
  intro l
  induction l with
  | nil => intro _ s _ R; exact R
  | cons r rs ih =>
    intro hl s h R
    have hr := hl r (List.mem_cons_self ..)
    exact ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) _
      (rootStep_spec hG s r hr h).1 (rootStep_roots hG s r hr h R)

/-- **Every root lies in its component**: `condensation adj` records one root per
component, and the `k`-th root is a member of the `k`-th component. -/
theorem condensation_roots_mem {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) :
    C.roots.size = C.comps.size ∧
      ∀ (k r : Nat) (c : Array Nat), C.roots[k]? = some r → C.comps[k]? = some c → r ∈ c := by
  rw [condensation_eq] at h
  simp only at h
  have I0 : RootInv (filt adj) (initSt adj.size, fuel0 adj).1 := by
    refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
    have := inv_init (filt adj); rw [filt_size] at this; exact this
  have R0 : RootsIn (initSt adj.size, fuel0 adj).1 :=
    ⟨by simp [initSt], fun k r c hk => by simp [initSt] at hk⟩
  have R := fold_roots (filt_bounded adj) (List.range adj.size)
    (fun r hr => by rw [filt_size]; simpa using hr) _ I0 R0
  generalize ((List.range adj.size).foldl (rootStep (filt adj)) (initSt adj.size, fuel0 adj)) = s
    at h R
  split at h
  · cases h
  · cases h
    exact R

/-- Indexed form of `condensation_roots_mem`. -/
theorem condensation_root_mem {adj : Array (Array Nat)} {C : Condensation}
    (h : condensation adj = some C) (k : Nat) (hk : k < C.comps.size) :
    C.roots[k]'(by rw [(condensation_roots_mem h).1]; exact hk) ∈ C.comps[k] :=
  (condensation_roots_mem h).2 k _ _ (Array.getElem?_eq_getElem _) (Array.getElem?_eq_getElem hk)

end Ix.Cert.CondenseRoots
