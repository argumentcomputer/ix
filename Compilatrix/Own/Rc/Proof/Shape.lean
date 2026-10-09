import Compilatrix.Own.Rc.Proof.ReleaseValue
import Compilatrix.Own.Proof.Heap

/-! Structural component of the initial counted heap invariant. Live cells
have positive counts and nonempty, correctly sized bodies whose location
fields refer to older cells. Balance separately establishes that each such
edge targets a live counted cell. Dead cells are permitted after release. -/

set_option autoImplicit false

namespace Compilatrix.Own.Rc

def BodyOk (l : Nat) (b : Body) : Prop :=
  b.fields.length = b.ctor.arity ∧ 0 < b.ctor.arity ∧
    ∀ k, RVal.loc k ∈ b.fields → k < l

def HeapOk (H : Heap) : Prop :=
  ∀ l rc m b, H.cell? l = some (.live rc m b) → m = .dyn ∧ 0 < rc ∧ BodyOk l b

theorem heapOk_empty : HeapOk {} := by
  intro l rc m b h
  simp [Heap.cell?] at h

theorem heapOk_set_count {H : Heap} {l rc rc' : Nat} {b : Body}
    (hh : HeapOk H) (hc : H.cell? l = some (.live rc .dyn b)) (hp : 0 < rc') :
    HeapOk (setCell H l (.live rc' .dyn b)) := by
  have hl := Proof.cell?_some hc
  intro k count mode body h
  rw [setCell_cell H l _ hl k] at h
  by_cases he : l = k
  · subst k
    simp only [ite_true, Option.some.injEq, Cell.live.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, hp, (hh l rc .dyn b hc).2.2⟩
  · rw [if_neg he] at h
    exact hh k count mode body h

theorem heapOk_free {H : Heap} {l : Nat}
    (hh : HeapOk H) (hl : l < H.size) : HeapOk (setCell H l .dead) := by
  intro k count mode body h
  rw [setCell_cell H l _ hl k] at h
  by_cases he : l = k
  · simp [he] at h
  · rw [if_neg he] at h
    exact hh k count mode body h

theorem heapOk_alloc {H : Heap} {b : Body}
    (hh : HeapOk H) (hb : BodyOk H.size b) : HeapOk (H.alloc .rc b).2 := by
  intro l rc m body hc
  have hl := Proof.cell?_some hc
  have hs := Proof.alloc_size .rc H b
  by_cases hold : l < H.size
  · rw [(Proof.Ext.alloc .rc H b).2 l hold] at hc
    exact hh l rc m body hc
  · have he : l = H.size := by omega
    subst l
    rw [Proof.alloc_cell] at hc
    simp only [AllocPol.mode, Option.some.injEq, Cell.live.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, by omega, hb⟩

/-- Fresh allocation ordering follows from actual field denotations. -/
theorem bodyOk_of_den {H : Heap} {b : Body} {ws : List Fir.Val}
    (hn : b.fields.length = b.ctor.arity) (hp : 0 < b.ctor.arity)
    (hv : Sem.Forall2 (Proof.Den H) b.fields ws) : BodyOk H.size b := by
  refine ⟨hn, hp, ?_⟩
  intro k hk
  have hfields : ∀ v, v ∈ b.fields → ∃ w, Proof.Den H v w := by
    generalize b.fields = fields at hv ⊢
    induction hv with
    | nil => simp
    | cons h hs ih =>
      intro v hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, h⟩
      · exact ih v hm
  obtain ⟨w, hw⟩ := hfields (.loc k) hk
  obtain ⟨rc, m, body, values, hc, _, _⟩ := Proof.den_loc hw
  exact Proof.cell?_some hc

theorem releaseOne_heapOk {H H' : Heap} {v : RVal} {pending pending' : List RVal}
    (hh : HeapOk H) (hop : releaseOne H v pending = some (H', pending')) : HeapOk H' := by
  cases v with
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [releaseOne, hc] at hop
    | some c =>
      cases c with
      | dead => simp [releaseOne, hc] at hop
      | live rc m b =>
        cases m with
        | static =>
          have hm := (hh l rc .static b hc).1
          cases hm
        | dyn =>
          cases rc with
          | zero => simp [releaseOne, hc] at hop
          | succ rc =>
            cases rc with
            | zero =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              rcases hop with ⟨rfl, rfl⟩
              exact heapOk_free hh (Proof.cell?_some hc)
            | succ rc =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              rcases hop with ⟨rfl, rfl⟩
              exact heapOk_set_count hh hc (by omega)
  | lit _ | ctor0 _ | erased =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    rcases hop with ⟨rfl, rfl⟩
    exact hh

theorem dropAll_heapOk (H : Heap) (pending : List RVal) {external : Nat → Nat}
    (hb : Balance H external pending) (hh : HeapOk H) :
    ∃ H', dropAll H pending = some H' ∧ Balance H' external [] ∧ HeapOk H' := by
  match hPending : pending with
  | [] => exact ⟨H, by simp [hPending, dropAll], by simpa [hPending] using hb, hh⟩
  | v :: ps =>
    have hb0 : Balance H external (v :: ps) := by simpa [hPending] using hb
    obtain ⟨H', ps', hstep, hb'⟩ := releaseOne_balance hb0
    obtain ⟨H'', hdrop, hend, hshape⟩ := dropAll_heapOk H' ps' hb' (releaseOne_heapOk hh hstep)
    refine ⟨H'', ?_, hend, hshape⟩
    rw [dropAll, hstep]
    exact hdrop
termination_by (mass H, pending.length)
decreasing_by
  have hd := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hd with hd | ⟨he, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩


end Compilatrix.Own.Rc
