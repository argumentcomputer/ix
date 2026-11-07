import IxCC.Own.Rc.Proof.Shape

/-! No live cells remain in an ordered counted heap with no owned roots.
The older-field shape condition is essential: numerical balance alone permits
unreachable cycles. Whole-program shape propagation is a separate companion
proof; this theorem does not assume it from balance. -/

set_option autoImplicit false

namespace IxCC.Own.Rc

theorem refsIn_zero_of_absent {l : Nat} {vs : List RVal}
    (h : RVal.loc l ∉ vs) : refsIn l vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hv : v ≠ .loc l := by intro he; subst v; exact h List.mem_cons_self
    have ht : RVal.loc l ∉ vs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [refsIn, hv, ih ht]

theorem total_zero_of_entries (f : Cell → Nat) (cells : List Cell)
    (h : ∀ (i : Nat) (cell : Cell), cells[i]? = some cell → f cell = 0) : total f cells = 0 := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    simp only [total]
    rw [h 0 cell rfl]
    simp only [Nat.zero_add]
    exact ih fun i cell hc => h (i+1) cell hc

theorem heapOk_zero_no_live {H : Heap} (hh : HeapOk H)
    (hb : Balance H (fun _ => 0) []) (l rc : Nat) (mode : OMode) (body : Body)
    (hc : H.cell? l = some (.live rc mode body)) : False := by
  obtain ⟨rfl, hpos, _⟩ := hh l rc mode body hc
  have hl : l < H.size := Proof.cell?_some hc
  have higherDead : ∀ parent count m b, l < parent →
      H.cell? parent = some (.live count m b) → False := by
    intro parent count m b hlt hparent
    exact heapOk_zero_no_live hh hb parent count m b hparent
  have hedges : edgeCount H l = 0 := by
    apply total_zero_of_entries
    intro parent cell hget
    have hparent : H.cell? parent = some cell := by simpa [Heap.cell?] using hget
    cases cell with
    | dead => rfl
    | live count m b =>
      have hshape := (hh parent count m b hparent).2.2
      change refsIn l b.fields = 0
      apply refsIn_zero_of_absent
      intro hfield
      exact higherDead parent count m b (hshape.2.2 l hfield) hparent
  have hcount := hb l
  simp only [dynCount, hc, refsIn, hedges, Nat.zero_add] at hcount
  omega
termination_by H.size - l
decreasing_by
  have hp : parent < H.size := Proof.cell?_some hparent
  omega

theorem heapOk_zero_all_dead {H : Heap} (hh : HeapOk H)
    (hb : Balance H (fun _ => 0) []) :
    ∀ l, l < H.size → H.cell? l = some .dead := by
  intro l hl
  cases hc : H.cell? l with
  | none =>
    have hl' : l < H.cells.size := hl
    have hn : H.cells[l]? ≠ none := by simp [hl']
    exact False.elim (hn hc)
  | some cell =>
    cases cell with
    | dead => rfl
    | live rc mode body => exact False.elim (heapOk_zero_no_live hh hb l rc mode body hc)

theorem dropAll_reclaims {H : Heap} {roots : List RVal}
    (hh : HeapOk H) (hb : Balance H (fun _ => 0) roots) :
    ∃ H', dropAll H roots = some H' ∧ ∀ l, l < H'.size → H'.cell? l = some .dead := by
  obtain ⟨H', hdrop, hb', hh'⟩ := dropAll_heapOk H roots hb hh
  exact ⟨H', hdrop, heapOk_zero_all_dead hh' hb'⟩


end IxCC.Own.Rc
