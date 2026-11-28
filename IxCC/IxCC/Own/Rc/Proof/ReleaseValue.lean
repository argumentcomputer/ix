import IxCC.Own.Rc.Release

set_option autoImplicit false

namespace IxCC.Own.Rc

/-! ## Surviving roots retain their complete structural value -/

theorem total_mem_le (f : Cell → Nat) {cs : List Cell} {c : Cell} (h : c ∈ cs) :
    f c ≤ total f cs := by
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [total]
    · have := ih h; simp only [total]; omega

theorem refsIn_pos {l : Nat} {vs : List RVal} (h : RVal.loc l ∈ vs) :
    0 < refsIn l vs := by
  induction vs with
  | nil => simp at h
  | cons v vs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst v; simp [refsIn]; omega
    · have := ih h; simp only [refsIn]; omega

/-- With no incoming references, no live body's fields can contain the
location. This conclusion is derived from the actual finite heap graph. -/
theorem fields_avoid {H : Heap} {l k rc : Nat} {m : OMode} {b : Body}
    (he : edgeCount H l = 0) (hc : H.cell? k = some (.live rc m b)) :
    RVal.loc l ∉ b.fields := by
  have hm : Cell.live rc m b ∈ H.cells.toList :=
    List.mem_of_getElem? (by simpa [Heap.cell?] using hc)
  have hle := total_mem_le (fieldRefs l) hm
  change refsIn l b.fields ≤ edgeCount H l at hle
  intro h
  have := refsIn_pos h
  omega

/-- Freeing a location with no incoming edges preserves every other value's
readback at every fuel. No acyclicity or pre-assumed denotation preservation
is needed: each recursive read follows an actual live body's fields. -/
theorem toFir_free {H : Heap} {l : Nat} (hl : l < H.size)
    (he : edgeCount H l = 0) :
    ∀ fuel v, v ≠ .loc l → toFir H fuel v = toFir (setCell H l .dead) fuel v := by
  intro fuel
  induction fuel with
  | zero => intro v _; cases v <;> simp [toFir]
  | succ fuel ih =>
    have hlist : ∀ vs, RVal.loc l ∉ vs →
        toFirList H fuel vs = toFirList (setCell H l .dead) fuel vs := by
      intro vs hn
      induction vs with
      | nil => simp [toFirList]
      | cons v vs ihvs =>
        have hv : v ≠ .loc l := by intro h; subst v; exact hn (by simp)
        have hvs : RVal.loc l ∉ vs := by intro h; exact hn (by simp [h])
        simp only [toFirList, ih v hv, ihvs hvs]
    intro v hv
    cases v with
    | lit _ => simp [toFir]
    | ctor0 _ => simp [toFir]
    | erased => simp [toFir]
    | loc k =>
      have hk : l ≠ k := by intro h; subst k; exact hv rfl
      simp only [toFir, setCell_cell H l .dead hl k, if_neg hk]
      cases hc : H.cell? k with
      | none => simp
      | some c =>
        cases c with
        | dead => simp
        | live rc m b =>
          simp only [hlist b.fields (fields_avoid he hc)]

def ExternalRoot (external : Nat → Nat) : RVal → Prop
  | .loc l => 0 < external l
  | _ => True

theorem free_external_ne {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l : Nat} {b : Body} (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: pending)) {root : RVal}
    (hr : ExternalRoot external root) : root ≠ .loc l ∧ edgeCount H l = 0 := by
  have h := hb l
  simp [dynCount, hc, refsIn] at h
  have hz : external l = 0 := by omega
  refine ⟨?_, by omega⟩
  intro hroot
  subst root
  simp [ExternalRoot, hz] at hr

theorem free_value {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l : Nat} {b : Body} (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: pending)) {root : RVal}
    (hr : ExternalRoot external root) :
    H.value? root = (setCell H l .dead).value? root := by
  obtain ⟨hne, he⟩ := free_external_ne hc hb hr
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  simp only [Heap.value?, setCell_size,
    toFir_free hl he (H.size + 1) root hne]

/-- Every accepted release step preserves all roots represented in the
external ownership multiset. Final-free preservation follows from `Balance`,
not a simulation premise supplied by the caller. -/
theorem releaseOne_value {H H' : Heap} {external : Nat → Nat}
    {v root : RVal} {pending pending' : List RVal}
    (hb : Balance H external (v :: pending)) (hr : ExternalRoot external root)
    (hop : releaseOne H v pending = some (H', pending')) :
    H.value? root = H'.value? root := by
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
          simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          rfl
        | dyn =>
          cases rc with
          | zero => simp [releaseOne, hc] at hop
          | succ rc =>
            cases rc with
            | zero =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              exact free_value hc hb hr
            | succ rc =>
              simp only [releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              exact value_sameBodies (sameBodies_set hc) root
  | lit l | ctor0 l =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rfl
  | erased =>
    simp only [releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    rfl

/-- Complete release succeeds, preserves exact counts and preserves every
surviving external root's full observation. -/
theorem dropAll_value (H : Heap) (pending : List RVal) {external : Nat → Nat}
    (hb : Balance H external pending) :
    ∃ H', dropAll H pending = some H' ∧ Balance H' external [] ∧
      ∀ root, ExternalRoot external root → H.value? root = H'.value? root := by
  match hPending : pending with
  | [] =>
    exact ⟨H, by simp [hPending, dropAll], by simpa [hPending] using hb, fun _ _ => rfl⟩
  | v :: ps =>
    have hb0 : Balance H external (v :: ps) := by simpa [hPending] using hb
    obtain ⟨H', ps', hstep, hb'⟩ := releaseOne_balance hb0
    obtain ⟨H'', hdrop, hend, hread⟩ := dropAll_value H' ps' hb'
    refine ⟨H'', ?_, hend, fun root hr => ?_⟩
    · rw [dropAll, hstep]; exact hdrop
    · exact (releaseOne_value hb0 hr hstep).trans (hread root hr)
termination_by (mass H, pending.length)
decreasing_by
  have hd := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hd with hd | ⟨he, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

theorem free_readback {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l : Nat} {b : Body} (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: pending)) {root : RVal}
    (hr : ExternalRoot external root) :
    H.readback root = (setCell H l .dead).readback root := by
  simp only [Heap.readback, free_value hc hb hr]

theorem releaseOne_readback {H H' : Heap} {external : Nat → Nat}
    {v root : RVal} {pending pending' : List RVal}
    (hb : Balance H external (v :: pending)) (hr : ExternalRoot external root)
    (hop : releaseOne H v pending = some (H', pending')) :
    H.readback root = H'.readback root := by
  simp only [Heap.readback, releaseOne_value hb hr hop]

theorem dropAll_sound (H : Heap) (pending : List RVal) {external : Nat → Nat}
    (hb : Balance H external pending) :
    ∃ H', dropAll H pending = some H' ∧ Balance H' external [] ∧
      ∀ root, ExternalRoot external root → H.readback root = H'.readback root := by
  obtain ⟨H', hd, hb', hv⟩ := dropAll_value H pending hb
  exact ⟨H', hd, hb', fun root hr => by simp only [Heap.readback, hv root hr]⟩


end IxCC.Own.Rc
