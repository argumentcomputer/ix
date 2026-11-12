import IxCC.Own.Rc.Unique
import IxCC.Own.Rc.Proof.Allocation
import IxCC.Own.Rc.Proof.Shape

set_option autoImplicit false

namespace IxCC.Own.Rc

/-! ## Reuse of a unique cell, abstractly

A cell whose one reference is the caller's token (`uniqueOf`) is given up and a fresh location is
appended with a new body whose tokens the caller holds: a release of the cell alone followed by an
allocation, with no free-list round trip (`reuseCell`). The abstract heap stays append-only, so
exact counts (`reuseCell_balance`), order (`reuseCell_heapOk`) and the readback of every other
value (`reuseCell_readback`) are kept. The tokens are accounted by one condition: the old cell's
fields and the caller's other tokens are, location by location, the new cell's fields and the
tokens the caller keeps (literals and other immediates are free). Physically the fresh location
takes the old cell's storage (`Rt.Rc.Gen.inPlace_ready`). Nothing in the pipeline emits a reuse
yet. -/

/-- Reuse in place, abstractly: the unique dynamic cell `l` dies and `b'` is appended, with one
reference. Any other cell (shared, static, dead or missing) is not reused. -/
def reuseCell (H : Heap) (l : Nat) (b' : Body) : Option (RVal × Heap) :=
  match H.cell? l with
  | some (.live 1 .dyn _) => some (Heap.alloc .rc (setCell H l .dead) b')
  | _ => none

/-- The heap after reusing `l` for `b'`. -/
def reusedHeap (H : Heap) (l : Nat) (b' : Body) : Heap := (Heap.alloc .rc (setCell H l .dead) b').2

theorem reuseCell_some {H : Heap} {l : Nat} {b b' : Body}
    (hc : H.cell? l = some (.live 1 .dyn b)) :
    reuseCell H l b' = some (.loc H.size, reusedHeap H l b') := by
  simp only [reuseCell, hc, reusedHeap]
  rw [show H.size = (setCell H l .dead).size from (setCell_size H l .dead).symm]
  rfl

theorem reuseCell_of_some {H H' : Heap} {l : Nat} {b b' : Body} {r : RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hr : reuseCell H l b' = some (r, H')) :
    r = .loc H.size ∧ H' = reusedHeap H l b' := by
  rw [reuseCell_some hc] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  exact ⟨hr.1.symm, hr.2.symm⟩

theorem reusedHeap_size (H : Heap) (l : Nat) (b' : Body) :
    (reusedHeap H l b').size = H.size + 1 := by
  simp only [reusedHeap, Proof.alloc_size, setCell_size]

theorem reusedHeap_new (H : Heap) (l : Nat) (b' : Body) :
    (reusedHeap H l b').cell? H.size = some (.live 1 .dyn b') := by
  have := Proof.alloc_cell .rc (setCell H l .dead) b'
  rw [setCell_size] at this
  simpa [reusedHeap, AllocPol.mode] using this

/-- Every cell of the reused heap: the new one at the fresh location, the reused one dead, the
others as before. -/
theorem reusedHeap_cell {H : Heap} {l : Nat} (hl : l < H.size) (b' : Body) (k : Nat) :
    (reusedHeap H l b').cell? k =
      if k = H.size then some (.live 1 .dyn b') else if l = k then some .dead else H.cell? k := by
  simp only [reusedHeap, Heap.alloc, Heap.cell?, Array.getElem?_push]
  have hs : (setCell H l .dead).cells.size = H.size := setCell_size H l .dead
  rw [hs]
  by_cases hk : k = H.size
  · simp [hk, AllocPol.mode]
  · rw [ite_eq_right hk, ite_eq_right hk]
    exact setCell_cell H l .dead hl k

/-! ## What uniqueness and balance give -/

/-- A live cell's fields are counted among the edges. -/
theorem refsIn_fields_le {H : Heap} {k rc : Nat} {m : OMode} {b : Body}
    (hc : H.cell? k = some (.live rc m b)) (j : Nat) : refsIn j b.fields ≤ edgeCount H j := by
  have hm : Cell.live rc m b ∈ H.cells.toList :=
    List.mem_of_getElem? (by simpa [Heap.cell?] using hc)
  exact total_mem_le (fieldRefs j) hm

theorem lt_size_of_dynCount {H : Heap} {k : Nat} (h : 0 < dynCount H k) : k < H.size := by
  cases hc : H.cell? k with
  | none => simp [dynCount, hc] at h
  | some c => exact Proof.cell?_some hc

theorem refsIn_eq_zero {k : Nat} {vs : List RVal} (h : refsIn k vs = 0) : RVal.loc k ∉ vs := by
  intro hm
  have := refsIn_pos hm
  omega

/-- With the caller's token for the unique cell `l` among balanced tokens: nothing else refers to
`l` (no external owner, no other token, no field anywhere, its own fields included), and nothing
refers to the next fresh location. -/
theorem reuse_exclusive {H : Heap} {external : Nat → Nat} {l : Nat} {b : Body} {rest : List RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest)) :
    external l = 0 ∧ refsIn l rest = 0 ∧ edgeCount H l = 0 ∧ refsIn l b.fields = 0 ∧
      refsIn H.size rest = 0 ∧ edgeCount H H.size = 0 ∧ refsIn H.size b.fields = 0 := by
  obtain ⟨h1, h2, h3⟩ := uniqueOf_exclusive hb (uniqueOf_loc.mpr ⟨b, hc⟩)
  have h4 := refsIn_fields_le hc l
  have hs := hb H.size
  rw [dynCount_fresh] at hs
  simp only [refsIn] at hs
  have h5 := refsIn_fields_le hc H.size
  refine ⟨h1, h2, h3, by omega, by omega, by omega, by omega⟩

/-- The new body and the kept tokens refer to neither the reused cell nor the fresh location. -/
theorem reuse_mass_avoid {H : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest kept : List RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest))
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept)) :
    refsIn l b'.fields = 0 ∧ refsIn l kept = 0 ∧ refsIn H.size b'.fields = 0 ∧
      refsIn H.size kept = 0 := by
  obtain ⟨_, h2, _, h4, h5, _, h7⟩ := reuse_exclusive hc hb
  have ml := hmass l
  have ms := hmass H.size
  rw [refsIn_append, refsIn_append] at ml ms
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Every location the new body or a kept token names is a live cell of `H` before the reuse. -/
theorem reuse_mass_live {H : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest kept : List RVal}
    (hb : Balance H external (.loc l :: rest)) (hc : H.cell? l = some (.live 1 .dyn b))
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept))
    {k : Nat} (hk : 0 < refsIn k (b'.fields ++ kept)) : 0 < dynCount H k := by
  have hm := hmass k
  rw [refsIn_append] at hm
  have he := refsIn_fields_le hc k
  have h := hb k
  simp only [refsIn] at h
  omega

/-! ## The three abstract facts -/

/-- Exact counts are kept: the old cell's field tokens come back to the caller, the new cell's are
taken from the caller (`hmass`); the fresh location has one reference, the caller's. -/
theorem reuseCell_balance {H : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest kept : List RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest))
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept)) :
    ∃ H', reuseCell H l b' = some (.loc H.size, H') ∧
      Balance H' external (.loc H.size :: kept) := by
  refine ⟨reusedHeap H l b', reuseCell_some hc, ?_⟩
  have hfree := balance_free hc hb
  have hmoved : Balance (setCell H l .dead) external (b'.fields ++ kept) := by
    intro k
    rw [← hmass k]
    exact hfree k
  intro k
  have ha := hmoved k
  have hs := setCell_size H l .dead
  have hd := dynCount_alloc (setCell H l .dead) b' k
  have he := edgeCount_alloc (setCell H l .dead) b' k
  rw [hs] at hd
  show dynCount (Heap.alloc .rc (setCell H l .dead) b').2 k = external k +
    refsIn k (.loc H.size :: kept) + edgeCount (Heap.alloc .rc (setCell H l .dead) b').2 k
  rw [hd, he]
  rw [refsIn_append] at ha
  by_cases hk : k = H.size
  · subst k
    have hz := dynCount_fresh (setCell H l .dead)
    rw [hs] at hz
    rw [hz] at ha
    have h1 : refsIn H.size (RVal.loc H.size :: kept) = 1 + refsIn H.size kept := by simp [refsIn]
    rw [h1, ite_eq_left rfl]
    omega
  · have hv : RVal.loc H.size ≠ RVal.loc k := by intro e; cases e; exact hk rfl
    have h1 : refsIn k (RVal.loc H.size :: kept) = refsIn k kept := by simp [refsIn, hv]
    rw [h1, ite_eq_right hk]
    omega

/-- Order is kept: the new cell is the newest, with a valid body whose fields name older cells. -/
theorem reuseCell_heapOk {H H' : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest kept : List RVal} {r : RVal}
    (hok : HeapOk H) (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: rest))
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept))
    (harity : b'.fields.length = b'.ctor.arity) (hpos : 0 < b'.ctor.arity)
    (hr : reuseCell H l b' = some (r, H')) : HeapOk H' := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  have hl : l < H.size := Proof.cell?_some hc
  have hfree := heapOk_free hok hl
  have hbody : BodyOk (setCell H l .dead).size b' := by
    refine ⟨harity, hpos, fun k hk => ?_⟩
    rw [setCell_size]
    have hp := refsIn_pos hk
    have hd := reuse_mass_live hb hc hmass (k := k) (by rw [refsIn_append]; omega)
    exact lt_size_of_dynCount hd
  exact heapOk_alloc hfree hbody

/-- Appending a cell keeps every value's readback when no live cell names the fresh location and
the value is not it. -/
theorem toFir_alloc {H : Heap} (pol : AllocPol) (b' : Body) (he : edgeCount H H.size = 0) :
    ∀ fuel v, v ≠ .loc H.size → toFir (H.alloc pol b').2 fuel v = toFir H fuel v := by
  intro fuel
  induction fuel with
  | zero => intro v _; cases v <;> simp [toFir]
  | succ fuel ih =>
    have hlist : ∀ vs, RVal.loc H.size ∉ vs →
        toFirList (H.alloc pol b').2 fuel vs = toFirList H fuel vs := by
      intro vs hn
      induction vs with
      | nil => simp [toFirList]
      | cons v vs ihvs =>
        have hv : v ≠ .loc H.size := by intro h; subst v; exact hn (by simp)
        have hvs : RVal.loc H.size ∉ vs := by intro h; exact hn (by simp [h])
        simp only [toFirList, ih v hv, ihvs hvs]
    intro v hv
    cases v with
    | lit _ => simp [toFir]
    | ctor0 _ => simp [toFir]
    | erased => simp [toFir]
    | loc k =>
      have hk : k ≠ H.size := by intro h; subst k; exact hv rfl
      have hcell : (H.alloc pol b').2.cell? k = H.cell? k := by
        simp only [Heap.alloc, Heap.cell?, Array.getElem?_push]
        have : k ≠ H.cells.size := hk
        simp [this]
      simp only [toFir, hcell]
      cases hc : H.cell? k with
      | none => simp
      | some c =>
        cases c with
        | dead => simp
        | live rc m bk =>
          simp only [hlist bk.fields (fields_avoid he hc)]

/-- With the order invariant, a location's readback does not depend on fuel beyond its depth. -/
theorem toFir_stable {H : Heap} (hok : HeapOk H) :
    ∀ k f, k < f → toFir H f (.loc k) = toFir H (k + 1) (.loc k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [toFir]
    cases hc : H.cell? k with
    | none => simp
    | some c =>
      cases c with
      | dead => simp
      | live rc m bk =>
        have hbody := (hok k rc m bk hc).2.2
        have hlist : ∀ vs : List RVal, (∀ j, RVal.loc j ∈ vs → j < k) →
            toFirList H f' vs = toFirList H k vs := by
          intro vs hvs
          induction vs with
          | nil => simp [toFirList]
          | cons v vs ihvs =>
            have hrest : ∀ j, RVal.loc j ∈ vs → j < k := fun j hj => hvs j (by simp [hj])
            have hv : toFir H f' v = toFir H k v := by
              cases v with
              | lit _ => simp [toFir]
              | ctor0 _ => simp [toFir]
              | erased => simp [toFir]
              | loc j =>
                have hj := hvs j (by simp)
                rw [ih j hj f' (by omega), ih j hj k (by omega)]
            simp only [toFirList, hv, ihvs hrest]
        simp only [hlist bk.fields hbody.2.2]

theorem toFirList_mapM (H : Heap) (fuel : Nat) :
    ∀ vs : List RVal, toFirList H fuel vs = vs.mapM (toFir H fuel)
  | [] => by simp [toFirList]
  | v :: vs => by
    simp only [toFirList, List.mapM_cons, toFirList_mapM H fuel vs]
    cases toFir H fuel v <;> cases vs.mapM (toFir H fuel) <;> rfl

/-- Readback is kept: every token the caller held and every old field reads back as before, and
the fresh location reads back as the new constructor over the values its fields had. -/
theorem reuseCell_readback {H H' : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest kept : List RVal} {r : RVal}
    (hok : HeapOk H) (hc : H.cell? l = some (.live 1 .dyn b))
    (hb : Balance H external (.loc l :: rest))
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept))
    (hr : reuseCell H l b' = some (r, H')) :
    (∀ u ∈ rest ++ b.fields, H'.value? u = H.value? u) ∧
      H'.value? r = (b'.fields.mapM H.value?).map (Fir.Val.ctor b'.ctor) := by
  obtain ⟨rfl, rfl⟩ := reuseCell_of_some hc hr
  obtain ⟨_, h2, h3, h4, h5, h6, h7⟩ := reuse_exclusive hc hb
  obtain ⟨a1, _, a3, _⟩ := reuse_mass_avoid hc hb hmass
  have hl : l < H.size := Proof.cell?_some hc
  have hs := setCell_size H l .dead
  -- no live cell of the released heap names the fresh location
  have he1 : edgeCount (setCell H l .dead) (setCell H l .dead).size = 0 := by
    have := edgeCount_free hc H.size
    rw [hs]
    omega
  -- a value naming neither `l` nor the fresh location reads back the same at every fuel
  have hsame : ∀ fuel v, v ≠ .loc l → v ≠ .loc H.size →
      toFir (reusedHeap H l b') fuel v = toFir H fuel v := by
    intro fuel v hvl hvs
    rw [reusedHeap, toFir_alloc .rc b' he1 fuel v (by rw [hs]; exact hvs)]
    exact (toFir_free hl h3 fuel v hvl).symm
  have hsize := reusedHeap_size H l b'
  refine ⟨fun u hu => ?_, ?_⟩
  · have hmem : u ∈ rest ∨ u ∈ b.fields := by simpa using hu
    have hvl : u ≠ .loc l := by
      intro e; subst u
      rcases hmem with hm | hm
      · exact refsIn_eq_zero h2 hm
      · exact refsIn_eq_zero h4 hm
    have hvs : u ≠ .loc H.size := by
      intro e; subst u
      rcases hmem with hm | hm
      · exact refsIn_eq_zero h5 hm
      · exact refsIn_eq_zero h7 hm
    unfold Heap.value?
    rw [hsize, hsame _ u hvl hvs]
    cases u with
    | lit _ => simp [toFir]
    | ctor0 _ => simp [toFir]
    | erased => simp [toFir]
    | loc k =>
      have hk : k < H.size := by
        rcases hmem with hm | hm
        · have h := hb k
          have hp := refsIn_pos hm
          simp only [refsIn] at h
          exact lt_size_of_dynCount (by omega)
        · exact Nat.lt_trans ((hok l 1 .dyn b hc).2.2.2.2 k hm) hl
      rw [toFir_stable hok k (H.size + 1 + 1) (by omega), toFir_stable hok k (H.size + 1) (by omega)]
  · simp only [Heap.value?, hsize, toFir, reusedHeap_new]
    rw [toFirList_mapM]
    have hfields : ∀ vs : List RVal, refsIn l vs = 0 → refsIn H.size vs = 0 →
        vs.mapM (toFir (reusedHeap H l b') (H.size + 1)) = vs.mapM (toFir H (H.size + 1)) := by
      intro vs
      induction vs with
      | nil => simp
      | cons v vs ih =>
        intro hl0 hs0
        simp only [refsIn] at hl0 hs0
        have hvl : v ≠ .loc l := by intro e; subst v; simp at hl0
        have hvs : v ≠ .loc H.size := by intro e; subst v; simp at hs0
        simp only [List.mapM_cons, hsame _ v hvl hvs, ih (by omega) (by omega)]
    rw [hfields b'.fields a1 a3]
    rfl

end IxCC.Own.Rc
