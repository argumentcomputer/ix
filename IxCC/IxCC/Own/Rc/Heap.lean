import IxCC.Own.Heap

/-! Checked count-only operations on the abstract heap (`SameBodies`,
`changeCount`, `inc`, `decShared`). Final decrements of a single reference return
`none` here and are handled by the iterative field-release worklist and
exact-token semantics in `Own.Rc.Release` and `Own.Plain`. -/

set_option autoImplicit false

namespace IxCC.Own.Rc

def body? : Cell → Option Body
  | .live _ _ b => some b
  | .dead => none

/-- Equal live bodies, allowing counts to differ. This is insufficient for
safe freeing; it is the observation invariant for count-only operations. -/
def SameBodies (H H' : Heap) : Prop :=
  H.size = H'.size ∧ ∀ l, (H.cell? l).bind body? = (H'.cell? l).bind body?

def setCell (H : Heap) (l : Nat) (c : Cell) : Heap :=
  { cells := H.cells.set! l c }

/-- A checked count update. Dead/missing cells and zero dynamic counts reject.
Immediates and static cells have no counted ownership and are unchanged. -/
def changeCount (f : Nat → Option Nat) (H : Heap) : RVal → Option Heap
  | .loc l => match H.cell? l with
    | some (.live rc .dyn b) => do
      if rc == 0 then none else do
        let rc' ← f rc
        if rc' == 0 then none else some (setCell H l (.live rc' .dyn b))
    | some (.live _ .static _) => some H
    | _ => none
  | _ => some H

def inc (H : Heap) (v : RVal) (n : Nat) : Option Heap :=
  changeCount (fun rc => some (rc + n)) H v

/-- Count-only decrement. `none` at one reference requests final-release
handling by the caller; this is not a full RC decrement implementation. -/
def decShared (H : Heap) (v : RVal) : Option Heap :=
  changeCount (fun rc => if rc > 1 then some (rc - 1) else none) H v

theorem inc_dyn {H : Heap} {l rc : Nat} {b : Body}
    (hc : H.cell? l = some (.live rc .dyn b)) (hp : 0 < rc) (n : Nat) :
    inc H (.loc l) n = some (setCell H l (.live (rc + n) .dyn b)) := by
  have hrc : rc ≠ 0 := by omega
  have hn : rc + n ≠ 0 := by omega
  simp [inc, changeCount, hc, hrc, hn]

theorem decShared_dyn {H : Heap} {l rc : Nat} {b : Body}
    (hc : H.cell? l = some (.live rc .dyn b)) (hp : 1 < rc) :
    decShared H (.loc l) = some (setCell H l (.live (rc - 1) .dyn b)) := by
  have hrc : rc ≠ 0 := by omega
  have hn : rc - 1 ≠ 0 := by omega
  simp [decShared, changeCount, hc, hrc, hn, hp]

theorem SameBodies.refl (H : Heap) : SameBodies H H := ⟨rfl, fun _ => rfl⟩

theorem setCell_size (H : Heap) (l : Nat) (c : Cell) :
    (setCell H l c).size = H.size := by
  simp [setCell, Heap.size]

theorem setCell_cell (H : Heap) (l : Nat) (c : Cell) (hl : l < H.size) (k : Nat) :
    (setCell H l c).cell? k = if l = k then some c else H.cell? k := by
  simp only [setCell, Heap.cell?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  have hl' : l < H.cells.size := hl
  simp only [hl', if_true]

theorem sameBodies_set {H : Heap} {l rc rc' : Nat} {m m' : OMode} {b : Body}
    (h : H.cell? l = some (.live rc m b)) :
    SameBodies H (setCell H l (.live rc' m' b)) := by
  have hl : l < H.size := by
    have := Array.getElem?_eq_some_iff.mp h
    exact this.1
  refine ⟨(setCell_size ..).symm, fun k => ?_⟩
  rw [setCell_cell H l _ hl k]
  split
  · next he => subst k; simp [h, body?]
  · rfl

/-- Dynamic reference mass at a location. Static and dead cells contribute
zero. `Counts` is only the numeric component of the future ownership invariant;
its reference function must be derived from roots and incoming live fields. -/
def dynCount (H : Heap) (l : Nat) : Nat :=
  match H.cell? l with
  | some (.live rc .dyn _) => rc
  | _ => 0

def Counts (H : Heap) (refs : Nat → Nat) : Prop :=
  ∀ l, dynCount H l = refs l

def replaceCount (refs : Nat → Nat) (l rc : Nat) : Nat → Nat :=
  fun k => if l = k then rc else refs k

theorem counts_set {H : Heap} {refs : Nat → Nat} (h : Counts H refs)
    {l : Nat} (hl : l < H.size) (rc : Nat) (b : Body) :
    Counts (setCell H l (.live rc .dyn b)) (replaceCount refs l rc) := by
  intro k
  by_cases he : l = k
  · subst k
    simp only [dynCount, setCell_cell H l _ hl l, if_pos rfl, replaceCount]
    simp
  · simpa [dynCount, setCell_cell H l _ hl k, replaceCount, he] using h k

/-- Increment changes precisely the matching reference count, alongside the
body invariant used for denotation. Clients must account for this extra mass
by adding owned tokens, rather than treating the number as a new premise. -/
theorem inc_counts {H : Heap} {refs : Nat → Nat} (h : Counts H refs)
    {l rc : Nat} {b : Body} (hc : H.cell? l = some (.live rc .dyn b))
    (hp : 0 < rc) (n : Nat) :
    ∃ H', inc H (.loc l) n = some H' ∧
      Counts H' (replaceCount refs l (refs l + n)) ∧ SameBodies H H' := by
  refine ⟨setCell H l (.live (rc + n) .dyn b), inc_dyn hc hp n, ?_, sameBodies_set hc⟩
  have he : rc = refs l := by simpa [dynCount, hc] using h l
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  rw [← he]
  exact counts_set h hl _ _

theorem decShared_counts {H : Heap} {refs : Nat → Nat} (h : Counts H refs)
    {l rc : Nat} {b : Body} (hc : H.cell? l = some (.live rc .dyn b))
    (hp : 1 < rc) :
    ∃ H', decShared H (.loc l) = some H' ∧
      Counts H' (replaceCount refs l (refs l - 1)) ∧ SameBodies H H' := by
  refine ⟨setCell H l (.live (rc - 1) .dyn b), decShared_dyn hc hp, ?_, sameBodies_set hc⟩
  have he : rc = refs l := by simpa [dynCount, hc] using h l
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  rw [← he]
  exact counts_set h hl _ _

theorem changeCount_sameBodies {f : Nat → Option Nat} {H H' : Heap} {v : RVal}
    (h : changeCount f H v = some H') : SameBodies H H' := by
  cases v with
  | loc l =>
    simp only [changeCount] at h
    split at h
    · next rc b hc =>
      split at h
      · cases h
      · cases hf : f rc with
        | none => simp [hf] at h
        | some rc' =>
          simp only [hf, bind, Option.bind] at h
          split at h
          · cases h
          · cases h; exact sameBodies_set hc
    · cases h; exact SameBodies.refl _
    · cases h
  | lit _ => cases h; exact SameBodies.refl _
  | ctor0 _ => cases h; exact SameBodies.refl _
  | erased => cases h; exact SameBodies.refl _

/-- A count-only heap change preserves structural readback at every fuel. -/
theorem toFir_sameBodies {H H' : Heap} (h : SameBodies H H') :
    ∀ fuel v, toFir H fuel v = toFir H' fuel v := by
  intro fuel
  induction fuel with
  | zero => intro v; cases v <;> simp [toFir]
  | succ fuel ih =>
    have hlist : ∀ vs, toFirList H fuel vs = toFirList H' fuel vs := by
      intro vs
      induction vs with
      | nil => simp [toFirList]
      | cons v vs hv => simp only [toFirList, ih, hv]
    intro v
    cases v with
    | lit _ => simp [toFir]
    | ctor0 _ => simp [toFir]
    | erased => simp [toFir]
    | loc l =>
      have hb := h.2 l
      cases hc : H.cell? l <;> cases hc' : H'.cell? l <;>
        simp only [hc, hc', Option.bind_none, Option.bind_some] at hb
      · simp [toFir, hc, hc']
      · next c => cases c <;> simp_all [body?, toFir]
      · next c => cases c <;> simp_all [body?, toFir]
      · next c c' => cases c <;> cases c' <;> simp_all [body?, toFir]

theorem value_sameBodies {H H' : Heap} (h : SameBodies H H') (v : RVal) :
    H.value? v = H'.value? v := by
  simp only [Heap.value?, toFir_sameBodies h, h.1]

theorem readback_sameBodies {H H' : Heap} (h : SameBodies H H') (v : RVal) :
    H.readback v = H'.readback v := by
  simp only [Heap.readback, value_sameBodies h]

theorem inc_readback {H H' : Heap} {v : RVal} {n : Nat} (h : inc H v n = some H')
    (root : RVal) : H.readback root = H'.readback root :=
  readback_sameBodies (changeCount_sameBodies h) root

theorem decShared_readback {H H' : Heap} {v : RVal} (h : decShared H v = some H')
    (root : RVal) : H.readback root = H'.readback root :=
  readback_sameBodies (changeCount_sameBodies h) root

end IxCC.Own.Rc
