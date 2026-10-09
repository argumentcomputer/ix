import Compilatrix.Own.Rc.Proof.ReleaseValue
import Compilatrix.Own.Proof.Heap

/-! Allocation and duplication transfer real root mass to/from heap edges.
These are operation invariants for the plain producer proof, not assumptions
standing in for that proof. This file is independent of the frozen runner. -/

set_option autoImplicit false

namespace Compilatrix.Own.Rc

theorem total_append (f : Cell → Nat) (xs ys : List Cell) :
    total f (xs ++ ys) = total f xs + total f ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

theorem edgeCount_alloc (H : Heap) (b : Body) (k : Nat) :
    edgeCount (H.alloc .rc b).2 k = edgeCount H k + refsIn k b.fields := by
  simp [edgeCount, Heap.alloc, total_append, total, fieldRefs]

theorem dynCount_alloc (H : Heap) (b : Body) (k : Nat) :
    dynCount (H.alloc .rc b).2 k = if k = H.size then 1 else dynCount H k := by
  simp only [dynCount, Heap.alloc, Heap.cell?, Array.getElem?_push]
  by_cases hk : k = H.cells.size
  · simp [hk, Heap.size, AllocPol.mode]
  · simp [hk, Heap.size]

theorem dynCount_fresh (H : Heap) : dynCount H H.size = 0 := by
  simp [dynCount, Heap.cell?, Heap.size]

/-- Allocation consumes the field roots and installs exactly those same
references as outgoing edges, adding one owned root for the fresh cell. -/
theorem balance_alloc {H : Heap} {external : Nat → Nat} {b : Body}
    (hb : Balance H external b.fields) :
    Balance (H.alloc .rc b).2 external [(H.alloc .rc b).1] := by
  intro k
  have h := hb k
  by_cases hk : k = H.size
  · subst k
    have hz := dynCount_fresh H
    have hn : dynCount (H.alloc .rc b).2 H.size = 1 :=
      (dynCount_alloc H b H.size).trans (ite_eq_left rfl)
    have hr : refsIn H.size [(H.alloc .rc b).1] = 1 := by
      simp [Heap.alloc, refsIn, Heap.size]
    rw [hn, hr, edgeCount_alloc]
    omega
  · have hn : dynCount (H.alloc .rc b).2 k = dynCount H k :=
      (dynCount_alloc H b k).trans (ite_eq_right hk)
    have hr : refsIn k [(H.alloc .rc b).1] = 0 := by
      simp only [Heap.alloc, refsIn]
      rw [Nat.add_zero]
      exact ite_eq_right (fun he => hk (RVal.loc.inj he).symm)
    rw [hn, hr, edgeCount_alloc]
    omega

/-- Existing denotation facts for allocation already cover the counted
policy. Combine them with derived exact root/edge accounting and preserve
every pre-existing denotation through the fresh extension. -/
theorem alloc_sound {H : Heap} {external : Nat → Nat} {b : Body} {ws : List Fir.Val}
    (hb : Balance H external b.fields)
    (hv : Sem.Forall2 (Proof.Den H) b.fields ws) :
    let allocated := H.alloc .rc b
    Balance allocated.2 external [allocated.1] ∧
      Proof.Den allocated.2 allocated.1 (.ctor b.ctor ws) ∧
      ∀ v w, Proof.Den H v w → Proof.Den allocated.2 v w := by
  refine ⟨balance_alloc hb, ?_, fun _ _ h => Proof.Den.ext (Proof.Ext.alloc .rc H b) h⟩
  exact Proof.den_alloc .rc H b.ctor hv

theorem balance_inc_cell {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {l rc : Nat} {b : Body} (hc : H.cell? l = some (.live rc .dyn b))
    (hb : Balance H external pending) :
    Balance (setCell H l (.live (rc + 1) .dyn b)) external (.loc l :: pending) := by
  have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
  intro k
  have h := hb k
  rw [edgeCount_set_count hc k]
  by_cases hk : l = k
  · subst k
    have hn : dynCount H l = rc := by simp [dynCount, hc]
    have hn' : dynCount (setCell H l (.live (rc + 1) .dyn b)) l = rc + 1 := by
      simp [dynCount, setCell_cell H l _ hl l]
    simp [refsIn]
    rw [hn']
    omega
  · have hn : dynCount (setCell H l (.live (rc + 1) .dyn b)) k = dynCount H k := by
      simp [dynCount, setCell_cell H l _ hl k, hk]
    have hv : RVal.loc l ≠ RVal.loc k := by intro he; cases he; exact hk rfl
    simp only [refsIn, if_neg hv]
    rw [hn]
    omega

def CanDup (H : Heap) : RVal → Prop
  | .loc l => 0 < dynCount H l
  | _ => True

/-- A pending owned token makes its value duplicable in the plain fragment. -/
theorem canDup_owned {H : Heap} {external : Nat → Nat} {pending : List RVal} {v : RVal}
    (hb : Balance H external (v :: pending)) : CanDup H v := by
  cases v with
  | loc l =>
    have h := hb l
    simp [refsIn] at h
    simp only [CanDup]
    omega
  | lit _ | ctor0 _ | erased => trivial

/-- A projected field has a live incoming edge. Its duplication permission
is derived from that concrete field and exact counts, not assumed separately. -/
theorem canDup_field {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {parent rc : Nat} {m : OMode} {b : Body} {v : RVal}
    (hb : Balance H external pending) (hc : H.cell? parent = some (.live rc m b))
    (hv : v ∈ b.fields) : CanDup H v := by
  cases v with
  | loc l =>
    have hp := refsIn_pos hv
    have hm : Cell.live rc m b ∈ H.cells.toList :=
      List.mem_of_getElem? (by simpa [Heap.cell?] using hc)
    have he := total_mem_le (fieldRefs l) hm
    change refsIn l b.fields ≤ edgeCount H l at he
    have h := hb l
    simp only [CanDup]
    omega
  | lit _ | ctor0 _ | erased => trivial

/-- Add one owned root by incrementing an actually live counted cell (or an
immediate). All existing full values are preserved. Static references are
outside this first numeric ownership fragment. -/
theorem inc_root {H : Heap} {external : Nat → Nat} {pending : List RVal} {v : RVal}
    (hb : Balance H external pending) (hd : CanDup H v) :
    ∃ H', inc H v 1 = some H' ∧ Balance H' external (v :: pending) ∧
      ∀ root, H.value? root = H'.value? root := by
  cases v with
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [CanDup, dynCount, hc] at hd
    | some c =>
      cases c with
      | dead => simp [CanDup, dynCount, hc] at hd
      | live rc m b =>
        cases m with
        | static => simp [CanDup, dynCount, hc] at hd
        | dyn =>
          have hp : 0 < rc := by simpa [CanDup, dynCount, hc] using hd
          refine ⟨_, inc_dyn hc hp 1, balance_inc_cell hc hb, ?_⟩
          exact value_sameBodies (sameBodies_set hc)
  | lit l =>
    refine ⟨H, rfl, ?_, fun _ => rfl⟩
    simpa [Balance, refsIn] using hb
  | ctor0 c =>
    refine ⟨H, rfl, ?_, fun _ => rfl⟩
    simpa [Balance, refsIn] using hb
  | erased =>
    refine ⟨H, rfl, ?_, fun _ => rfl⟩
    simpa [Balance, refsIn] using hb

theorem dup_owned {H : Heap} {external : Nat → Nat} {pending : List RVal} {v : RVal}
    (hb : Balance H external (v :: pending)) :
    ∃ H', inc H v 1 = some H' ∧ Balance H' external (v :: v :: pending) ∧
      ∀ root, H.value? root = H'.value? root :=
  inc_root hb (canDup_owned hb)

theorem dup_projection {H : Heap} {external : Nat → Nat} {pending : List RVal}
    {parent rc : Nat} {m : OMode} {b : Body} {v : RVal}
    (hb : Balance H external pending) (hc : H.cell? parent = some (.live rc m b))
    (hv : v ∈ b.fields) :
    ∃ H', inc H v 1 = some H' ∧ Balance H' external (v :: pending) ∧
      ∀ root, H.value? root = H'.value? root :=
  inc_root hb (canDup_field hb hc hv)


end Compilatrix.Own.Rc
