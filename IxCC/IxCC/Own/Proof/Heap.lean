import IxCC.Own.Heap
import IxCC.Src.Proof.NatMap
import IxCC.Sem.Forall2

/-! # The immortal heap: extension, denotation, the invariant

What the Fir → Own refinement (`Own.Proof.Immortal`) keeps of the heap:

* `Ext H H'`: `H'` extends `H` (allocation only appends; nothing is freed
  under the immortal policy);
* `Den H v w`: Own value `v` denotes Fir value `w` in `H`
  (`H.value? v = some w`), stable under extension (`Den.ext`);
* `Heap.immortalOk`: every cell live, static, saturated, its fields
  immediates or older cells; an immortal allocation of denoting fields keeps
  it (`immortalOk_alloc`). -/

set_option autoImplicit false

namespace IxCC.Own.Proof

open IxCC.Src (NatMap)
open IxCC.Sem (Forall2)

/-! ## Maps -/

theorem get?_map {α β : Type} (f : α → β) : ∀ (m : NatMap α) (k : Nat), (m.map f).get? k = (m.get? k).map f
  | .leaf, _ => rfl
  | .node v z o, k => by
    simp only [NatMap.map, NatMap.get?]
    split
    · rfl
    · split
      · exact get?_map f z (k / 2)
      · exact get?_map f o (k / 2)

/-! ## Extension -/

/-- `H'` extends `H`: the old cells are unchanged. -/
def Ext (H H' : Heap) : Prop := H.size ≤ H'.size ∧ ∀ ℓ, ℓ < H.size → H'.cell? ℓ = H.cell? ℓ

theorem Ext.refl (H : Heap) : Ext H H := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {H₁ H₂ H₃ : Heap} (h₁ : Ext H₁ H₂) (h₂ : Ext H₂ H₃) : Ext H₁ H₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun ℓ hℓ => (h₂.2 ℓ (Nat.lt_of_lt_of_le hℓ h₁.1)).trans (h₁.2 ℓ hℓ)⟩

theorem cell?_some {H : Heap} {ℓ : Nat} {c : Cell} (h : H.cell? ℓ = some c) : ℓ < H.size := by
  simp only [Heap.cell?] at h
  rcases Nat.lt_or_ge ℓ H.size with hn | hn
  · exact hn
  rw [Array.getElem?_eq_none (by simpa [Heap.size] using hn)] at h
  cases h

/-- An allocation extends the heap. -/
theorem Ext.alloc (pol : AllocPol) (H : Heap) (b : Body) : Ext H (H.alloc pol b).2 := by
  refine ⟨by simp [Heap.alloc, Heap.size], fun ℓ hℓ => ?_⟩
  simp only [Heap.alloc, Heap.cell?]
  rw [Array.getElem?_push]
  have : ℓ ≠ H.cells.size := by simp only [Heap.size] at hℓ; omega
  simp [this]

theorem alloc_cell (pol : AllocPol) (H : Heap) (b : Body) :
    (H.alloc pol b).2.cell? H.size = some (.live 1 pol.mode b) := by
  simp [Heap.alloc, Heap.cell?, Heap.size]

theorem alloc_size (pol : AllocPol) (H : Heap) (b : Body) : (H.alloc pol b).2.size = H.size + 1 := by
  simp [Heap.alloc, Heap.size]

theorem alloc_fst (pol : AllocPol) (H : Heap) (b : Body) : (H.alloc pol b).1 = .loc H.size := rfl

/-! ## Denotation -/

mutual

theorem toFir_ext {H H' : Heap} (hx : Ext H H') :
    ∀ {fuel fuel' : Nat} {v : RVal} {w : Fir.Val}, fuel ≤ fuel' → toFir H fuel v = some w →
      toFir H' fuel' v = some w
  | _, _, .lit _, _, _, h => by simpa [toFir] using h
  | _, _, .ctor0 _, _, _, h => by simpa [toFir] using h
  | _, _, .erased, _, _, h => by simpa [toFir] using h
  | 0, _, .loc _, _, _, h => by simp [toFir] at h
  | fuel + 1, fuel', .loc ℓ, w, hle, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [toFir] at h ⊢
    split at h
    · next r m b hc =>
      rw [hx.2 ℓ (cell?_some hc), hc]
      cases hl : toFirList H fuel b.fields with
      | none => rw [hl] at h; cases h
      | some ws =>
        rw [hl] at h
        simp only [toFirList_ext hx (fuel := fuel) (fuel' := f) (by omega) hl]
        exact h
    · cases h

theorem toFirList_ext {H H' : Heap} (hx : Ext H H') :
    ∀ {fuel fuel' : Nat} {vs : List RVal} {ws : List Fir.Val}, fuel ≤ fuel' →
      toFirList H fuel vs = some ws → toFirList H' fuel' vs = some ws
  | _, _, [], _, _, h => by simpa [toFirList] using h
  | fuel, fuel', v :: vs, ws, hle, h => by
    simp only [toFirList] at h ⊢
    cases hv : toFir H fuel v with
    | none => rw [hv] at h; cases h
    | some w =>
      cases hvs : toFirList H fuel vs with
      | none => rw [hv, hvs] at h; cases h
      | some ws' =>
        rw [hv, hvs] at h
        rw [toFir_ext hx hle hv, toFirList_ext hx hle hvs]
        exact h

end

/-- Own value `v` denotes Fir value `w` in heap `H`. -/
def Den (H : Heap) (v : RVal) (w : Fir.Val) : Prop := H.value? v = some w

theorem Den.ext {H H' : Heap} (hx : Ext H H') {v : RVal} {w : Fir.Val} (h : Den H v w) : Den H' v w :=
  toFir_ext hx (by have := hx.1; omega) h

theorem den_lit (H : Heap) (l : Lam.Lit) : Den H (.lit l) (.lit l) := by simp [Den, Heap.value?, toFir]

theorem den_erased (H : Heap) : Den H .erased .erased := by simp [Den, Heap.value?, toFir]

theorem den_ctor0 (H : Heap) (c : Fir.CtorInfo) : Den H (.ctor0 c) (.ctor c []) := by
  simp [Den, Heap.value?, toFir]

/-- The denotation of a cell: its constructor over its fields' denotations. -/
theorem den_loc {H : Heap} {ℓ : Nat} {w : Fir.Val} (h : Den H (.loc ℓ) w) :
    ∃ r m b ws, H.cell? ℓ = some (.live r m b) ∧ w = .ctor b.ctor ws ∧
      toFirList H H.size b.fields = some ws := by
  simp only [Den, Heap.value?, toFir] at h
  split at h
  · next r m b hc =>
    cases hl : toFirList H H.size b.fields with
    | none => rw [hl] at h; cases h
    | some ws => rw [hl] at h; cases h; exact ⟨r, m, b, ws, hc, rfl, hl⟩
  · cases h

/-- A list of denotations at the heap's fuel. -/
theorem toFirList_of_dens {H : Heap} :
    ∀ {vs : List RVal} {ws : List Fir.Val}, Forall2 (Den H) vs ws → toFirList H (H.size + 1) vs = some ws
  | _, _, .nil => by simp [toFirList]
  | _, _, .cons hv hvs => by
    simp only [toFirList]
    rw [show toFir H (H.size + 1) _ = some _ from hv, toFirList_of_dens hvs]

/-- A fresh cell of denoting fields denotes its constructor over them. -/
theorem den_alloc (pol : AllocPol) (H : Heap) (c : Fir.CtorInfo) {vs : List RVal} {ws : List Fir.Val}
    (hds : Forall2 (Den H) vs ws) :
    Den (H.alloc pol { ctor := c, fields := vs }).2 (H.alloc pol { ctor := c, fields := vs }).1
      (.ctor c ws) := by
  have hx := Ext.alloc pol H { ctor := c, fields := vs }
  have hl := toFirList_ext hx (fuel' := H.size + 1) (Nat.le_refl _) (toFirList_of_dens hds)
  have hc := alloc_cell pol H { ctor := c, fields := vs }
  have hs := alloc_size pol H { ctor := c, fields := vs }
  rw [alloc_fst]
  generalize (H.alloc pol { ctor := c, fields := vs }).2 = H' at hx hl hc hs ⊢
  unfold Den Heap.value?
  simp only [toFir]
  rw [hc]
  simp only [hs, hl]
  rfl

end IxCC.Own.Proof
