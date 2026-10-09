import Compilatrix.Own.Rc.Heap
import Compilatrix.Rt.Rc.Proof.CountPreserve
import Compilatrix.Rt.Rc.Proof.ObjectFrame

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

theorem count_live_iff {heap : Heap} {location refs body}
    (hc : heap.cell? location = some (.live refs .dyn body)) (newRefs loc : Nat) (other : Own.Body) :
    (∃ r, (setCell heap location (.live newRefs .dyn body)).cell? loc = some (.live r .dyn other)) ↔
      ∃ r, heap.cell? loc = some (.live r .dyn other) := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  by_cases he : location = loc
  · subst loc
    simp [setCell_cell heap location _ hl, hc]
  · simp [setCell_cell heap location _ hl, he]

theorem HeapLive.update_count {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    (h : HeapLive heap addresses mem) {location refs body address}
    (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (newRefs : Nat)
    (hp : 0 < newRefs) (hb : newRefs ≤ maxCount) :
    HeapLive (setCell heap location (.live newRefs .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat (newRefs-1))) := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  obtain ⟨_, addr, had, target⟩ := h.cell location refs .dyn body hc
  have haeq : addr = address := by rw [ha] at had; exact (Option.some.inj had).symm
  subst addr
  have htfit := target.fit
  have hlen := target.fields_positive
  have haddr4 : (address+4).toNat = address.toNat+4 := by
    apply addr_toNat (a := address) (i := 4)
    simp only [cellBytes] at htfit
    omega
  refine { cell := ?_, fields_live := ?_, disjoint := ?_ }
  · intro loc r mode b hcell
    by_cases he : location = loc
    · subst loc
      have eqs : newRefs = r ∧ .dyn = mode ∧ body = b := by
        simpa [setCell_cell heap location _ hl] using hcell
      rcases eqs with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, address, ha, target.update_count newRefs hp hb⟩
    · have hold : heap.cell? loc = some (.live r mode b) := by
        simpa [setCell_cell heap location _ hl, he] using hcell
      obtain ⟨hm, a, hmapping, hrep⟩ := h.cell loc r mode b hold
      subst mode
      refine ⟨rfl, a, hmapping, hrep.frame ?_⟩
      have hd := h.disjoint loc location r refs b body a address hold hc hmapping ha (Ne.symm he)
      have hf := hrep.fit
      apply objectFrame_write mem a (address+4) (UInt64.ofNat (newRefs-1)) _ .w32
      · omega
      · simp only [X86.Width.bytes]; rw [haddr4]
        simp only [cellBytes] at htfit
        omega
      · simp only [X86.Width.bytes]; rw [haddr4]
        simp only [cellBytes] at htfit hd ⊢
        rcases hd with hd | hd <;> omega
  · intro loc r b child hcell hmem
    obtain ⟨oldRefs, hold⟩ := (count_live_iff hc newRefs loc b).mp ⟨r, hcell⟩
    obtain ⟨childRefs, childBody, hchild⟩ := h.fields_live loc oldRefs b child hold hmem
    obtain ⟨newChildRefs, hnew⟩ := (count_live_iff hc newRefs child childBody).mpr ⟨childRefs, hchild⟩
    exact ⟨newChildRefs, childBody, hnew⟩
  · intro l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ h₁ h₂ ha₁ ha₂ hne
    obtain ⟨old₁, ho₁⟩ := (count_live_iff hc newRefs l₁ b₁).mp ⟨r₁, h₁⟩
    obtain ⟨old₂, ho₂⟩ := (count_live_iff hc newRefs l₂ b₂).mp ⟨r₂, h₂⟩
    exact h.disjoint l₁ l₂ old₁ old₂ b₁ b₂ a₁ a₂ ho₁ ho₂ ha₁ ha₂ hne



end Compilatrix.Rt.Rc.Procs
