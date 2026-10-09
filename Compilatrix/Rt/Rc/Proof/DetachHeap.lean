import Compilatrix.Rt.Rc.Proof.PendingBalance
import Compilatrix.Rt.Rc.Proof.ObjectFrame

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

theorem free_live_old {heap : Heap} {location refs body}
    (hc : heap.cell? location = some (.live refs .dyn body))
    {loc r mode b} (hnew : (setCell heap location .dead).cell? loc = some (.live r mode b)) :
    location ≠ loc ∧ heap.cell? loc = some (.live r mode b) := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  rw [setCell_cell heap location _ hl] at hnew
  split at hnew
  · cases hnew
  · rename_i he
    exact ⟨he, hnew⟩

/-- Unique detachment removes the abstract parent and overwrites only its
own scan/link bytes. Absence of incoming edges (derived from Balance at the
call site) guarantees surviving source fields do not become dangling. -/
theorem HeapLive.detach {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    (h : HeapLive heap addresses mem) {location body address}
    (hc : heap.cell? location = some (.live 1 .dyn body))
    (ha : addresses location = some address) (hedges : edgeCount heap location = 0)
    (predecessor : Word) :
    HeapLive (setCell heap location .dead) addresses
      (detachParent mem address predecessor body.fields.length) := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  obtain ⟨_, addr, had, target⟩ := h.cell location 1 .dyn body hc
  have heq : addr = address := by rw [ha] at had; exact (Option.some.inj had).symm
  subst addr
  have htfit := target.fit
  have hlen := target.fields_positive
  have ha8 : (address+8).toNat = address.toNat+8 := by
    apply addr_toNat (a := address) (i := 8)
    simp only [cellBytes] at htfit
    omega
  refine { cell := ?_, fields_live := ?_, disjoint := ?_ }
  · intro loc r mode b hnew
    obtain ⟨hne, hold⟩ := free_live_old hc hnew
    obtain ⟨hm, a, hmapping, hrep⟩ := h.cell loc r mode b hold
    subst mode
    refine ⟨rfl, a, hmapping, hrep.frame ?_⟩
    have hd := h.disjoint loc location r 1 b body a address hold hc hmapping ha (Ne.symm hne)
    have hf := hrep.fit
    have hfit : a.toNat+cellBytes b.fields.length ≤ 2^64 := by omega
    have hw64 : (address+8).toNat+8 ≤ 2^64 := by
      rw [ha8]; simp only [cellBytes] at htfit; omega
    have hw8 : address.toNat+1 ≤ 2^64 := by simp only [cellBytes] at htfit; omega
    have sep64 : a.toNat+cellBytes b.fields.length ≤ (address+8).toNat ∨
        (address+8).toNat+8 ≤ a.toNat := by
      rw [ha8]
      simp only [cellBytes] at hd ⊢
      rcases hd with hd | hd <;> omega
    have sep8 : a.toNat+cellBytes b.fields.length ≤ address.toNat ∨ address.toNat+1 ≤ a.toNat := by
      simp only [cellBytes] at hd ⊢
      rcases hd with hd | hd <;> omega
    exact (objectFrame_write mem a (address+8) predecessor _ .w64 hfit hw64 sep64).trans
      (objectFrame_write (mem.write .w64 (address+8) predecessor) a address
        (UInt64.ofNat (body.fields.length-1)) _ .w8 hfit hw8 sep8)
  · intro loc r b child hnew hmem
    obtain ⟨hne, hold⟩ := free_live_old hc hnew
    obtain ⟨childRefs, childBody, hchild⟩ := h.fields_live loc r b child hold hmem
    have hn : location ≠ child := by
      intro eq
      subst child
      exact fields_avoid hedges hold hmem
    exact ⟨childRefs, childBody, by simpa [setCell_cell heap location _ hl, hn] using hchild⟩
  · intro l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ h₁ h₂ ha₁ ha₂ hne
    exact h.disjoint l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ (free_live_old hc h₁).2
      (free_live_old hc h₂).2 ha₁ ha₂ hne



end Compilatrix.Rt.Rc.Procs
