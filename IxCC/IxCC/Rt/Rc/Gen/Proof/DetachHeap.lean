import IxCC.Rt.Rc.Proof.PendingBalance
import IxCC.Rt.Rc.Proof.DetachHeap
import IxCC.Rt.Rc.Gen.Proof.ObjectFrame
import IxCC.Rt.Rc.Gen.Proof.Pending

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

/-- A cell without incoming edges dies, and memory changes only outside every other live cell:
the other cells keep their representation. -/
theorem HeapLive.kill {heap : Heap} {addresses : AddressMap} {mem after : X86.Memory}
    (h : HeapLive heap addresses mem) {location refs body}
    (hc : heap.cell? location = some (.live refs .dyn body)) (hedges : edgeCount heap location = 0)
    (hf : ∀ loc r b a, loc ≠ location → heap.cell? loc = some (.live r .dyn b) →
      addresses loc = some a → ObjectFrame mem after a (cellBytesOf b.ctor)) :
    HeapLive (setCell heap location .dead) addresses after := by
  have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hc).1
  refine { cell := ?_, fields_live := ?_, disjoint := ?_ }
  · intro loc r mode b hnew
    obtain ⟨hne, hold⟩ := free_live_old hc hnew
    obtain ⟨hm, a, hmapping, hrep⟩ := h.cell loc r mode b hold
    subst mode
    exact ⟨rfl, a, hmapping, hrep.frame (hf loc r b a (Ne.symm hne) hold hmapping)⟩
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

/-- Unique detachment removes the abstract parent and overwrites only its own link and count
bytes. -/
theorem HeapLive.detach {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    (h : HeapLive heap addresses mem) {location body address}
    (hc : heap.cell? location = some (.live 1 .dyn body))
    (ha : addresses location = some address) (hedges : edgeCount heap location = 0)
    (predecessor : Word) :
    HeapLive (setCell heap location .dead) addresses
      (detachParent mem address predecessor body.ctor.nobj) := by
  obtain ⟨_, addr, had, target⟩ := h.cell location 1 .dyn body hc
  have heq : addr = address := by rw [ha] at had; exact (Option.some.inj had).symm
  subst addr
  have htfit := target.fit
  have hlen := target.bytes
  have ha8 : (address+8).toNat = address.toNat+8 := addr_toNat (a := address) (i := 8) (by omega)
  have ha4 : (address+4).toNat = address.toNat+4 := addr_toNat (a := address) (i := 4) (by omega)
  apply h.kill hc hedges
  intro loc r b a hne hold hmapping
  have hd := h.disjoint loc location r 1 b body a address hold hc hmapping ha hne
  obtain ⟨_, a', ha', hrep⟩ := h.cell loc r .dyn b hold
  have hae : a' = a := by rw [hmapping] at ha'; exact (Option.some.inj ha').symm
  subst a'
  have hf := hrep.fit
  have hfit : a.toNat+cellBytesOf b.ctor ≤ 2^64 := by omega
  have hw64 : (address+8).toNat+8 ≤ 2^64 := by rw [ha8]; omega
  have hw4 : (address+4).toNat+4 ≤ 2^64 := by rw [ha4]; omega
  have sep64 : a.toNat+cellBytesOf b.ctor ≤ (address+8).toNat ∨ (address+8).toNat+8 ≤ a.toNat := by
    rw [ha8]; rcases hd with hd | hd <;> omega
  have sep4 : a.toNat+cellBytesOf b.ctor ≤ (address+4).toNat ∨ (address+4).toNat+4 ≤ a.toNat := by
    rw [ha4]; rcases hd with hd | hd <;> omega
  unfold detachParent storeCount
  exact (objectFrame_write mem a (address+8) predecessor _ .w64 hfit hw64 sep64).trans
    (objectFrame_write (mem.write .w64 (address+8) predecessor) a (address+4)
      (UInt64.ofNat (body.ctor.nobj-1)) _ .w32 hfit hw4 sep4)

end IxCC.Rt.Rc.Gen
