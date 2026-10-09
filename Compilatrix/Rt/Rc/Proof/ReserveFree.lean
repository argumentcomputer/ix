import Compilatrix.Rt.Rc.Proof.ReserveIdle
import Compilatrix.Rt.Rc.Proof.AllocatorAccess

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

/-- The actual free-pop allocation path, with all machine safety facts derived
from allocator-ready state. Logical ownership is unchanged until publication. -/
theorem AllocatorReady.reserve_free
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {fields tag : Nat} (hc : target.cls = smallClass fields)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag) (clock : Nat) :
    let after := reserveFree mem context target.address (tail.headD 0) fields tag
    eval (allocProgram fields tag) clock [] mem context = .ok ([target.address], after) ∧
    AllocatorReady heap addresses after external context base bump limit
      (reserveSlots target.address slots) (popFree lists target.cls) ∧
    ({target with kind := .reserved} : Slot) ∈ reserveSlots target.address slots ∧
    WordAt after target.address (dynamicHeader fields (smallClass fields) tag 1) := by
  have vt := h.idle.partition.valid target ht
  have wh := h.idle.free_heads target.cls vt.1 vt.2.1
  rw [hhead] at wh
  have wn := h.idle.free_chains target.cls
  rw [hhead] at wn
  have hh : loadWord mem .w64 .zero (headAddress context fields) = some target.address := by
    rw [headAddress_eq, ← hc]
    simp [loadWord, wh.read64, truncate_w64]
  have hn : loadWord mem .w64 .zero target.address = some (tail.headD 0) := by
    simp [loadWord, wn.1.read64, truncate_w64]
  have hw : ∀ j < 8, mem.writable (target.address+UInt64.ofNat j) = true := by
    intro j hj
    exact (h.slot_access ht (by omega)).2
  have hr : ∀ j < 8, mem.readable (target.address+UInt64.ofNat j) = true := by
    intro j hj
    exact (h.slot_access ht (by omega)).1
  refine ⟨alloc_free mem context target.address (tail.headD 0) fields tag clock hpos hsmall htag
    (h.slot_nonzero ht) hh hn ?_ hw,
    h.after_protected (h.idle.reserve_protected ht hc tag _) (h.idle.reserve_idle ht hhead hc tag),
    ?_, ?_⟩
  · simpa only [headAddress_eq, ← hc] using h.idle.head_writable target.cls vt.1 vt.2.1
  · exact List.mem_map.mpr ⟨target, ht, by simp⟩
  · apply wordAt_write64
    simpa [X86.Memory.write] using hr


end Compilatrix.Rt.Rc.Procs
