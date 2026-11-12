import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant
import IxCC.Rt.Rc.Proof.CursorLoads

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

/-- The countdown in a suspended parent's count word, and its scan and class bytes, as the
actual loads of blocks 7 and 9 read them. -/
theorem ReleaseInvariant.cursor_loads
    {heap addresses mem external current frame tail context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current (frame :: tail)
      context base bump limit slots lists) :
    loadWord mem .w32 .zero (frame.address+4) =
      some (UInt64.ofNat (frame.original.ctor.nobj-frame.visited)) ∧
    loadWord mem .w8 .zero frame.address = some (UInt64.ofNat frame.original.ctor.nobj) ∧
    loadWord mem .w8 .zero (frame.address+1) =
      some (UInt64.ofNat (classOf frame.original.ctor)) := by
  have hc := h.cursors.2.1
  have hlt := classOf_lt hc.layout
  have hbytes := h.cursor_bytes (frame := frame) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold loadWord
    have hr : ∀ j < X86.Width.w32.bytes, mem.readable ((frame.address+4)+UInt64.ofNat j) = true := by
      intro j hj
      rw [cell_offset4]
      exact (h.cursor_access frame (by simp) (4+j) (by simp only [X86.Width.bytes] at hj; omega)).1
    rw [read?_ok hr, hc.remaining]
  · apply byte_load_nat hlt.2.1 _ (h.cursor_scan frame (by simp))
    have hr := (h.cursor_access frame (by simp) 0 (by omega)).1
    simpa using hr
  · apply byte_load_nat hlt.1 _ (h.cursor_class frame (by simp))
    have hr := (h.cursor_access frame (by simp) 1 (by omega)).1
    simpa using hr

end IxCC.Rt.Rc.Gen
