import IxCC.Rt.Rc.Gen.Proof.LiveMemory
import IxCC.Rt.Rc.Proof.ObjectFrame

/-! Byte-level frames for every unrelated live object of any layout. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem LiveCell.frame {addresses before after address refs body}
    (h : LiveCell addresses before address refs body)
    (hf : ObjectFrame before after address (cellBytesOf body.ctor)) :
    LiveCell addresses after address refs body := by
  have hb := h.bytes
  refine { h with readable := ?_, writable := ?_, header := ?_, count := ?_, fields := ?_ }
  · intro j hj; rw [hf.readable]; exact h.readable j hj
  · intro j hj; rw [hf.writable]; exact h.writable j hj
  · rw [← h.header]
    apply X86.Memory.readLittle_congr
    intro j hj
    apply hf.bytes_eq
    simp only [X86.Width.bytes] at hj
    omega
  · rw [← h.count]
    apply X86.Memory.readLittle_congr
    intro j hj
    rw [cell_offset4]
    apply hf.bytes_eq
    simp only [X86.Width.bytes] at hj
    omega
  · intro j value hj
    obtain ⟨word, hv, hw⟩ := h.fields j value hj
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    exact ⟨word, hv, hf.word (by omega) hw⟩

end IxCC.Rt.Rc.Gen
