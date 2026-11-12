import IxCC.Rt.Rc.Gen.Proof.CountPreserve

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem LiveCell.pointer_branch {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    Cond.holds .tnz .w64 address 1 = false := by
  have hz : address &&& 1 = 0 := by
    apply UInt64.toNat_inj.mp
    have he : address.toNat % 2 = 0 := by have := h.aligned; omega
    simpa [UInt64.toNat_and, Nat.and_one_is_mod] using he
  simp [Cond.holds, hz]

theorem LiveCell.dynamic_branch {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    Cond.holds .slt .w32 (UInt64.ofNat (refs-1)) 0 = false := by
  let count := UInt64.ofNat (refs-1)
  have hb := h.bounded
  have hp := h.positive
  have hc : count.toNat = refs-1 := h.count_encoding
  have hs : count.toNat < 2^31 := by unfold maxCount at hb; omega
  have ht : X86.Width.w32.truncate count = count := truncate32_small (by omega)
  have hi : X86.Width.w32.signedValue count = Int.ofNat count.toNat := by
    simp [X86.Width.signedValue, X86.Width.bits, ht, hs]
  change decide (X86.Width.w32.signedValue count < X86.Width.w32.signedValue 0) = false
  rw [hi, show X86.Width.w32.signedValue 0 = 0 from by decide]
  simp

theorem LiveCell.shared_branch {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) (hs : 1 < refs) :
    Cond.holds .eq .w32 (UInt64.ofNat (refs-1)) 0 = false := by
  let count := UInt64.ofNat (refs-1)
  have hc : count.toNat = refs-1 := h.count_encoding
  have hb := h.bounded
  have ht : X86.Width.w32.truncate count = count := by
    apply truncate32_small
    unfold maxCount at hb
    omega
  have hn : count ≠ 0 := by intro hz; rw [hz] at hc; change 0 = refs-1 at hc; omega
  change (X86.Width.w32.truncate count == X86.Width.w32.truncate 0) = false
  rw [ht, show X86.Width.w32.truncate 0 = 0 from by decide]
  simp [hn]




end IxCC.Rt.Rc.Gen
