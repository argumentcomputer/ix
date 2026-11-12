import IxCC.Rt.Rc.Gen.Proof.IncrementIdle
import IxCC.Rt.Rc.Proof.Inc
import IxCC.Rt.Rc.Gen.Proof.LiveBranches
import IxCC.Rt.Rc.Proof.CountEncoding

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

theorem LiveCell.increment_room_branch {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) (hroom : refs < maxCount) :
    Cond.holds .eq .w32 (UInt64.ofNat (refs-1)) (UInt64.ofNat (maxCount-1)) = false := by
  let count := UInt64.ofNat (refs-1)
  have hc : count.toNat = refs-1 := h.count_encoding
  have hp := h.positive
  have ht : X86.Width.w32.truncate count = count := truncate32_small (by unfold maxCount at hroom; omega)
  have hm : X86.Width.w32.truncate (UInt64.ofNat (maxCount-1)) = UInt64.ofNat (maxCount-1) := by decide
  have hn : count ≠ UInt64.ofNat (maxCount-1) := by
    intro he
    have he' := congrArg UInt64.toNat he
    rw [hc] at he'
    change refs-1 = 2147483647 at he'
    unfold maxCount at hroom
    omega
  change (X86.Width.w32.truncate count == X86.Width.w32.truncate (UInt64.ofNat (maxCount-1))) = false
  rw [ht, hm]
  simp [hn]

theorem increment_entry_complete
    {heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none [] context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (hroom : refs < maxCount) :
    Own.Rc.inc heap (.loc location) 1 = some (setCell heap location (.live (refs+1) .dyn body)) ∧
    ReleaseInvariant cmax (setCell heap location (.live (refs+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat refs))
      (fun k => external k + refsIn k [.loc location]) none [] context base bump limit slots lists ∧
    eval incProgram 0 [address] mem context = .ok ([], storeCount mem address (UInt64.ofNat refs)) := by
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location refs .dyn body hc
  have heq : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  have hnext : X86.Width.w32.truncate (UInt64.ofNat (refs-1)+1) = UInt64.ofNat refs := by
    apply UInt64.toNat_inj.mp
    rw [increment_count cell.positive hroom cell.count_encoding]
    rw [toNat_ofNat_lt (by unfold maxCount at hroom; omega)]
    omega
  refine ⟨inc_dyn hc cell.positive 1, h.increment_idle hc ha hroom, ?_⟩
  simpa only [hnext] using inc_dynamic mem context address (UInt64.ofNat (refs-1)) 0
    cell.pointer_branch cell.count_load cell.dynamic_branch (cell.increment_room_branch hroom) cell.count_writable



end IxCC.Rt.Rc.Gen
