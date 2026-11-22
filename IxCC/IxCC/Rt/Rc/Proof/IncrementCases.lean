import IxCC.Rt.Rc.Proof.IncrementEntry
import IxCC.Rt.Rc.Proof.ImmediateStep

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem increment_immediate_entry
    {heap addresses mem external context base bump limit slots lists value}
    (h : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    (hn : ∀ location, value ≠ .loc location)
    (word : Word) (hw : valueWord addresses value = some word) :
    Own.Rc.inc heap value 1 = some heap ∧
    ReleaseInvariant heap addresses mem (fun k => external k + refsIn k [value]) none []
      context base bump limit slots lists ∧
    eval incProgram 0 [word] mem context = .ok ([], mem) := by
  have hext : (fun k => external k + refsIn k [value]) = external := by
    funext k
    simp [refsIn, hn k]
  refine ⟨?_, by simpa only [hext] using h, ?_⟩
  · cases value with
    | loc l => exact False.elim (hn l rfl)
    | lit l => rfl
    | ctor0 c => rfl
    | erased => rfl
  · apply inc_immediate
    have htag := valueWord_immediate_tag hw hn
    simp [Cond.holds, htag]

/-- The maximal representable dynamic count takes the existing heap-resource
failure branch before any store; it is not silently assumed to have room. -/
theorem increment_max_failure
    {heap addresses mem external context base bump limit slots lists location body address}
    (h : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    (hc : heap.cell? location = some (.live maxCount .dyn body))
    (ha : addresses location = some address) :
    eval incProgram 0 [address] mem context = .resource .heap := by
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location maxCount .dyn body hc
  have heq : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  exact inc_overflow mem context address (UInt64.ofNat (maxCount-1)) 0 cell.pointer_branch
    cell.count_load cell.dynamic_branch (by simp [Cond.holds])



end IxCC.Rt.Rc.Procs
