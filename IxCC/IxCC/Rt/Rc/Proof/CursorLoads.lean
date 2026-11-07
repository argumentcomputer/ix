import IxCC.Rt.Rc.Proof.ReleaseInvariant

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem byte_load_nat {mem : X86.Memory} {address : Word} {value : Nat}
    (hv : value < 256) (hr : mem.readable address = true)
    (hb : mem.bytes address = (UInt64.ofNat value).toUInt8) :
    loadWord mem .w8 .zero address = some (UInt64.ofNat value) := by
  have he : (UInt64.ofNat value).toUInt8.toUInt64 = UInt64.ofNat value := by
    apply UInt64.toNat_inj.mp
    simp only [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_ofNat']
    omega
  have hp : ∀ j < X86.Width.w8.bytes, mem.readable (address+UInt64.ofNat j) = true := by
    intro j hj
    have : j = 0 := by simp only [X86.Width.bytes] at hj; omega
    subst j
    simpa using hr
  unfold loadWord
  rw [read?_ok hp]
  simp [X86.Memory.read, X86.Memory.readLittle, X86.Width.bytes, hb]
  simpa using he

/-- Actual block7 scan/class loads follow from the loop's byte invariant.
The scan is the number of still-unvisited fields, not an assumed branch. -/
theorem ReleaseInvariant.cursor_loads
    {heap addresses mem external current frame tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (frame :: tail)
      context base bump limit slots lists) :
    loadWord mem .w8 .zero frame.address =
      some (UInt64.ofNat (frame.original.fields.length-frame.visited)) ∧
    loadWord mem .w8 .zero (frame.address+1) =
      some (UInt64.ofNat (smallClass frame.original.fields.length)) := by
  have hc := h.cursors.2.1
  have hp := hc.visited_positive
  have hl := hc.visited_le
  have hs := hc.small
  constructor
  · apply byte_load_nat (by omega) _ hc.remaining
    have hr := (h.cursor_access frame (by simp) 0 (by simp [cellBytes]; omega)).1
    simpa using hr
  · apply byte_load_nat (by simp only [smallClass]; omega) _ (h.cursor_class frame (by simp))
    have hr := (h.cursor_access frame (by simp) 1 (by simp [cellBytes]; omega)).1
    simpa using hr



end IxCC.Rt.Rc.Procs
