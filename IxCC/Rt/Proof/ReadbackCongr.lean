import IxCC.Rt.Readback
import IxCC.Rt.Proof.Mem

/-!
# Readback reads only readable bytes

`Rt.readback` reads memory through `read64?`, which faults on a byte that is
not readable. So two memories with the same readable bytes, holding the
same values there, read every word back alike (`readback_congr`). The
backend half uses it to observe a result in the object's memory as
`Rt.Loaded` observes it in Lir's: the two agree on Lir's readable bytes.
-/

namespace IxCC.Rt

open IxCC.X86 (Memory)

/-- Two memories with the same readable bytes, holding the same values
there. -/
structure SameReadable (m₁ m₂ : Memory) : Prop where
  readable : m₁.readable = m₂.readable
  bytes : ∀ a, m₁.readable a = true → m₁.bytes a = m₂.bytes a

theorem SameReadable.read? {m₁ m₂ : Memory} (h : SameReadable m₁ m₂) (w : X86.Width) (a : X86.Word) :
    m₁.read? w a = m₂.read? w a := by
  unfold Memory.read?
  rw [← h.readable]
  split
  · rename_i hok
    have hall := (Proof.rangeAllowed_iff _ _ _).1 hok
    congr 1
    exact Memory.readLittle_congr _ _ _ _ fun i hi => h.bytes _ (hall i hi)
  · rfl

/-- **Readback reads only readable bytes.** -/
theorem readback_congr {m₁ m₂ : Memory} (h : SameReadable m₁ m₂) (sig : Sig) :
    ∀ (fuel : Nat) (ty : FoTy) (w : X86.Word), readback sig fuel m₁ ty w = readback sig fuel m₂ ty w
  | _, .nat, w => by simp [readback]
  | 0, .ind i, w => by simp [readback]
  | fuel + 1, .ind i, w => by
    simp only [readback]
    split
    · rfl
    · have hr := h.read? .w64 w
      unfold Memory.read64?
      rw [hr]
      split
      · rfl
      · rename_i hd _
        split
        · rename_i tys _
          split
          · congr 2
            funext x
            have hx := h.read? .w64 (w + UInt64.ofNat (8 + 8 * x.2))
            simp only [hx]
            cases m₂.read? X86.Width.w64 (w + UInt64.ofNat (8 + 8 * x.2)) with
            | ok v => exact readback_congr h sig fuel _ _
            | error e => rfl
          · rfl
        · rfl

end IxCC.Rt
