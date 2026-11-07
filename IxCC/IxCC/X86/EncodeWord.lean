import IxCC.X86.EncodeBytes
import IxCC.X86.Width

/-! Canonical-immediate and signed-displacement laws that refer to the
encoder's fields and range checks. -/

namespace IxCC.X86.Encode

theorem norm_idem (kind : ImmKind) (value : Word) : kind.norm (kind.norm value) = kind.norm value := by
  by_cases present : kind = .none
  · subst present; rfl
  · rw [← imm_decode kind (kind.norm value) present, norm_low kind value present,
      imm_decode kind value present]


theorem signExtend32_ofInt (value : Int) (fits : fitsSigned32 value = true) :
    (signExtend32 (Int32.ofInt value).toUInt32).toBitVec = BitVec.ofInt 64 value := by
  simp only [fitsSigned32, decide_eq_true_eq] at fits
  exact signExtend32_ofInt_of_bounds value fits.1 fits.2

end IxCC.X86.Encode
