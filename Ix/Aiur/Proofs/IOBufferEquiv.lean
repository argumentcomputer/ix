module
public import Ix.Aiur.Semantics.Relation

public section

namespace Aiur

private theorem iobuffer_equiv_iff (x y : IOBuffer) :
    IOBuffer.equiv x y ↔ x.data == y.data ∧ x.map.Equiv y.map := by
  simp only [IOBuffer.equiv, BEq.beq, Bool.and_eq_true]
  exact ⟨fun ⟨hd, hm⟩ => ⟨hd, Std.HashMap.beq_iff_equiv.mp hm⟩,
         fun ⟨hd, hm⟩ => ⟨hd, Std.HashMap.beq_iff_equiv.mpr hm⟩⟩

theorem IOBuffer.equiv_refl (io : IOBuffer) : IOBuffer.equiv io io := by
  rw [iobuffer_equiv_iff]
  exact ⟨beq_self_eq_true io.data, Std.HashMap.Equiv.refl io.map⟩

theorem IOBuffer.equiv_symm {a b : IOBuffer} (h : IOBuffer.equiv a b) :
    IOBuffer.equiv b a := by
  rw [iobuffer_equiv_iff] at *
  exact ⟨by rw [beq_iff_eq] at *; exact h.1.symm, h.2.symm⟩

theorem IOBuffer.equiv_trans {a b c : IOBuffer}
    (hab : IOBuffer.equiv a b) (hbc : IOBuffer.equiv b c) :
    IOBuffer.equiv a c := by
  rw [iobuffer_equiv_iff] at *
  exact ⟨by rw [beq_iff_eq] at *; exact hab.1.trans hbc.1, hab.2.trans hbc.2⟩

end Aiur

end
