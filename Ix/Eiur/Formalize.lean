theorem List.exists_mem_cons_of_exists_mem {p : α → Prop}
    (h : ∃ x, x ∈ xs ∧ p x) : ∃ x, x ∈ y :: xs ∧ p x := by
  have ⟨x, ⟨hx_mem, hpx⟩⟩ := h
  exact ⟨x, ⟨List.mem_cons_of_mem y hx_mem, hpx⟩⟩

inductive Bit
  | b0 | b1

namespace Bit

def xor : Bit → Bit → Bit
  | b0, b0 => b0
  | b0, b1 => b1
  | b1, b0 => b1
  | b1, b1 => b0

def xorl : List Bit → Bit
  | [] => b0
  | b :: bs => b.xor $ xorl bs

theorem xorl_eq_b1_of_xorl_consb0_eq_b1 (h : xorl (b0 :: l) = b1) : xorl l = b1 := by
  cases h' : xorl l with
  | b0 => simp [xor, xorl, h'] at h
  | b1 => eq_refl

theorem exists_mem_b1_of_xorl_eq_b1 (h : xorl l = b1) : ∃ b ∈ l, b = b1 := by
  induction l with
  | nil => simp [xorl] at h
  | cons b _ ih =>
    cases b with
    | b0 =>
      have xorl_eq_b1 := xorl_eq_b1_of_xorl_consb0_eq_b1 h
      have exists_mem_b1_of_tail := ih xorl_eq_b1
      exact List.exists_mem_cons_of_exists_mem exists_mem_b1_of_tail
    | b1 => exact ⟨b1, ⟨List.mem_cons_self _ _, rfl⟩⟩

end Bit
