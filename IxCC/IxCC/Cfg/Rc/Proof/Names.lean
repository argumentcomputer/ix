import IxCC.Cfg.Rc.Names
import IxCC.Cfg.Rc.Proof.Lower
import IxCC.Cfg.Proof.Sim

set_option autoImplicit false
namespace IxCC.Cfg.Rc


theorem paramBound_base (lo : Nat) (ps : List Fir.Var) : lo ≤ paramBound lo ps := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih => simp only [paramBound]; omega

theorem paramBound_mem (lo : Nat) {ps : List Fir.Var} {x : Fir.Var} (h : x ∈ ps) :
    x < paramBound lo ps := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.mem_cons] at h
    simp only [paramBound]
    rcases h with h | h
    · subst x
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self p) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)

mutual
theorem names_sound (lo : Nat) : ∀ c, names lo c = true →
    Cfg.Proof.Scoped lo (Own.immCode (Own.Plain.eraseCode c))
  | .act _ k, h => names_sound lo k h
  | .bind x r k, h => by
    simp only [names, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, names_sound (x + 1) k h.2⟩
  | .jp j ps captured rec b k, h => by
    simp only [names, Bool.and_eq_true] at h
    refine ⟨?_, ⟨paramBound lo ps, paramBound_base lo ps, ?_, names_sound _ b h.1.2⟩,
      names_sound lo k h.2⟩
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact of_decide_eq_true ((List.all_eq_true.mp h.1.1) x hx)
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact paramBound_mem lo hx
  | .case x alts d, h => by
    simp only [names, Bool.and_eq_true] at h
    exact ⟨namesAlts_sound lo alts h.1, namesOpt_sound lo d h.2⟩
  | .jmp .., _ | .ret .., _ | .tcall .., _ | .trap, _ => True.intro
theorem namesAlts_sound (lo : Nat) : ∀ alts, namesAlts lo alts = true →
    Cfg.Proof.ScopedAlts lo (Own.immAlts (Own.Plain.eraseAlts alts))
  | [], _ => True.intro
  | .mk key b :: rest, h => by
    simp only [namesAlts, Bool.and_eq_true] at h
    exact ⟨names_sound lo b h.1, namesAlts_sound lo rest h.2⟩
theorem namesOpt_sound (lo : Nat) : ∀ d, namesOpt lo d = true →
    Cfg.Proof.ScopedOpt lo (Own.immOpt (Own.Plain.eraseOpt d))
  | none, _ => True.intro
  | some c, h => names_sound lo c h
end

end IxCC.Cfg.Rc
