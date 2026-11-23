import IxCC.Cfg.Rc.Scoped
import IxCC.Cfg.Rc.Proof.ProgramSound
import IxCC.Cfg.Rc.Proof.Names

set_option autoImplicit false
namespace IxCC.Cfg.Rc


theorem checkScopedProgram_parts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (h : checkScopedProgram F bodies P borrows uniqs = true) :
    checkProgram F bodies P borrows uniqs = true ∧ programNames F bodies = true := by
  simp only [checkScopedProgram, Bool.and_eq_true] at h
  exact h.1

theorem checked_source_dense {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (h : checkScopedProgram F bodies P borrows uniqs = true)
    {f : Nat} {fd : Fir.Fun} (lookup : F.fun? f = some fd) : f < F.size := by
  simp only [checkScopedProgram, Bool.and_eq_true] at h
  exact of_decide_eq_true ((List.all_eq_true.mp h.2) (f, fd) (Src.NatMap.mem_toList lookup))

theorem programNames_parts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    (h : programNames F bodies = true) {f : Nat} (hf : f < F.size)
    {fd : Fir.Fun} {body : Own.Plain.Code} (source : F.fun? f = some fd)
    (code : bodies.get? f = some body) :
    names (paramBound 0 (fd.params.map (·.1))) body = true ∧
    fd.params.all (fun p => decide (p.1 < fd.vars)) = true ∧
    varsBelow fd.vars body = true ∧
    reuseCtorsOk F.ctors body = true := by
  have check := (List.all_eq_true.mp h) f (List.mem_range.mpr hf)
  simp only [source, code, Bool.and_eq_true] at check
  exact ⟨check.1.1.1, check.1.1.2, check.1.2, check.2⟩

theorem programNames_lookup {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    (h : programNames F bodies = true) {f : Nat} (hf : f < F.size)
    {fd : Fir.Fun} {body : Own.Plain.Code} (source : F.fun? f = some fd)
    (code : bodies.get? f = some body) :
    names (paramBound 0 (fd.params.map (·.1))) body = true :=
  (programNames_parts h hf source code).1

theorem checked_names {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (h : checkScopedProgram F bodies P borrows uniqs = true)
    {f : Nat} (hf : f < F.size) {fd : Fir.Fun} {body : Own.Plain.Code}
    (source : F.fun? f = some fd) (code : bodies.get? f = some body) :
    ∃ lo, (∀ p ∈ fd.params.map (·.1), p < lo) ∧
      names lo body = true ∧ Cfg.Proof.Scoped lo (Own.immCode (Own.Plain.eraseCode body)) := by
  have checked := programNames_lookup (checkScopedProgram_parts h).2 hf source code
  exact ⟨_, fun _ member => paramBound_mem 0 member, checked, names_sound _ _ checked⟩

theorem checked_names_full {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (h : checkScopedProgram F bodies P borrows uniqs = true)
    {f : Nat} (hf : f < F.size) {fd : Fir.Fun} {body : Own.Plain.Code}
    (source : F.fun? f = some fd) (code : bodies.get? f = some body) :
    ∃ lo, (∀ p ∈ fd.params.map (·.1), p < lo) ∧ lo ≤ fd.vars ∧
      names lo body = true ∧ varsBelow fd.vars body = true ∧
      reuseCtorsOk F.ctors body = true := by
  obtain ⟨hn, hp, hv, hr⟩ := programNames_parts (checkScopedProgram_parts h).2 hf source code
  refine ⟨paramBound 0 (fd.params.map (·.1)), fun _ member => paramBound_mem 0 member, ?_, hn, hv, hr⟩
  apply paramBound_le (Nat.zero_le _)
  intro x hx
  obtain ⟨p, hmem, rfl⟩ := List.mem_map.mp hx
  exact of_decide_eq_true ((List.all_eq_true.mp hp) p hmem)

end IxCC.Cfg.Rc
