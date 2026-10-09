import Compilatrix.Cfg.Rc.Scoped
import Compilatrix.Cfg.Rc.Proof.ProgramSound
import Compilatrix.Cfg.Rc.Proof.Names

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


theorem checkScopedProgram_parts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (h : checkScopedProgram F bodies P = true) :
    checkProgram F bodies P = true ∧ programNames F bodies = true := by
  simp only [checkScopedProgram, Bool.and_eq_true] at h
  exact h.1

theorem checked_source_dense {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (h : checkScopedProgram F bodies P = true) {f : Nat} {fd : Fir.Fun}
    (lookup : F.fun? f = some fd) : f < F.size := by
  simp only [checkScopedProgram, Bool.and_eq_true] at h
  exact of_decide_eq_true ((List.all_eq_true.mp h.2) (f, fd) (Src.NatMap.mem_toList lookup))

theorem programNames_lookup {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    (h : programNames F bodies = true) {f : Nat} (hf : f < F.size)
    {fd : Fir.Fun} {body : Own.Plain.Code} (source : F.fun? f = some fd)
    (code : bodies.get? f = some body) :
    names (paramBound 0 (fd.params.map (·.1))) body = true := by
  have check := (List.all_eq_true.mp h) f (List.mem_range.mpr hf)
  simpa only [source, code] using check

theorem checked_names {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (h : checkScopedProgram F bodies P = true) {f : Nat} (hf : f < F.size)
    {fd : Fir.Fun} {body : Own.Plain.Code} (source : F.fun? f = some fd)
    (code : bodies.get? f = some body) :
    ∃ lo, (∀ p ∈ fd.params.map (·.1), p < lo) ∧
      names lo body = true ∧ Cfg.Proof.Scoped lo (Own.immCode (Own.Plain.eraseCode body)) := by
  have checked := programNames_lookup (checkScopedProgram_parts h).2 hf source code
  exact ⟨_, fun _ member => paramBound_mem 0 member, checked, names_sound _ _ checked⟩

end Compilatrix.Cfg.Rc
