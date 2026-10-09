import Compilatrix.Own.Plain.Proof.Retained

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result ClockMono Lang Sim)

theorem checked_retained {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true) :
    ∀ i, Sim Eq id
      (Own.Plain.plainRun {source := F, bodies} i) (cfgRun P i) := by
  intro i
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Own.Plain.plainRun {source := F, bodies} (r, ns)) (cfgRun P (r, ns))
  unfold Own.Plain.plainRun cfgRun
  have basic := (checkScopedProgram_parts checked).1
  simp only [generate_exports (checkProgram_parts basic).2]
  cases hr : F.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only
    cases hf : F.fun? f with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      have range := checked_source_dense checked hf
      obtain ⟨target, table, targetLookup, _, source, body, sourceLookup, _, lowering, _, _⟩ :=
        checked_entry basic range
      have eq : source = fd := Option.some.inj (sourceLookup.symm.trans hf)
      subst source
      simp only [targetLookup, lowering, lowerFunction_params, List.length_map]
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact checked_correct checked f (Own.Plain.litArgs ns) {}
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := Eq) rfl
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := Eq)
              rfl (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (R := Eq) (g := fun _ _ => .stuck)
            (checked_correct checked f (Own.Plain.litArgs (ns.take fd.params.length)) {})
            fun _ _ _ => rfl



end Compilatrix.Cfg.Rc
