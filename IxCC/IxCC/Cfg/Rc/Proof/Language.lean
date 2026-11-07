import IxCC.Cfg.Rc.Proof.Correct
import IxCC.Own.Plain.Proof.Language
import IxCC.Cfg.Proof.Lang

/-! The actual checked RC Cfg machine as a Nat-input language. Complete value
and heap equality is supplied by the proved abstract simulation, including
all source entry arity conventions. Physical representation is a later pass. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result ClockMono Lang Sim)

theorem run_clockMono (P : Program) (f : Nat) (args : List Own.RVal) (H : Own.Heap) :
    ClockMono fun k => run P k f args H :=
  Sem.ClockMono.runClocked (step P)
    (fun hk => by unfold Cfg.fuelFor; exact Nat.mul_le_mul_right _ (by omega))
    (.call f args [] H)

def cfgRun (P : Program) (i : Nat × List Nat) (k : Nat) : Result (Own.RVal × Own.Heap) :=
  match P.base.exports[i.1]? with
  | some f =>
    match P.base.fun? f with
    | some fd => Sem.entryRun fd.params.length (.erased, {})
        (fun ns k => run P k f (Own.Plain.litArgs ns) {}) i.2 k
    | none => .stuck
  | none => .stuck

instance : Lang (Nat × List Nat) Program where
  Val := Own.RVal × Own.Heap
  run := cfgRun
  mono P i := by
    unfold cfgRun
    split
    · split
      · exact Sem.entryRun_mono (fun ns => run_clockMono P _ _ _) _
      · exact ClockMono.const _
    · exact ClockMono.const _
  obs := Own.Plain.obsV

theorem generate_exports {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : generate F bodies = some P) : P.base.exports = F.exports := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    subst P
    rfl

theorem lowerFunction_params (limit f : Nat) (source : Fir.Fun) (body : Own.Plain.Code) :
    (lowerFunction limit f source body).params = source.params.map (·.1) := by
  unfold lowerFunction
  rw [Cfg.function_params f (by simp [Own.immFun])]
  rfl

theorem checked_refines_lang {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true) :
    Sem.Refines ({source := F, bodies} : Own.Plain.Program) P := by
  refine Sem.Refines.of_sim (R := Lang.ObsEq) (fun _ _ h => h) fun i => ⟨id, ?_⟩
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
        exact (checked_correct checked f (Own.Plain.litArgs ns) {}).mono fun _ _ h => by rw [h]; rfl
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := Lang.ObsEq (S := Own.Plain.Program) (T := Program)) rfl
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := Lang.ObsEq (S := Own.Plain.Program) (T := Program))
              rfl (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (R := Eq) (g := fun _ _ => .stuck)
            (checked_correct checked f (Own.Plain.litArgs (ns.take fd.params.length)) {})
            fun _ _ _ => rfl

theorem checked_lower_refines {A : Anf.Program} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (lowered : Fir.lower A = .ok F) (checked : checkScopedProgram F bodies P = true) :
    Sem.Refines A P :=
  (Own.Plain.checked_lower_refines lowered
    (checkProgram_parts (checkScopedProgram_parts checked).1).1).trans
    (checked_refines_lang checked)




end IxCC.Cfg.Rc
