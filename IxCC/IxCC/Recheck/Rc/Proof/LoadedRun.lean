import IxCC.Recheck.Rc.Proof.LoadedCalls

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang Result Sim)

theorem loaded_root_shape {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) :
    f.lowered.roots.map Prod.fst = f.fir.exports := by
  obtain ⟨_, _, _, _, _, generated, _⟩ := runFront_spec accepted
  obtain ⟨original, native, equal, _⟩ := Cfg.Rc.Public.Spec.lower_parts (runFront_native accepted).2
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, _, _, _, _, _, roots, _⟩ :=
    Cfg.Rc.Native.Spec.lower_parts native
  have shape : f.lowered.roots.map Prod.fst = f.cfg.base.exports := by
    have lowered := congrArg (fun value : Cfg.Rc.Public.Lowered => value.runtime.roots.map Prod.fst) equal
    change f.lowered.roots.map Prod.fst = original.roots.map Prod.fst at lowered
    rw [lowered, roots]
    simp [Cfg.Rc.Native.Spec.rootsOf, List.map_map, Function.comp_def]
  exact shape.trans (Cfg.Rc.generate_exports generated)

/-- The whole driver entry convention: exact arguments execute the physical
call, partial applications preserve the unobserved value, and extra inputs
follow the same first-order stuck continuation. -/
theorem loaded_run_sim {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) {model : Rt.Model}
    (region : Rt.Proof.RegionOk model.ctx model.size)
    (readable : Rt.Proof.LirRegion model.mem model.ctx model.size)
    (input : Nat × List Nat) :
    Sim (ViewedFirRel f input.1) Nat.succ
      (Fir.firRun f.fir input) ((f.loaded model).run input) := by
  obtain ⟨root, numbers⟩ := input
  change Sim (ViewedFirRel f root) Nat.succ (Fir.firRun f.fir (root, numbers))
    (fun clock => Rt.Loaded.run (f.loaded model) (root, numbers) clock)
  obtain ⟨_, _, _, _, _, _, checked⟩ := runFront_spec accepted
  have basic := (Cfg.Rc.checkScopedProgram_parts checked).1
  unfold Fir.firRun
  cases rootLookup : f.fir.exports[root]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some fn =>
    simp only
    cases sourceLookup : f.fir.fun? fn with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some source =>
      have range := Cfg.Rc.checked_source_dense checked sourceLookup
      obtain ⟨target, table, targetLookup, _, actual, body, actualLookup, _, lowering, _, _⟩ :=
        Cfg.Rc.checked_entry basic range
      have same : actual = source := Option.some.inj (actualLookup.symm.trans sourceLookup)
      subst actual
      have mapped : (f.lowered.roots[root]?).map Prod.fst = some fn := by
        rw [← List.getElem?_map, loaded_root_shape accepted]
        exact rootLookup
      obtain ⟨⟨fn', name⟩, loweredRoot, sameFn⟩ := Option.map_eq_some_iff.mp mapped
      simp only at sameFn
      subst fn'
      have entry : (f.loaded model).entries[root]? =
          some {fn := fn, params := source.params.length, ty := f.tys root} := by
        change (Rt.entriesOf f.cfg.base f.lowered.roots f.tys)[root]? = _
        rw [Rt.entriesOf_get, loweredRoot]
        simp [targetLookup, lowering, Cfg.Rc.lowerFunction_params]
      simp only [Rt.Loaded.run, entry]
      by_cases exactArity : numbers.length = source.params.length
      · simp only [Sem.entryRun, exactArity, ↓reduceIte]
        exact loaded_call_sim accepted region readable root fn sourceLookup numbers exactArity
      · by_cases underapplied : numbers.length < source.params.length
        · simp only [Sem.entryRun, exactArity, underapplied, ↓reduceIte]
          by_cases empty : numbers = []
          · simp only [empty, ↓reduceIte]
            exact Sim.okConst (erased_view f root)
          · simp only [empty, ↓reduceIte]
            exact Sim.laterConst (f := Nat.succ) (erased_view f root) (fun _ h => by omega)
        · simp only [Sem.entryRun, exactArity, underapplied, ↓reduceIte]
          exact Sim.bindStuck (g := fun _ _ => .stuck)
            (loaded_call_sim accepted region readable root fn sourceLookup
              (numbers.take source.params.length) (by simp only [List.length_take]; omega))
            (fun _ _ _ => rfl)

theorem loaded_run_refines {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) {model : Rt.Model}
    (region : Rt.Proof.RegionOk model.ctx model.size)
    (readable : Rt.Proof.LirRegion model.mem model.ctx model.size)
    (input : Nat × List Nat) :
    Sem.Behaviour.Refines (ViewedFirRel f input.1)
      (Lang.behaviour f.fir input) (Lang.behaviour (f.loaded model) input) :=
  Sem.Sim.refines (Lang.mono f.fir input) (Lang.mono (f.loaded model) input)
    (loaded_run_sim accepted region readable input)

theorem front_refines_lir {cfg : Config} {P : Src.Program} {cert : Cert} {f : Front}
    (accepted : runFront cfg P cert = .ok f) {model : Rt.Model}
    (region : Rt.Proof.RegionOk model.ctx model.size)
    (readable : Rt.Proof.LirRegion model.mem model.ctx model.size) :
    Sem.Refines f.source (f.loaded model) :=
  source_view_refines_of_fir accepted model (loaded_run_refines accepted region readable)





end IxCC.Recheck.RcReplay
