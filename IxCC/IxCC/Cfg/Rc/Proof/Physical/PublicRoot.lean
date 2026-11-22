import IxCC.Cfg.Rc.Proof.Physical.PublicEval

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

/-- The driver may select any exported root. Retargeting changes only the
entry function and preserves the actual three layout simulations. -/
theorem accepted_root_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    (checked : checkScopedProgram F bodies P = true)
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ pairs functions, CodeAdmission F bodies P config pairs functions ∧
      ∀ root clock words memory context,
        Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
          clock words memory context ≠ .stuck →
        Lir.eval {lowered.runtime.program with main := root} clock words memory context =
          Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
            clock words memory context := by
  obtain ⟨original, native, equal, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, switches, entry, _, consuming, lowering, length, program, _⟩ :=
    Native.Spec.lower_parts native
  have splitEq : lowered.runtime.program =
      (Public.Spec.rawPublicProgram (layoutOf P) functions main).splitCriticalEdges := by
    rw [equal]
    exact Public.Spec.assemble_split program
  have split : Lir.ProgSim (Public.Spec.rawPublicProgram (layoutOf P) functions main)
      lowered.runtime.program (Public.Spec.labels (Public.Spec.rawPublicProgram (layoutOf P) functions main)) :=
    splitEq ▸ Public.Spec.program_split _
  refine ⟨pairs, functions, ⟨checked, consuming, lowering, switches⟩, ?_⟩
  intro root clock words memory context regular
  have splitRoot : Lir.ProgSim (Public.Spec.rawPublicProgram (layoutOf P) functions root)
      {lowered.runtime.program with main := root}
      (Public.Spec.labels (Public.Spec.rawPublicProgram (layoutOf P) functions main)) :=
    ⟨rfl, split.funcs⟩
  have first := program_eval_transfer (Public.Spec.source_raw_pruned lowering root)
    clock words memory context regular
  have second := program_eval_transfer (Public.Spec.source_pruned_split lowering root)
    clock words memory context (by rw [first]; exact regular)
  have third := program_eval_transfer splitRoot clock words memory context
    (by rw [second, first]; exact regular)
  exact third.trans (second.trans first)



/-- Reuse the exact admission already obtained by initialization. Successful
deterministic consumption identifies the intermediate program receipt. -/
theorem admitted_root_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    (root clock : Nat) (words : List Lir.Word) (memory : X86.Memory) (context : Lir.Word)
    (regular : Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
      clock words memory context ≠ .stuck) :
    Lir.eval {lowered.runtime.program with main := root} clock words memory context =
      Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
        clock words memory context := by
  obtain ⟨pairs', functions', admission', transfer⟩ :=
    accepted_root_eval_stages admission.scopedProgram accepted
  have same : pairs' = pairs := Except.ok.inj (admission'.consuming.symm.trans admission.consuming)
  subst pairs'
  exact transfer root clock words memory context regular


end IxCC.Cfg.Rc.Native.Spec
