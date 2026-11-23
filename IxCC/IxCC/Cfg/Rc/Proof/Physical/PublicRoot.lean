import IxCC.Cfg.Rc.Proof.Physical.PublicEval

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

/-- The driver may select any exported root. Retargeting changes only the
entry function and preserves all layout and inline RC simulations. -/
theorem accepted_root_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered) :
    ∃ pairs functions, CodeAdmission F bodies P config pairs functions borrows uniqs ∧
      ∀ root, root < P.base.size → ∀ words memory context,
        Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
          (fun clock => Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
            clock words memory context)
          (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := by
  obtain ⟨original, native, equal, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, switches, entry, _, consuming, lowering, length, program, _⟩ :=
    Native.Spec.lower_parts native
  have splitEq : lowered.runtime.program =
      (Public.Spec.inlinedPublicProgram (layoutOf P) functions main).splitCriticalEdges := by
    rw [equal]
    exact Public.Spec.assemble_split program
  have split : Lir.ProgSim (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)
      lowered.runtime.program
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)) :=
    splitEq ▸ Public.Spec.program_split _
  refine ⟨pairs, functions, ⟨checked, consuming, lowering, switches⟩, ?_⟩
  intro root hroot words memory context
  have splitRoot : Lir.ProgSim (Public.Spec.inlinedPublicProgram (layoutOf P) functions root)
      {lowered.runtime.program with main := root}
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)) :=
    ⟨rfl, split.funcs⟩
  have inlEq := Public.Spec.inlinedPublicProgram_eq_inline (layoutOf P) functions root length
  have hr := Public.Spec.rawPublicProgram_runtimeFuncs (l := layoutOf P) length root
  have hno := Public.Spec.rawPublicProgram_noRuntimeReuseCalls (l := layoutOf P) length root
  have hrootNp : Prune.isPrunableReuse (layoutOf P)
      (Public.Spec.rawPublicProgram (layoutOf P) functions root).main = false := by
    dsimp only [Prune.isPrunableReuse, Public.Spec.rawPublicProgram, rawProgram, layoutOf,
      Layout.isUniqueProc, Layout.init, Layout.incProc]
    exact decide_eq_false fun ⟨h1, _⟩ =>
      Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt hroot) (by omega)) h1
  have stage12 : ∀ clock,
      Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
        clock words memory context ≠ .stuck →
      Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions root)
        clock words memory context =
        Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
          clock words memory context := by
    intro clock regular
    have first := program_eval_transfer (Public.Spec.source_raw_pruned lowering root)
      clock words memory context regular
    have second := program_eval_transfer (Public.Spec.source_pruned_split lowering root)
      clock words memory context (by rw [first]; exact regular)
    exact second.trans first
  have hsimInl : Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions root)
        clock words memory context)
      (fun clock => Lir.eval (Public.Spec.inlinedPublicProgram (layoutOf P) functions root)
        clock words memory context) := by
    rw [inlEq]
    apply Prune.pruneUnusedReuse_inlineProgram_sim_clock hr hno hrootNp words memory context
    intro k
    have hle := Inline.fuelFor_le_split (Public.Spec.inlinedPublicProgram (layoutOf P) functions main) k
    have hsame : Lir.fuelFor (Public.Spec.inlinedPublicProgram (layoutOf P) functions root) k =
        Lir.fuelFor (Public.Spec.inlinedPublicProgram (layoutOf P) functions main) k := rfl
    rw [← splitEq] at hle
    rw [← inlEq, hsame]
    unfold Inline.inlineClock
    omega
  have hsimInl3 : Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions root)
        clock words memory context)
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := {
    forward := fun k hk => by
      obtain ⟨k', hr'⟩ := hsimInl.forward k hk
      by_cases hst : Lir.eval (Public.Spec.inlinedPublicProgram (layoutOf P) functions root)
          k' words memory context = .stuck
      · exact ⟨0, (hst ▸ hr').of_stuck ▸ .stuck⟩
      · exact ⟨k', (program_eval_transfer splitRoot k' words memory context hst).symm ▸ hr'⟩
    timeout := fun k hk => by
      rcases hsimInl.timeout k hk with hto | ⟨r, hfail⟩
      · exact .inl ((program_eval_transfer splitRoot k words memory context (by rw [hto]; intro h; cases h)).trans hto)
      · exact .inr ⟨r, (program_eval_transfer splitRoot k words memory context (by rw [hfail]; intro h; cases h)).trans hfail⟩ }
  exact {
    forward := fun k hk => by
      by_cases hst : Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
          k words memory context = .stuck
      · exact ⟨0, hst ▸ .stuck⟩
      · have heq := stage12 k hst
        obtain ⟨k', hr'⟩ := hsimInl3.forward k (by rw [heq]; exact hk)
        exact ⟨k', heq ▸ hr'⟩
    timeout := fun k hk =>
      hsimInl3.timeout k ((stage12 _ (by rw [hk]; intro h; cases h)).trans hk) }

/-- Reuse the exact admission already obtained by initialization. Successful
deterministic consumption identifies the intermediate program receipt. -/
theorem admitted_root_eval_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered)
    (root : Nat) (hroot : root < P.base.size)
    (words : List Lir.Word) (memory : X86.Memory) (context : Lir.Word) :
    Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) root)
        clock words memory context)
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := by
  obtain ⟨pairs', functions', admission', transfer⟩ :=
    accepted_root_eval_stages admission.scopedProgram accepted
  have same : pairs' = pairs := Except.ok.inj (admission'.consuming.symm.trans admission.consuming)
  subst pairs'
  exact transfer root hroot words memory context


end IxCC.Cfg.Rc.Native.Spec
