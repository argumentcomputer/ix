import IxCC.Cfg.Rc.Proof.Physical.PublicEval

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

theorem inlinedPublicProgram_main_upd (l : Layout) (funcs : List Lir.Func) (main target : Nat) :
    Public.Spec.inlinedPublicProgram l funcs target =
      { Public.Spec.inlinedPublicProgram l funcs main with main := target } := by
  have hraw : rawProgram l funcs target = { rawProgram l funcs main with main := target } := rfl
  have h1 : ∀ p, Inline.inlineProgram l { p with main := target } =
      { Inline.inlineProgram l p with main := target } := fun _ => rfl
  have h2 : ∀ p, Prune.pruneUnusedReuse l { p with main := target } =
      { Prune.pruneUnusedReuse l p with main := target } := fun _ => rfl
  have h3 : ∀ p, InlineWrappers.inlineProgram l { p with main := target } =
      { InlineWrappers.inlineProgram l p with main := target } := fun _ => rfl
  have h4 : ∀ p, FastDec.install l { p with main := target } =
      { FastDec.install l p with main := target } := fun _ => rfl
  have h5 : ∀ p, Prune.pruneDeadRuntime l { p with main := target } =
      { Prune.pruneDeadRuntime l p with main := target } := fun _ => rfl
  unfold Public.Spec.inlinedPublicProgram inlinedProgram
  rw [hraw, h1, h2, h3, h4, h5]

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
  obtain ⟨main, pairs, functions, _, switches, entry, hok, consuming, lowering, length, program, _⟩ :=
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
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions main)) := by
    rw [inlinedPublicProgram_main_upd (layoutOf P) functions main root]
    exact ⟨rfl, split.funcs⟩
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
        clock words memory context) :=
    sim_raw_to_inlined length hok hroot splitEq words memory context
  have hsimInl3 : Sem.Sim Eq (Inline.inlineClock lowered.runtime.program)
      (fun clock => Lir.eval (Public.Spec.rawPublicProgram (layoutOf P) functions root)
        clock words memory context)
      (fun clock => Lir.eval {lowered.runtime.program with main := root} clock words memory context) := {
    forward := fun k hk => by
      obtain ⟨k', hr'⟩ := hsimInl.forward k hk
      by_cases hst : Lir.eval (Public.Spec.inlinedPublicProgram (layoutOf P) functions root)
          k' words memory context = .stuck
      · rw [hst] at hr'
        exact ⟨0, by rw [hr'.of_stuck]; exact .stuck⟩
      · have htr := program_eval_transfer splitRoot k' words memory context hst
        exact ⟨k', by rw [htr]; exact hr'⟩
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
