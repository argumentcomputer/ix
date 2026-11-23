import IxCC.Cfg.Rc.Proof.Native.SourceStages

/-! Initialize the actual three-stage label relation from native function
entry. The same arguments and memory reach the accepted public runtime;
complete non-stuck executions then transfer at the same clock and result. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public.Spec
open Native.Spec

theorem accepted_source_entry {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    {borrows : Own.Plain.BorrowSigs}
    (accepted : Public.lower config F bodies P borrows = .ok lowered) :
    ∃ main pairs funcs,
      consumeAll P = .ok pairs ∧
      Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
        (List.range P.base.size) = .ok funcs ∧
      funcs.length = P.base.size ∧
      ∀ (f : Nat) (words : List Lir.Word) (source : Lir.Frame),
        Lir.enter (sourceStage P (rawSource config P pairs) main) f words = some source →
        ∃ target, Lir.enter (rawPublicProgram (layoutOf P) funcs main) f words = some target ∧
          ∀ (mem : X86.Memory) (context : Lir.Word),
            sourceStageRel config P pairs funcs main
              {mem, ctx := context, stack := [source]}
              {mem, ctx := context, stack := [target]} ∧
            ∀ clock outcome,
              Sem.Reaches (Lir.semStep (sourceStage P (rawSource config P pairs) main))
                {mem, ctx := context, stack := [source]} clock outcome →
              outcome ≠ .stuck →
              Sem.Reaches (Lir.semStep (rawPublicProgram (layoutOf P) funcs main))
                {mem, ctx := context, stack := [target]} clock outcome := by
  obtain ⟨main, pairs, funcs, consuming, lowering, length, _, _⟩ := accepted_split accepted
  have pruning := source_raw_pruned lowering main
  have sourceSplitting := source_pruned_split lowering main
  have lock : Sem.LockStep
      (Lir.semStep (sourceStage P (rawSource config P pairs) main))
      (Lir.semStep (rawPublicProgram (layoutOf P) funcs main)) (sourceStageRel config P pairs funcs main) :=
    pruning.lockStep.comp sourceSplitting.lockStep
  refine ⟨main, pairs, funcs, consuming, lowering, length, ?_⟩
  intro f words source entered
  obtain ⟨pruned, enteredPruned, first⟩ := pruning.enter entered
  obtain ⟨target, enteredTarget, second⟩ := sourceSplitting.enter enteredPruned
  refine ⟨target, enteredTarget, ?_⟩
  intro mem context
  have related : sourceStageRel config P pairs funcs main
      {mem, ctx := context, stack := [source]} {mem, ctx := context, stack := [target]} :=
    ⟨{mem, ctx := context, stack := [pruned]}, ⟨rfl, rfl, .cons first .nil⟩,
      ⟨rfl, rfl, .cons second .nil⟩⟩
  exact ⟨related, fun _ _ reaches regular => lock.reaches reaches regular related⟩


end IxCC.Cfg.Rc.Public.Spec
