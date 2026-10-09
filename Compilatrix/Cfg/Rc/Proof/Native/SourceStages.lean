import Compilatrix.Cfg.Rc.Proof.Native.RawSource

/-! Actual accepted public output is reached through source-only pruning,
source-only splitting and the final whole-program split. The composed relation
preserves memory, results and clock charges. It does not assume the missing
source-to-physical execution theorem. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Public.Spec
open Native.Spec

def sourceStageRel (config : Rt.Config) (P : Program) (pairs : List (Nat × Cfg.Fun))
    (funcs : List Lir.Func) (main : Nat) (source target : Lir.State) : Prop :=
  ∃ pruned, Lir.StateRel (sourcePruneLabels P pairs) source pruned ∧
    ∃ split, Lir.StateRel (sourceSplitLabels config P pairs) pruned split ∧
      Lir.StateRel (labels (rawPublicProgram (layoutOf P) funcs main)) split target

theorem accepted_source_stages {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs funcs,
      consumeAll P = .ok pairs ∧
      Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
        (List.range P.base.size) = .ok funcs ∧
      funcs.length = P.base.size ∧
      Sem.LockStep (Lir.semStep (sourceStage P (rawSource config P pairs) main))
        (Lir.semStep lowered.runtime.program) (sourceStageRel config P pairs funcs main) := by
  obtain ⟨main, pairs, funcs, consuming, lowering, length, _, split⟩ := accepted_split accepted
  refine ⟨main, pairs, funcs, consuming, lowering, length, ?_⟩
  exact (source_raw_pruned lowering main).lockStep.comp
    ((source_pruned_split lowering main).lockStep.comp split.lockStep)

theorem sourceStageRel_memory {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func} {main : Nat}
    {source target : Lir.State} (related : sourceStageRel config P pairs funcs main source target) :
    target.mem = source.mem ∧ target.ctx = source.ctx := by
  obtain ⟨pruned, first, split, second, third⟩ := related
  exact ⟨third.1.trans (second.1.trans first.1), third.2.1.trans (second.2.1.trans first.2.1)⟩



end Compilatrix.Cfg.Rc.Public.Spec
