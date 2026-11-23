import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Fir.Proof.Unfold

/-! The entry of a run over the typing context. The source's call of a function costs one clock
unit; the native entry has already bound the arguments, so source `clock + 1` corresponds to
native `clock`. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx)

theorem entry_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {main clock : Nat} (complete : PhysicalAtClock F P config pairs main clock borrows bodies uniqs)
    {f : Nat} {sourceFunction : Fir.Fun} (sourceLookup : F.fun? f = some sourceFunction)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
    (den : Sem.Forall2 (Own.Proof.Den H) values logical)
    (balance : Own.Rc.Balance H external (Own.Plain.selectOwnedVals (borrows.getD f []) values))
    (hbrw : ∀ v, v ∈ Own.Plain.selectBorrowedVals (borrows.getD f []) values →
      Own.Plain.ReachableFrom H external v)
    (huniq : ∀ v, v ∈ Own.Plain.selectUniqueVals (borrows.getD f []) (uniqs.getD f ([], false)).1 values →
      Own.Plain.UniqVal F.ctors H external (Own.Plain.selectOwnedVals (borrows.getD f []) values) v)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external
      (Own.Plain.selectOwnedVals (borrows.getD f []) values)
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    ∃ callee, Lir.enter lp f words = some callee ∧
      ResultAt P pairs lp H addresses external context base limit regionBytes clock
        {mem := memory, ctx := context, stack := callee :: callers} callers
        (Fir.evalCall F (clock+1) f logical) := by
  dsimp only
  obtain ⟨fd, block, consumedFd, callee, targetEnv, offset, code, lookup, blockLookup, erased,
    entered, trace, sourceStep, activation⟩ := entry_activation admission.scopedProgram
      admission.consuming admission.lowering main sourceLookup den balance hbrw huniq
      (fun _ h => False.elim h) (fun _ h => False.elim h) (fun _ h => False.elim h)
      represented compatible arity [] memory context callers
  have body := complete [] code H addresses external (uniqs.getD f ([], false)).2 (fun _ => False)
    .leaf [] (sourceFunction.params.map Prod.fst)
    (Ctx.entryWith (sourceFunction.params.map Prod.fst) (borrows.getD f []) (uniqs.getD f ([], false)).1) .leaf
    (Fir.bindAll .leaf (sourceFunction.params.map Prod.fst) logical)
    (Own.bindAll .leaf (sourceFunction.params.map Prod.fst) values)
    (Own.Plain.selectOwnedVals (borrows.getD f []) values) [] [] sourceFunction
    consumedFd
    {fn := f, blk := 0, rest := block.body, env := Own.bindAll .leaf (sourceFunction.params.map Prod.fst) values}
    {fn := f, label := offset, pos := 0, env := targetEnv}
    memory context base bump limit regionBytes slots lists callers sourceLookup activation
    (by simpa only [List.append_nil] using heap)
  rw [erased] at body
  refine ⟨callee, entered, ?_⟩
  have sourceArity : logical.length = sourceFunction.params.length := den.length.symm.trans arity
  rw [Fir.evalCall_of F (clock+1) sourceLookup, Fir.callFun, if_pos sourceArity]
  simp only [Sem.later]
  exact ResultAt.weaken (fun h => by cases h) (fun _ h => False.elim h)
    (ResultAt.prefix trace (Own.Plain.ReachablePreserved.refl H external)
      (Own.Plain.PrivPreserved.refl (fun _ h => False.elim h))
      (HeapHistory.refl _ _) (by omega) body)

theorem main_entry_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {main clock : Nat} (complete : PhysicalAtClock F P config pairs main clock borrows bodies uniqs)
    {sourceFunction : Fir.Fun} (sourceLookup : F.fun? main = some sourceFunction)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
    (den : Sem.Forall2 (Own.Proof.Den H) values logical)
    (balance : Own.Rc.Balance H external (Own.Plain.selectOwnedVals (borrows.getD main []) values))
    (hbrw : ∀ v, v ∈ Own.Plain.selectBorrowedVals (borrows.getD main []) values →
      Own.Plain.ReachableFrom H external v)
    (huniq : ∀ v, v ∈ Own.Plain.selectUniqueVals (borrows.getD main []) (uniqs.getD main ([], false)).1 values →
      Own.Plain.UniqVal F.ctors H external (Own.Plain.selectOwnedVals (borrows.getD main []) values) v)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = sourceFunction.params.length)
    {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external
      (Own.Plain.selectOwnedVals (borrows.getD main []) values)
      context base bump limit regionBytes slots lists) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    ∃ callee, Lir.State.initial lp words memory context =
        some {mem := memory, ctx := context, stack := [callee]} ∧
      ResultAt P pairs lp H addresses external context base limit regionBytes clock
        {mem := memory, ctx := context, stack := [callee]} [] (Fir.run F (clock+1) main logical) := by
  dsimp only
  obtain ⟨callee, entered, execution⟩ := entry_result admission complete sourceLookup den balance
    hbrw huniq represented compatible arity heap []
  refine ⟨callee, ?_, execution⟩
  change (Lir.enter (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) main words).bind
    (fun frame => some ({mem := memory, ctx := context, stack := [frame]} : Lir.State)) = _
  rw [entered]
  rfl

end IxCC.Cfg.Rc.Native.Spec
