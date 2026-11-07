import IxCC.Cfg.Rc.Proof.Physical.CallActivation
import IxCC.Cfg.Rc.Proof.Physical.ResumeActivation
import IxCC.Cfg.Rc.Proof.Physical.TailResult
import IxCC.Cfg.Rc.Proof.Native.CodeRecursion

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

/-- The non-tail call clause applies the recursive physical claim only at a
strictly smaller source clock, then the fixed caller continuation at its
original clock. All copies, actual call/return steps, ownership changes and
callee heap history are concrete operation receipts. -/
theorem call_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main clock : Nat)
    (smaller : ∀ next, next < clock → PhysicalAtClock F P config pairs main next)
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {x f : Nat} {args : List Fir.Arg} {cont : Fir.Code} {sourceFunction : Fir.Fun}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs
      (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
      external live ρf ρo roots joins Jf Jo (.bind x (.call f args) cont)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame)
    (next : PhysicalCode F P config pairs main clock Jf cont) :
    ResultAt P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external context base limit regionBytes clock
      {mem, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock ρf Jf (.bind x (.call f args) cont)) := by
  have initialHeap : HeapState P pairs H addresses mem external (roots ++ [])
      context base bump limit regionBytes slots lists := by
    simpa only [List.append_nil] using heap
  rcases call_activation admission.scopedProgram admission.consuming admission.lowering main
      (external := external) (held := []) before sourceLookup initialHeap [] callers with success | failed
  · obtain ⟨callee, fields, logical, copied, mem', middle, sourceTail, saved, targetEnv, offset,
      fd, block, consumedFd, calleeLookup, ownArgs, sourceArgs, actions, size, copies,
      copiedState, savedFrame, destination, savedLayout, fused, fresh, real, scope,
      fdLookup, blockLookup, activation, globalHeap, calleeHeap, trace, sourceCall, sourceEntry, savedEq⟩ := success
    have scopeParts : x ∉ live ∧
        ((Own.Plain.signatures F).lookup f = some args.length ∧ args.all (Own.Plain.argIn live) = true) ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities Jf) cont = true := by
      simpa [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc] using before.scope
    have arity := source_call_arity scopeParts.2.1.1 calleeLookup sourceArgs
    rw [Fir.eval_bindCall, sourceArgs]
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
    rw [Fir.evalCall_of F clock calleeLookup logical]
    unfold Fir.callFun
    rw [if_pos arity]
    cases clock with
    | zero =>
      simp only [Sem.later_zero, Sem.Result.bind]
      exact .inl (Sem.Reaches.timeout_of_star trace (by omega))
    | succ smallerClock =>
      simp only [Sem.later_succ]
      let calleeCfg : Cfg.Frame := {
        fn := f
        blk := 0
        rest := block.body
        env := Own.bindAll .leaf (callee.params.map Prod.fst) fields }
      let calleeNative : Lir.Frame := {fn := f, label := offset, pos := 0, env := targetEnv}
      have execution := smaller smallerClock (Nat.lt_succ_self _) copied addresses
        (holdRoots external (roots ++ [])) (callee.params.map Prod.fst)
        (Fir.bindAll .leaf (callee.params.map Prod.fst) logical)
        (Own.bindAll .leaf (callee.params.map Prod.fst) fields) fields [] [] [] callee.body
        callee consumedFd calleeCfg calleeNative mem' context base bump limit regionBytes slots lists
        (saved :: callers) calleeLookup activation calleeHeap
      cases result : Fir.eval F smallerClock (Fir.bindAll .leaf (callee.params.map Prod.fst) logical)
          [] callee.body with
      | ok value =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        rcases execution with ⟨returned, calleeCost, calleeTrace⟩ | failed
        · obtain ⟨returnStep, resumed, resumedHeap, finalGlobalHeap, preserved, history⟩ :=
            resume_activation (external := external) (held := []) before.canonical size copies
              savedFrame destination real savedLayout fused fresh scope returned callers
          let finalSource : Cfg.Frame :=
            {source with rest := sourceTail, env := source.env.insert x returned.value}
          let finalTarget : Lir.Frame :=
            {saved with env := saved.env.insert x returned.word, dsts := []}
          have continuation := next returned.heap returned.addresses external (live ++ [x])
            (ρf.insert x value) (ρo.insert x returned.value) (roots ++ [returned.value]) joins Jo
            sourceFunction function finalSource finalTarget returned.memory context base returned.bump limit
            regionBytes returned.slots returned.lists callers sourceLookup resumed resumedHeap
          have allTrace := trace.trans (calleeTrace.trans (Lir.star_of_step returnStep))
          exact ResultAt.prefix allTrace preserved history (by omega) continuation
        · exact ResultAt.of_fails (fails_prefix trace failed)
      | timeout =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        exact Sem.Forward.TimeoutOrFail.star trace fun enough => execution.down (by omega)
      | resource resource =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        exact fails_prefix trace execution
      | trap =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        rcases execution with ⟨cost, terminal, calleeTrace, trapped⟩ | failed
        · exact .inl ⟨2 * (Own.Plain.copies args).length + 1 + cost, terminal,
            trace.trans calleeTrace, trapped⟩
        · exact .inr (fails_prefix trace failed)
      | stuck => trivial
  · exact ResultAt.of_fails failed


end IxCC.Cfg.Rc.Native.Spec
