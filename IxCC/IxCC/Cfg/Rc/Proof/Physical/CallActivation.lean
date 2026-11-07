import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Physical.CallResume
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.CopyState
import IxCC.Cfg.Rc.Proof.Physical.StateEnvironments
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.CallStep
import IxCC.Own.Plain.Proof.TailCall

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Execute the canonical copies and actual non-tail call. Callee bounds,
arity, code, scope, and entry all come from the checked source program.
The suspended caller retains its lexical joins and its whole Cfg map. -/
theorem call_activation {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs) (main : Nat)
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {x f : Nat} {args : List Fir.Arg} {cont : Fir.Code} {sourceFunction : Fir.Fun}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs
      (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
      (holdRoots external held) live ρf ρo roots joins Jf Jo (.bind x (.call f args) cont)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external (roots ++ held)
      context base bump limit regionBytes slots lists)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    (∃ calleeSource fields logical copied mem', ∃ middle : Lir.Frame,
      ∃ sourceTail saved targetEnv offset originalFd block consumedFd,
      F.fun? f = some calleeSource ∧
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies args) = .ok copied ∧
      copied.size = H.size ∧ (∀ value, H.value? value = copied.value? value) ∧
      Own.Plain.State (Own.Plain.signatures F) copied (holdRoots external (fields ++ held))
        live ρf ρo roots joins Jf Jo ∧
      FrameState P pairs lp addresses copied.size sourceFunction.vars function
        {source with rest := sourceTail} saved ∧ saved.dsts = [x] ∧
      (∀ value, At F P {source with rest := sourceTail, env := source.env.insert x value}
        (ρo.insert x value) Jo (Own.Plain.lowerCode (live ++ [x]) joins cont)) ∧
      (∀ value block, function.blocks[source.blk]? = some block →
        Rt.Proof.FusedDone (tablesOf P pairs) function block
          {source with rest := sourceTail, env := source.env.insert x value}) ∧
      x ∉ live ∧ x < sourceFunction.vars ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities Jf) cont = true ∧
      P.base.fun? f = some originalFd ∧ originalFd.blocks[0]? = some block ∧
      Activation F P pairs lp copied addresses (holdRoots external (roots ++ held))
        (calleeSource.params.map Prod.fst)
        (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical)
        (Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields) fields [] [] []
        calleeSource.body calleeSource.vars consumedFd
        {fn := f, blk := 0, rest := block.body,
          env := Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields}
        {fn := f, label := offset, pos := 0, env := targetEnv} ∧
      HeapState P pairs copied addresses mem' external (fields ++ (roots ++ held))
        context base bump limit regionBytes slots lists ∧
      HeapState P pairs copied addresses mem' (holdRoots external (roots ++ held)) fields
        context base bump limit regionBytes slots lists ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers}
        (2 * (Own.Plain.copies args).length + 1)
        (Lir.atState mem' context f offset 0 targetEnv (saved :: callers)) ∧
      step P (.run {source with rest := .bind x (.fir (.call f args)) :: sourceTail}
        sourceCallers copied) =
        .next (.call f fields (({source with rest := sourceTail}, x) :: sourceCallers) copied) false ∧
      step P (.call f fields (({source with rest := sourceTail}, x) :: sourceCallers) copied) =
        .next (.run {
          fn := f
          blk := 0
          rest := block.body
          env := Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields }
          (({source with rest := sourceTail}, x) :: sourceCallers) copied) true ∧
      saved = {middle with pos := middle.pos + 1, dsts := [x]}) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  have scopeParts : x ∉ live ∧
      ((Own.Plain.signatures F).lookup f = some args.length ∧ args.all (Own.Plain.argIn live) = true) ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities Jf) cont = true := by
    simpa [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨calleeSource, sourceRange, calleeLookup, calleeArity⟩ :=
    Own.Plain.signatures_lookup scopeParts.2.1.1
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have range : f < P.base.size := by simpa only [programSize] using sourceRange
  have initialLayout : At F P source ρo Jo (Own.Plain.actionPrefix (Own.Plain.copies args)
      (.bind x (.call f args) (Own.Plain.lowerCode (live ++ [x]) joins cont))) := before.layout
  obtain ⟨first, tail, head, callLayout, absent⟩ :=
    checked_prefix_cursor checked initialLayout sourceLookup before.frame.words
  have ordinary : reserved P.base.size (.bind x (.fir (.call f args))) = false := by
    simp [reserved, show f ≠ P.base.size by omega, show f ≠ P.base.size + 1 by omega]
  have destination := checked_bind_real checked callLayout sourceLookup ordinary
  have lexical := before.lexical.1
  rcases copy_prefix_state (Public.Spec.rawSource config P pairs) main args before.frame.cursor
      head before.frame.lookup (state_extend before.canonical lexical) scopeParts.2.1.2
      heap.ready before.frame.words absent before.running callers with success | failure
  · obtain ⟨fields, copied, mem', middle, frameArgs, actions, framedState, ready, trace₁,
      cursor, words₁, running, preserved⟩ := success
    have size := actions_size actions
    obtain ⟨original, logical, originalArgs, sourceArgs, den⟩ :=
      Own.Plain.args_den before.canonical.env args scopeParts.2.1.2
    have equal : original = fields := Option.some.inj
      ((Cfg.Proof.evalArgs_sub lexical originalArgs).symm.trans frameArgs)
    subst original
    have copies : Own.Plain.evalActions ρo H (Own.Plain.copies args) = .ok copied := by
      rw [copies_eval_sub lexical (Tokens.present (Tokens.ofState before.canonical))
        args scopeParts.2.1.2 H]
      exact actions
    have suspendedState : Own.Plain.State (Own.Plain.signatures F) copied
        (holdRoots external (fields ++ held)) live ρf ρo roots joins Jf Jo :=
      ⟨before.canonical.env.transport before.canonical.roots (fun value _ => preserved value),
        before.canonical.roots, framedState.counts, before.canonical.distinct,
        before.canonical.stack.transport (fun value _ => preserved value),
        before.canonical.views, before.canonical.scope⟩
    have balance : Balance copied (holdRoots external (roots ++ held)) fields := by
      intro location
      have counted := framedState.counts location
      simp only [holdRoots, refsIn_append] at counted ⊢
      omega
    have ready' : AllocatorReady copied addresses mem' (holdRoots external (fields ++ (roots ++ held)))
        context base bump limit slots lists := by
      have rearrange : holdRoots external (roots ++ (fields ++ held)) =
          holdRoots external (fields ++ (roots ++ held)) := by
        funext location
        simp only [holdRoots, refsIn_append]
        omega
      rw [← rearrange]
      exact ready
    have nested : holdRoots external (fields ++ (roots ++ held)) =
        holdRoots (holdRoots external (roots ++ held)) fields := by
      funext location
      simp only [holdRoots, refsIn_append]
      omega
    have finalHeap : HeapState P pairs copied addresses mem' external (fields ++ (roots ++ held))
        context base bump limit regionBytes slots lists :=
      ⟨ready', actions_heapOk heap.ordered actions, heap.compatible.evalActions actions, heap.extent⟩
    have calleeHeap : HeapState P pairs copied addresses mem' (holdRoots external (roots ++ held)) fields
        context base bump limit regionBytes slots lists :=
      ⟨by rw [← nested]; exact ready', finalHeap.ordered, finalHeap.compatible, heap.extent⟩
    obtain ⟨sourceTail, callHead, resume⟩ := callLayout.bind_continuation
    have head' : ({source with rest := tail} : Cfg.Frame).rest =
        .bind x (.fir (.call f args)) :: sourceTail := callHead
    rcases cursor.call head' (consume_user_call range) mem' context callers with called | failure
    · obtain ⟨operands, nativeFunction, output, operandsLowered, functionLookup,
        outputLookup, position, statement, continuation⟩ := called
      have liveArgs := consumed_call_live cursor head' (consume_user_call range) before.frame.lookup
      obtain ⟨argumentWords, evaluated, represented, _⟩ :=
        fused_operands_words words₁ operandsLowered liveArgs frameArgs
      have compatible := before.frame.compatible.args liveArgs frameArgs
      have arity : fields.length = calleeSource.params.length :=
        (Own.evalArgs_length ρo originalArgs).trans calleeArity.symm
      let saved : Lir.Frame := {middle with pos := middle.pos + 1, dsts := [x]}
      obtain ⟨fd, block, consumedFd, callee, targetEnv, offset, lookup, blockLookup,
        entered, traceEntry, sourceEntry, activation⟩ :=
        entry_activation checked consuming lowered main calleeLookup
          (Own.Plain.dens_transport den (fun value _ => preserved value)) balance represented
          compatible arity (({source with rest := sourceTail}, x) :: sourceCallers)
          mem' context (saved :: callers)
      have calledStep := Lir.step_call (mem := mem') (ctx := context) (rest := callers)
        functionLookup outputLookup position statement evaluated entered
      have trace₂ := (Lir.star_of_step calledStep).trans traceEntry
      have savedFrame : FrameState P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
          addresses copied.size sourceFunction.vars function {source with rest := sourceTail} saved :=
        ⟨before.frame.lookup, continuation.withEnvs source.env middle.env [x], words₁,
          by rw [size]; exact before.frame.bounded, before.frame.compatible⟩
      have fused : ∀ value block, function.blocks[source.blk]? = some block →
          Rt.Proof.FusedDone (tablesOf P pairs) function block
            {source with rest := sourceTail, env := source.env.insert x value} :=
        fun value => consumed_call_done (source := {source with rest := tail})
          before.frame.lookup cursor head' (consume_user_call range)
          (source.env.insert x value)
      have sourceCall : step P
          (.run {source with rest := .bind x (.fir (.call f args)) :: sourceTail} sourceCallers copied) =
          .next (.call f fields (({source with rest := sourceTail}, x) :: sourceCallers) copied) false := by
        rw [step_ordinary rfl ordinary]
        exact Cfg.Proof.step_run_call rfl frameArgs
      refine .inl ⟨calleeSource, fields, logical, copied, mem', middle, sourceTail, saved,
        targetEnv, offset, fd, block, consumedFd, calleeLookup, originalArgs, sourceArgs,
        copies, size, preserved, suspendedState, savedFrame, rfl, resume, fused, scopeParts.1, destination,
        scopeParts.2.2, lookup, blockLookup, activation, finalHeap, calleeHeap,
        ?_, sourceCall, sourceEntry, rfl⟩
      exact trace₁.trans trace₂
    · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
      have same : Lir.atState mem' context middle.fn middle.label middle.pos middle.env callers =
          {mem := mem', ctx := context, stack := middle :: callers} := by
        cases middle
        simp_all [Lir.atState]
      rw [same] at trace₂
      exact .inr ⟨2 * (Own.Plain.copies args).length + cost, terminal, resource,
        trace₁.trans trace₂, failed⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native.Spec
