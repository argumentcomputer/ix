import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Physical.TailCall
import IxCC.Cfg.Rc.Proof.Physical.SelfEntry
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.TransferPrefix
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.Physical.TokenEnvironments
import IxCC.Own.Plain.Proof.Results

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Canonical tail transfer executes all copies and cleanup, then replaces
the actual active native frame with a fully checked callee activation.
Older callers remain literal stack entries throughout the finite trace. -/
theorem tail_activation {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs) (main : Nat)
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {f : Nat} {args : List Fir.Arg} {sourceFunction : Fir.Fun}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs
      (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
      external live ρf ρo roots joins Jf Jo (.tcall f args)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots
      context base bump limit regionBytes slots lists)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    (∃ calleeSource fields logical afterHeap mem' slots' lists' consumedFd after final cost,
      F.fun? f = some calleeSource ∧
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies args ++ Own.Plain.drops [] live) = .ok afterHeap ∧
      afterHeap.size = H.size ∧ Own.Plain.ExternalPreserved H afterHeap external ∧
      HeapHistory H.size addresses afterHeap.size addresses ∧
      Activation F P pairs lp afterHeap addresses external (calleeSource.params.map Prod.fst)
        (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical)
        (Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields) fields [] [] []
        calleeSource.body calleeSource.vars consumedFd after final ∧ after.fn = f ∧
      HeapState P pairs afterHeap addresses mem' external fields
        context base bump limit regionBytes slots' lists' ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem := mem', ctx := context, stack := final :: callers} ∧ 1 ≤ cost) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  have scope : (Own.Plain.signatures F).lookup f = some args.length ∧
      args.all (Own.Plain.argIn live) = true := by
    simpa [Own.Plain.scopeOk, Bool.and_eq_true] using before.scope
  obtain ⟨calleeSource, calleeRange, calleeLookup, calleeArity⟩ := Own.Plain.signatures_lookup scope.1
  obtain ⟨originalFields, logical₀, originalArgs, sourceArgs₀, originalDen⟩ :=
    Own.Plain.args_den before.canonical.env args scope.2
  have lexical := before.lexical.1
  have prefixLayout : At F P source ρo Jo (Own.Plain.actionPrefix
      (Own.Plain.copies args ++ Own.Plain.drops [] live) (.tcall f args)) := before.layout
  obtain ⟨first, tail, head, tailLayout, absent⟩ :=
    checked_prefix_cursor checked prefixLayout sourceLookup before.frame.words
  have entryLayout := tailLayout
  obtain ⟨fd, scopeNames, params, acc, next, supply, low, lookup, sourceRange, layout, cursor,
    sub, below, names, saved⟩ := tailLayout
  have tailEmpty : tail = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  subst tail
  let sourceBlock : Cfg.Block := {params, body := acc.reverse, term := Cfg.Proof.tcallTerm source.fn f args}
  have blockLookup : fd.blocks[source.blk]? = some sourceBlock := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using sourceRange
  have initialTokens := Tokens.extend
    (Tokens.ofState (external := external) (held := []) before.canonical) lexical
  have initialReady : AllocatorReady H addresses mem (holdRoots external (roots ++ []))
      context base bump limit slots lists := by simpa only [List.append_nil] using heap.ready
  rcases transfer_prefix (Public.Spec.rawSource config P pairs) main args [] live before.frame.cursor
      head before.frame.lookup initialTokens scope.2 initialReady before.frame.words absent
      before.running callers with success | failure
  · obtain ⟨fields, logical, kept, afterHeap, mem', slots', lists', final, cost,
      frameArgs, sourceArgs, actions, tokens, den, ready, trace₁, afterCursor, words,
      running, subset, preserved, externalPreserved⟩ := success
    have fieldsEqual : originalFields = fields :=
      Option.some.inj ((Cfg.Proof.evalArgs_sub lexical originalArgs).symm.trans frameArgs)
    subst originalFields
    have keptEmpty : kept = [] := by
      have exactRoots := tokens.exactRoots
      have noRetained : Own.Plain.retained [] live = [] := by simp [Own.Plain.retained]
      simpa only [Own.Plain.EnvRoots, noRetained, List.map_nil, Own.evalArgs,
        Option.some.injEq] using exactRoots.symm
    subst kept
    have effect : Own.Plain.evalActions ρo H
        (Own.Plain.copies args ++ Own.Plain.drops [] live) = .ok afterHeap := by
      rw [transfer_eval_sub [] live lexical
        (Tokens.present (Tokens.ofState (external := external) (held := []) before.canonical))
        args scope.2 H]
      exact actions
    have balance : Balance afterHeap external fields := by
      apply balance_unhold
      simpa only [List.append_nil] using tokens.balance
    have size := actions_size actions
    have finalHeap : HeapState P pairs afterHeap addresses mem' external fields
        context base bump limit regionBytes slots' lists' :=
      ⟨by simpa only [List.nil_append, List.append_nil] using ready,
        actions_heapOk heap.ordered actions, heap.compatible.evalActions actions, heap.extent⟩
    have externalValues : Own.Plain.ExternalPreserved H afterHeap external := by
      intro value logical externalRoot den
      change afterHeap.value? value = some logical
      rw [← externalPreserved value externalRoot]
      exact den
    have history : HeapHistory H.size addresses afterHeap.size addresses :=
      ⟨by omega, fun _ _ => rfl⟩
    have arity : fields.length = calleeSource.params.length :=
      (Own.evalArgs_length ρo originalArgs).trans calleeArity.symm
    by_cases self : f = source.fn
    · subst f
      have sameCallee : calleeSource = sourceFunction := Option.some.inj (calleeLookup.symm.trans sourceLookup)
      subst calleeSource
      have afterFrame : FrameState P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
          addresses afterHeap.size sourceFunction.vars function {source with rest := []} final :=
        ⟨before.frame.lookup, afterCursor, words, by rw [size]; exact before.frame.bounded,
          before.frame.compatible⟩
      rcases self_entry_activation checked consuming (source := {source with rest := []})
          sourceLookup entryLayout afterFrame originalArgs den balance arity running
          mem' context sourceCallers callers with entered | failure
      · obtain ⟨after, final', edgeCost, activation, sameFn, trace₂, charged⟩ := entered
        exact .inl ⟨sourceFunction, fields, logical, afterHeap, mem', slots', lists', function,
          after, final', cost + edgeCost, sourceLookup, originalArgs, sourceArgs, effect, size,
          externalValues, history, activation, sameFn, finalHeap, trace₁.trans trace₂, by omega⟩
      · obtain ⟨charges, terminal, resource, trace₂, failed⟩ := failure
        exact .inr ⟨cost + charges, terminal, resource, trace₁.trans trace₂, failed⟩
    have terminal : sourceBlock.term = .tcall f args := by
      simp [sourceBlock, Cfg.Proof.tcallTerm, self]
    obtain ⟨original, actual, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming nativeRange
    have sameOriginal : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
    subst original
    have sameActual : actual = function := Option.some.inj (consumedLookup.symm.trans before.frame.lookup)
    subst actual
    obtain ⟨consumedBody, consumedBodyEq, consumedBlock⟩ :=
      (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
    have argsLive : ∀ arg ∈ args, Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg :=
      fused_term_live consumedBlock (fun x member => by
        simp only [Rt.Proof.otherUses, List.mem_append]
        exact .inr (by simpa [sourceBlock, Cfg.Proof.tcallTerm, self, Cfg.Check.termVars]
          using Rt.Proof.argVars_of_mem member))
    have compatible := before.frame.compatible.args argsLive frameArgs
    obtain ⟨rest, consumeRest, position⟩ := afterCursor
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
    subst rest
    rcases position.tail_receipt before.frame.lookup consumedBlock rfl terminal words frameArgs
        running mem' context callers with success | failure
    · obtain ⟨argumentWords, nativeFunction, output, operands, represented, functionLookup,
        outputLookup, pos, term, evaluated⟩ := success
      obtain ⟨originalFd, block, consumedFd, callee, targetEnv, offset, calleeCfgLookup,
        calleeBlockLookup, entered, traceEntry, sourceEntry, activation⟩ :=
        entry_activation checked consuming lowered main calleeLookup den balance represented
          compatible arity sourceCallers mem' context callers
      have called := Lir.step_tail (mem := mem') (ctx := context) (rest := callers)
        functionLookup outputLookup pos term evaluated entered
      have trace₂ := (Lir.star_of_step called).trans traceEntry
      exact .inl ⟨calleeSource, fields, logical, afterHeap, mem', slots', lists', consumedFd,
        _, _, cost + 1, calleeLookup, originalArgs, sourceArgs, effect, size, externalValues,
        history, activation, rfl, finalHeap, trace₁.trans trace₂, by omega⟩
    · obtain ⟨charges, terminal, resource, trace₂, failed⟩ := failure
      exact .inr ⟨cost + charges, terminal, resource, trace₁.trans trace₂, failed⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native.Spec
