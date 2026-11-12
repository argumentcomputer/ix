import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Physical.SelfEntry
import IxCC.Cfg.Rc.Proof.Physical.TailCall
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Owned.Takes
import IxCC.Fir.Proof.Unfold

/-! A tail call over the typing context: the checker took the arguments' tokens and found none
left (`closed`), so the arguments' values are exactly the path's roots and every token goes to the
callee. No action prefix and no heap change before the jump: a tail call to another function
replaces the frame (`entry_activation`), a tail call to the function itself re-enters block zero
(`self_entry_activation`). The callee runs at a strictly smaller source clock. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

theorem source_call_arity {F : Fir.Program} {f : Nat} {args : List Fir.Arg}
    (signature : (Own.Plain.signatures F).lookup f = some args.length)
    {callee : Fir.Fun} (lookup : F.fun? f = some callee)
    {env : Fir.Env} {logical : List Fir.Val} (arguments : Fir.evalArgs env args = some logical) :
    logical.length = callee.params.length := by
  obtain ⟨actual, _, actualLookup, arity⟩ := Own.Plain.signatures_lookup signature
  have same : actual = callee := Option.some.inj (actualLookup.symm.trans lookup)
  subst actual
  exact (Fir.evalArgs_length env arguments).trans arity.symm

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **A tail call**: the callee runs at a strictly smaller source clock. -/
theorem tail_result (admission : CodeAdmission F bodies P config pairs functions)
    (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k)
    {f : Fir.FunId} {args : List Fir.Arg} :
    PhysicalCode F P config pairs main clock sourceJoins (.tcall f args) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins (.tcall f args))
  have scope : (Own.Plain.signatures F).lookup f = some args.length ∧
      args.all (Own.Plain.argIn live) = true := by
    simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true] using before.scope
  obtain ⟨calleeSource, calleeRange, calleeLookup, calleeArity⟩ :=
    Own.Plain.signatures_lookup scope.1
  obtain ⟨Γ', taken, closed⟩ := Own.Plain.checkCode_tcall before.typed
  obtain ⟨fields, logical, owned₁, ownArgs, sourceArgs, den, inv₁, refs, _⟩ :=
    Own.Plain.takeArgs_sem before.owned.takeInv taken
  obtain ⟨toks₁, tokens₁, roots₁⟩ := inv₁.roots
  have none := Own.Plain.closed_nil tokens₁ closed
  subst none
  have empty := Own.Plain.EnvRoots.nil_inv roots₁
  subst empty
  have refs' : Own.Plain.SameRefs roots fields := by simpa using refs
  have balance : Balance H external fields := refs'.balance before.owned.counts
  have calleeHeap : HeapState P pairs H addresses memory external fields
      context base bump limit regionBytes slots lists :=
    ⟨by rw [← holdRoots_sameRefs refs']; exact heap.ready, heap.ordered, heap.compatible,
      heap.extent⟩
  have arity := source_call_arity scope.1 calleeLookup sourceArgs
  have fieldsArity : fields.length = calleeSource.params.length :=
    (Own.evalArgs_length ownedEnv ownArgs).trans calleeArity.symm
  have lexical := before.lexical.1
  have frameArgs : Own.evalArgs source.env args = some fields := Cfg.Proof.evalArgs_sub lexical ownArgs
  have preserved : Own.Plain.ExternalPreserved H H external := fun _ _ _ h => h
  have history : HeapHistory H.size addresses H.size addresses := ⟨Nat.le_refl _, fun _ _ => rfl⟩
  rw [Fir.eval_tcall, sourceArgs]
  simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
  rw [Fir.evalCall_of F clock calleeLookup logical]
  unfold Fir.callFun
  rw [if_pos arity]
  have entryLayout := before.layout
  obtain ⟨fd, scopeNames, params, acc, next, supply, low, lookup, sourceRange, layout, cursor,
    sub, below, names, saved⟩ := before.layout
  have finished : source.rest = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  let sourceBlock : Cfg.Block :=
    {params, body := acc.reverse, term := Cfg.Proof.tcallTerm source.fn f args}
  have blockLookup : fd.blocks[source.blk]? = some sourceBlock := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using sourceRange
  by_cases self : f = source.fn
  · subst f
    have sameCallee : calleeSource = sourceFunction :=
      Option.some.inj (calleeLookup.symm.trans sourceLookup)
    subst calleeSource
    rcases self_entry_activation admission.scopedProgram admission.consuming sourceLookup
        entryLayout before.frame ownArgs den balance fieldsArity before.running memory context []
        callers with entered | failure
    · obtain ⟨after, final, cost, body, erased, activation, sameFn, trace, charged⟩ := entered
      apply ResultAt.charge trace charged preserved history
      intro next' clockEq
      have execution := smaller next' (by omega) [] body H addresses external
        (sourceFunction.params.map Prod.fst) (Ctx.entry (sourceFunction.params.map Prod.fst)) .leaf
        (Fir.bindAll .leaf (sourceFunction.params.map Prod.fst) logical)
        (Own.bindAll .leaf (sourceFunction.params.map Prod.fst) fields) fields [] [] sourceFunction
        function after final memory context base bump limit regionBytes slots lists callers
        (by rw [sameFn]; exact sourceLookup) activation calleeHeap
      rwa [erased] at execution
    · exact ResultAt.of_fails failure
  · have terminal : sourceBlock.term = .tcall f args := by
      simp [sourceBlock, Cfg.Proof.tcallTerm, self]
    obtain ⟨original, actual, originalLookup, receipt, consumedLookup⟩ :=
      consumed_entry admission.consuming nativeRange
    have sameOriginal : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
    subst original
    have sameActual : actual = function :=
      Option.some.inj (consumedLookup.symm.trans before.frame.lookup)
    subst actual
    obtain ⟨consumedBody, consumedBodyEq, consumedBlock⟩ :=
      (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
    have argsLive : ∀ arg ∈ args, Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg :=
      fused_term_live consumedBlock (fun x member => by
        simp only [Rt.Proof.otherUses, List.mem_append]
        exact .inr (by simpa [sourceBlock, Cfg.Proof.tcallTerm, self, Cfg.Check.termVars]
          using Rt.Proof.argVars_of_mem member))
    have compatible := before.frame.compatible.args argsLive frameArgs
    obtain ⟨rest, consumeRest, position⟩ := before.frame.cursor
    rw [finished] at consumeRest
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
    subst rest
    rcases position.tail_receipt before.frame.lookup consumedBlock rfl terminal before.frame.words
        frameArgs before.running memory context callers with success | failure
    · obtain ⟨argumentWords, nativeFunction, output, operands, represented, functionLookup,
        outputLookup, pos, term, evaluated⟩ := success
      obtain ⟨originalFd, block, consumedFd, callee, targetEnv, offset, body, calleeCfgLookup,
        calleeBlockLookup, erased, entered, traceEntry, _, activation⟩ :=
        entry_activation admission.scopedProgram admission.consuming admission.lowering main
          calleeLookup den balance represented compatible fieldsArity [] memory context callers
      have called := Lir.step_tail (mem := memory) (ctx := context) (rest := callers)
        functionLookup outputLookup pos term evaluated entered
      have trace := (Lir.star_of_step called).trans traceEntry
      simp only [Bool.toNat_true, Nat.add_zero] at trace
      apply ResultAt.charge trace (Nat.le_refl 1) preserved history
      intro next' clockEq
      have execution := smaller next' (by omega) [] body H addresses external
        (calleeSource.params.map Prod.fst) (Ctx.entry (calleeSource.params.map Prod.fst)) .leaf
        (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical)
        (Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields) fields [] [] calleeSource
        consumedFd _ _ memory context base bump limit regionBytes slots lists callers
        calleeLookup activation calleeHeap
      rwa [erased] at execution
    · exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
