import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Physical.CallResume
import IxCC.Cfg.Rc.Proof.Physical.TailResult
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands
import IxCC.Cfg.Rc.Proof.Native.CallEntry
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Cfg.Rc.Proof.CallStep
import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.Frames
import IxCC.Fir.Proof.Unfold

/-! `x := f(args)` over the typing context: the arguments' tokens **move** to the callee
(`takeArgs`); the caller's frame is saved holding the rest of its tokens, which the callee sees as
external owners; on return the result owns one token and nothing stays borrowed (a call is a
release). The callee runs at a strictly smaller source clock, the caller's continuation at the
same clock. No action prefix. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`x := f(args)`**: the callee runs at a strictly smaller source clock; the caller's
continuation at the same clock. -/
theorem call_result (admission : CodeAdmission F bodies P config pairs functions)
    (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k)
    {x f : Nat} {args : List Fir.Arg} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.call f args) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.call f args) (Own.Plain.eraseCode k)))
  have scopeParts : x ∉ live ∧
      ((Own.Plain.signatures F).lookup f = some args.length ∧ args.all (Own.Plain.argIn live) = true) ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
    simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc]
      using before.scope
  obtain ⟨fresh, ⟨signature, _⟩, bodyScope⟩ := scopeParts
  obtain ⟨calleeSource, sourceRange, calleeLookup, calleeArity⟩ :=
    Own.Plain.signatures_lookup signature
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
  have range : f < P.base.size := by simpa only [programSize] using sourceRange
  obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
  obtain ⟨Γ₁, taken, hΓ⟩ := Own.Plain.except_bind_ok hbind
  have hΓ := Own.Plain.except_pure_ok hΓ
  subst hΓ
  obtain ⟨fields, logical, owned₁, ownArgs, sourceArgs, den, inv₁, refs, weaker⟩ :=
    Own.Plain.takeArgs_sem before.owned.takeInv taken
  have balance : Balance H (holdRoots external owned₁) fields :=
    balance_hold.mp (refs.balance before.owned.counts)
  have lexical := before.lexical.1
  have frameArgs : Own.evalArgs source.env args = some fields := Cfg.Proof.evalArgs_sub lexical ownArgs
  obtain ⟨sourceTail, callHead, resume⟩ := before.layout.bind_continuation
  have head : source.rest = .bind x (.fir (.call f args)) :: sourceTail := callHead
  have ordinary : reserved P.base.size (.bind x (.fir (.call f args))) = false := by
    simp [reserved, show f ≠ P.base.size by omega, show f ≠ P.base.size + 1 by omega]
  have destination := checked_bind_real admission.scopedProgram before.layout sourceLookup ordinary
  have arity := source_call_arity signature calleeLookup sourceArgs
  rw [Fir.eval_bindCall, sourceArgs]
  simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
  rw [Fir.evalCall_of F clock calleeLookup logical]
  unfold Fir.callFun
  rw [if_pos arity]
  rcases before.frame.cursor.call head (consume_user_call range) memory context callers with
    called | failure
  · obtain ⟨operands, nativeFunction, output, operandsLowered, functionLookup,
      outputLookup, position, statement, continuation⟩ := called
    have liveArgs := consumed_call_live before.frame.cursor head (consume_user_call range)
      before.frame.lookup
    obtain ⟨argumentWords, evaluated, represented, _⟩ :=
      fused_operands_words before.frame.words operandsLowered liveArgs frameArgs
    have compatible := before.frame.compatible.args liveArgs frameArgs
    have fieldsArity : fields.length = calleeSource.params.length :=
      (Own.evalArgs_length ownedEnv ownArgs).trans calleeArity.symm
    let saved : Lir.Frame := {target with pos := target.pos + 1, dsts := [x]}
    obtain ⟨fd, block, consumedFd, callee, targetEnv, offset, body, lookup, blockLookup, erased,
      entered, traceEntry, _, activation⟩ :=
      entry_activation admission.scopedProgram admission.consuming admission.lowering main
        calleeLookup den balance represented compatible fieldsArity
        (({source with rest := sourceTail}, x) :: []) memory context (saved :: callers)
    have calledStep := Lir.step_call (mem := memory) (ctx := context) (rest := callers)
      functionLookup outputLookup position statement evaluated entered
    have trace := (Lir.star_of_step calledStep).trans traceEntry
    simp only [Bool.toNat_true, Nat.add_zero] at trace
    have savedFrame : FrameState P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
        addresses H.size sourceFunction.vars function {source with rest := sourceTail} saved :=
      ⟨before.frame.lookup, continuation.withEnvs source.env target.env [x], before.frame.words,
        before.frame.bounded, before.frame.compatible⟩
    have fused : ∀ value block, function.blocks[source.blk]? = some block →
        Rt.Proof.FusedDone (tablesOf P pairs) function block
          {source with rest := sourceTail, env := source.env.insert x value} :=
      fun value => consumed_call_done before.frame.lookup before.frame.cursor head
        (consume_user_call range) (source.env.insert x value)
    have nested : holdRoots external roots = holdRoots (holdRoots external owned₁) fields := by
      rw [holdRoots_sameRefs refs]
      funext location
      simp only [holdRoots, refsIn_append]
      omega
    have calleeHeap : HeapState P pairs H addresses memory (holdRoots external owned₁) fields
        context base bump limit regionBytes slots lists :=
      ⟨by rw [← nested]; exact heap.ready, heap.ordered, heap.compatible, heap.extent⟩
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
        env := Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields }
      let calleeNative : Lir.Frame := {fn := f, label := offset, pos := 0, env := targetEnv}
      have execution := smaller smallerClock (Nat.lt_succ_self _) [] body H addresses
        (holdRoots external owned₁) (calleeSource.params.map Prod.fst)
        (Ctx.entry (calleeSource.params.map Prod.fst)) .leaf
        (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical)
        (Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields) fields [] []
        calleeSource consumedFd calleeCfg calleeNative memory context base bump limit regionBytes
        slots lists (saved :: callers) calleeLookup activation calleeHeap
      rw [erased] at execution
      cases result : Fir.eval F smallerClock
          (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical) [] calleeSource.body with
      | ok value =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        rcases execution with ⟨returned, calleeCost, calleeTrace⟩ | failed
        · have preservedCallee : Own.Plain.ExternalPreserved H returned.heap
              (holdRoots external owned₁) := returned.preserved
          have pre₁ := before.owned.pre.weaker weaker inv₁.roots
          have pre₂ := pre₁.release.call (Own.Plain.release_borrowed pre₁.epochs) preservedCallee
          have state := pre₂.bindOwned fresh returned.den
            ((Own.Plain.SameRefs.comm _ _).balance (Own.Plain.balance_resume returned.balance))
          obtain ⟨returnStep, resumedFrame⟩ := returned.history.resume savedFrame rfl destination
            returned.represented returned.bounded returned.compatible returned.terminator
            returned.memory context callers
          let finalSource : Cfg.Frame :=
            {source with rest := sourceTail, env := source.env.insert x returned.value}
          let finalTarget : Lir.Frame :=
            {saved with env := saved.env.insert x returned.word, dsts := []}
          have resumed : Activation F P pairs
              (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) returned.heap
              returned.addresses external (live ++ [x]) (Γ₁.release.addOwn x 1) Δ
              (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
              (returned.value :: owned₁) lex sourceJoins ownedJoins k sourceFunction.vars function
              finalSource finalTarget :=
            ⟨state, typed, resume returned.value, resumedFrame, bodyScope, rfl,
              fused returned.value⟩
          have rootEq : holdRoots (holdRoots external owned₁) [returned.value] =
              holdRoots external (returned.value :: owned₁) := by
            funext location
            rw [show returned.value :: owned₁ = [returned.value] ++ owned₁ from rfl]
            simp only [holdRoots, refsIn_append]
            omega
          have resumedHeap : HeapState P pairs returned.heap returned.addresses returned.memory
              external (returned.value :: owned₁) context base returned.bump limit regionBytes
              returned.slots returned.lists :=
            ⟨by rw [← rootEq]; exact returned.state.ready, returned.state.ordered,
              returned.state.compatible, returned.state.extent⟩
          have preserved : Own.Plain.ExternalPreserved H returned.heap external :=
            fun root logical' externalRoot den' =>
              preservedCallee root logical' (external_hold externalRoot) den'
          have continuation' := next returned.heap returned.addresses external (live ++ [x])
            (Γ₁.release.addOwn x 1) Δ (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
            (returned.value :: owned₁) lex ownedJoins sourceFunction function finalSource
            finalTarget returned.memory context base returned.bump limit regionBytes
            returned.slots returned.lists callers sourceLookup resumed resumedHeap
          have allTrace := trace.trans (calleeTrace.trans (Lir.star_of_step returnStep))
          exact ResultAt.prefix allTrace preserved returned.history (by omega) continuation'
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
        · exact .inl ⟨_, terminal, trace.trans calleeTrace, trapped⟩
        · exact .inr (fails_prefix trace failed)
      | stuck => trivial
  · have same : Lir.atState memory context target.fn target.label target.pos target.env callers =
        ({mem := memory, ctx := context, stack := target :: callers} : Lir.State) :=
      (Rt.Proof.state_eq (s := {mem := memory, ctx := context, stack := target :: callers}) rfl
        before.running).symm
    rw [same] at failure
    exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
