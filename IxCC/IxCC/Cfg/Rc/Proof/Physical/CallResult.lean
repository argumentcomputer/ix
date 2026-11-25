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
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

private theorem call_evalArgs_mem_arg {ρo : Own.Env} :
    ∀ {args : List Fir.Arg} {vs : List RVal}, Own.evalArgs ρo args = some vs →
      ∀ v, v ∈ vs → (∃ a, a ∈ args ∧ Own.evalArg ρo a = some v)
  | [], _, hev, _, hm => by simp [Own.evalArgs] at hev; subst hev; cases hm
  | a :: as, vs, hev, v, hm => by
    cases ha : Own.evalArg ρo a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v0 =>
      cases has : Own.evalArgs ρo as with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have : v0 :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst this
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨a', hm'', ha'⟩ := call_evalArgs_mem_arg has v hm'
          exact ⟨a', List.mem_cons_of_mem _ hm'', ha'⟩

private theorem call_evalArgs_mem_split {ρo : Own.Env} :
    ∀ (bs : List Bool) (args : List Fir.Arg) (vs : List RVal),
      Own.evalArgs ρo args = some vs →
      ∀ v, v ∈ vs →
        v ∈ Own.Plain.selectOwnedVals bs vs ∨
        ∃ a, a ∈ (bs.zip args).filterMap (fun p => if p.1 then some p.2 else none) ∧
          Own.evalArg ρo a = some v
  | _, [], _, hev, _, hm => by simp [Own.evalArgs] at hev; subst hev; cases hm
  | [], a :: as, _, hev, v, hm => by
    left; rw [Own.Plain.selectOwnedVals_nil_left]; exact hm
  | b :: bs, a :: as, vs, hev, v, hm => by
    cases ha : Own.evalArg ρo a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v0 =>
      cases has : Own.evalArgs ρo as with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have : v0 :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst this
        cases b with
        | false =>
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inl List.mem_cons_self
          · rcases call_evalArgs_mem_split bs as vs' has v hm' with h1 | ⟨a', h2, h3⟩
            · exact Or.inl (List.mem_cons_of_mem _ h1)
            · exact Or.inr ⟨a', by simp [List.zip_cons_cons, h2], h3⟩
        | true =>
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inr ⟨a, by simp [List.zip_cons_cons], ha⟩
          · rcases call_evalArgs_mem_split bs as vs' has v hm' with h1 | ⟨a', h2, h3⟩
            · exact Or.inl h1
            · exact Or.inr ⟨a', by simp [List.zip_cons_cons, h2], h3⟩

private theorem call_checkCallBorrowed_zip {Γ : Ctx} :
    ∀ {bs : List Bool} {args : List Fir.Arg},
      Γ.checkCallBorrowed bs args = .ok () →
      ∀ x, Fir.Arg.var x ∈ (bs.zip args).filterMap (fun p => if p.1 then some p.2 else none) →
        Γ.borrowable x = true
  | [], _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, hm => by simp at hm
  | false :: bs, _ :: as, h, x, hm => by
    simp only [Own.Plain.Ctx.checkCallBorrowed] at h
    simp only [List.zip_cons_cons, List.filterMap_cons, Bool.false_eq_true, ↓reduceIte] at hm
    exact call_checkCallBorrowed_zip h x hm
  | true :: bs, a :: as, h, x, hm => by
    simp only [List.zip_cons_cons, List.filterMap_cons, ↓reduceIte, List.mem_cons] at hm
    cases a with
    | var y =>
      simp only [Own.Plain.Ctx.checkCallBorrowed] at h
      cases hb : Γ.borrowable y with
      | false => simp [hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | true =>
        simp only [hb, ↓reduceIte] at h
        rcases hm with hEq | hm'
        · cases hEq; exact hb
        · exact call_checkCallBorrowed_zip h x hm'
    | lit _ | erased =>
      simp only [Own.Plain.Ctx.checkCallBorrowed] at h
      rcases hm with hEq | hm'
      · cases hEq
      · exact call_checkCallBorrowed_zip h x hm'

/-- **`x := f(args)`**: the callee runs at a strictly smaller source clock; the caller's
continuation at the same clock. -/
theorem call_result (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k borrows bodies uniqs)
    {x f : Nat} {args : List Fir.Arg} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.call f args) k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.call f args) (Own.Plain.eraseCode k)))
    F.ctors retUniq priv
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
  simp only [Own.Plain.bindCtx] at hbind
  obtain ⟨Γ₁, taken, hrest⟩ := Own.Plain.except_bind_ok hbind
  obtain ⟨_, hcb, hΓ⟩ := Own.Plain.except_bind_ok hrest
  have hΓ := Own.Plain.except_pure_ok hΓ
  subst hΓ
  let bs := borrows.getD f []
  let us := (uniqs.getD f ([], false)).1
  let retU := (uniqs.getD f ([], false)).2
  obtain ⟨fields, logical, owned₁, ownArgs, sourceArgs, den, inv₁, refs, weaker, hbrw, huniq, havArgs⟩ :=
    Own.Plain.takeOwnedUniqueArgs_call_sem before.owned taken hcb
  have hle₁ : ∀ l, refsIn l owned₁ ≤ refsIn l roots := fun l => by
    have := refs l; rw [refsIn_append] at this; omega
  have hwkClr := Own.Plain.Ctx.clearBorrowedUniq_weaker Γ₁ bs args
  have hownClr := Own.Plain.Ctx.clearBorrowedUniq_own Γ₁ bs args
  obtain ⟨toks₁, htok₁, hroots₁⟩ := inv₁.roots
  have hrootsClr : ∃ toks, Own.Plain.Ctx.Tokens (Γ₁.clearBorrowedUniq bs args) toks ∧
      Own.Plain.EnvRoots ownedEnv toks owned₁ :=
    ⟨toks₁, htok₁.same hownClr.1 hownClr.2, hroots₁⟩
  have pre₁ := before.owned.pre.weaker (hwkClr.trans weaker) hrootsClr hle₁
  have pre₂ := pre₁.release
  have refsAll : Own.Plain.SameRefs (roots ++ slotVals)
      (Own.Plain.selectOwnedVals bs fields ++ (owned₁ ++ slotVals)) := by
    intro l
    have h1 := refs l
    simp only [refsIn_append] at h1 ⊢; dsimp only [bs]; omega
  have balance : Balance H (holdRoots external (owned₁ ++ slotVals))
      (Own.Plain.selectOwnedVals bs fields) :=
    balance_hold.mp (refsAll.balance before.owned.counts)
  have hprivArgs : ∀ l, pre₂.localPriv l → ∀ v, v ∈ fields → v ≠ .loc l := by
    intro l hl v hv hEq; subst hEq
    rcases hl with hp | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hvz⟩
    · obtain ⟨a, hma, ha⟩ := call_evalArgs_mem_arg ownArgs (.loc l) hv
      cases a with
      | lit _ | erased => simp [Own.evalArg] at ha
      | var y => exact before.owned.privNoVar l hp y (havArgs y hma) ha
    · rcases call_evalArgs_mem_split bs args fields ownArgs (.loc l) hv with hownV | ⟨a, hma, ha⟩
      · obtain ⟨skeys, hsk, hsroots⟩ := before.owned.slotRoots
        have hrs0 : Γ.rset.get? s = some (cls, u) := by
          rw [← (hwkClr.trans weaker).rset]; exact hrs
        obtain ⟨sv, hsv, hcase⟩ := before.owned.rsetOk s cls u hrs0
        have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
        rcases hcase with ⟨hc0, _⟩ | ⟨_, _, hEq', _, _, _, _, _, hrefsL⟩
        · cases hc0
        · cases hEq'
          have hmS : RVal.loc l ∈ slotVals :=
            hsroots.member ((hsk.mem s).mpr (by simp [Src.NatMap.contains, hrs0])) hsv
          have hp1 := refsIn_pos hmS
          have hp2 := refsIn_pos hownV
          rw [refsIn_append, refs l, refsIn_append] at hrefsL; dsimp only [bs] at hp2; omega
      · cases a with
        | lit _ | erased => simp [Own.evalArg] at ha
        | var y =>
          have hbrwY := call_checkCallBorrowed_zip hcb y hma
          obtain ⟨skeys, hsk, hsroots⟩ := before.owned.slotRoots
          have hrs0 : Γ.rset.get? s = some (cls, u) := by
            rw [← (hwkClr.trans weaker).rset]; exact hrs
          obtain ⟨sv, hsv, hcase⟩ := before.owned.rsetOk s cls u hrs0
          have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
          rcases hcase with ⟨hc0, _⟩ | ⟨_, _, hEq', _, _, _, hextL, hedgeL, hrefsL⟩
          · cases hc0
          · cases hEq'
            have hmS : RVal.loc l ∈ slotVals :=
              hsroots.member ((hsk.mem s).mpr (by simp [Src.NatMap.contains, hrs0])) hsv
            have hpS := refsIn_pos hmS
            simp only [Own.Plain.Ctx.borrowable_eq, Bool.or_eq_true, decide_eq_true_eq] at hbrwY
            rcases hbrwY with (hi | hpb) | htk
            · obtain ⟨u', hu', himm⟩ := before.owned.immOk y (by rw [← weaker.isImm y]; exact hi)
              have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
              exact himm l rfl
            · obtain ⟨u', hu', hreach⟩ := before.owned.pbrwOk y (by rw [← weaker.isPbrw y]; exact hpb)
              have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
              exact Own.Plain.ReachableFrom.not_of_zero hextL hedgeL hreach
            · have hpO := refsIn_pos (hroots₁.member (htok₁.mem htk) ha)
              rw [refsIn_append, refs l, refsIn_append] at hrefsL; omega
    · rcases call_evalArgs_mem_split bs args fields ownArgs (.loc l) hv with hownV | ⟨a, hma, ha⟩
      · obtain ⟨hmeta, v', hv', hvu⟩ := pre₂.uniqOk z huz
        have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz); subst this
        obtain ⟨_, _, _, _, hrefsL⟩ := hvu
        have hrefs0 : refsIn l (roots ++ slotVals) = 1 := by
          obtain ⟨_, v0, hv0, hvu0⟩ := before.owned.uniqOk z ((hwkClr.trans weaker).isUniq z huz)
          have : v0 = .loc l := Option.some.inj (hv0.symm.trans hvz); subst this
          obtain ⟨_, _, _, _, hr0⟩ := hvu0; exact hr0
        have hp1 := refsIn_pos hownV
        rw [refsIn_append, refs l, refsIn_append] at hrefs0
        rw [refsIn_append] at hrefsL; dsimp only [bs] at hp1; omega
      · cases a with
        | lit _ | erased => simp [Own.evalArg] at ha
        | var y =>
          have hneYZ : y ≠ z := fun hEq => by
            subst hEq
            exact Own.Plain.Ctx.clearBorrowedUniq_avoids Γ₁ bs args huz hiz (.var y) hma rfl
          have hbrwY := call_checkCallBorrowed_zip hcb y hma
          obtain ⟨hmeta, v', hv', hvu⟩ := pre₂.uniqOk z huz
          have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz); subst this
          obtain ⟨_, _, hextL, hedgeL, hrefsL⟩ := hvu
          simp only [Own.Plain.Ctx.borrowable_eq, Bool.or_eq_true, decide_eq_true_eq] at hbrwY
          rcases hbrwY with (hi | hpb) | htk
          · obtain ⟨u', hu', himm⟩ := before.owned.immOk y (by rw [← weaker.isImm y]; exact hi)
            have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
            exact himm l rfl
          · obtain ⟨u', hu', hreach⟩ := before.owned.pbrwOk y (by rw [← weaker.isPbrw y]; exact hpb)
            have : u' = .loc l := Option.some.inj (hu'.symm.trans ha); subst this
            exact Own.Plain.ReachableFrom.not_of_zero hextL hedgeL hreach
          · have hyMem : y ∈ toks₁ := htok₁.mem htk
            have hzTok : Γ₁.tokens z = 1 := by
              have h1 := (hmeta hiz).1
              change (Γ₁.clearBorrowedUniq bs args).tokens z = 1 at h1
              rw [Own.Plain.Ctx.tokens_eq, hownClr.1] at h1; exact h1
            have hzMem : z ∈ toks₁ := htok₁.mem (by omega)
            have h2 := Own.Plain.envRoots_distinct_ne hroots₁ hneYZ hyMem hzMem ha hvz
            rw [refsIn_append] at hrefsL; omega
  have lexical := before.lexical.1
  have frameArgs : Own.evalArgs source.env args = some fields := Cfg.Proof.evalArgs_sub lexical ownArgs
  obtain ⟨sourceTail, callHead, resume⟩ := before.layout.bind_continuation
  have head : source.rest = .bind x (.fir (.call f args)) :: sourceTail := callHead
  have ordinary : reserved P.base.size (.bind x (.fir (.call f args))) = false := by
    simp [reserved, show f ≠ P.base.size by omega, show f ≠ P.base.size + 1 by omega]
  have nonReuse : isReuseOp P.base.size (.bind x (.fir (.call f args))) = false := by
    simp [isReuseOp, show f ≠ P.base.size + 2 by omega, show f ≠ P.base.size + 3 by omega]
  have destination := checked_bind_real admission.scopedProgram before.layout sourceLookup
    ordinary nonReuse
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
    rw [admission.tagged.operandsAt_params] at operandsLowered
    obtain ⟨argumentWords, evaluated, represented, _⟩ :=
      fused_operands_words before.frame.words operandsLowered liveArgs frameArgs
    have compatible := before.frame.compatible.args liveArgs frameArgs
    have fieldsArity : fields.length = calleeSource.params.length :=
      (Own.evalArgs_length ownedEnv ownArgs).trans calleeArity.symm
    let saved : Lir.Frame := {target with pos := target.pos + 1, dsts := [x]}
    obtain ⟨fd, block, consumedFd, callee, targetEnv, offset, body, lookup, blockLookup, erased,
      entered, traceEntry, _, activation⟩ :=
      entry_activation admission.scopedProgram admission.consuming admission.lowering main
        calleeLookup (priv := pre₂.localPriv) den balance hbrw huniq
        (fun l hl => (pre₂.localPriv_facts hl).1) (fun l hl => (pre₂.localPriv_facts hl).2)
        hprivArgs represented compatible fieldsArity
        (({source with rest := sourceTail}, x) :: []) memory context (saved :: callers)
    have calledStep := Lir.step_call (mem := memory) (ctx := context) (rest := callers)
      functionLookup outputLookup position statement evaluated entered
    have trace := (Lir.star_of_step calledStep).trans traceEntry
    simp only [Bool.toNat_true, Nat.add_zero] at trace
    have savedFrame : FrameState P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
        addresses H.size (funcFirst bodies source.fn sourceFunction) function
        {source with rest := sourceTail} saved :=
      ⟨before.frame.lookup, continuation.withEnvs source.env target.env [x], before.frame.words,
        before.frame.bounded, before.frame.compatible⟩
    have fused : ∀ value block, function.blocks[source.blk]? = some block →
        Rt.Proof.FusedDone (tablesOf P pairs) function block
          {source with rest := sourceTail, env := source.env.insert x value} :=
      fun value => consumed_call_done before.frame.lookup before.frame.cursor head
        (consume_user_call range) (source.env.insert x value)
    have nested : holdRoots external (roots ++ slotVals) =
        holdRoots (holdRoots external (owned₁ ++ slotVals))
          (Own.Plain.selectOwnedVals bs fields ++ []) := by
      rw [holdRoots_sameRefs refsAll]
      funext location
      simp only [holdRoots, refsIn_append, List.append_nil, bs]
      omega
    have calleeHeap : HeapState P pairs H addresses memory (holdRoots external (owned₁ ++ slotVals))
        (Own.Plain.selectOwnedVals bs fields ++ []) context base bump limit regionBytes slots lists :=
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
        (holdRoots external (owned₁ ++ slotVals)) retU pre₂.localPriv .leaf []
        (calleeSource.params.map Prod.fst)
        (Ctx.entryWith (calleeSource.params.map Prod.fst) bs us) .leaf
        (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical)
        (Own.bindAll .leaf (calleeSource.params.map Prod.fst) fields)
        (Own.Plain.selectOwnedVals bs fields) [] []
        calleeSource consumedFd calleeCfg calleeNative memory context base bump limit regionBytes
        slots lists (saved :: callers) calleeLookup activation calleeHeap
      rw [erased] at execution
      cases result : Fir.eval F smallerClock
          (Fir.bindAll .leaf (calleeSource.params.map Prod.fst) logical) [] calleeSource.body with
      | ok value =>
        rw [result] at execution
        simp only [Sem.Result.bind]
        rcases execution with ⟨returned, calleeCost, calleeTrace⟩ | failed
        · have reachCallee : Own.Plain.ReachablePreserved H returned.heap
              (holdRoots external (owned₁ ++ slotVals)) := returned.reachable
          have pre₃ := pre₂.call (Own.Plain.release_borrowed pre₁.epochs) reachCallee
            returned.privPreserved
          have hbalAfter : Balance returned.heap external ((returned.value :: owned₁) ++ slotVals) := by
            have hr' := Own.Plain.balance_resume returned.balance
            refine Own.Plain.SameRefs.balance ?_ hr'
            intro l; simp only [List.cons_append, refsIn_append, refsIn]; omega
          obtain ⟨returnStep, resumedFrame⟩ := returned.history.resume savedFrame rfl destination
            returned.represented returned.bounded returned.compatible returned.terminator
            returned.memory context callers
          let finalSource : Cfg.Frame :=
            {source with rest := sourceTail, env := source.env.insert x returned.value}
          let finalTarget : Lir.Frame :=
            {saved with env := saved.env.insert x returned.word, dsts := []}
          have rootEq : holdRoots (holdRoots external (owned₁ ++ slotVals)) [returned.value] =
              holdRoots external ((returned.value :: owned₁) ++ slotVals) := by
            funext location
            simp only [holdRoots, List.cons_append, refsIn_append, refsIn]
            omega
          have resumedHeap : HeapState P pairs returned.heap returned.addresses returned.memory
              external ((returned.value :: owned₁) ++ slotVals) context base returned.bump limit
              regionBytes returned.slots returned.lists :=
            ⟨by rw [← rootEq]; exact returned.state.ready, returned.state.ordered,
              returned.state.compatible, returned.state.extent⟩
          have hreach : Own.Plain.ReachablePreserved H returned.heap external :=
            reachCallee.of_holdRoots
          have hpriv' : Own.Plain.PrivPreserved H returned.heap priv :=
            returned.privPreserved.mono (fun _ h => Or.inl h)
          have allTrace := trace.trans (calleeTrace.trans (Lir.star_of_step returnStep))
          cases hru : (uniqs.getD f ([], false)).2 with
          | true =>
            simp only [hru, ↓reduceIte] at typed
            have hvU : Own.Plain.UniqVal F.ctors returned.heap external
                ((returned.value :: owned₁) ++ slotVals) returned.value := by
              have hvU0 := returned.uniqRet hru
              cases hvEq : returned.value with
              | lit _ | erased => trivial
              | ctor0 c => simpa [hvEq, Own.Plain.UniqVal] using hvU0
              | loc l =>
                rw [hvEq] at hvU0
                obtain ⟨b, hc, hextH, hedge, _⟩ := hvU0
                simp only [holdRoots, refsIn_append] at hextH
                exact ⟨b, hc, by omega, hedge,
                  by simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega⟩
            have state := pre₃.bindUniqOwned fresh returned.den hbalAfter hvU returned.retNoPriv
            have resumed : Activation F P pairs
                (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) returned.heap
                returned.addresses external (live ++ [x])
                ((Γ₁.clearBorrowedUniq bs args).release.addUniqOwn x) Δ
                (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
                (returned.value :: owned₁) lex sourceJoins ownedJoins k
                (funcFirst bodies source.fn sourceFunction) function
                finalSource finalTarget borrows uniqs retUniq priv rslots slotVals :=
              ⟨state, typed, resume returned.value, resumedFrame, bodyScope, rfl,
                fused returned.value⟩
            exact ResultAt.prefix allTrace hreach hpriv' returned.history (by omega)
              (next returned.heap returned.addresses external retUniq priv rslots slotVals
                (live ++ [x]) ((Γ₁.clearBorrowedUniq bs args).release.addUniqOwn x) Δ
                (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
                (returned.value :: owned₁) lex ownedJoins sourceFunction function finalSource
                finalTarget returned.memory context base returned.bump limit regionBytes
                returned.slots returned.lists callers sourceLookup resumed resumedHeap)
          | false =>
            simp only [hru, Bool.false_eq_true, ↓reduceIte] at typed
            have state := pre₃.bindOwned fresh returned.den hbalAfter returned.retNoPriv
            have resumed : Activation F P pairs
                (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) returned.heap
                returned.addresses external (live ++ [x])
                ((Γ₁.clearBorrowedUniq bs args).release.addOwn x 1) Δ
                (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
                (returned.value :: owned₁) lex sourceJoins ownedJoins k
                (funcFirst bodies source.fn sourceFunction) function
                finalSource finalTarget borrows uniqs retUniq priv rslots slotVals :=
              ⟨state, typed, resume returned.value, resumedFrame, bodyScope, rfl,
                fused returned.value⟩
            exact ResultAt.prefix allTrace hreach hpriv' returned.history (by omega)
              (next returned.heap returned.addresses external retUniq priv rslots slotVals
                (live ++ [x]) ((Γ₁.clearBorrowedUniq bs args).release.addOwn x 1) Δ
                (sourceEnv.insert x value) (ownedEnv.insert x returned.value)
                (returned.value :: owned₁) lex ownedJoins sourceFunction function finalSource
                finalTarget returned.memory context base returned.bump limit regionBytes
                returned.slots returned.lists callers sourceLookup resumed resumedHeap)
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
