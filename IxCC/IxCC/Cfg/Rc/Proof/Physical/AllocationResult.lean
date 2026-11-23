import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Owned.AllocationStep
import IxCC.Cfg.Rc.Proof.Physical.BindLayout
import IxCC.Cfg.Rc.Proof.Physical.FrameTransport
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorTables
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Fir.Proof.Unfold

/-! `x := C a₁ … aₙ` (n > 0) over the typing context: the arguments' tokens move into the new
cell (`takeArgs`), which `x` then owns with one token. No action prefix: an argument the path still
needs was incremented by an `inc` placed before. The native step is the allocation wrapper
(`allocation_step_of`). -/
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

private theorem alloc_takeArgs_noPriv {Γ Γ₁ : Ctx} {ρo : Own.Env} {priv : Nat → Prop}
    (hpriv : ∀ l, priv l → ∀ x, Γ.avail x = true → ρo.get? x ≠ some (.loc l))
    {args : List Fir.Arg} {vs : List RVal}
    (hev : Own.evalArgs ρo args = some vs) (ht : Γ.takeArgs args = .ok Γ₁) :
    ∀ l, priv l → refsIn l vs = 0 := by
  intro l hl
  by_cases hnz : refsIn l vs = 0
  · exact hnz
  · exfalso
    have hmem : RVal.loc l ∈ vs := Own.Plain.mem_of_refsIn_pos (by omega)
    have hfind : ∀ (as' : List Fir.Arg) (vs' : List RVal) (Γa Γb : Ctx),
        Own.evalArgs ρo as' = some vs' → Γa.takeArgs as' = .ok Γb → Own.Plain.Ctx.Weaker Γa Γ →
        RVal.loc l ∈ vs' → False := by
      intro as'
      induction as' with
      | nil => intro vs' _ _ hev' _ _ hm'; simp [Own.evalArgs] at hev'; subst hev'; cases hm'
      | cons a as'' ih =>
        intro vs' Γa Γb hev' hta' hwa hm'
        cases ha : Own.evalArg ρo a with
        | none => simp [Own.evalArgs, ha] at hev'
        | some v0 =>
          cases has : Own.evalArgs ρo as'' with
          | none => simp [Own.evalArgs, ha, has] at hev'
          | some vs'' =>
            have : v0 :: vs'' = vs' := by simpa [Own.evalArgs, ha, has] using hev'
            subst this
            simp only [Own.Plain.Ctx.takeArgs] at hta'
            cases hta0 : Γa.takeArg a with
            | error _ => rw [hta0] at hta'; cases hta'
            | ok Γm =>
              rw [hta0] at hta'
              rcases List.mem_cons.mp hm' with hEq | hm''
              · subst hEq
                cases a with
                | lit _ | erased => simp [Own.evalArg] at ha
                | var y =>
                  have havy : Γa.avail y = true := by
                    rcases Own.Plain.Ctx.take_ok hta0 with ⟨hi', _⟩ | ⟨_, n, hn, _⟩
                    · simp [Own.Plain.Ctx.avail_eq, hi']
                    · simp [Own.Plain.Ctx.avail_eq, Own.Plain.Ctx.tokens_eq, hn]
                  exact hpriv l hl y (hwa.avail havy) ha
              · exact ih vs'' Γm Γb has hta' ((Own.Plain.Ctx.takeArg_weaker hta0).trans hwa) hm''
    exact hfind args vs Γ Γ₁ hev ht (Own.Plain.Ctx.Weaker.refl Γ) hmem

/-- **`x := C args`** with at least one field. -/
theorem allocation_result (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {x : Fir.Var} {ctor : Fir.CtorInfo} {args : List Fir.Arg} (positive : 0 < ctor.arity)
    {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.ctor ctor args) (Own.Plain.eraseCode k)))
    F.ctors retUniq priv
  have scopeFacts := before.scope
  simp only [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] at scopeFacts
  obtain ⟨freshBool, rhsScope, bodyScope⟩ := scopeFacts
  have fresh : x ∉ live := by simpa using freshBool
  have argsArity : args.length = ctor.arity := by
    simp only [Own.Plain.rhsIn, Bool.and_eq_true, decide_eq_true_eq] at rhsScope
    exact rhsScope.1.1.1.1
  obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
  have nonzero : (ctor.arity == 0) = false := by simp; omega
  simp only [Own.Plain.bindCtx, nonzero, Bool.false_eq_true, ↓reduceIte] at hbind
  obtain ⟨Γ₁, taken, hΓ⟩ := Own.Plain.except_bind_ok hbind
  have hΓ := Own.Plain.except_pure_ok hΓ
  subst hΓ
  obtain ⟨fields, logical, owned₁, ownArgs, sourceArgs, den, inv₁, refs, weaker⟩ :=
    Own.Plain.takeArgs_sem before.owned.takeInv taken
  have arity : fields.length = ctor.arity := (Own.evalArgs_length ownedEnv ownArgs).trans argsArity
  have logicalArity : logical.length = ctor.arity := den.length.symm.trans arity
  rw [Fir.eval_bind_ctor, Fir.evalRhs_ctor, sourceArgs]
  simp only [Sem.Result.ofOption, Sem.Result.bind_ok, if_pos logicalArity]
  have refsAll : Own.Plain.SameRefs (roots ++ slotVals) (fields ++ (owned₁ ++ slotVals)) := by
    intro l
    have h1 := refs l
    simp only [refsIn_append] at h1 ⊢; omega
  have balance : Balance H (holdRoots external (owned₁ ++ slotVals)) fields :=
    balance_hold.mp (refsAll.balance before.owned.counts)
  have ready : Gen.AllocatorReady maxClass H addresses memory
      (holdRoots external (fields ++ (owned₁ ++ slotVals)))
      context base bump limit slots lists := by
    rw [← holdRoots_sameRefs refsAll]; exact heap.ready
  have lexical := before.lexical.1
  have frameArgs : Own.evalArgs source.env args = some fields := Cfg.Proof.evalArgs_sub lexical ownArgs
  obtain ⟨tail, bindingHead, _⟩ := bind_layout before.layout .erased
  have head : source.rest = .bind x (.alloc ctor args .shared) :: tail := bindingHead
  have real := checked_binding_real admission.scopedProgram before.layout sourceLookup
    (by simp [Own.immRhs, reserved]) (by simp [Own.immRhs, isReuseOp])
  rcases allocation_step_of (Public.Spec.rawSource config P pairs) main before.frame.cursor
      {ctors := F.ctors, known := F.known} ctor args x head before.frame.lookup frameArgs den balance
      positive ready before.frame.words real before.frame.bounded before.running callers with
      success | failure
  · obtain ⟨address, bump', memory', slots', lists', _, result, counts, preserve, restored, trace,
      cursor', words'⟩ := success
    let allocated := H.alloc .rc {ctor, fields}
    obtain ⟨actualTail, actualHead, actualLayout⟩ := bind_layout before.layout allocated.1
    have tailEqual : actualTail = tail := (List.cons.inj (actualHead.symm.trans bindingHead)).2
    subst actualTail
    obtain ⟨actual, rest, consuming, _, _⟩ := before.frame.cursor.next head
    have accepted : ∃ result, consume P (layoutOf P) (.bind x (.alloc ctor args .shared)) =
        .ok result := ⟨actual, consuming⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, index, _, shape⟩ := consume_allocation positive consuming
    rw [shape] at consuming
    have liveArgs := consumed_call_live before.frame.cursor head consuming before.frame.lookup
    have bounds := (frame_allocation_transport (H := H) (body := {ctor, fields}) rfl
      before.frame.words before.frame.bounded real address).2
    have frame : FrameState P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
        (placeFresh addresses H.size address) allocated.2.size
        (funcFirst bodies source.fn sourceFunction) function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []} :=
      ⟨before.frame.lookup, cursor', words', bounds,
        before.frame.compatible.bind x (show ValueCtorOk (tablesOf P pairs) allocated.1 by trivial)⟩
    have fused := consumed_call_done before.frame.lookup before.frame.cursor head consuming
      (source.env.insert x allocated.1)
    have hreach := Own.Plain.ReachablePreserved.alloc H external {ctor, fields}
    have hle : ∀ l, refsIn l owned₁ ≤ refsIn l roots := fun l => by
      have := refs l; rw [refsIn_append] at this; omega
    have pre₁ := before.owned.pre.weaker weaker inv₁.roots hle
    have hpriv_vs := alloc_takeArgs_noPriv before.owned.privNoVar ownArgs taken
    have hloc_vs : ∀ l, pre₁.localPriv l → refsIn l fields = 0 := by
      intro l hl
      rcases hl with hpr | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hz⟩
      · exact hpriv_vs l hpr
      · obtain ⟨sv, hsv, hrc⟩ := pre₁.rsetOk s cls u hrs
        have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
        rcases hrc with ⟨hc0, _⟩ | ⟨l', _, hEq', _, _, _, _, _, hrefs⟩
        · cases hc0
        · cases hEq'
          have hrefs0 : refsIn l (roots ++ slotVals) = 1 := by
            obtain ⟨sv', hsv', hrc'⟩ := before.owned.rsetOk s cls u (by rw [← weaker.rset]; exact hrs)
            have : sv' = .loc l := Option.some.inj (hsv'.symm.trans hsl); subst this
            rcases hrc' with ⟨hc0, _⟩ | ⟨l'', _, hEq'', _, _, _, _, _, hr0⟩
            · cases hc0
            · cases hEq''; exact hr0
          rw [refsIn_append, refs l, refsIn_append] at hrefs0
          rw [refsIn_append] at hrefs
          omega
      · obtain ⟨_, u', hu', hvu⟩ := pre₁.uniqOk z huz
        have : u' = .loc l := Option.some.inj (hu'.symm.trans hz); subst this
        obtain ⟨_, _, _, _, hrefs⟩ := hvu
        have hrefs0 : refsIn l (roots ++ slotVals) = 1 := by
          obtain ⟨_, u'', hu'', hvu0⟩ := before.owned.uniqOk z (weaker.isUniq z huz)
          have : u'' = .loc l := Option.some.inj (hu''.symm.trans hz); subst this
          obtain ⟨_, _, _, _, hr0⟩ := hvu0; exact hr0
        rw [refsIn_append, refs l, refsIn_append] at hrefs0
        rw [refsIn_append] at hrefs
        omega
    have hprivLoc : Own.Plain.PrivPreserved H allocated.2 pre₁.localPriv :=
      Own.Plain.PrivPreserved.alloc (fun l hl => (pre₁.localPriv_facts hl).1)
        (fun l hl => (pre₁.localPriv_facts hl).2) hloc_vs
    have pre₂ := pre₁.transport preserve (fun v hv => hv.alloc _) hreach
      (fun _ _ _ _ _ _ hac => Own.Plain.asCtor_alloc hac) hprivLoc
    have hbal' : Balance allocated.2 external ((allocated.1 :: owned₁) ++ slotVals) := by
      have hr' := Own.Plain.balance_resume counts
      refine Own.Plain.SameRefs.balance ?_ hr'
      intro l; dsimp only [allocated]; simp only [List.cons_append, refsIn_append, refsIn]; omega
    have hfresh0 := before.owned.counts H.size
    rw [Own.Rc.dynCount_fresh] at hfresh0
    have hfreshExt : external H.size = 0 := by omega
    have hfreshOwned : refsIn H.size (roots ++ slotVals) = 0 := by omega
    have hfreshEdge : edgeCount H H.size = 0 := by omega
    have hfreshSplit : refsIn H.size fields + refsIn H.size owned₁ + refsIn H.size slotVals = 0 := by
      rw [refsIn_append, refs H.size, refsIn_append] at hfreshOwned; omega
    have hvU : Own.Plain.UniqVal F.ctors allocated.2 external ((allocated.1 :: owned₁) ++ slotVals)
        allocated.1 := by
      show ∃ b', allocated.2.cell? H.size = some (.live 1 .dyn b') ∧
        external H.size = 0 ∧
        edgeCount allocated.2 H.size = 0 ∧
        refsIn H.size ((.loc H.size :: owned₁) ++ slotVals) = 1
      refine ⟨{ ctor, fields }, ?_, hfreshExt, ?_, ?_⟩
      · simpa [Own.AllocPol.mode] using Own.Proof.alloc_cell .rc H { ctor, fields }
      · dsimp only [allocated]; simp only [Own.Rc.edgeCount_alloc]; omega
      · simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega
    have hpvNew : ∀ l, pre₂.localPriv l → allocated.1 ≠ .loc l := by
      intro l hl hEq
      have hlt : l < H.size := (pre₁.localPriv_facts hl).1
      simp only [allocated, Own.Heap.alloc, Own.Heap.size] at hEq hlt
      cases hEq; omega
    have state := pre₂.bindUniqOwned fresh result hbal' hvU hpvNew
    have activation : Activation F P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) allocated.2
        (placeFresh addresses H.size address) external (live ++ [x]) (Γ₁.addUniqOwn x) Δ
        (sourceEnv.insert x (.ctor ctor logical)) (ownedEnv.insert x allocated.1)
        (allocated.1 :: owned₁) lex sourceJoins ownedJoins k
        (funcFirst bodies source.fn sourceFunction) function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []}
        borrows uniqs retUniq priv rslots slotVals :=
      ⟨state, typed, actualLayout, frame, bodyScope, rfl, fused⟩
    have fieldBounds := before.frame.bounded.args args frameArgs
    have bodyOk : BodyOk H.size {ctor, fields} := by
      refine ⟨arity, positive, ?_⟩
      intro location member
      exact fieldBounds (.loc location) member
    obtain ⟨actualInstruction, acceptedInstruction⟩ := accepted
    have admitted := admitted_ctor_positive positive acceptedInstruction
    have bodyCompatible : BodyCtorOk (tablesOf P pairs) {ctor, fields} :=
      ⟨ctorOk_tablesOf pairs admitted.1, admitted.2, before.frame.compatible.args liveArgs frameArgs⟩
    have heap' : HeapState P pairs allocated.2 (placeFresh addresses H.size address) memory' external
        ((allocated.1 :: owned₁) ++ slotVals) context base bump' limit regionBytes slots' lists' :=
      ⟨by simpa only [List.cons_append] using restored,
        heapOk_alloc heap.ordered bodyOk, heap.compatible.alloc bodyCompatible, heap.extent⟩
    have history : HeapHistory H.size addresses allocated.2.size (placeFresh addresses H.size address) :=
      HeapHistory.allocate H {ctor, fields} addresses address
    exact ResultAt.prefix trace hreach (hprivLoc.mono (fun _ h => Or.inl h)) history
      (by omega)
      (next allocated.2 (placeFresh addresses H.size address) external retUniq priv rslots slotVals
        (live ++ [x]) (Γ₁.addUniqOwn x) Δ
        (sourceEnv.insert x (.ctor ctor logical)) (ownedEnv.insert x allocated.1)
        (allocated.1 :: owned₁) lex ownedJoins sourceFunction function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []}
        memory' context base bump' limit regionBytes slots' lists' callers sourceLookup activation heap')
  · exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
