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
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`x := C args`** with at least one field. -/
theorem allocation_result (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} {ctor : Fir.CtorInfo} {args : List Fir.Arg} (positive : 0 < ctor.arity)
    {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.ctor ctor args) (Own.Plain.eraseCode k)))
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
  have balance : Balance H (holdRoots external owned₁) fields :=
    balance_hold.mp (refs.balance before.owned.counts)
  have ready : Gen.AllocatorReady maxClass H addresses memory (holdRoots external (fields ++ owned₁))
      context base bump limit slots lists := by
    rw [← holdRoots_sameRefs refs]; exact heap.ready
  have lexical := before.lexical.1
  have frameArgs : Own.evalArgs source.env args = some fields := Cfg.Proof.evalArgs_sub lexical ownArgs
  obtain ⟨tail, bindingHead, _⟩ := bind_layout before.layout .erased
  have head : source.rest = .bind x (.alloc ctor args .shared) :: tail := bindingHead
  have real := checked_binding_real admission.scopedProgram before.layout sourceLookup
    (by simp [Own.immRhs, reserved])
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
        (placeFresh addresses H.size address) allocated.2.size sourceFunction.vars function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []} :=
      ⟨before.frame.lookup, cursor', words', bounds,
        before.frame.compatible.bind x (show ValueCtorOk (tablesOf P pairs) allocated.1 by trivial)⟩
    have fused := consumed_call_done before.frame.lookup before.frame.cursor head consuming
      (source.env.insert x allocated.1)
    have pre₁ := ((before.owned.pre.weaker weaker inv₁.roots).transport preserve
      (fun v hv => Own.Plain.canDup_alloc hv _))
    have state := pre₁.bindOwned fresh result
      ((Own.Plain.SameRefs.comm _ _).balance (Own.Plain.balance_resume counts))
    have activation : Activation F P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) allocated.2
        (placeFresh addresses H.size address) external (live ++ [x]) (Γ₁.addOwn x 1) Δ
        (sourceEnv.insert x (.ctor ctor logical)) (ownedEnv.insert x allocated.1)
        (allocated.1 :: owned₁) lex sourceJoins ownedJoins k sourceFunction.vars function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []} :=
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
        (allocated.1 :: owned₁) context base bump' limit regionBytes slots' lists' :=
      ⟨restored, heapOk_alloc heap.ordered bodyOk, heap.compatible.alloc bodyCompatible, heap.extent⟩
    have history : HeapHistory H.size addresses allocated.2.size (placeFresh addresses H.size address) :=
      HeapHistory.allocate H {ctor, fields} addresses address
    exact ResultAt.prefix trace (fun value logical _ den => preserve value logical den) history
      (by omega)
      (next allocated.2 (placeFresh addresses H.size address) external (live ++ [x]) (Γ₁.addOwn x 1) Δ
        (sourceEnv.insert x (.ctor ctor logical)) (ownedEnv.insert x allocated.1)
        (allocated.1 :: owned₁) lex ownedJoins sourceFunction function
        {source with rest := tail, env := source.env.insert x allocated.1}
        {target with pos := target.pos+1, env := target.env.insert x address, dsts := []}
        memory' context base bump' limit regionBytes slots' lists' callers sourceLookup activation heap')
  · exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
