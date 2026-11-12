import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Own.Plain.Proof.Owned.Actions
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.CopyStep
import IxCC.Cfg.Rc.Proof.Physical.DropStep
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation
import IxCC.Cfg.Rc.Proof.Physical.FrameTransport
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.Physical.CtorActions
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Cfg.Rc.Proof.Native.HeapHistory

/-! # One `inc`, one `dec` (heap stage 2)

The two cases of the physical induction that the canonical layer never had alone: a single
increment or decrement marker, wherever the certificate places it. The token taken or added may
be any of the context's (the typing context's tokens are a multiset); an immediate's action is a
no-op on a vacuous token; an increment of a borrowed variable makes it owned. The native steps are
the canonical layer's single-marker steps, with every token of the activation held as an outer
owner (`Tokens` over an empty lexical list), so no distinctness of the token list is needed. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs
open IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- `copy_marker_step` for any value that may be duplicated (an owned token's, a borrowed
projection's, an immediate), not only a lexical token's. -/
theorem copy_marker_step_of
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    {dummy x : Nat} {tail : List Cfg.Instr}
    (head : source.rest = marker P.base.size dummy (.inc x 1) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {value : RVal}
    (before : Tokens H external held live ρf ρo roots)
    (lookup : ρo.get? x = some value) (permission : CanDup H value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ρo.get? dummy = none) (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ H' mem',
      Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external (value :: held) live ρf ρo roots ∧
      Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external (roots ++ value :: held))
        context base bump limit slots lists ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} 2
        {mem := mem', ctx := context,
          stack := {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo (target.env.insert dummy 1) ∧
      (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have consuming : consume P (layoutOf P) (marker P.base.size dummy (.inc x 1)) =
      .ok (.bind dummy (.fir (.call P.base.size [.var x, .lit (.nat 1)]))) :=
    IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_increment P (layoutOf P) dummy x
  have liveOperand : ¬ Rt.Proof.Fused (tablesOf P pairs) function x :=
    consumed_call_live cursor head consuming sourceLookup (.var x) (by simp) x rfl
  rcases cursor.call head consuming mem context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookup,
      position, statement, continuation⟩ := success
    have operandsKnown : Rt.Lower.operands source.fn [.var x, .lit (.nat 1)] =
        .ok (some [.v x, .imm 3]) := rfl
    rw [operandsKnown] at lowered
    cases lowered
    obtain ⟨wrapperLookup, procedureLookup⟩ := source_stage_increment_runtime P functions main
    obtain ⟨H', action, tokens, values, outcome⟩ :=
      fused_increment_ready_instruction_fresh before lookup permission ready
        wrapperLookup procedureLookup target callers functionLookup blockLookup position statement
        registers liveOperand absent
    rcases outcome with ⟨mem', restored, trace, words⟩ | failed
    · exact .inl ⟨H', mem', action, tokens, restored, trace,
        continuation.withEnvs source.env (target.env.insert dummy 1) [], words, values⟩
    · exact .inr (reaches_resource_fails failed)
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure

theorem evalActions_single {ρ : Own.Env} {H H' : Heap} {a : Own.Plain.Action}
    (h : Own.Plain.evalAction ρ H a = .ok H') : Own.Plain.evalActions ρ H [a] = .ok H' := by
  simp [Own.Plain.evalActions, h, Sem.Result.bind]

/-- Same lookup, same action. -/
theorem evalAction_inc_congr {ρ ρ' : Own.Env} {H : Heap} {x : Fir.Var} {n : Nat}
    (same : ρ.get? x = ρ'.get? x) :
    Own.Plain.evalAction ρ H (.inc x n) = Own.Plain.evalAction ρ' H (.inc x n) := by
  simp only [Own.Plain.evalAction, same]

theorem evalAction_dec_congr {ρ ρ' : Own.Env} {H : Heap} {x : Fir.Var}
    (same : ρ.get? x = ρ'.get? x) :
    Own.Plain.evalAction ρ H (.dec x) = Own.Plain.evalAction ρ' H (.dec x) := by
  simp only [Own.Plain.evalAction, same]

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **One increment**, of an owned, borrowed or immediate variable. -/
theorem physical_inc (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} {n : Nat} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k) :
    PhysicalCode F P config pairs main clock sourceJoins (.act (.inc x n) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  obtain ⟨Γ', hinc, typed⟩ := Own.Plain.checkCode_inc before.typed
  obtain ⟨value, H', owned', rfl, ownLookup, permission, ownAction, state, preserved, refs⟩ :=
    Own.Plain.inc_step_refs before.owned hinc
  have sub := before.lexical.1
  have frameLookup : source.env.get? x = some value := sub x value ownLookup
  have layout : At F P source ownedEnv ownedJoins (Own.Plain.actionPrefix [.inc x 1] k) :=
    before.layout
  obtain ⟨first, tail, head, after, absent⟩ :=
    checked_prefix_cursor admission.scopedProgram layout sourceLookup before.frame.words
  have head' : source.rest = marker P.base.size first (.inc x 1) :: tail := by
    simpa [encodePrefix] using head
  have tokens : Tokens H external roots [] sourceEnv source.env [] :=
    ⟨(fun _ h => by cases h), rfl,
      (Own.Rc.balance_hold (active := []) (held := roots)).mp (by simpa using before.owned.counts),
      List.nodup_nil⟩
  have ready : Gen.AllocatorReady maxClass H addresses memory (holdRoots external ([] ++ roots))
      context base bump limit slots lists := by simpa using heap.ready
  rcases copy_marker_step_of (Public.Spec.rawSource config P pairs) main before.frame.cursor head'
      before.frame.lookup tokens frameLookup permission ready before.frame.words
      (absent first (Nat.le_refl _)) before.running callers with stepped | failed
  · obtain ⟨H₂, mem', action, _, ready', trace, cursor', words', values⟩ := stepped
    have same : Own.Plain.evalAction source.env H (.inc x 1) =
        Own.Plain.evalAction ownedEnv H (.inc x 1) :=
      evalAction_inc_congr (by rw [frameLookup, ownLookup])
    rw [same, ownAction] at action
    have eq : H' = H₂ := by injection action
    subst eq
    have single := evalActions_single ownAction
    have size : H'.size = H.size := actions_size single
    have heap' : HeapState P pairs H' addresses mem' external owned' context base bump limit
        regionBytes slots lists :=
      ⟨by rw [holdRoots_sameRefs refs]; simpa using ready', actions_heapOk heap.ordered single,
        heap.compatible.evalActions single, heap.extent⟩
    have consuming : consume P (layoutOf P) (marker P.base.size first (.inc x 1)) =
        .ok (.bind first (.fir (.call P.base.size [.var x, .lit (.nat 1)]))) :=
      IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_increment P (layoutOf P) first x
    have activation : Activation F P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H' addresses external
        live Γ' Δ sourceEnv ownedEnv owned' lex sourceJoins ownedJoins k sourceFunction.vars function
        {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert first 1, dsts := []} :=
      ⟨state, typed, after,
        ⟨before.frame.lookup, cursor', words', by rw [size]; exact before.frame.bounded,
          before.frame.compatible⟩,
        before.scope, rfl,
        consumed_call_done before.frame.lookup before.frame.cursor head' consuming source.env⟩
    have history : HeapHistory H.size addresses H'.size addresses := ⟨by omega, fun _ _ => rfl⟩
    exact ResultAt.prefix trace preserved history (by omega)
      (next H' addresses external live Γ' Δ sourceEnv ownedEnv owned' lex ownedJoins sourceFunction
        function {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert first 1, dsts := []} mem'
        context base bump limit regionBytes slots lists callers sourceLookup activation heap')
  · exact ResultAt.of_fails failed

/-- **One decrement**, of an owned or immediate variable: a release. -/
theorem physical_dec (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k) :
    PhysicalCode F P config pairs main clock sourceJoins (.act (.dec x) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  obtain ⟨Γ', hdec, typed⟩ := Own.Plain.checkCode_dec before.typed
  obtain ⟨value, H', owned', ownLookup, refs, ownAction, state, preserved⟩ :=
    Own.Plain.dec_step_refs before.owned hdec
  have sub := before.lexical.1
  have frameLookup : source.env.get? x = some value := sub x value ownLookup
  have layout : At F P source ownedEnv ownedJoins (Own.Plain.actionPrefix [.dec x] k) :=
    before.layout
  obtain ⟨first, tail, head, after, absent⟩ :=
    checked_prefix_cursor admission.scopedProgram layout sourceLookup before.frame.words
  have head' : source.rest = marker P.base.size first (.dec x) :: tail := by
    simpa [encodePrefix] using head
  have havail : Γ.avail x = true := by
    obtain ⟨Γ₁, ht, _⟩ := Own.Plain.Ctx.dec_ok hdec
    rcases Own.Plain.Ctx.take_ok ht with ⟨hi, _⟩ | ⟨_, m, hm, _⟩
    · simp [Own.Plain.Ctx.avail_eq, hi]
    · simp [Own.Plain.Ctx.avail_eq, Own.Plain.Ctx.tokens, Src.NatMap.getD, hm]
  obtain ⟨u, w, hu, hw, den⟩ := before.owned.den x havail
  have : u = value := Option.some.inj (hu.symm.trans ownLookup)
  subst u
  have tokens : Tokens H external owned' [x] sourceEnv source.env [value] :=
    ⟨fun y hy => by
        simp only [List.mem_singleton] at hy
        subst hy
        exact ⟨value, w, frameLookup, hw, den⟩,
      by simp [Own.Plain.EnvRoots, Own.evalArgs, Own.evalArg, frameLookup],
      (Own.Rc.balance_hold (active := [value]) (held := owned')).mp
        (by simpa using refs.balance before.owned.counts),
      by simp⟩
  have ready : Gen.AllocatorReady maxClass H addresses memory (holdRoots external ([value] ++ owned'))
      context base bump limit slots lists := by
    rw [List.singleton_append, ← holdRoots_sameRefs refs]; exact heap.ready
  rcases drop_marker_step (Public.Spec.rawSource config P pairs) main before.frame.cursor head'
      before.frame.lookup tokens ready before.frame.words
      (absent first (Nat.le_refl _)) before.running callers with stepped | failed
  · obtain ⟨value', remaining, H₂, mem', slots', lists', charges, lookup', equal, action, _,
      ready', trace, cursor', words', _⟩ := stepped
    have same : Own.Plain.evalAction source.env H (.dec x) =
        Own.Plain.evalAction ownedEnv H (.dec x) :=
      evalAction_dec_congr (by rw [frameLookup, ownLookup])
    rw [same, ownAction] at action
    have eq : H' = H₂ := by injection action
    subst eq
    obtain ⟨rfl, rfl⟩ : value' = value ∧ remaining = [] := by
      simp only [List.cons.injEq] at equal
      exact ⟨equal.1.symm, equal.2.symm⟩
    have single := evalActions_single ownAction
    have size : H'.size = H.size := actions_size single
    have heap' : HeapState P pairs H' addresses mem' external owned' context base bump limit
        regionBytes slots' lists' :=
      ⟨by simpa using ready', actions_heapOk heap.ordered single,
        heap.compatible.evalActions single, heap.extent⟩
    have consuming : consume P (layoutOf P) (marker P.base.size first (.dec x)) =
        .ok (.bind first (.fir (.call (P.base.size+1) [.var x]))) :=
      IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_decrement P (layoutOf P) first x
    have activation : Activation F P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H' addresses external
        live Γ' Δ sourceEnv ownedEnv owned' lex sourceJoins ownedJoins k sourceFunction.vars function
        {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert first 1, dsts := []} :=
      ⟨state, typed, after,
        ⟨before.frame.lookup, cursor', words', by rw [size]; exact before.frame.bounded,
          before.frame.compatible⟩,
        before.scope, rfl,
        consumed_call_done before.frame.lookup before.frame.cursor head' consuming source.env⟩
    have history : HeapHistory H.size addresses H'.size addresses := ⟨by omega, fun _ _ => rfl⟩
    exact ResultAt.prefix trace preserved history (by omega)
      (next H' addresses external live Γ' Δ sourceEnv ownedEnv owned' lex ownedJoins sourceFunction
        function {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert first 1, dsts := []} mem'
        context base bump limit regionBytes slots' lists' callers sourceLookup activation heap')
  · exact ResultAt.of_fails failed

end

end IxCC.Cfg.Rc.Native.Spec
