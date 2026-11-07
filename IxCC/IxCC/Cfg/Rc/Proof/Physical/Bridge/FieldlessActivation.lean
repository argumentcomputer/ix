import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarActivation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs

/-- A checked zero-field constructor has no copy prefix or allocation. Its
actual admitted assignment binds the immediate and retains full readiness. -/
theorem fieldless_activation {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {x : Nat} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {body : Fir.Code}
    (zero : ctor.arity = 0)
    {sourceFd : Fir.Fun} {fd : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (sourceLookup : F.fun? source.fn = some sourceFd)
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.bind x (.ctor ctor args) body)
      sourceFd.vars fd source target)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    {logical : Fir.Val} (evaluation : Fir.evalRhs F sourceEnv (.ctor ctor args) = .ok logical)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    (∃ tail charge after,
      step P (.run source sourceCallers H) =
        .next (.run {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} sourceCallers H) false ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} charge
        {mem, ctx := context, stack := after :: callers} ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
        (live ++ [x]) (sourceEnv.insert x logical) (ownedEnv.insert x (.ctor0 ctor)) (roots ++ [.ctor0 ctor])
        joins sourceJoins ownedJoins body sourceFd.vars fd
        {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after ∧
      HeapState P pairs H addresses mem external (roots ++ [.ctor0 ctor])
        context base bump limit regionBytes slots lists) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have scope : x ∉ live ∧ Own.Plain.rhsIn (Own.Plain.signatures F) live (.ctor ctor args) = true ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities sourceJoins) body = true := by
    simpa [Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨fresh, rhsScope, bodyScope⟩ := scope
  have arity : args.length = ctor.arity := by
    simp only [Own.Plain.rhsIn, Bool.and_eq_true, decide_eq_true_eq] at rhsScope
    exact rhsScope.1.1.1.1
  have empty : args = [] := List.length_eq_zero_iff.mp (arity.trans zero)
  subst args
  have logicalEqual : Fir.Val.ctor ctor [] = logical := by
    simpa [Fir.evalRhs, Fir.evalArgs, zero] using evaluation
  subst logical
  have fieldless : ctor.fieldless = true := by simp [Fir.CtorInfo.fieldless, zero]
  have atBind : At F P source ownedEnv ownedJoins
      (.bind x (.ctor ctor []) (Own.Plain.lowerCode (live ++ [x]) joins body)) := before.layout
  obtain ⟨tail, head, continuation⟩ := atBind.bind_continuation
  have pureRhs : PureRhs (Own.immRhs (.ctor ctor [])) := fieldless
  have effect : Own.evalRhs .rc P.base.tables source.env H (Own.immRhs (.ctor ctor [])) =
      .ok (.ctor0 ctor, H) := by simp [Own.immRhs, Own.evalRhs, Own.evalArgs, zero, fieldless]
  obtain ⟨supply, real⟩ := checked_binding_bounds checked consuming sourceLookup before.frame.lookup atBind pureRhs
  obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs functions main
  rcases (frame_step pow gcd before.frame supply head pureRhs real effect
      before.running mem context callers).2 with scalar | failed
  · obtain ⟨charge, after, running, trace, frame, fused⟩ := scalar
    have immediate : ∀ l, (Own.RVal.ctor0 ctor) ≠ .loc l := by intro l; simp
    have balance : Own.Rc.Balance H external (roots ++ [.ctor0 ctor]) :=
      Own.Plain.balance_append_comm (show Own.Rc.Balance H external ([.ctor0 ctor] ++ roots) from
        Own.Plain.balance_immediate before.canonical.counts immediate)
    have nextState := before.canonical.bind x fresh (Own.Proof.den_ctor0 H ctor) balance (fun _ _ => rfl)
    have unchanged : Own.Rc.holdRoots external (roots ++ [.ctor0 ctor]) = Own.Rc.holdRoots external roots := by
      funext location
      simp [Own.Rc.holdRoots, Own.Rc.refsIn_append, Own.Rc.refsIn]
    refine .inl ⟨tail, charge, after, ?_, trace,
      ⟨nextState, continuation (.ctor0 ctor), frame, bodyScope, running, fused⟩, ?_⟩
    · rw [step_ordinary head (pure_unreserved P.base.size x pureRhs)]
      rw [Cfg.Proof.step_run_bind head (by intro f as equal; cases equal), effect]
    · exact ⟨by rw [unchanged]; exact heap.ready, heap.ordered, heap.compatible, heap.extent⟩
  · exact .inr failed


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
