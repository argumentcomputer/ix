import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarConsumed
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarRuntime
import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Own.Plain.Proof.Scalars
import IxCC.Own.Plain.Proof.Scope

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs

/-- Execute a real source primitive binding, including omitted comparisons.
The canonical state, allocator readiness, full frame and source/native cursors
all advance together. Checked admission supplies pins and register bounds. -/
theorem primitive_activation {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {x : Nat} {op : Lam.Prim} {args : List Fir.Arg} {body : Fir.Code}
    {sourceFd : Fir.Fun} {fd : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (sourceLookup : F.fun? source.fn = some sourceFd)
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.bind x (.prim op args) body)
      sourceFd.vars fd source target imm)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    {logical : Fir.Val} (evaluation : Fir.evalRhs F sourceEnv (.prim op args) = .ok logical)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    (∃ value tail charge after,
      step P (.run source sourceCallers H) =
        .next (.run {source with rest := tail, env := source.env.insert x value} sourceCallers H) false ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} charge
        {mem, ctx := context, stack := after :: callers} ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
        (live ++ [x]) (sourceEnv.insert x logical) (ownedEnv.insert x value) (roots ++ [value])
        joins sourceJoins ownedJoins body sourceFd.vars fd
        {source with rest := tail, env := source.env.insert x value} after
        (Own.Plain.nextImm imm x (.prim op args)) ∧
      HeapState P pairs H addresses mem external (roots ++ [value])
        context base bump limit regionBytes slots lists) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have scope : x ∉ live ∧ args.length = op.arity ∧ args.all (Own.Plain.argIn live) = true ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities sourceJoins) body = true := by
    simpa [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨fresh, arity, argsScope, bodyScope⟩ := scope
  have checkedPlain := Own.Plain.checkPlainMap_parts
    (checkProgram_parts (checkScopedProgram_parts checked).1).1
  have pins := Own.Plain.checkBoolPins_sound checkedPlain.2.1
  obtain ⟨values, logicalArgs, arguments, sourceArgs, denArgs⟩ :=
    Own.Plain.args_den before.canonical.env args argsScope
  have primitive : Fir.primResult F op logicalArgs = .ok logical := by
    simpa only [Fir.evalRhs, sourceArgs] using evaluation
  obtain ⟨value, result, den, immediate⟩ := Own.Plain.primResult_immediate pins denArgs primitive
  have lexicalEffect : Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
      ownedEnv H (.fir (.prim op args)) = .ok (value, H) := by
    simp [Own.evalRhs, arguments, result, Sem.Result.map]
  have atBind : At F P source ownedEnv ownedJoins
      (.bind x (.prim op args) (Own.Plain.lowerCode (live ++ [x]) joins body
        (Own.Plain.nextImm imm x (.prim op args)))) := before.layout
  obtain ⟨tail, head, continuation⟩ := atBind.bind_continuation
  have sub := before.lexical.1
  have fullEffect : Own.evalRhs .rc P.base.tables source.env H (.fir (.prim op args)) =
      .ok (value, H) := by
    rw [generate_tables (checkProgram_parts (checkScopedProgram_parts checked).1).2]
    exact Cfg.Proof.evalRhs_sub_ok sub lexicalEffect
  obtain ⟨supply, real⟩ := checked_binding_bounds checked consuming sourceLookup before.frame.lookup atBind trivial
  obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs functions main
  obtain ⟨_, physical⟩ := frame_step pow gcd before.frame supply head trivial real fullEffect
    before.running mem context callers
  rcases physical with ⟨charge, after, running, trace, frame, fused⟩ | failed
  · have balance : Own.Rc.Balance H external (roots ++ [value]) :=
      Own.Plain.balance_append_comm (show Own.Rc.Balance H external ([value] ++ roots) from
        Own.Plain.balance_immediate before.canonical.counts immediate)
    have hargs_imm : Own.Plain.ImmEnv ownedEnv (Own.Plain.argVars args) :=
      Own.Plain.immEnv_argVars arguments (Own.Plain.primResult_args_immediate denArgs primitive)
    have nextState := before.canonical.bind_prim x op args fresh argsScope hargs_imm immediate
      den balance (fun _ _ => rfl)
    have unchanged : Own.Rc.holdRoots external (roots ++ [value]) = Own.Rc.holdRoots external roots := by
      funext location
      simp [Own.Rc.holdRoots, Own.Rc.refsIn_append, Own.Rc.refsIn, immediate location]
    refine .inl ⟨value, tail, charge, after, ?_, trace,
      ⟨nextState, continuation value, frame, bodyScope, running, fused⟩, ?_⟩
    · rw [step_ordinary head (pure_unreserved P.base.size x (rhs := .fir (.prim op args)) trivial)]
      rw [Cfg.Proof.step_run_bind head (by intro f as equal; cases equal)]
      simp only [Own.immRhs]
      rw [fullEffect]
    · exact ⟨by rw [unchanged]; exact heap.ready, heap.ordered, heap.compatible, heap.extent⟩
  · exact .inr failed


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
