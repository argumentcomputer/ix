import IxCC.Cfg.Rc.Proof.Physical.TailActivation
import IxCC.Cfg.Rc.Proof.Native.CodeContract
import IxCC.Fir.Proof.Unfold

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

theorem source_call_arity {F : Fir.Program} {f : Nat} {args : List Fir.Arg}
    (signature : (Own.Plain.signatures F).lookup f = some args.length)
    {callee : Fir.Fun} (lookup : F.fun? f = some callee)
    {env : Fir.Env} {logical : List Fir.Val} (arguments : Fir.evalArgs env args = some logical) :
    logical.length = callee.params.length := by
  obtain ⟨actual, _, actualLookup, arity⟩ := Own.Plain.signatures_lookup signature
  have same : actual = callee := Option.some.inj (actualLookup.symm.trans lookup)
  subst actual
  exact (Fir.evalArgs_length env arguments).trans arity.symm

/-- The complete source tail-call clause uses only the smaller source-clock
claim. Cleanup, self-tail back edges, ordinary native tail entry, and source
callee arity are derived before applying that claim. -/
theorem tail_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    (admission : CodeAdmission F bodies P config pairs functions) (main clock : Nat)
    (smaller : ∀ next, next < clock → PhysicalAtClock F P config pairs main next)
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
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    ResultAt P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external context base limit regionBytes clock
      {mem, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock ρf Jf (.tcall f args)) := by
  rcases tail_activation admission.scopedProgram admission.consuming admission.lowering main
      before sourceLookup heap [] callers with success | failed
  · obtain ⟨callee, fields, logical, H', mem', slots', lists', consumedFd, after, final, cost,
      calleeLookup, ownArgs, sourceArgs, actions, size, preserved, history, activation,
      sameFn, heap', trace, charged⟩ := success
    have scope : (Own.Plain.signatures F).lookup f = some args.length ∧
        args.all (Own.Plain.argIn live) = true := by
      simpa [Own.Plain.scopeOk, Bool.and_eq_true] using before.scope
    have arity := source_call_arity scope.1 calleeLookup sourceArgs
    rw [Fir.eval_tcall, sourceArgs]
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
    rw [Fir.evalCall_of F clock calleeLookup logical]
    unfold Fir.callFun
    rw [if_pos arity]
    apply ResultAt.charge trace charged preserved history
    intro next eqClock
    exact smaller next (by omega) H' addresses external (callee.params.map Prod.fst)
      (Fir.bindAll .leaf (callee.params.map Prod.fst) logical)
      (Own.bindAll .leaf (callee.params.map Prod.fst) fields) fields [] [] []
      callee.body callee consumedFd after final mem' context base bump limit regionBytes slots' lists' callers
      (by rw [sameFn]; exact calleeLookup) activation heap'
  · exact ResultAt.of_fails failed



end IxCC.Cfg.Rc.Native.Spec
