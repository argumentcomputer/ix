import IxCC.Cfg.Rc.Proof.Physical.NativeMarkers
import IxCC.Rt.Rc.Proof.ReleaseCaller

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Actual ordinary-call dec wrapper, complete release, and erased dummy
return. All physical heap/partition facts are restored from the runtime's proved idle
invariant; the caller supplies no release simulation. -/
theorem decrement_body_complete
    {heap : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {value : RVal} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists)
    {word : Word} (represented : valueWord addresses value = some word)
    {P : Lir.Program} {wrapper procedure dummy : Nat} {env : Lir.Env} {wrapperFunction : Lir.Func}
    (wrapperLookup : P.funcs[wrapper]? = some wrapperFunction)
    (wrapperBody : wrapperFunction.blocks[0]? = some {
      body := #[.call [] procedure [.v 0]], term := .ret [.imm 1] })
    (procedureLookup : P.funcs[procedure]? = some dec)
    (argument : env[0]? = some word)
    (caller : Lir.Frame) (callers : List Lir.Frame) (destination : caller.dsts = [dummy]) :
    ∃ heap' mem' slots' lists' charges,
      dropAll heap [value] = some heap' ∧
      ReleaseInvariant heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
        (1 + charges)
        {mem := mem', ctx := context,
          stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} := by
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := []}
  have enter : Lir.enter P procedure [word] =
      some {fn := procedure, label := 0, pos := 0, env := decEnv word} := by
    simp [Lir.enter, procedureLookup, dec, Lir.bindParams, decEnv]
  have callStep := marker_call (g := wrapper) (env := env)
    (rest := caller :: callers) (mem := mem) (ctx := context) wrapperLookup wrapperBody argument enter
  obtain ⟨heap', mem', slots', lists', charges, released, restored, procedureTrace⟩ :=
    release_caller_complete idle word represented P procedure procedureLookup
      continuation (caller :: callers) rfl
  have returnStep := marker_return (callee := procedure) (env := env) (caller := caller)
    (rest := callers) (mem := mem') (ctx := context) wrapperLookup wrapperBody destination
  refine ⟨heap', mem', slots', lists', charges, released, restored, ?_⟩
  have composed := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (procedureTrace.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep)))
  simpa [continuation] using composed

theorem decrement_wrapper_complete
    {heap : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {value : RVal} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists)
    {word : Word} (represented : valueWord addresses value = some word)
    {P : Lir.Program} {wrapper procedure dummy : Nat} {env : Lir.Env}
    (wrapperLookup : P.funcs[wrapper]? = some (decrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some dec)
    (argument : env[0]? = some word)
    (caller : Lir.Frame) (callers : List Lir.Frame) (destination : caller.dsts = [dummy]) :
    ∃ heap' mem' slots' lists' charges,
      dropAll heap [value] = some heap' ∧
      ReleaseInvariant heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
        (1 + charges)
        {mem := mem', ctx := context,
          stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} :=
  decrement_body_complete idle represented wrapperLookup rfl procedureLookup argument caller callers destination



end IxCC.Cfg.Rc.Native
