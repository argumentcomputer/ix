import IxCC.Cfg.Rc.Proof.Physical.NativeMarkers
import IxCC.Rt.Rc.Proof.IncrementCaller

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- The successful dynamic inc1 wrapper performs the exact count-memory
update, restores the idle ownership invariant with one additional token and
returns erased1 into the reserved dummy destination. Native admission checks
the marker's literal one; the body invokes the one-increment procedure. -/
theorem increment_body_complete
    {heap : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {location refs : Nat} {body : Own.Body} {address : Word}
    (cell : heap.cell? location = some (.live refs .dyn body))
    (placement : addresses location = some address) (room : refs < Rt.Rc.maxCount)
    {P : Lir.Program} {wrapper procedure dummy : Nat} {env : Lir.Env} {wrapperFunction : Lir.Func}
    (wrapperLookup : P.funcs[wrapper]? = some wrapperFunction)
    (wrapperBody : wrapperFunction.blocks[0]? = some {
      body := #[.call [] procedure [.v 0]], term := .ret [.imm 1] })
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (argument : env[0]? = some address)
    (caller : Lir.Frame) (callers : List Lir.Frame) (destination : caller.dsts = [dummy]) :
    Own.Rc.inc heap (.loc location) 1 = some (setCell heap location (.live (refs+1) .dyn body)) ∧
    ReleaseInvariant (setCell heap location (.live (refs+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat refs))
      (fun k => external k + refsIn k [.loc location]) none [] context base bump limit slots lists ∧
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := storeCount mem address (UInt64.ofNat refs), ctx := context,
        stack := {caller with env := caller.env.insert dummy 1, dsts := []} :: callers} := by
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := []}
  have enter : Lir.enter P procedure [address] =
      some {fn := procedure, label := 0, pos := 0, env := incEnv address} := by
    simp [Lir.enter, procedureLookup, Rt.Rc.Procs.inc, Lir.bindParams, incEnv]
  have callStep := marker_call (g := wrapper) (env := env)
    (rest := caller :: callers) (mem := mem) (ctx := context) wrapperLookup wrapperBody argument enter
  obtain ⟨incremented, restored, procedureTrace⟩ := increment_caller_complete idle cell placement room
    P procedure procedureLookup continuation (caller :: callers) rfl
  have returnStep := marker_return (callee := procedure) (env := env) (caller := caller)
    (rest := callers) (mem := storeCount mem address (UInt64.ofNat refs)) (ctx := context)
    wrapperLookup wrapperBody destination
  refine ⟨incremented, restored, ?_⟩
  have composed := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (procedureTrace.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep)))
  simpa [continuation] using composed


end IxCC.Cfg.Rc.Native
