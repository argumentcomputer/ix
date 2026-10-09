import Compilatrix.Cfg.Rc.Proof.Physical.AllocationFreeComplete
import Compilatrix.Cfg.Rc.Proof.Physical.AllocationBumpComplete

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs

/-- Select the actual allocator branch from its concrete free list. Available
space is required only if that class has no reusable slot. Both branches
establish the same complete ownership and ordinary caller-return contract. -/
theorem allocation_available {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : AllocatorReady heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    (positive : 0 < body.fields.length) (small : body.fields.length < 32)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (space : lists (smallClass body.fields.length) = [] →
      bump.toNat + cellBytes body.fields.length ≤ limit.toNat)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} (words : Nat → Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure body.fields.length))
    (procedureLookup : P.funcs[procedure]? = some (alloc body.fields.length body.ctor.tag))
    (registers : ∀ i < body.fields.length, env[i]? = some (words i))
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    ∃ address next finalMem finalSlots finalLists,
      AllocatorReady (heap.alloc .rc body).2 (placeFresh addresses heap.size address)
        finalMem (fun location => external location + refsIn location [(heap.alloc .rc body).1])
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
        {mem := finalMem, ctx := context,
          stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers} := by
  cases head : lists (smallClass body.fields.length) with
  | nil =>
    have result := allocation_bump_complete ready positive small tagBound nobj nscalar shared
      head (space head) words wrapperLookup procedureLookup registers values caller callers dest
    exact ⟨bump, _, _, _, _, result⟩
  | cons address tail =>
    have present : address ∈ lists (smallClass body.fields.length) := by simp [head]
    obtain ⟨target, member, targetAddress, targetClass, _⟩ :=
      ready.idle.free_placed (smallClass body.fields.length) address present
    have selected : lists target.cls = target.address :: tail := by rw [targetClass, targetAddress, head]
    have result := allocation_free_complete ready member selected targetClass positive small
      tagBound nobj nscalar shared words wrapperLookup procedureLookup registers values caller callers dest
    exact ⟨target.address, bump, _, _, _, result⟩


end Compilatrix.Cfg.Rc.Native
