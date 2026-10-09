import Compilatrix.Cfg.Rc.Proof.Physical.AllocationFreeReady
import Compilatrix.Cfg.Rc.Proof.Physical.AllocWrapper

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs

/-- Full free-slot allocation and publication in an arbitrary ambient program.
The actual wrapper returns the initialized address to its caller, while the
same final memory satisfies complete ownership, placement and allocator facts. -/
theorem allocation_free_complete {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : AllocatorReady heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    {target : Slot} (member : target ∈ slots) {tail : List Word}
    (head : lists target.cls = target.address :: tail)
    (sizeClass : target.cls = smallClass body.fields.length)
    (positive : 0 < body.fields.length) (small : body.fields.length < 32)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} (words : Nat → Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure body.fields.length))
    (procedureLookup : P.funcs[procedure]? = some (alloc body.fields.length body.ctor.tag))
    (registers : ∀ i < body.fields.length, env[i]? = some (words i))
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    let finalMem := publishFields
      (reserveFree mem context target.address (tail.headD 0) body.fields.length body.ctor.tag)
      target.address words (List.range body.fields.length)
    AllocatorReady (heap.alloc .rc body).2 (placeFresh addresses heap.size target.address)
      finalMem (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base bump limit
      (publishSlots heap.size target.address (reserveSlots target.address slots)) (popFree lists target.cls) ∧
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := finalMem, ctx := context,
        stack := {caller with env := caller.env.insert destination target.address, dsts := []} :: callers} := by
  obtain ⟨execution, finalReady⟩ := allocation_free_ready ready member head sizeClass
    positive small tagBound nobj nscalar shared words values
  refine ⟨finalReady, allocation_wrapper_success positive small tagBound execution
    wrapperLookup procedureLookup registers ?_ caller callers dest⟩
  intro i hi byte hb
  have access := ready.slot_access member (j := 8 * (i + 1) + byte) (by
    rw [sizeClass]
    simp only [smallClass]
    omega)
  simpa [reserveFree, X86.Memory.write, fieldAddress_byte] using access.2


end Compilatrix.Cfg.Rc.Native
