import IxCC.Cfg.Rc.Proof.Physical.AllocationAvailable
import IxCC.Cfg.Rc.Proof.Physical.AllocationFailure
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Complete positive-constructor operation: actual initialized return with
full allocator state, or actual bounded-storage failure. No space, success,
or desired simulation premise is required. -/
theorem allocation_outcome {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    (positive : 0 < body.fields.length) (small : body.fields.length ≤ maxFields)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} (words : Nat → Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure body.fields.length))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields body.fields.length body.ctor.tag)))
    (registers : ∀ i < body.fields.length, env[i]? = some (words i))
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    (∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size address)
        finalMem (fun location => external location + refsIn location [(heap.alloc .rc body).1])
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
        {mem := finalMem, ctx := context,
          stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers}) ∨
    Sem.Reaches (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
      1 (.resource .heap) := by
  by_cases empty : lists (fieldsClass body.fields.length) = []
  · by_cases space : bump.toNat + classBytes (fieldsClass body.fields.length) ≤ limit.toNat
    · exact .inl (allocation_available ready positive small tagBound nobj nscalar shared
        (fun _ => space) words wrapperLookup procedureLookup registers values caller callers dest)
    · exact .inr (allocation_short_failure ready positive small tagBound empty
        (by omega) wrapperLookup procedureLookup (caller :: callers))
  · exact .inl (allocation_available ready positive small tagBound nobj nscalar shared
      (fun h => False.elim (empty h)) words wrapperLookup procedureLookup registers values caller callers dest)


end IxCC.Cfg.Rc.Native
