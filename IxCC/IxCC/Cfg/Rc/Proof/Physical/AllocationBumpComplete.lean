import IxCC.Cfg.Rc.Proof.Physical.AllocationBumpReady
import IxCC.Cfg.Rc.Proof.Physical.AllocWrapper
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- The actual bump-path wrapper returns its initialized pointer and the
identical final memory has complete ownership, placement and allocator facts. -/
theorem allocation_bump_complete {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    (positive : 0 < body.fields.length) (small : body.fields.length ≤ maxFields)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (empty : lists (fieldsClass body.fields.length) = [])
    (space : bump.toNat + classBytes (fieldsClass body.fields.length) ≤ limit.toNat)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} (words : Nat → Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure body.fields.length))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields body.fields.length body.ctor.tag)))
    (registers : ∀ i < body.fields.length, env[i]? = some (words i))
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    let next := bump + UInt64.ofNat (classBytes (fieldsClass body.fields.length))
    let finalMem := publishFields
      (Gen.reserveBump mem context bump next (CellLayout.ofFields body.fields.length body.ctor.tag) (fieldsClass body.fields.length))
      bump words (List.range body.fields.length)
    Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size bump)
      finalMem (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base next limit
      (publishSlots heap.size bump (Gen.bumpSlot bump (fieldsClass body.fields.length) :: slots)) lists ∧
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := finalMem, ctx := context,
        stack := {caller with env := caller.env.insert destination bump, dsts := []} :: callers} := by
  obtain ⟨execution, finalReady⟩ := allocation_bump_ready ready
    positive small tagBound nobj nscalar shared empty space words values
  refine ⟨finalReady, allocation_wrapper_success positive small tagBound execution
    wrapperLookup procedureLookup registers ?_ caller callers dest⟩
  intro i hi byte hb
  have bounds := ready.idle.partition.bounds
  obtain ⟨_, _, hlow, _⟩ := Gen.fieldsClass_spec positive small
  have offsetBound : 8 * (i + 1) + byte < classBytes (fieldsClass body.fields.length) := by
    omega
  have addressNat : (bump + UInt64.ofNat (8 * (i + 1) + byte)).toNat =
      bump.toNat + (8 * (i + 1) + byte) := Rt.Proof.addr_toNat (by omega)
  have access := ready.arena_access (bump + UInt64.ofNat (8 * (i + 1) + byte))
    (by rw [addressNat]; omega) (by rw [addressNat]; omega)
  simpa [Gen.reserveBump, X86.Memory.write, fieldAddress_byte] using access.2


end IxCC.Cfg.Rc.Native
