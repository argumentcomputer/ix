import IxCC.Cfg.Rc.Proof.Physical.ReservedHeader
import IxCC.Rt.Rc.Gen.Proof.AllocatorAccess
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs

theorem reserved_from_ready {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem external context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (body : Own.Body)
    (sizeClass : chosen.cls = fieldsClass body.fields.length)
    (positive : 0 < body.fields.length) (small : body.fields.length ≤ maxFields)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (header : WordAt mem chosen.address
      (dynamicHeader body.fields.length (fieldsClass body.fields.length) body.ctor.tag 1)) :
    ReservedCell mem chosen.address body := by
  have valid := ready.idle.partition.valid chosen member
  have bounds := ready.idle.partition.bounds
  have byteSize : classBytes (fieldsClass body.fields.length) = 8 * classWords chosen.cls := by
    rw [sizeClass]; rfl
  have reads := unique_header_reads small tagBound header
  refine {
    fields_positive := positive
    fields_small := small
    tag := tagBound
    nobj
    nscalar
    shared
    nonzero := ready.slot_nonzero member
    aligned := ?_
    fit := ?_
    readable := ?_
    writable := ?_
    header := reads.1
    count := reads.2 }
  · exact valid.2.2.1
  · rw [byteSize]; omega
  · intro j hj; exact (ready.slot_access member (by rwa [byteSize] at hj)).1
  · intro j hj; exact (ready.slot_access member (by rwa [byteSize] at hj)).2


end IxCC.Cfg.Rc.Native
