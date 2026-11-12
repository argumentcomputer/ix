import IxCC.Cfg.Rc.Proof.Physical.PublicationInvariant
import IxCC.Cfg.Rc.Proof.Physical.PublicationMetadata
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Publication retains the actual allocator control words and arena access
alongside the complete new ownership and physical heap invariant. -/
theorem publication_ready {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (sizeClass : chosen.cls = fieldsClass body.fields.length)
    (storage : ReservedCell mem chosen.address body) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base bump limit (publishSlots heap.size chosen.address slots) lists := by
  exact ready.after_protected
    (publication_protected ready.idle member sizeClass words (List.range body.fields.length)
      (fun _ h => List.mem_range.mp h) mem)
    (publication_idle ready.idle member reserved sizeClass storage words values)


end IxCC.Cfg.Rc.Native
