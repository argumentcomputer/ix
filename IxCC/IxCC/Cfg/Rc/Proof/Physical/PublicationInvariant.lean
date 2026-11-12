import IxCC.Cfg.Rc.Proof.Physical.PublicationFree
import IxCC.Cfg.Rc.Proof.Physical.PublicationKinds
import IxCC.Cfg.Rc.Proof.Physical.PublicationLive
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Publishing a reserved object establishes the complete idle invariant.
The actual payload writes consume the existing field tokens as incoming
edges and return one fresh logical root, including when the slot is recycled. -/
theorem publication_idle {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields) none []
      context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (sizeClass : chosen.cls = fieldsClass body.fields.length)
    (storage : ReservedCell mem chosen.address body) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    Gen.ReleaseInvariant maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1]) none []
      context base bump limit (publishSlots heap.size chosen.address slots) lists := by
  refine {
    balance := ?_
    live := publication_heapLive idle member reserved sizeClass storage words values
    partition := partition_publish idle.partition member reserved body (by
      rw [sizeClass, Gen.classOf_fields storage.nscalar (by rw [storage.nobj]; exact storage.fields_small),
        storage.nobj])
    cursors := trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_layout := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursor_scan := by simp
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := publication_free_exact idle member reserved heap.size
    free_distinct := idle.free_distinct
    free_placed := publication_free_placed idle member reserved heap.size
    free_chains := publication_free_chains idle member reserved sizeClass words
    free_heads := fun _ lo hi => publication_free_heads idle member sizeClass words lo hi
    head_writable := ?_
    head_fit := idle.head_fit
    context_fit := idle.context_fit
    head_disjoint := ?_ }
  · simpa [cursorTokens, flattenPending] using publication_balance (idle_field_tokens idle)
  · intro earlier frame tail impossible
    have lengths := congrArg List.length impossible
    simp at lengths
  · intro slot present location suffix predecessor
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
    rw [publishSlot_pending idle.partition member reserved oldMember heap.size location suffix predecessor]
    have old := idle.pending_exact old oldMember location suffix predecessor
    simpa using old
  · intro cls lower upper j bound
    have frame := publication_head_frame idle member sizeClass words lower upper
    rw [frame.writable]
    exact idle.head_writable cls lower upper j bound
  · intro cls lower upper slot present
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
    simpa using idle.head_disjoint cls lower upper old oldMember


end IxCC.Cfg.Rc.Native
