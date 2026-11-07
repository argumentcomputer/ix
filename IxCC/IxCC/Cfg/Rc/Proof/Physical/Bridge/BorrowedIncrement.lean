import IxCC.Cfg.Rc.Proof.Physical.Bridge.Projection
import IxCC.Rt.Rc.Proof.ReadyOperations
import IxCC.Rt.Rc.Proof.IncrementCases

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- The explicit increment after a borrowed field load gets its token from
the live edge. No owned occurrence of the child in roots is assumed. The
actual maximal-count branch is retained, and successful execution preserves
allocator metadata for the next allocation. -/
theorem borrowed_increment
    {H : Heap} {external : Nat → Nat} {roots : List RVal}
    (balance : Balance H external roots)
    {parent refs : Nat} {body : Own.Body} {value : RVal}
    (cell : H.cell? parent = some (.live refs .dyn body)) (field : value ∈ body.fields)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external roots)
      context base bump limit slots lists)
    {word : Lir.Word} (represented : valueWord addresses value = some word) :
    ∃ H', Own.Rc.inc H value 1 = some H' ∧ Balance H' external (value :: roots) ∧
      (∀ root, H.value? root = H'.value? root) ∧
      ((∃ mem', AllocatorReady H' addresses mem' (holdRoots external (value :: roots))
          context base bump limit slots lists ∧
          Lir.eval incProgram 0 [word] mem context = .ok ([], mem')) ∨
        Lir.eval incProgram 0 [word] mem context = .resource .heap) := by
  obtain ⟨H', incremented, counted, values⟩ := dup_projection balance cell field
  refine ⟨H', incremented, counted, values, ?_⟩
  have rebase : (fun location => holdRoots external roots location + refsIn location [value]) =
      holdRoots external (value :: roots) := by
    funext location
    simp only [holdRoots, refsIn]
    omega
  by_cases isLocation : ∃ location, value = .loc location
  · obtain ⟨location, rfl⟩ := isLocation
    obtain ⟨childRefs, childBody, child⟩ := ready.idle.live.fields_live parent refs body location cell field
    obtain ⟨_, address, placed, physical⟩ := ready.idle.live.cell location childRefs .dyn childBody child
    have placement : addresses location = some word := represented
    by_cases room : childRefs < Rt.Rc.maxCount
    · obtain ⟨effect, restored, result⟩ := ready.increment_ready child placement room
      have equal := Option.some.inj (effect.symm.trans incremented)
      rw [equal, rebase] at restored
      exact .inl ⟨_, restored, result⟩
    · have maxed : childRefs = Rt.Rc.maxCount := by have bounded := physical.bounded; omega
      subst childRefs
      exact .inr (increment_max_failure ready.idle child placement)
  · have immediate : ∀ location, value ≠ .loc location := fun location equal =>
      isLocation ⟨location, equal⟩
    obtain ⟨effect, _, result⟩ := increment_immediate_entry ready.idle immediate word represented
    have equal : H = H' := Option.some.inj (effect.symm.trans incremented)
    have unchanged : holdRoots external (value :: roots) = holdRoots external roots := by
      funext location
      simp [holdRoots, refsIn, immediate location]
    exact .inl ⟨mem, by rw [← equal, unchanged]; exact ready, result⟩


end IxCC.Cfg.Rc.Proof.Physical.Bridge
