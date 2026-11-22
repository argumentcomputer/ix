import IxCC.Own.Rc.Proof.ReleaseValue
import IxCC.Rt.Rc.Proof.Pending

/-! Abstract/physical unique-parent bridge. Suspended suffixes flatten in DFS
order. The currently loaded child is counted separately, exactly once. -/
namespace IxCC.Rt.Rc.Procs
open IxCC.Own
open IxCC.Own.Rc
open Lir

def flattenPending : List (List RVal) → List RVal
  | [] => []
  | suffix :: parents => suffix ++ flattenPending parents

theorem unique_has_no_survivor {heap : Heap} {external : Nat → Nat}
    {pending : List RVal} {location : Nat} {body : Body}
    (hc : heap.cell? location = some (.live 1 .dyn body))
    (hb : Balance heap external (.loc location :: pending)) :
    external location = 0 ∧ refsIn location pending = 0 ∧ edgeCount heap location = 0 := by
  have he := hb location
  simp [dynCount, hc, refsIn] at he
  omega

/-- No abstract live root/edge may observe overwritten parent metadata.
Its fields become pending tokens, matching current child plus suffix stack. -/
theorem detach_worklist {heap : Heap} {external : Nat → Nat}
    {parents : List (List RVal)} {location : Nat} {body : Body}
    {child : RVal} {suffix : List RVal}
    (hc : heap.cell? location = some (.live 1 .dyn body))
    (hb : Balance heap external (.loc location :: flattenPending parents))
    (hfields : body.fields = child :: suffix) :
    releaseOne heap (.loc location) (flattenPending parents) =
        some (setCell heap location .dead, child :: flattenPending (suffix :: parents)) ∧
    Balance (setCell heap location .dead) external (child :: flattenPending (suffix :: parents)) ∧
    external location = 0 ∧ refsIn location (flattenPending parents) = 0 ∧
    edgeCount heap location = 0 := by
  refine ⟨?_, ?_, unique_has_no_survivor hc hb⟩
  · simp [releaseOne, hc, hfields, flattenPending]
  · simpa [hfields, flattenPending] using balance_free hc hb

/-- Concrete child load and pending parent bytes accompany the abstract
transfer. This is a local release bridge, not whole-loop termination or
ambient-program simulation. -/
theorem detach_correspondence {heap : Heap} {external : Nat → Nat}
    {parents : List (List RVal)} {location : Nat} {body : Body}
    {child : RVal} {suffix : List RVal} {addresses : AddressMap}
    {mem : X86.Memory} {address : Word}
    (hc : heap.cell? location = some (.live 1 .dyn body))
    (hb : Balance heap external (.loc location :: flattenPending parents))
    (hfields : body.fields = child :: suffix)
    (hcell : LiveCell addresses mem address 1 body) (predecessor : Word) :
    ∃ childWord,
      valueWord addresses child = some childWord ∧
      loadWord mem .w64 .zero (address+8) = some childWord ∧
      PendingParent addresses mem (detachParent mem address predecessor body.fields.length)
        address predecessor body ∧
      Balance (setCell heap location .dead) external (child :: flattenPending (suffix :: parents)) := by
  obtain ⟨word, hv, hr⟩ := hcell.first_child (child := child) (by simp [hfields])
  exact ⟨word, hv, hr, hcell.detach_pending predecessor, (detach_worklist hc hb hfields).2.1⟩




end IxCC.Rt.Rc.Procs
