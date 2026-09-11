import Ix.Compiler.IxIR2.ReservationHeap
import Ix.Compiler.IxIR2.CallResources

/-!
# Linear ownership of physical reservations

Credit consumption removes exactly one entry from a frame. Edge transfer moves
the complete remaining credit file. Reservations are unique across the active
frame and every continuation, and each names an existing empty heap slot.
-/

namespace Ix.Compiler.IxIR2.Eval

def Credit.reservation? (credit : Credit) : Option Nat :=
  match credit.presence with
  | .present location => location
  | .absent => none

def Frame.liveCredits (frame : Frame) : List Credit := frame.credits.toList.filterMap id

def Frame.reservations (frame : Frame) : List Nat :=
  frame.liveCredits.filterMap Credit.reservation?

def Continuation.reservations : Continuation → List Nat
  | .resume frame | .applyMore _ frame => frame.reservations

def Machine.reservations (machine : Machine) : List Nat :=
  match machine.control with
  | .halted _ => []
  | .running frame stack => frame.reservations ++ stack.flatMap Continuation.reservations

private theorem filterMap_set_none_perm {α : Type} {slots : List (Option α)}
    {index : Nat} {value : α} (found : slots[index]? = some (some value)) :
    (slots.filterMap id).Perm (value :: (slots.set index none).filterMap id) := by
  induction slots generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          cases head with
          | none => simpa using ih found
          | some head =>
              simpa using ((ih found).cons head).trans (List.Perm.swap _ _ _)

theorem CreditTake.liveCredits {frame target : Frame} {index : Nat} {credit : Credit}
    (taken : CreditTake frame index target credit) :
    frame.liveCredits.Perm (credit :: target.liveCredits) := by
  obtain ⟨rfl, found⟩ := taken.target_eq
  simpa only [Frame.liveCredits, Array.toList_setIfInBounds] using
    filterMap_set_none_perm (slots := frame.credits.toList) (by simpa using found)

theorem CreditTake.reservations {frame target : Frame} {index : Nat} {credit : Credit}
    (taken : CreditTake frame index target credit) :
    frame.reservations.Perm (credit.reservation?.toList ++ target.reservations) := by
  cases present : credit.reservation? <;>
    simpa [Frame.reservations, List.filterMap_cons, present] using
      taken.liveCredits.filterMap Credit.reservation?

theorem CreditTakeSequence.liveCredits {frame target : Frame} {indices : List Nat}
    {credits : List Credit} (taken : CreditTakeSequence frame indices target credits) :
    frame.liveCredits.Perm (credits ++ target.liveCredits) := by
  induction taken with
  | nil => exact .refl _
  | cons head tail ih => exact head.liveCredits.trans (ih.cons _)

theorem CreditTakeMany.liveCredits {frame target : Frame} {indices : Array Nat}
    {credits : Array Credit} (taken : CreditTakeMany frame indices target credits) :
    frame.liveCredits.Perm (credits.toList ++ target.liveCredits) :=
  taken.sequence.liveCredits

theorem NoLiveCredits.liveCredits_nil {frame : Frame} (cleared : NoLiveCredits frame) :
    frame.liveCredits = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro credit member
  have absent := Array.any_eq_false'.mp cleared credit (by simpa using member)
  cases credit <;> simp_all

theorem NoLiveCredits.reservations_nil {frame : Frame} (cleared : NoLiveCredits frame) :
    frame.reservations = [] := by
  simp [Frame.reservations, cleared.liveCredits_nil]

theorem EdgeTransfer.liveCredits {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal} (transferred : EdgeTransfer frame edge implicitValues target) :
    frame.liveCredits.Perm target.liveCredits := by
  obtain ⟨values, credits, after, block, _, taken, cleared, _, _, _, rfl⟩ := transferred.parts
  have permuted := taken.liveCredits
  rw [cleared.liveCredits_nil, List.append_nil] at permuted
  simpa [Frame.liveCredits] using permuted

theorem EdgeTransfer.reservations {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal} (transferred : EdgeTransfer frame edge implicitValues target) :
    frame.reservations.Perm target.reservations :=
  transferred.liveCredits.filterMap Credit.reservation?

@[simp] theorem Frame.reservations_empty (definition : Function) (block pc : Nat)
    (values : Array RVal) :
    ({ definition, block, pc, values, credits := #[] } : Frame).reservations = [] := rfl

@[simp] theorem Frame.reservations_push (frame : Frame) (credit : Credit) :
    ({ frame with credits := frame.credits.push (some credit) } : Frame).reservations =
      frame.reservations ++ credit.reservation?.toList := by
  cases present : credit.reservation? <;>
    simp [Frame.reservations, Frame.liveCredits, List.filterMap_append, present]

structure ReservationsOwned (store : Store) (locations : List Nat) : Prop where
  unique : locations.Nodup
  empty : ∀ location ∈ locations, store.EmptySlot location

namespace ReservationsOwned

theorem nil (store : Store) : ReservationsOwned store [] := ⟨by simp, by simp⟩

theorem perm {store : Store} {left right : List Nat}
    (owned : ReservationsOwned store left) (permuted : left.Perm right) :
    ReservationsOwned store right :=
  ⟨permuted.nodup_iff.mp owned.unique,
    fun location member => owned.empty location (permuted.mem_iff.mpr member)⟩

theorem preserve {before after : Store} {locations : List Nat}
    (owned : ReservationsOwned before locations) (preserved : EmptySlotsPreserved before after) :
    ReservationsOwned after locations :=
  ⟨owned.unique, fun location member => preserved location (owned.empty location member)⟩

theorem congr_nodes {before after : Store} {locations : List Nat}
    (owned : ReservationsOwned before locations)
    (same : after.heap.nodes = before.heap.nodes) : ReservationsOwned after locations :=
  owned.preserve (.of_nodes same)

theorem cons_parts {store : Store} {location : Nat} {locations : List Nat}
    (owned : ReservationsOwned store (location :: locations)) :
    location ∉ locations ∧ store.EmptySlot location ∧ ReservationsOwned store locations := by
  have unique := List.nodup_cons.mp owned.unique
  exact ⟨unique.1, owned.empty location (by simp), unique.2,
    fun other member => owned.empty other (by simp [member])⟩

theorem not_live {store : Store} {locations : List Nat} {location : Nat}
    (owned : ReservationsOwned store locations) (member : location ∈ locations) :
    store.get? location = none := (owned.empty location member).not_live

theorem live_not_owned {store : Store} {locations : List Nat} {location : Nat}
    {box : IxIR1.NodeBox} (owned : ReservationsOwned store locations)
    (live : store.get? location = some box) : location ∉ locations := by
  intro member
  rw [owned.not_live member] at live
  cases live

theorem reserve {store : Store} {locations : List Nat} {location : Nat}
    {box : IxIR1.NodeBox} (owned : ReservationsOwned store locations)
    (live : store.get? location = some box) :
    ReservationsOwned (store.reserve location) (locations ++ [location]) := by
  have fresh := owned.live_not_owned live
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨owned.unique, by simp, ?_⟩
    intro other member last lastMember same
    have lastEq : last = location := by simpa using lastMember
    exact fresh ((same.trans lastEq) ▸ member)
  · intro other member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact EmptySlotsPreserved.reserve store location other (owned.empty other member)
    · exact Store.reserve_empty live

theorem reuse {store output : Store} {location payload : Nat} {locations : List Nat}
    {world : Ixon.Owned} {node : IxIR1.Node}
    (owned : ReservationsOwned store (location :: locations))
    (reused : store.reuseReservation location world node payload = .ok output) :
    ReservationsOwned output locations := by
  obtain ⟨absent, _, rest⟩ := owned.cons_parts
  exact ⟨rest.unique, fun other member => Store.reuseReservation_preservesOther reused
    (fun same => absent (same ▸ member)) (rest.empty other member)⟩

end ReservationsOwned

def Machine.ReservationOwnership (machine : Machine) : Prop :=
  ReservationsOwned machine.store machine.reservations

theorem Machine.ReservationOwnership.callee_exclusion {machine : Machine} {location : Nat}
    (owned : machine.ReservationOwnership) (reserved : location ∈ machine.reservations) :
    machine.store.get? location = none := owned.not_live reserved

end Ix.Compiler.IxIR2.Eval
