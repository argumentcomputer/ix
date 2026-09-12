import Compilatrix.X86.PhysicalHeapReleaseEval

namespace Compilatrix.X86.PhysicalHeap
open IxIR2.Eval (Frame Credit Continuation)

abbrev activeReservations (frame : Frame) (stack : List Continuation) : List Nat :=
  frame.reservations ++ suspendedReservations stack

theorem HeapAt.reservations_perm {schemas constructors offset store before after words}
    (related : HeapAt schemas constructors offset store before words) (permuted : before.Perm after) :
    HeapAt schemas constructors offset store after words := by
  refine { related with reservations := by simpa only [permuted.length_eq] using related.reservations, dead := ?_ }
  intro location above below empty
  rcases related.dead location above below empty with free | ⟨tag, member⟩
  · exact .inl free
  · exact .inr ⟨tag, permuted.mem_iff.mp member⟩

theorem reservation_take {frame target : Frame} {index : Nat} {credit : Credit} {location : Nat}
    (taken : IxIR2.Eval.CreditTake frame index target credit) (present : credit.presence = .present (some location))
    (stack : List Continuation) :
    (activeReservations frame stack).Perm (location :: activeReservations target stack) := by
  simpa [activeReservations, IxIR2.Eval.Credit.reservation?, present] using
    taken.reservations.append_right (suspendedReservations stack)

theorem reservation_take_kept {frame target : Frame} {index : Nat} {credit : Credit} {location : Nat}
    (taken : IxIR2.Eval.CreditTake frame index target credit) (present : credit.presence = .present (some location))
    (stack : List Continuation) :
    (∀ other, other ≠ location → other ∈ activeReservations frame stack → other ∈ activeReservations target stack) ∧
      (activeReservations target stack).length + 1 = (activeReservations frame stack).length := by
  have permuted := reservation_take taken present stack
  refine ⟨?_, by simpa [Nat.add_comm] using permuted.length_eq.symm⟩
  intro other different member
  have after := permuted.mem_iff.mp member
  simpa [different] using after

theorem reservation_push (frame : Frame) (stack : List Continuation) (id : IxIR2.LayoutId) (location : Nat) :
    let output := { frame with credits := frame.credits.push (some ⟨id, .present (some location)⟩) }
    (∀ other, other ∈ activeReservations frame stack → other ∈ activeReservations output stack) ∧
      location ∈ activeReservations output stack ∧
      (activeReservations output stack).length = (activeReservations frame stack).length + 1 := by
  simp only [activeReservations, IxIR2.Eval.Frame.reservations_push, IxIR2.Eval.Credit.reservation?, Option.toList_some]
  constructor
  · intro other member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    exact member.elim (fun left => .inl (.inl left)) Or.inr
  · constructor
    · simp
    · simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Compilatrix.X86.PhysicalHeap
