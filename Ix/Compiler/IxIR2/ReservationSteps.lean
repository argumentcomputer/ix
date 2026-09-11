import Ix.Compiler.IxIR2.ReservationOwnership

/-!
# Reservation ownership through actual executions

Every successful physical step preserves a unique owning credit for each
reserved slot. Calls move those credits into one continuation; returns restore
them, and allocation/discard consumes them. The invariant is derived from an
initial machine, so callers do not supply a callee-exclusion assumption.
-/

namespace Ix.Compiler.IxIR2.Eval

theorem Machine.ReservationOwnership.of_preserved {before after : Machine}
    (owned : before.ReservationOwnership)
    (preserved : EmptySlotsPreserved before.store after.store)
    (credits : before.reservations.Perm after.reservations) : after.ReservationOwnership :=
  (owned.perm credits).preserve preserved

theorem ApplyTransferCase.reservations {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal}
    {resume : Frame} {stack : List Continuation} {function : RVal} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    target.reservations = resume.reservations ++ stack.flatMap Continuation.reservations := by
  cases classified with
  | erased => rfl
  | papUnder => rfl
  | papExtern => rfl
  | papFn =>
      simp only [Machine.reservations, Frame.reservations_empty, List.nil_append,
        List.flatMap_cons]
      split <;> rfl

theorem ApplyTransfer.reservationOwnership {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {arguments : Array RVal}
    {resume : Frame} {stack : List Continuation} {function : RVal} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel function
      arguments resume stack target)
    (owned : (Machine.mk store heapFuel (.running resume stack)).ReservationOwnership) :
    target.ReservationOwnership :=
  owned.of_preserved transferred.preservesEmpty (by rw [transferred.classify.reservations]; rfl)

private theorem takeNoReservation {frame target : Frame} {index : Nat} {credit : Credit}
    (taken : CreditTake frame index target credit) (absent : credit.reservation? = none)
    (stack : List Continuation) :
    (frame.reservations ++ stack.flatMap Continuation.reservations).Perm
      (target.reservations ++ stack.flatMap Continuation.reservations) := by
  simpa [absent] using taken.reservations.append_right (stack.flatMap Continuation.reservations)

private theorem takeReservation {store : Store} {frame target : Frame} {index location : Nat}
    {credit : Credit} {stack : List Continuation}
    (owned : ReservationsOwned store
      (frame.reservations ++ stack.flatMap Continuation.reservations))
    (taken : CreditTake frame index target credit)
    (present : credit.presence = .present (some location)) :
    ReservationsOwned store (location ::
      (target.reservations ++ stack.flatMap Continuation.reservations)) := by
  apply owned.perm
  simpa [Credit.reservation?, present, List.append_assoc] using
    taken.reservations.append_right (stack.flatMap Continuation.reservations)

private theorem reserveAtFrame {store : Store} {frame : Frame} {stack : List Continuation}
    {location : Nat} {box : IxIR1.NodeBox}
    (owned : ReservationsOwned store
      (frame.reservations ++ stack.flatMap Continuation.reservations))
    (found : store.get? location = some box) :
    ReservationsOwned (store.reserve location)
      ((frame.reservations ++ [location]) ++ stack.flatMap Continuation.reservations) := by
  apply (owned.reserve found).perm
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := stack.flatMap Continuation.reservations)
      (l₂ := [location])).append_left frame.reservations

theorem InstructionTransferCase.reservationOwnership {context : Context}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context .physical store heapFuel frame
      stack instruction target)
    (owned : (Machine.mk store heapFuel (.running frame stack)).ReservationOwnership) :
    target.ReservationOwnership := by
  cases classified with
  | move resolved => exact owned
  | alloc schemaAt resolved fields =>
      exact owned.of_preserved (EmptySlotsPreserved.allocNode _ _ _) (.refl _)
  | allocWithAbsent schemaAt resolved fields taken layout absent =>
      exact owned.of_preserved (EmptySlotsPreserved.allocNode _ _ _)
        (takeNoReservation taken (by simp [Credit.reservation?, absent]) stack)
  | allocWithLogical mode => cases mode
  | allocWithPhysical mode schemaAt resolved fields taken layout present reused =>
      exact (takeReservation (frame := { frame with pc := frame.pc + 1 })
        owned taken present).reuse reused
  | discardAbsent taken absent =>
      exact owned.of_preserved (.refl _)
        (takeNoReservation taken (by simp [Credit.reservation?, absent]) stack)
  | discardLogical mode => cases mode
  | discardPhysical mode taken present released =>
      exact (takeReservation (frame := { frame with pc := frame.pc + 1 })
        owned taken present).cons_parts.2.2.preserve
        (Store.releaseReservation_preservesEmpty released)
  | takeUniqueLogical mode => cases mode
  | takeUniquePhysical mode schemaAt resolved viewed unitRC =>
      have reserved := reserveAtFrame owned viewed.parts.1
      simpa [Machine.ReservationOwnership, Machine.reservations,
        Frame.reservations, Frame.liveCredits, Credit.reservation?] using reserved
  | resetSharedLogicalHot mode => cases mode
  | resetSharedPhysicalHot mode schemaAt resolved viewed unitRC =>
      have reserved := reserveAtFrame owned viewed.parts.1
      have reserved' := reserved.congr_nodes
        (after := ((store.tickResetAttempt).reserve _).tickHotReset) rfl
      simpa [Machine.ReservationOwnership, Machine.reservations,
        Frame.reservations, Frame.liveCredits, Credit.reservation?] using reserved'
  | resetSharedCold schemaAt resolved viewed shared retained =>
      have preserved : EmptySlotsPreserved store _ :=
        (EmptySlotsPreserved.setBox viewed.parts.1).trans
          (retained.preservesEmpty)
      exact owned.of_preserved preserved (by
        simp [Machine.reservations, Frame.reservations, Frame.liveCredits]
        rfl)
  | retainShared resolved retained =>
      exact owned.of_preserved (retainShared_preservesEmpty retained) (.refl _)
  | releaseShared resolved released =>
      exact owned.of_preserved (releaseSharedWork_preservesEmpty released) (.refl _)
  | dropUnique resolved dropped =>
      exact owned.of_preserved (dropUniqueWork_preservesEmpty dropped) (.refl _)
  | freeUnique resolved viewed scalarFields =>
      exact owned.of_preserved (EmptySlotsPreserved.kill _ _) (.refl _)
  | fetch resolved boxAt node fieldAt => exact owned
  | callFn noCredits resolved declaration arity nonempty =>
      exact owned.of_preserved (.refl _) (by
        simp [Machine.reservations, Frame.reservations, Frame.liveCredits, Continuation.reservations])
  | callSelf noCredits resolved arity nonempty =>
      exact owned.of_preserved (.refl _) (by
        simp [Machine.reservations, Frame.reservations, Frame.liveCredits, Continuation.reservations])
  | pappFn noCredits declaration papSafe resolved under =>
      exact owned.of_preserved (EmptySlotsPreserved.allocNode _ _ _) (.refl _)
  | pappExtern noCredits declaration resolved under =>
      exact owned.of_preserved (EmptySlotsPreserved.allocNode _ _ _) (.refl _)
  | apply noCredits functionResolved argumentsResolved transferred =>
      exact transferred.reservationOwnership owned
  | extern noCredits resolved declaration argumentArity called => exact owned

theorem TerminatorTransferCase.reservationOwnership {context : Context}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context .physical store heapFuel frame
      stack terminator target)
    (owned : (Machine.mk store heapFuel (.running frame stack)).ReservationOwnership) :
    target.ReservationOwnership := by
  cases classified with
  | jump transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | switchCtor resolved boxAt node alternativeAt transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | switchNatZero resolved transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | switchNatSucc resolved transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | branchPresent lookedUp present transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | branchAbsent lookedUp absent transferred =>
      exact owned.of_preserved (.refl _) (transferred.reservations.append_right _)
  | retResume resolved noCredits world =>
      exact owned.of_preserved (.refl _) (by
        simp only [Machine.reservations, noCredits.reservations_nil,
          List.nil_append, List.flatMap_cons, Continuation.reservations]
        rfl)
  | retHalt resolved noCredits world => exact .nil _
  | retApplyMore resolved noCredits world transferred =>
      apply transferred.reservationOwnership
      simpa only [Machine.ReservationOwnership, Machine.reservations, List.flatMap_cons,
        Continuation.reservations, noCredits.reservations_nil, List.nil_append] using owned
  | tailCallFn noCredits resolved declaration arity nonempty =>
      exact owned.of_preserved (.refl _) (by
        simp [Machine.reservations, noCredits.reservations_nil])
  | tailCallSelf noCredits resolved arity nonempty =>
      exact owned.of_preserved (.refl _) (by
        simp [Machine.reservations, noCredits.reservations_nil])

theorem Step.reservationOwnership {context : Context} {before after : Machine}
    (stepped : Step context .physical before after) (owned : before.ReservationOwnership) :
    after.ReservationOwnership := by
  cases stepped.classify with
  | halted => exact owned
  | instruction blockAt pc instructionAt classified => exact classified.reservationOwnership owned
  | terminator blockAt pc terminatorAt classified => exact classified.reservationOwnership owned

namespace Policy

theorem suspendCall_reservations {context : Context} {before after : Machine}
    {frame : Frame} {stack : List Continuation} {call : DirectCall}
    (running : before.control = .running frame stack)
    (called : suspendCall context before frame stack call = .ok after) :
    after.reservations = before.reservations := by
  obtain ⟨values, definition, _, _, _, _, rfl⟩ := suspendCall_iff.mp called
  simp [Machine.reservations, running, Frame.reservations, Frame.liveCredits,
    Continuation.reservations]

theorem Step.reservationOwnership {policy : CreditPolicy} {context : Context}
    {before after : Machine} (stepped : Step policy context .physical before after)
    (owned : before.ReservationOwnership) : after.ReservationOwnership := by
  rcases stepped.classify with original | ⟨frame, stack, call, _, running, _, called⟩
  · exact original.reservationOwnership owned
  · exact owned.of_preserved (.of_nodes (by rw [(suspendCall_resources running called).1]))
      (by rw [suspendCall_reservations running called])

theorem Steps.reservationOwnership {policy : CreditPolicy} {context : Context}
    {count : Nat} {before after : Machine}
    (steps : Steps policy context .physical count before after)
    (owned : before.ReservationOwnership) : after.ReservationOwnership := by
  induction steps with
  | refl => exact owned
  | cons running head tail ih => exact ih (head.reservationOwnership owned)

theorem initialMachine_reservationOwnership (definition : Function)
    (arguments : Array RVal) (heapFuel : Nat) (store : Store := {}) :
    (initialMachine definition arguments heapFuel store).ReservationOwnership := .nil _

/-- Every reservation in every actual execution prefix has exactly one owning
credit and is excluded from the live heap, even through nested calls. -/
theorem runMain_prefix_reservationOwnership {policy : CreditPolicy} {context : Context}
    {program : Program} {heapFuel count : Nat} {middle : Machine}
    (prefixSteps : Steps policy context .physical count
      (initialMachine program.main #[] heapFuel) middle) :
    middle.ReservationOwnership :=
  prefixSteps.reservationOwnership (initialMachine_reservationOwnership ..)

end Policy

end Ix.Compiler.IxIR2.Eval
