import Ix.Compiler.X86.StreamTrace

/-! Executable decisions for the concrete call/stack conditions. These
instances evaluate the stated predicates; they introduce no reflection axiom. -/

namespace Ix.Compiler.X86.Stream

instance (result : Except MemoryFault Word) (value : Word) : Decidable (result = .ok value) := by
  cases result with
  | error fault => exact isFalse (by intro impossible; cases impossible)
  | ok result => exact decidable_of_iff (result = value) ⟨congrArg Except.ok, Except.ok.inj⟩

instance (address candidate : Word) (count : Nat) : Decidable (inRange address count candidate) := by
  unfold inRange
  infer_instance

instance (holes : Holes) [DecidablePred holes] (address : Word) (count : Nat) :
    DecidablePred (addRange holes address count) := fun candidate => by
  unfold addRange
  infer_instance

instance (holes : Holes) [DecidablePred holes] (address : Word) (count : Nat) :
    DecidablePred (clearRange holes address count) := fun candidate => by
  unfold clearRange
  infer_instance

instance (holes : Holes) [DecidablePred holes] (address : Word) (count : Nat) :
    Decidable (ReadableData holes address count) := by
  unfold ReadableData
  infer_instance

instance (frames : List ReturnFrame) (address : Word) (count : Nat) :
    Decidable (FramesDisjoint frames address count) := by
  unfold FramesDisjoint
  infer_instance

instance (holes : Holes) [DecidablePred holes] (frames : List ReturnFrame)
    (operation : Decode.Operation) (core : Core) : Decidable (OperationSafe holes frames operation core) := by
  unfold OperationSafe
  repeat' split
  all_goals infer_instance

instance (holes : Holes) [DecidablePred holes] (operation : Decode.Operation) (core : Core) :
    DecidablePred (nextHoles holes operation core) := by
  unfold nextHoles
  split <;> infer_instance

instance (program : Program) (machine : Machine) (holes : Holes) [DecidablePred holes] :
    DecidablePred (holeStep program machine holes) := by
  unfold holeStep
  repeat' split
  all_goals infer_instance

instance (program : Program) (holes : Holes) [DecidablePred holes] (machine : Machine) :
    Decidable (SafeAt program holes machine) := by
  unfold SafeAt
  repeat' split
  all_goals infer_instance

def safeTraceDecidable (runtime : Runtime) (checked : Checked) (fuel : Nat)
    (holes : Holes) [DecidablePred holes] (machine : Machine) : Decidable (SafeTrace runtime checked fuel holes machine) :=
  match fuel with
  | 0 => isTrue trivial
  | fuel + 1 => by
      unfold SafeTrace
      letI := safeTraceDecidable runtime checked fuel (holeStep checked.program machine holes) (step runtime checked machine)
      split <;> infer_instance

instance (runtime : Runtime) (checked : Checked) (fuel : Nat) (holes : Holes) [DecidablePred holes] (machine : Machine) :
    Decidable (SafeTrace runtime checked fuel holes machine) := safeTraceDecidable runtime checked fuel holes machine

end Ix.Compiler.X86.Stream
