/-! # Shared semantic vocabulary

Outcomes, behaviours and first-order observations shared by every IR of the
rebuilt pipeline, from the source evaluator down to machine readback.

Every executable semantics takes a clock `k : Nat` and returns a `Result`.
The clock is charged only at calls and loop back edges, so straight-line
reasoning never counts it. `timeout` means only that the clock ran out;
`stuck` is a semantic error that well-formed programs never reach. -/

namespace IxCC.Sem

/-- Explicit resource failures, which the top theorem allows the target to
add. No IR above Lir produces one: `Nat` is exact down to Cfg, and
`natOverflow` is a target failure until bignums land. -/
inductive Resource
  | heap
  | stack
  | natOverflow
  deriving DecidableEq, Repr, Inhabited

/-- One clocked evaluation outcome. -/
inductive Result (α : Type) where
  | ok (value : α)
  | timeout
  | resource (failure : Resource)
  | trap
  | stuck
  deriving DecidableEq, Repr, Inhabited

namespace Result

/-- Sequencing: every outcome other than `ok` is final. -/
@[inline] def bind {α β : Type} : Result α → (α → Result β) → Result β
  | ok value, next => next value
  | timeout, _ => timeout
  | resource failure, _ => resource failure
  | trap, _ => trap
  | stuck, _ => stuck

instance : Monad Result where
  pure := ok
  bind := bind

@[simp] theorem bind_ok {α β : Type} (value : α) (next : α → Result β) :
    bind (ok value) next = next value := rfl

@[simp] theorem pure_eq {α : Type} (value : α) : (pure value : Result α) = ok value := rfl

@[simp] theorem bind_eq {α β : Type} (result : Result α) (next : α → Result β) :
    result >>= next = bind result next := rfl

/-- Map the value of a successful outcome. -/
@[inline] def map {α β : Type} (f : α → β) (result : Result α) : Result β :=
  bind result (fun value => ok (f value))

/-- Lift a partial step: `none` is `stuck`. -/
@[inline] def ofOption {α : Type} : Option α → Result α
  | some value => ok value
  | none => stuck

/-- Whether the outcome is a successful value. -/
def isOk {α : Type} : Result α → Bool
  | ok _ => true
  | _ => false

end Result

/-- Observable behaviour of a deterministic clocked semantics: the outcome at
any clock that does not time out, or `diverges` if every clock times out. -/
inductive Behaviour (α : Type) where
  | terminates (value : α)
  | diverges
  | resource (failure : Resource)
  | trap
  | stuck
  deriving DecidableEq, Repr, Inhabited

/-- First-order observations, shared by every IR down to machine readback.
Constructor fields are listed in the relevant-field order the source layer
fixes. -/
inductive Obs where
  | nat (value : Nat)
  | word (value : UInt64)
  | ctor (tag : Nat) (fields : List Obs)
  | bytes (data : List UInt8)
  deriving BEq, Repr, Inhabited

end IxCC.Sem
