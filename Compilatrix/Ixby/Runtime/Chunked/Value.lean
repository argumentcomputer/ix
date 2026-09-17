import Compilatrix.Ixby.Runtime.Chunked.Builder

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Scalar CtorId FunctionId)

/-- Only builders change representation; constructors, PAPs and arrays retain
their exact tags, ordered children, and immutable alias semantics. -/
inductive Value where
  | scalar (value : Scalar)
  | ctor (id : CtorId) (fields : Array Value)
  | pap (function : FunctionId) (captured : Array Value)
  | erased
  | array (elements : Array Value)
  | byteBuilder (builder : Builder)
  deriving Repr, Inhabited

@[simp] def Value.toReference (value : Value) : Ix.Ixby.Value := match value with
  | .scalar value => .scalar value
  | .ctor id fields => .ctor id (fields.attach.map fun v => v.val.toReference)
  | .pap function captured => .pap function (captured.attach.map fun v => v.val.toReference)
  | .erased => .erased
  | .array elements => .array (elements.attach.map fun v => v.val.toReference)
  | .byteBuilder builder => .byteBuilder builder.freeze
termination_by sizeOf value
decreasing_by all_goals have h := Array.sizeOf_lt_of_mem v.property; simp_wf; omega

@[simp] def Value.ofReference (value : Ix.Ixby.Value) : Value := match value with
  | .scalar value => .scalar value
  | .ctor id fields => .ctor id (fields.attach.map fun v => Value.ofReference v.val)
  | .pap function captured => .pap function (captured.attach.map fun v => Value.ofReference v.val)
  | .erased => .erased
  | .array elements => .array (elements.attach.map fun v => Value.ofReference v.val)
  | .byteBuilder bytes => .byteBuilder (Builder.ofBytes bytes)
termination_by sizeOf value
decreasing_by all_goals have h := Array.sizeOf_lt_of_mem v.property; simp_wf; omega

@[simp] theorem Value.toReference_ofReference (value : Ix.Ixby.Value) :
    (Value.ofReference value).toReference = value := by
  cases value with
  | scalar value => simp
  | ctor id fields =>
    simp only [Value.ofReference, Value.toReference, Array.attach_map_val, Array.map_map]
    congr 1
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp only [Array.getElem_map]
      exact Value.toReference_ofReference fields[i]
  | pap function captured =>
    simp only [Value.ofReference, Value.toReference, Array.attach_map_val, Array.map_map]
    congr 1
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp only [Array.getElem_map]
      exact Value.toReference_ofReference captured[i]
  | erased => simp
  | array elements =>
    simp only [Value.ofReference, Value.toReference, Array.attach_map_val, Array.map_map]
    congr 1
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp only [Array.getElem_map]
      exact Value.toReference_ofReference elements[i]
  | byteBuilder bytes => simp [Value.ofReference, Value.toReference]
termination_by sizeOf value

@[simp] theorem Value.toReference_eq_scalar (value : Value) (scalar : Scalar) :
    value.toReference = .scalar scalar ↔ value = .scalar scalar := by
  cases value <;> simp

@[simp] theorem map_toReference_eq_scalar_cons (values : List Value) (scalar : Scalar)
    (rest : List Ix.Ixby.Value) :
    values.map Value.toReference = .scalar scalar :: rest ↔
      ∃ tail, values = .scalar scalar :: tail ∧ tail.map Value.toReference = rest := by
  cases values with
  | nil => simp
  | cons value tail =>
    simp only [List.map_cons, List.cons.injEq, Value.toReference_eq_scalar]
    constructor
    · rintro ⟨h, mapped⟩
      exact ⟨tail, ⟨h, rfl⟩, mapped⟩
    · rintro ⟨tail', ⟨h, rfl⟩, mapped⟩
      exact ⟨h, mapped⟩

end Compilatrix.Ixby.Runtime.Chunked
