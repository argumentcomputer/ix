import Compilatrix.Ixby.Runtime.Native.Values

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby

theorem eval_arrayEmpty (limits : Limits) :
    Primitive.arrayEmpty.eval limits [] = .ok (.array #[]) := rfl

theorem eval_arrayLength (limits : Limits) (values : Array Value)
    (bound : values.size < 2 ^ 32) (valid : NatValid limits values.size) :
    Primitive.arrayLength.eval limits [.array values] = .ok (natural values.size) := by
  simp [Primitive.eval, Primitive.arity, Nat.not_le.mpr bound, natural, NatValid] at *
  simp [valid, bind, Except.bind, pure, Except.pure] <;> rfl

theorem eval_arrayGet (limits : Limits) (values : Array Value) (index : Nat) (value : Value)
    (bound : values.size < 2 ^ 32) (valid : NatValid limits index)
    (found : values[index]? = some value) (result : ResultValid limits value) :
    Primitive.arrayGet.eval limits [.array values, natural index] = .ok value := by
  cases value <;> simp_all [Primitive.eval, Primitive.arity, Nat.not_le.mpr bound,
    natural, NatValid, ResultValid, bind, Except.bind, pure, Except.pure]

theorem eval_arraySet (limits : Limits) (values : Array Value) (index : Nat) (value : Value)
    (bound : values.size < 2 ^ 32) (valid : NatValid limits index)
    (inside : index < values.size) (argument : ArgumentValid limits value) :
    Primitive.arraySet.eval limits [.array values, natural index, value] =
      .ok (.array (values.set! index value)) := by
  cases value <;> simp_all [Primitive.eval, Primitive.arity, Nat.not_le.mpr bound,
    natural, NatValid, ArgumentValid, bind, Except.bind, pure, Except.pure]
  rename_i elements
  simp [show ¬4294967296 ≤ elements.size by omega]

theorem eval_arrayPush (limits : Limits) (values : Array Value) (value : Value)
    (bound : values.size + 1 < 2 ^ 32) (argument : ArgumentValid limits value) :
    Primitive.arrayPush.eval limits [.array values, value] = .ok (.array (values.push value)) := by
  have oldBound : values.size < 2 ^ 32 := by omega
  cases value <;> simp_all [Primitive.eval, Primitive.arity, Nat.not_le.mpr oldBound,
    ArgumentValid, bind, Except.bind, pure, Except.pure]
  rename_i elements
  simp [show ¬4294967296 ≤ elements.size by omega]

theorem eval_arrayGet_outside (limits : Limits) (values : Array Value) (index : Nat)
    (bound : values.size < 2 ^ 32) (valid : NatValid limits index)
    (outside : values.size ≤ index) :
    Primitive.arrayGet.eval limits [.array values, natural index] =
      .error (.primitiveValue .arrayGet) := by
  simp_all [Primitive.eval, Primitive.arity, Nat.not_le.mpr bound, natural, NatValid,
    Array.getElem?_eq_none, bind, Except.bind, pure, Except.pure] <;> rfl

theorem eval_builderEmpty (limits : Limits) :
    Primitive.byteBuilderEmpty.eval limits [] = .ok (.byteBuilder #[]) := rfl

theorem eval_builderAppend (limits : Limits) (before chunk : Array UInt8)
    (capacity : before.size + chunk.size ≤ limits.byteArrayBytes) :
    Primitive.byteBuilderAppend.eval limits [.byteBuilder before, .scalar (.bytes chunk)] =
      .ok (.byteBuilder (before ++ chunk)) := by
  have a : ¬limits.byteArrayBytes < before.size := by omega
  have b : ¬limits.byteArrayBytes < chunk.size := by omega
  simp [Primitive.eval, Primitive.arity, Scalar.validate, a, b, Nat.not_lt.mpr capacity,
    bind, Except.bind, pure, Except.pure]

theorem eval_builderFreeze (limits : Limits) (bytes : Array UInt8)
    (capacity : bytes.size ≤ limits.byteArrayBytes) :
    Primitive.byteBuilderFreeze.eval limits [.byteBuilder bytes] = .ok (.scalar (.bytes bytes)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate, Nat.not_lt.mpr capacity,
    bind, Except.bind, pure, Except.pure]

theorem eval_builderLength (limits : Limits) (bytes : Array UInt8)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (valid : NatValid limits bytes.size) :
    Primitive.byteBuilderLength.eval limits [.byteBuilder bytes] = .ok (natural bytes.size) := by
  simp only [NatValid] at valid
  simp [Primitive.eval, Primitive.arity, valid, natural,
    show (Scalar.bytes bytes).validate limits = .ok () from by
      simp [Scalar.validate, Nat.not_lt.mpr capacity], bind, Except.bind, pure, Except.pure]

/-- Both immutable aliases can be frozen independently, including an empty or
unaligned appended chunk. There are no heap addresses in the relation. -/
theorem builder_append_alias (limits : Limits) (before chunk : Array UInt8)
    (capacity : before.size + chunk.size ≤ limits.byteArrayBytes) :
    Primitive.byteBuilderAppend.eval limits [.byteBuilder before, .scalar (.bytes chunk)] =
      .ok (.byteBuilder (before ++ chunk)) ∧
    Primitive.byteBuilderFreeze.eval limits [.byteBuilder before] = .ok (.scalar (.bytes before)) ∧
    Primitive.byteBuilderFreeze.eval limits [.byteBuilder (before ++ chunk)] =
      .ok (.scalar (.bytes (before ++ chunk))) := by
  exact ⟨eval_builderAppend limits before chunk capacity,
    eval_builderFreeze limits before (by omega),
    eval_builderFreeze limits (before ++ chunk) (by simpa using capacity)⟩

end Compilatrix.Ixby.Runtime.Native
