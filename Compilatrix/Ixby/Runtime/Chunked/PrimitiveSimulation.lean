import Compilatrix.Ixby.Runtime.Chunked.ScalarSimulation

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Primitive Limits Error Scalar)

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

@[simp] theorem except_throw_eq (error : ε) : (throw error : Except ε α) = .error error := rfl

@[simp] theorem except_pure_eq (value : α) : (pure value : Except ε α) = .ok value := rfl

def referenceValidateArg (limits : Limits) (primitive : Primitive) :
    Ix.Ixby.Value → Except Error Unit
  | .scalar value => value.validate limits
  | .array values =>
    if values.size ≥ 2 ^ 32 then .error (.primitiveValue primitive) else .ok ()
  | .byteBuilder bytes => (Scalar.bytes bytes).validate limits
  | _ => pure ()

@[simp] theorem validateArg_sim (limits : Limits) (primitive : Primitive) (value : Value) :
    referenceValidateArg limits primitive value.toReference =
      validateArg limits primitive value := by
  cases value <;> simp [referenceValidateArg, validateArg, Scalar.validate, Array.attach_map_val]

def referenceEvalUnchecked (limits : Limits) (primitive : Primitive)
    (args : List Ix.Ixby.Value) : Except Error Ix.Ixby.Value := match primitive, args with
  | .arrayEmpty, [] => pure (.array #[])
  | .arrayLength, [.array values] => pure (.scalar (.nat values.size))
  | .arrayGet, [.array values, .scalar (.nat i)] =>
    match values[i]? with
    | some value => pure value
    | none => throw (.primitiveValue primitive)
  | .arraySet, [.array values, .scalar (.nat i), value] =>
    if i < values.size then pure (.array (values.set! i value))
    else throw (.primitiveValue primitive)
  | .arrayPush, [.array values, value] =>
    if values.size + 1 < 2 ^ 32 then pure (.array (values.push value))
    else throw (.primitiveValue primitive)
  | .byteBuilderEmpty, [] => pure (.byteBuilder #[])
  | .byteBuilderAppend, [.byteBuilder bytes, .scalar (.bytes chunk)] =>
    if bytes.size + chunk.size > limits.byteArrayBytes then throw (.limit .byteArrayBytes)
    else pure (.byteBuilder (bytes ++ chunk))
  | .byteBuilderFreeze, [.byteBuilder bytes] => pure (.scalar (.bytes bytes))
  | .byteBuilderLength, [.byteBuilder bytes] => pure (.scalar (.nat bytes.size))
  | .bytesAppend, [.scalar (.bytes a), .scalar (.bytes b)] =>
    if a.size + b.size > limits.byteArrayBytes then throw (.limit .byteArrayBytes)
    else pure (.scalar (.bytes (a ++ b)))
  | _, _ => primitive.evalScalarUnchecked args

@[simp] theorem Value.toReference_eq_array (value : Value) (elements : Array Ix.Ixby.Value) :
    value.toReference = .array elements ↔
      ∃ values, value = .array values ∧ values.map Value.toReference = elements := by
  cases value <;> simp [Array.attach_map_val]

@[simp] theorem Value.toReference_eq_builder (value : Value) (bytes : Array UInt8) :
    value.toReference = .byteBuilder bytes ↔
      ∃ builder, value = .byteBuilder builder ∧ builder.freeze = bytes := by
  cases value <;> simp

theorem evalUnchecked_sim (limits : Limits) (primitive : Primitive) (args : List Value) :
    (evalUnchecked limits primitive args).map Value.toReference =
      referenceEvalUnchecked limits primitive (args.map Value.toReference) := by
  unfold evalUnchecked referenceEvalUnchecked
  split
  case h_3 values index =>
    cases found : values[index]? <;> simp [found, Array.attach_map_val, Except.map]
  case h_11 =>
    rw [evalScalarUnchecked_sim]
    split <;> simp_all [List.map_eq_cons_iff, Array.attach_map_val] <;> grind
  all_goals simp_all [Array.attach_map_val, Except.map, pure, Except.pure,
    apply_ite]

def referenceValidateResult (limits : Limits) (result : Ix.Ixby.Value) :
    Except Error Ix.Ixby.Value := do
  if let .scalar value := result then value.validate limits
  return result

@[simp] theorem validateResult_sim (limits : Limits) (value : Value) :
    (validateResult limits value).map Value.toReference =
      referenceValidateResult limits value.toReference := by
  cases value with
  | scalar scalar =>
    cases valid : scalar.validate limits <;>
      simp [validateResult, referenceValidateResult, valid, Except.map, bind, Except.bind]
  | _ => simp [validateResult, referenceValidateResult, Except.map, bind, Except.bind,
      pure, Except.pure]

theorem eval_sim (limits : Limits) (primitive : Primitive) (args : List Value) :
    (eval limits primitive args).map Value.toReference =
      primitive.eval limits (args.map Value.toReference) := by
  have refForm (values : List Ix.Ixby.Value) : primitive.eval limits values = (do
    if values.length != primitive.arity then
      throw (.arityMismatch primitive.arity values.length)
    for arg in values do referenceValidateArg limits primitive arg
    referenceValidateResult limits (← referenceEvalUnchecked limits primitive values)) := by
    simp only [Primitive.eval, referenceValidateArg, referenceValidateResult, referenceEvalUnchecked,
      bind, Except.bind, pure, Except.pure]
    congr 1
    congr 1
    · congr 1
      funext arg scratch
      cases arg <;> simp
      split <;> rfl
    · funext scratch
      split <;> simp_all [Except.map, bind, Except.bind, pure, Except.pure, apply_ite]
      all_goals repeat first | split | (solve | simp_all [Except.map,
        bind, Except.bind, pure, Except.pure, apply_ite])
      all_goals simp_all [Except.map, bind, Except.bind, pure, Except.pure, apply_ite]
      all_goals grind
  rw [refForm]
  change (eval limits primitive args).map Value.toReference = (do
    if (args.map Value.toReference).length != primitive.arity then
      throw (.arityMismatch primitive.arity (args.map Value.toReference).length)
    for arg in args.map Value.toReference do referenceValidateArg limits primitive arg
    referenceValidateResult limits (← referenceEvalUnchecked limits primitive
      (args.map Value.toReference)))
  simp only [eval, List.length_map, List.forIn_map, validateArg_sim]
  split
  · rfl
  · rw [← evalUnchecked_sim]
    generalize h : ForIn.forIn args () (fun arg _ => do
      validateArg limits primitive arg
      pure (.yield ())) = admitted
    cases admitted with
    | error error => rfl
    | ok unit =>
      cases result : evalUnchecked limits primitive args with
      | error error => rfl
      | ok value => simpa [bind, Except.bind, Except.map] using validateResult_sim limits value

end Compilatrix.Ixby.Runtime.Chunked
