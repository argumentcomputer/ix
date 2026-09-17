import Compilatrix.Ixby.Inline.Layout

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem SameLayout.validateInput {source target} (same : SameLayout source target)
    (limits : Limits) (fuel : Nat) (values : List Value) :
    validateInputValues limits source fuel values = validateInputValues limits target fuel values := by
  induction fuel generalizing values with
  | zero => cases values <;> rfl
  | succ fuel ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      cases value with
      | pap callee captured =>
        have functions := same.getFunction callee
        cases left : source.getFunction callee with
        | error error =>
          cases right : target.getFunction callee <;>
            simp_all [validateInputValues, Except.map, bind, Except.bind]
        | ok first =>
          cases right : target.getFunction callee with
          | error error => simp [left, right, Except.map] at functions
          | ok second =>
            have layouts : functionLayout first = functionLayout second := by
              simpa [left, right, Except.map] using functions
            have arity := congrArg FunctionLayout.arity layouts
            change first.arity = second.arity at arity
            simp only [validateInputValues, left, right, bind, Except.bind, arity, ih]
      | _ => simp only [validateInputValues, Program.findConstructor, same.constructors, ih]

/-- Admission and the exact initial state, including all input rejection
conditions, agree between the two complete checked programs. -/
theorem Certificate.initialState_eq {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix) (input : Array Value) :
    initialState limits source input = initialState limits target input := by
  simp only [initialState, certificate.sourceAdmitted, certificate.targetAdmitted,
    certificate.relation.entry, certificate.relation.layout.enter, certificate.relation.layout.validateInput]

theorem initialState_continuation {limits : Limits} {program : Program} {input : Array Value} {state : State}
    (initialized : initialState limits program input = .ok state) : state.continuation = #[] := by
  cases admitted : validateProgram limits program with
  | error error => simp [initialState, admitted, bind, Except.bind] at initialized
  | ok admittedUnit =>
    cases admittedUnit
    cases entered : enter limits program program.entry input with
    | error error => simp [initialState, admitted, entered, bind, Except.bind] at initialized
    | ok frame =>
      cases inputs : validateInputValues limits program limits.inputNodes input.toList with
      | error error => simp [initialState, admitted, entered, inputs, bind, Except.bind] at initialized
      | ok inputUnit =>
        cases inputUnit
        have equal : state = ⟨.eval frame, #[]⟩ := by
          simpa [initialState, admitted, entered, inputs, bind, Except.bind] using initialized.symm
        subst state
        rfl

end Compilatrix.Ixby.Inline
