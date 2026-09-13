import Compilatrix.Ixby.SymbolicTarget

namespace Compilatrix.Ixby.SymbolicTarget

open Ix.Ixby (Program Limits Error Operand Op Instr)

@[simp] private theorem pure_ok {α : Type} (value : α) : (pure value : Except Error α) = .ok value := rfl

@[simp] private theorem isEmpty_map {α β : Type} (values : Array α) (f : α → β) :
    (values.map f).isEmpty = values.isEmpty := by simp [Array.isEmpty]

private theorem bind_ok {α β : Type} (value : Except Error α) (f : α → Except Error β) (out : β) :
    (value >>= f) = .ok out ↔ ∃ x, value = .ok x ∧ f x = .ok out := by
  cases value <;> simp [Bind.bind, Except.bind]

@[simp] theorem Frame.check_instantiate (frame : Frame) (input : Nat → Ix.Ixby.Value)
    (limits : Limits) (program : Program) :
    (frame.instantiate input).check limits program = frame.check limits program := by
  simp [Ix.Ixby.Frame.check, Frame.check, Frame.instantiate]

theorem Frame.read_sound {frame : Frame} {operand value}
    (accepted : frame.read operand = .ok value) (input : Nat → Ix.Ixby.Value) :
    (frame.instantiate input).read operand = .ok (value.instantiate input) := by
  cases operand with
  | literal scalar =>
      simp only [Frame.read, Except.ok.injEq] at accepted
      subst value
      simp [Ix.Ixby.Frame.read, Value.instantiate]
  | erased =>
      simp only [Frame.read, Except.ok.injEq] at accepted
      subst value
      simp [Ix.Ixby.Frame.read, Value.instantiate]
  | «local» index =>
      cases h : frame.locals[index]? with
      | none => simp [Frame.read, h] at accepted
      | some found =>
          simp only [Frame.read, h, Except.ok.injEq] at accepted
          subst value
          simp [Ix.Ixby.Frame.read, Frame.instantiate, h]

theorem Frame.readOperands_sound {frame : Frame} {operands values}
    (accepted : frame.readOperands operands = .ok values) (input : Nat → Ix.Ixby.Value) :
    (frame.instantiate input).readOperands operands = .ok (values.map (Value.instantiate input)) := by
  induction operands generalizing values with
  | nil =>
      simp only [Frame.readOperands, Except.ok.injEq] at accepted
      subst values
      rfl
  | cons operand rest ih =>
      simp only [Frame.readOperands, bind_ok] at accepted
      obtain ⟨value, hv, values, hs, h⟩ := accepted
      cases h
      simp [Ix.Ixby.Frame.readOperands, Frame.read_sound hv input, ih hs,
        Bind.bind, Except.bind]

theorem enter_sound {limits program callee args frame}
    (accepted : enter limits program callee args = .ok frame) (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.enter limits program callee (args.map (Value.instantiate input)) =
      .ok (frame.instantiate input) := by
  simp only [enter, bind_ok] at accepted
  obtain ⟨function, hf, h⟩ := accepted
  split at h
  · contradiction
  · rename_i arity
    simp only [bind_ok] at h
    obtain ⟨block, hb, h⟩ := h
    cases h
    have concrete := Frame.check_instantiate
      { function := callee, block := function.entry, locals := args } input limits program
    simp only [hb] at concrete
    simp only [Frame.instantiate] at concrete
    simp [Ix.Ixby.enter, hf, arity, Bind.bind, Except.bind, Frame.instantiate, concrete]

theorem Frame.transfer_sound {limits program target extra frame next}
    (accepted : Frame.transfer frame limits program target extra = .ok next)
    (input : Nat → Ix.Ixby.Value) :
    (frame.instantiate input).transfer limits program target (extra.map (Value.instantiate input)) =
      .ok (next.instantiate input) := by
  simp only [Frame.transfer, bind_ok] at accepted
  obtain ⟨block, hb, h⟩ := accepted
  cases h
  have concrete := Frame.check_instantiate
    { frame with block := target, locals := frame.locals ++ extra } input limits program
  simp only [hb] at concrete
  simp only [Frame.instantiate, Array.map_append] at concrete
  simp [Ix.Ixby.Frame.transfer, Frame.instantiate, concrete, Bind.bind, Except.bind]

theorem State.push_sound {state limits next pushed}
    (accepted : State.push state limits next = .ok pushed) (input : Nat → Ix.Ixby.Value) :
    (state.instantiate input).push limits (next.instantiate input) = .ok (pushed.instantiate input) := by
  simp only [State.push] at accepted
  split at accepted
  · contradiction
  · rename_i capacity
    cases accepted
    simp [Ix.Ixby.State.push, State.instantiate, capacity]

theorem evalOp_sound {limits program frame op action}
    (accepted : evalOp limits program frame op = .ok action) (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.evalOp limits program (frame.instantiate input) op = .ok (action.instantiate input) := by
  cases op with
  | copy operand =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨value, hv, h⟩ := accepted
      cases h
      simp [Ix.Ixby.evalOp, Frame.read_sound hv input, Action.instantiate, Bind.bind, Except.bind]
  | primitive prim args => simp [evalOp] at accepted
  | construct ctor args =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨decl, hd, fields, hf, h⟩ := accepted
      split at h
      · contradiction
      · rename_i arity
        cases h
        simp [Ix.Ixby.evalOp, hd, Frame.readOperands_sound hf input, arity,
          Bind.bind, Except.bind, Action.instantiate, Value.instantiate]
  | project operand field =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨object, ho, h⟩ := accepted
      have read := Frame.read_sound ho input
      cases object <;> try contradiction
      · rename_i id fields
        cases hv : fields[field]? with
        | none => simp [hv] at h
        | some value =>
            simp only [hv] at h
            cases h
            simp [Ix.Ixby.evalOp, read, Value.instantiate, hv, Action.instantiate, Bind.bind, Except.bind]
      · cases h
        simp [Ix.Ixby.evalOp, read, Value.instantiate, Action.instantiate, Bind.bind, Except.bind]
  | closure callee args =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨function, hf, captured, hc, h⟩ := accepted
      split at h
      · contradiction
      · rename_i arity
        cases h
        simp [Ix.Ixby.evalOp, hf, Frame.readOperands_sound hc input, arity,
          Bind.bind, Except.bind, Action.instantiate, Value.instantiate]
  | call callee args =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨values, hv, h⟩ := accepted
      cases h
      simp [Ix.Ixby.evalOp, Frame.readOperands_sound hv input, Action.instantiate, Bind.bind, Except.bind]
  | callSelf args =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨values, hv, h⟩ := accepted
      cases h
      have read := Frame.readOperands_sound hv input
      simp only [Frame.instantiate] at read
      simp [Ix.Ixby.evalOp, read, Action.instantiate,
        Frame.instantiate, Bind.bind, Except.bind]
  | apply operand args =>
      simp only [evalOp, bind_ok] at accepted
      obtain ⟨fn, hf, values, hv, h⟩ := accepted
      cases h
      simp [Ix.Ixby.evalOp, Frame.read_sound hf input, Frame.readOperands_sound hv input,
        Action.instantiate, Bind.bind, Except.bind]

theorem stepEval_sound {limits program state frame transition}
    (accepted : stepEval limits program state frame = .ok transition)
    (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.stepEval limits program (state.instantiate input) (frame.instantiate input) =
      .ok (transition.instantiate input) := by
  simp only [stepEval, bind_ok] at accepted
  obtain ⟨block, hb, h⟩ := accepted
  simp only [Ix.Ixby.stepEval, Frame.check_instantiate, hb, Bind.bind, Except.bind]
  cases instruction : block.instruction with
  | letOp op target =>
      simp only [instruction, bind_ok] at h
      obtain ⟨action, ha, h⟩ := h
      simp only [evalOp_sound ha input]
      cases action with
      | value value =>
          simp only [bind_ok] at h
          obtain ⟨next, hn, h⟩ := h
          cases h
          have transfer := Frame.transfer_sound hn input
          simp only [Array.map_singleton] at transfer
          simp only [Action.instantiate]
          rw [transfer]
          simp [Transition.instantiate, State.instantiate, Control.instantiate]
      | call callee args =>
          simp only [bind_ok] at h
          obtain ⟨pushed, hp, next, hn, h⟩ := h
          cases h
          have push := State.push_sound hp input
          simp only [Continuation.instantiate, Frame.instantiate] at push
          simp only [Action.instantiate, Frame.instantiate]
          rw [push]
          simp [enter_sound hn input,
            Transition.instantiate, State.instantiate, Control.instantiate,
            Frame.instantiate]
      | apply fn args =>
          simp only [bind_ok] at h
          obtain ⟨pushed, hp, h⟩ := h
          cases h
          have push := State.push_sound hp input
          simp only [Continuation.instantiate, Frame.instantiate] at push
          simp only [Action.instantiate, Frame.instantiate]
          rw [push]
          simp [Transition.instantiate,
            State.instantiate, Control.instantiate, Frame.instantiate]
  | ret operand =>
      simp only [instruction, bind_ok] at h
      obtain ⟨value, hv, h⟩ := h
      cases h
      simp [Frame.read_sound hv input, Transition.instantiate,
        State.instantiate, Control.instantiate]
  | tailCall callee operands =>
      simp only [instruction, bind_ok] at h
      obtain ⟨args, ha, next, hn, h⟩ := h
      cases h
      have entered := enter_sound hn input
      simp only [List.map_toArray] at entered
      simp [Frame.readOperands_sound ha input, entered,
        Transition.instantiate, State.instantiate, Control.instantiate]
  | tailCallSelf operands =>
      simp only [instruction, bind_ok] at h
      obtain ⟨args, ha, next, hn, h⟩ := h
      cases h
      have entered := enter_sound hn input
      simp only [Frame.instantiate, List.map_toArray] at entered
      have read := Frame.readOperands_sound ha input
      simp only [Frame.instantiate] at read
      simp [read, entered,
        Transition.instantiate, State.instantiate, Control.instantiate, Frame.instantiate]
  | tailApply operand operands =>
      simp only [instruction, bind_ok] at h
      obtain ⟨fn, hf, args, ha, h⟩ := h
      cases h
      simp [Frame.read_sound hf input, Frame.readOperands_sound ha input,
        Transition.instantiate, State.instantiate, Control.instantiate]
  | caseCtor operand alternatives =>
      simp only [instruction, bind_ok] at h
      obtain ⟨object, ho, h⟩ := h
      cases object <;> try contradiction
      rename_i id fields
      simp only [bind_ok] at h
      obtain ⟨target, ht, next, hn, h⟩ := h
      cases h
      simp [Frame.read_sound ho input, Value.instantiate, ht,
        Frame.transfer_sound hn input, Transition.instantiate,
        State.instantiate, Control.instantiate]
  | caseNat operand ifZero ifSucc =>
      simp only [instruction, bind_ok] at h
      obtain ⟨object, ho, h⟩ := h
      cases object <;> try contradiction
      rename_i scalar
      cases scalar <;> try contradiction
      rename_i n
      cases n with
      | zero =>
          simp only [bind_ok] at h
          obtain ⟨next, hn, h⟩ := h
          cases h
          have transfer := Frame.transfer_sound hn input
          simp only [Array.map_empty] at transfer
          simp [Frame.read_sound ho input, Value.instantiate, transfer,
            Transition.instantiate, State.instantiate, Control.instantiate]
      | succ n =>
          simp only [bind_ok] at h
          obtain ⟨next, hn, h⟩ := h
          cases h
          have transfer := Frame.transfer_sound hn input
          simp only [Array.map_singleton, Value.instantiate] at transfer
          simp [Frame.read_sound ho input, Value.instantiate, transfer,
            Transition.instantiate, State.instantiate, Control.instantiate]
  | branch operand yes no =>
      simp only [instruction, bind_ok] at h
      obtain ⟨object, ho, h⟩ := h
      cases object <;> try contradiction
      rename_i scalar
      cases scalar <;> try contradiction
      rename_i condition
      simp only [bind_ok] at h
      obtain ⟨next, hn, h⟩ := h
      cases h
      have transfer := Frame.transfer_sound hn input
      simp only [Array.map_empty] at transfer
      simp [Frame.read_sound ho input, Value.instantiate, transfer,
        Transition.instantiate, State.instantiate, Control.instantiate]

private theorem push_optional_sound {limits state args next}
    (accepted : (if args.isEmpty then pure state else State.push state limits (.apply args)) = .ok next)
    (input : Nat → Ix.Ixby.Value) :
    (if args.isEmpty then pure (state.instantiate input)
      else (state.instantiate input).push limits (.apply (args.map (Value.instantiate input)))) =
      .ok (next.instantiate input) := by
  split at accepted
  · rename_i empty
    cases accepted
    simp [empty]
  · rename_i nonempty
    simpa [nonempty, Continuation.instantiate] using State.push_sound accepted input

theorem stepApply_sound {limits program state value args transition}
    (accepted : stepApply limits program state value args = .ok transition)
    (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.stepApply limits program (state.instantiate input)
      (value.instantiate input) (args.map (Value.instantiate input)) =
      .ok (transition.instantiate input) := by
  simp only [stepApply] at accepted
  split at accepted
  · rename_i empty
    cases accepted
    simp only [Ix.Ixby.stepApply, isEmpty_map, empty, ↓reduceIte]
    simp [Transition.instantiate, State.instantiate, Control.instantiate]
  · rename_i nonempty
    cases value <;> try contradiction
    · rename_i callee captured
      simp only [bind_ok] at accepted
      obtain ⟨function, hf, h⟩ := accepted
      split at h
      · contradiction
      · rename_i capturedArity
        split at h
        · rename_i partialArity
          cases h
          have partialSize : captured.size + args.size < function.arity := by simpa using partialArity
          simp only [Ix.Ixby.stepApply, isEmpty_map, nonempty, ↓reduceIte, Value.instantiate,
            hf, Bind.bind, Except.bind, Array.size_map, capturedArity, Array.size_append, partialSize]
          simp [Transition.instantiate, State.instantiate, Control.instantiate, Value.instantiate]
        · rename_i saturated
          split at h <;> rename_i restCondition
          all_goals
            simp only [bind_ok] at h
            obtain ⟨next, hp, frame, he, h⟩ := h
            cases h
            have combined :
                (if ((captured ++ args).extract function.arity).isEmpty then pure state
                  else state.push limits (.apply ((captured ++ args).extract function.arity))) = .ok next := by
              simpa only [restCondition, Bool.false_eq_true, ↓reduceIte] using hp
            have push := push_optional_sound combined input
            simp only [restCondition, Bool.false_eq_true, ↓reduceIte] at push
            have entered := enter_sound he input
            simp only [Ix.Ixby.stepApply, Value.instantiate, isEmpty_map,
              nonempty, Bool.false_eq_true, ↓reduceIte, hf, Bind.bind, Except.bind, Array.size_map, capturedArity]
            simp only [← Array.map_append, Array.size_map, saturated, ↓reduceIte]
            simp only [← Array.map_extract, isEmpty_map, restCondition, Bool.false_eq_true, ↓reduceIte]
            rw [push]
            rw [entered]
            simp [Transition.instantiate, State.instantiate, Control.instantiate]
    · cases accepted
      simp [Ix.Ixby.stepApply, nonempty, Value.instantiate,
        Transition.instantiate, State.instantiate, Control.instantiate]

theorem step_sound {limits program state transition}
    (accepted : step limits program state = .ok transition) (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.step limits program (state.instantiate input) = .ok (transition.instantiate input) := by
  cases control : state.control with
  | eval frame =>
      simp only [step, control] at accepted
      simpa only [Ix.Ixby.step, State.instantiate, Control.instantiate, control] using
        stepEval_sound accepted input
  | apply value args =>
      simp only [step, control] at accepted
      simpa only [Ix.Ixby.step, State.instantiate, Control.instantiate, control] using
        stepApply_sound accepted input
  | ret value =>
      simp only [step, control] at accepted
      cases back : state.continuation.back? with
      | none =>
          simp only [back] at accepted
          cases accepted
          simp [Ix.Ixby.step, State.instantiate, Control.instantiate, control, back,
            Transition.instantiate]
      | some continuation =>
          simp only [back] at accepted
          cases continuation with
          | apply args =>
              cases accepted
              simp [Ix.Ixby.step, State.instantiate, Control.instantiate, control, back,
                Continuation.instantiate, Transition.instantiate]
          | resume frame =>
              simp only [bind_ok] at accepted
              obtain ⟨next, hn, h⟩ := accepted
              cases h
              have transfer := Frame.transfer_sound hn input
              simp only [Array.map_singleton, Frame.instantiate] at transfer
              simp [Ix.Ixby.step, State.instantiate, Control.instantiate, control, back,
                Continuation.instantiate, Transition.instantiate, Frame.instantiate, transfer,
                Bind.bind, Except.bind]

/-- Every successful symbolic machine run is a concrete run under every
substitution of runtime values, with the same exact program and limits. -/
theorem run_sound {limits program fuel state value}
    (accepted : run limits program fuel state = .ok value) (input : Nat → Ix.Ixby.Value) :
    Ix.Ixby.run limits program fuel (state.instantiate input) = .ok (value.instantiate input) := by
  induction fuel generalizing state with
  | zero => simp [run] at accepted
  | succ fuel ih =>
      simp only [run, bind_ok] at accepted
      obtain ⟨transition, ht, h⟩ := accepted
      have concrete := step_sound ht input
      cases transition with
      | halted result =>
          cases h
          simp [Ix.Ixby.run, concrete, Transition.instantiate]
      | next state =>
          simpa [Ix.Ixby.run, concrete, Transition.instantiate] using ih h

private theorem run_deterministic {limits program state fuel1 fuel2 left right}
    (first : Ix.Ixby.run limits program fuel1 state = .ok left)
    (second : Ix.Ixby.run limits program fuel2 state = .ok right) : left = right := by
  have one := Ix.Ixby.run_add_fuel first fuel2
  have two := Ix.Ixby.run_add_fuel second fuel1
  rw [Nat.add_comm fuel2 fuel1] at two
  exact Except.ok.inj (one.symm.trans two)

/-- A symbolic check pins every successful whole-program result, at any fuel.
Whole-program validation and input admission are obtained from that successful
execution; no resource adequacy or source termination is assumed. -/
theorem reflects_output {limits program args frame fuel value output}
    (entered : enter limits program program.entry args = .ok frame)
    (accepted : run limits program fuel { control := .eval frame } = .ok value)
    (input : Nat → Ix.Ixby.Value)
    (executed : Ix.Ixby.Evaluates limits program (args.map (Value.instantiate input)) output) :
    output = value.instantiate input := by
  obtain ⟨runtimeFuel, execution⟩ := executed
  cases initial : Ix.Ixby.initialState limits program (args.map (Value.instantiate input)) with
  | error error => simp [Ix.Ixby.execute, initial] at execution
  | ok state =>
      have initialEq : state = ({ control := .eval frame } : State).instantiate input := by
        simp only [Ix.Ixby.initialState, Bind.bind, Except.bind] at initial
        cases checked : Ix.Ixby.validateProgram limits program with
        | error error => simp [checked] at initial
        | ok _ =>
            simp only [checked, enter_sound entered input] at initial
            split at initial
            · contradiction
            · simpa [State.instantiate, Control.instantiate] using (Except.ok.inj initial).symm
      have concrete := run_sound accepted input
      have actual : Ix.Ixby.run limits program runtimeFuel state = .ok output := by
        simpa only [Ix.Ixby.execute, initial] using execution
      rw [initialEq] at actual
      exact run_deterministic actual concrete

end Compilatrix.Ixby.SymbolicTarget
