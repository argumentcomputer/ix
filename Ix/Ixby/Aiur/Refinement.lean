module
public import Ix.Ixby.Aiur.Fragment

/-! Logical representation contract for scalar CEK control.

These kernel-checked lemmas relate reverse-ordered local/continuation lists to
the reference machine's arrays. They cover immutable extension, argument order,
branches, calls, tail calls, and separate return/pop/terminal transitions.

This module deliberately imports no Aiur FFI or circuit semantics. `RevFrame`
is the finite logical view of an `ICFrame`, not a proof that an arbitrary Aiur
pointer graph has that view. Canonical table decoding, bounded field counters,
primitive gadgets, memory acyclicity/consistency, and compiler/AIR refinement
must still be connected to this contract. These are not axioms hidden in a
claimed end-to-end execution theorem. -/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend.Refinement

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

private theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

private theorem except_map_error {ε α β : Type} (e : ε) (f : α → β) :
    f <$> (Except.error e : Except ε α) = .error e := rfl

attribute [local simp] except_bind_ok except_map_ok except_bind_error except_map_error

structure RevFrame where
  function : FunctionId
  block : BlockId
  /-- Newest local first, as in `ICFrame`. -/
  locals : List Value
  deriving BEq, Repr, Inhabited

def RevFrame.decode (frame : RevFrame) : Frame :=
  ⟨frame.function, frame.block, frame.locals.reverse.toArray⟩

def RevFrame.encode (frame : Frame) : RevFrame :=
  ⟨frame.function, frame.block, frame.locals.toList.reverse⟩

def RevFrame.bind (frame : RevFrame) (target : BlockId) (value : Value) : RevFrame :=
  { frame with block := target, locals := value :: frame.locals }

def RevFrame.read (frame : RevFrame) : Operand → Except Error Value
  | .local index =>
    if index < frame.locals.length then
      match frame.locals[frame.locals.length - (index + 1)]? with
      | some value => .ok value
      | none => .error (.invalidLocal index)
    else .error (.invalidLocal index)
  | .literal value => .ok (.scalar value)
  | .erased => .ok .erased

/-- Logical version of the left-to-right `ic_args` accumulator. -/
def RevFrame.readArgs (frame : RevFrame) : List Operand → List Value → Except Error (List Value)
  | [], reversed => .ok reversed
  | operand :: rest, reversed => do
    let value ← frame.read operand
    frame.readArgs rest (value :: reversed)

inductive RevControl where
  | eval (frame : RevFrame)
  | ret (value : Value)
  deriving BEq, Repr, Inhabited

def RevControl.decode : RevControl → Control
  | .eval frame => .eval frame.decode
  | .ret value => .ret value

/-- Stack head is the next frame to resume. Only resume continuations belong
to this slice; general application and its continuation are not represented. -/
def decodeStack : List RevFrame → Array Continuation
  | [] => #[]
  | frame :: rest => (decodeStack rest).push (.resume frame.decode)

def decodeState (control : RevControl) (stack : List RevFrame) : State :=
  ⟨control.decode, decodeStack stack⟩

/-- Explicit refinement relation; it includes the complete saved stack. -/
def Represents (control : RevControl) (stack : List RevFrame) (state : State) : Prop :=
  decodeState control stack = state

@[simp] theorem decode_encode (frame : Frame) : (RevFrame.encode frame).decode = frame := by
  cases frame
  simp [RevFrame.encode, RevFrame.decode]

@[simp] theorem encode_decode (frame : RevFrame) : RevFrame.encode frame.decode = frame := by
  cases frame
  simp [RevFrame.encode, RevFrame.decode]

@[simp] theorem decode_locals_size (frame : RevFrame) :
    frame.decode.locals.size = frame.locals.length := by
  simp [RevFrame.decode]

@[simp] theorem decode_bind (frame : RevFrame) (target : BlockId) (value : Value) :
    (frame.bind target value).decode =
      { frame.decode with block := target, locals := frame.decode.locals.push value } := by
  cases frame
  simp [RevFrame.bind, RevFrame.decode, List.reverse_cons]

@[simp] theorem decode_at_block (frame : RevFrame) (target : BlockId) :
    ({ frame with block := target } : RevFrame).decode = { frame.decode with block := target } := rfl

theorem decode_stack_order (stack : List RevFrame) :
    decodeStack stack = (stack.reverse.map (Continuation.resume ∘ RevFrame.decode)).toArray := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => simp [decodeStack, ih, List.reverse_cons]

@[simp] theorem decode_stack_size (stack : List RevFrame) :
    (decodeStack stack).size = stack.length := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => simp [decodeStack, ih]

/-- Decoded tables retain wire order; unlike local frames, they are not
reversed. This is the logical lookup used for function/block/operand tables. -/
theorem ordered_table_lookup {α : Type} (table : List α) (index : Nat) :
    table.toArray[index]? = table[index]? := by simp

/-- The subtraction in `ic_operand` is `count - (index + 1)`. The guard is
essential: truncated Nat subtraction alone would alias an invalid local. -/
theorem read_decode (frame : RevFrame) (operand : Operand) :
    frame.read operand = frame.decode.read operand := by
  cases operand with
  | literal value => rfl
  | erased => rfl
  | «local» index =>
    simp only [RevFrame.read, Frame.read, RevFrame.decode, List.getElem?_toArray]
    by_cases h : index < frame.locals.length
    · rw [if_pos h, List.getElem?_reverse h]
      congr 2
      omega
    · simp [h]

/-- The accumulator of `ic_args` reverses once, preserving the original
argument order when entering a reference frame. -/
theorem reversed_arguments (args : List Value) : args.reverse.reverse.toArray = args.toArray := by
  simp

theorem read_args_decode (frame : RevFrame) (operands : List Operand) (acc : List Value) :
    frame.readArgs operands acc =
      (fun args => args.reverse ++ acc) <$> frame.decode.readOperands operands := by
  induction operands generalizing acc with
  | nil => rfl
  | cons operand rest ih =>
    cases h : frame.decode.read operand with
    | error e => simp [RevFrame.readArgs, Frame.readOperands, read_decode, h]
    | ok value =>
      cases hr : frame.decode.readOperands rest <;>
        simp [RevFrame.readArgs, Frame.readOperands, read_decode, h, ih, hr,
          List.reverse_cons, List.append_assoc]

theorem enter_reversed (limits : Limits) (program : Program) (id : FunctionId)
    (function : Function) (args : List Value) (block : Block)
    (found : program.getFunction id = .ok function)
    (arity : args.length = function.arity)
    (checked : (RevFrame.mk id function.entry args.reverse).decode.check limits program = .ok block) :
    enter limits program id args.toArray = .ok (RevFrame.mk id function.entry args.reverse).decode := by
  simp only [RevFrame.decode, List.reverse_reverse] at checked ⊢
  simp [enter, found, arity, checked]

theorem bind_transfer (frame : RevFrame) (target : BlockId) (value : Value)
    (limits : Limits) (program : Program) (block : Block)
    (checked : (frame.bind target value).decode.check limits program = .ok block) :
    frame.decode.transfer limits program target #[value] = .ok (frame.bind target value).decode := by
  have h := checked
  simp only [decode_bind] at h
  simp [Frame.transfer, h]

theorem branch_transfer (frame : RevFrame) (target : BlockId)
    (limits : Limits) (program : Program) (block : Block)
    (checked : ({ frame with block := target } : RevFrame).decode.check limits program = .ok block) :
    frame.decode.transfer limits program target = .ok ({ frame with block := target } : RevFrame).decode := by
  have h := checked
  simp only [decode_at_block] at h
  simp [Frame.transfer, h]

/-- A terminal return takes a transition, even though the stack is empty. -/
theorem return_empty (limits : Limits) (program : Program) (value : Value) :
    step limits program (decodeState (.ret value) []) = .ok (.halted value) := rfl

theorem return_resume (limits : Limits) (program : Program) (value : Value)
    (saved : RevFrame) (rest : List RevFrame) (block : Block)
    (checked : (saved.bind saved.block value).decode.check limits program = .ok block) :
    step limits program (decodeState (.ret value) (saved :: rest)) =
      .ok (.next (decodeState (.eval (saved.bind saved.block value)) rest)) := by
  have block_eq : saved.decode.block = saved.block := rfl
  simp [step, decodeState, RevControl.decode, decodeStack, block_eq,
    bind_transfer saved saved.block value limits program block checked]

theorem return_instruction (limits : Limits) (program : Program) (frame : RevFrame)
    (stack : List RevFrame) (operand : Operand) (value : Value) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .ret operand⟩)
    (read : frame.decode.read operand = .ok value) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.ret value) stack)) := by
  simp [step, stepEval, decodeState, RevControl.decode, checked, read]

theorem pure_let (limits : Limits) (program : Program) (frame : RevFrame)
    (stack : List RevFrame) (op : Op) (target : BlockId) (value : Value)
    (declared : Nat) (next : Block)
    (checked : frame.decode.check limits program = .ok ⟨declared, .letOp op target⟩)
    (evaluated : evalOp limits program frame.decode op = .ok (.value value))
    (nextChecked : (frame.bind target value).decode.check limits program = .ok next) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval (frame.bind target value)) stack)) := by
  simp [step, stepEval, decodeState, RevControl.decode, checked, evaluated,
    bind_transfer frame target value limits program next nextChecked]

theorem branch (limits : Limits) (program : Program) (frame : RevFrame)
    (stack : List RevFrame) (condition : Operand) (yes no : BlockId) (b : Bool)
    (declared : Nat) (next : Block)
    (checked : frame.decode.check limits program = .ok ⟨declared, .branch condition yes no⟩)
    (read : frame.decode.read condition = .ok (.scalar (.bool b)))
    (nextChecked : ({ frame with block := if b then yes else no } : RevFrame).decode.check limits program = .ok next) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval { frame with block := if b then yes else no }) stack)) := by
  simp [step, stepEval, decodeState, RevControl.decode, checked, read,
    branch_transfer frame (if b then yes else no) limits program next nextChecked]

theorem direct_call (limits : Limits) (program : Program) (frame callee : RevFrame)
    (stack : List RevFrame) (function : FunctionId) (operands : List Operand)
    (args : List Value) (target : BlockId) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .letOp (.call function operands) target⟩)
    (read : frame.decode.readOperands operands = .ok args)
    (entered : enter limits program function args.toArray = .ok callee.decode)
    (capacity : stack.length < limits.continuations) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval callee) ({ frame with block := target } :: stack))) := by
  simp [step, stepEval, evalOp, State.push, decodeState, RevControl.decode,
    decodeStack, checked, read, entered, Nat.not_le.mpr capacity]

theorem self_call (limits : Limits) (program : Program) (frame callee : RevFrame)
    (stack : List RevFrame) (operands : List Operand) (args : List Value)
    (target : BlockId) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .letOp (.callSelf operands) target⟩)
    (read : frame.decode.readOperands operands = .ok args)
    (entered : enter limits program frame.function args.toArray = .ok callee.decode)
    (capacity : stack.length < limits.continuations) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval callee) ({ frame with block := target } :: stack))) := by
  have fn_eq : frame.decode.function = frame.function := rfl
  simp [step, stepEval, evalOp, State.push, decodeState, RevControl.decode,
    decodeStack, checked, read, entered, fn_eq, Nat.not_le.mpr capacity]

/-- Tail calls leave every saved caller intact and need no stack capacity. -/
theorem tail_call (limits : Limits) (program : Program) (frame callee : RevFrame)
    (stack : List RevFrame) (function : FunctionId) (operands : List Operand)
    (args : List Value) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .tailCall function operands⟩)
    (read : frame.decode.readOperands operands = .ok args)
    (entered : enter limits program function args.toArray = .ok callee.decode) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval callee) stack)) := by
  simp [step, stepEval, decodeState, RevControl.decode, checked, read, entered]

theorem tail_self_call (limits : Limits) (program : Program) (frame callee : RevFrame)
    (stack : List RevFrame) (operands : List Operand) (args : List Value) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .tailCallSelf operands⟩)
    (read : frame.decode.readOperands operands = .ok args)
    (entered : enter limits program frame.function args.toArray = .ok callee.decode) :
    step limits program (decodeState (.eval frame) stack) =
      .ok (.next (decodeState (.eval callee) stack)) := by
  have fn_eq : frame.decode.function = frame.function := rfl
  simp [step, stepEval, decodeState, RevControl.decode,
    checked, read, entered, fn_eq]

theorem direct_call_overflow (limits : Limits) (program : Program) (frame : RevFrame)
    (stack : List RevFrame) (function : FunctionId) (operands : List Operand)
    (args : List Value) (target : BlockId) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .letOp (.call function operands) target⟩)
    (read : frame.decode.readOperands operands = .ok args)
    (full : limits.continuations ≤ stack.length) :
    step limits program (decodeState (.eval frame) stack) = .error (.limit .continuations) := by
  simp [step, stepEval, evalOp, State.push, decodeState, RevControl.decode, checked, read, full]

theorem zero_fuel (limits : Limits) (program : Program) (control : RevControl) (stack : List RevFrame) :
    run limits program 0 (decodeState control stack) = .error .outOfFuel := rfl

theorem transition_consumes_fuel (limits : Limits) (program : Program) (fuel : Nat)
    (before after : RevControl) (stack nextStack : List RevFrame)
    (transition : step limits program (decodeState before stack) =
      .ok (.next (decodeState after nextStack))) :
    run limits program (fuel + 1) (decodeState before stack) =
      run limits program fuel (decodeState after nextStack) := by
  simp [run, transition]

/-- A return instruction is not itself a terminal machine state. This is why
`ic_machine` must not skip the final transition when its budget reaches one. -/
theorem return_instruction_needs_two (limits : Limits) (program : Program) (frame : RevFrame)
    (operand : Operand) (value : Value) (declared : Nat)
    (checked : frame.decode.check limits program = .ok ⟨declared, .ret operand⟩)
    (read : frame.decode.read operand = .ok value) :
    run limits program 1 (decodeState (.eval frame) []) = .error .outOfFuel ∧
      run limits program 2 (decodeState (.eval frame) []) = .ok value := by
  have h := return_instruction limits program frame [] operand value declared checked read
  simp [run, h, return_empty]

end Ix.Ixby.AiurBackend.Refinement
