module
public import Ix.Ixby.Aiur.Objects.Scalars
import all Ix.Aiur.Goldilocks

/-! Complete checked leaf-operand decoding. Operand lists, operations,
instructions, and whole block/function admission remain separate obligations.
The local-count u32 premise is explicit; checked block headers derive ≤64.
These are Lean bytecode contracts, not compiler/gadget/AIR soundness claims.
-/

namespace Ix.Ixby.AiurBackend.Objects.Operands

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open Objects.Refinement Objects.Memory Objects.Parser Objects.Identity Objects.Equality
open Objects.Scalars

def localGuardOps : Array Aiur.Bytecode.Op :=
  #[.u32LessThan 20 1, .const 1, .assertEq #[21] #[22] (some "IxBy code local index"), .const 0, .const 0]
def localOperand (reader : Nat) : ReturnSpec :=
  ⟨inlineWordOps reader 4 3 ++ localGuardOps, 0, #[23, 20, 24, 24, 24, 24, 11]⟩
def literalOperand (scalar : Nat) : ReturnSpec :=
  ⟨#[.call scalar #[3] 6 false, .const 1], 1, #[10, 4, 5, 6, 7, 8, 9]⟩
def erasedOperand : ReturnSpec :=
  ⟨#[.const 1, .const 4, .const 4], 2, #[4, 5, 6, 6, 6, 6, 3]⟩
def unsupportedOperand : ReturnSpec :=
  ⟨#[.const 0, .const 1, .assertEq #[4] #[5] (some "IxBy unknown operand"), .const 1, .const 4, .const 4],
    3, #[6, 7, 8, 8, 8, 8, 3]⟩
def operandCases (reader scalar : Nat) : List (G × ReturnSpec) :=
  [(0, localOperand reader), (1, literalOperand scalar), (2, erasedOperand)]
def operandReaderBody (reader scalar : Nat) : Aiur.Bytecode.Block :=
  dispatchBody #[.call reader #[0] 2 false] 2 (operandCases reader scalar) unsupportedOperand
def checkOperandReader (f : Aiur.Bytecode.Function) (reader scalar : Nat) : Bool :=
  checkDispatch f 2 #[.call reader #[0] 2 false] 2 (operandCases reader scalar) unsupportedOperand

theorem operand_reader_checked (f : Aiur.Bytecode.Function) (reader scalar : Nat)
    (checked : checkOperandReader f reader scalar = true) :
    f.layout.inputSize = 2 ∧ f.body = operandReaderBody reader scalar :=
  dispatch_checked f 2 _ 2 _ _ checked

structure OperandCode where
  scalars : ScalarCode
  operand : Nat
structure CheckedOperands (t : Bytecode.Toplevel) (code : OperandCode) where
  scalars : CheckedScalars t code.scalars
  operandFn : Aiur.Bytecode.Function
  operandFunction : t.functions[code.operand]? = some operandFn
  operandChecked : checkOperandReader operandFn code.scalars.reader code.scalars.scalar = true
def checkOperandCode (t : Bytecode.Toplevel) (code : OperandCode) : Bool :=
  match t.functions[code.operand]? with
  | some f => checkScalarCode t code.scalars && checkOperandReader f code.scalars.reader code.scalars.scalar
  | none => false

theorem operand_code_checked (t : Bytecode.Toplevel) (code : OperandCode)
    (checked : checkOperandCode t code = true) : Nonempty (CheckedOperands t code) := by
  unfold checkOperandCode at checked
  split at checked
  · rename_i f found
    simp only [Bool.and_eq_true] at checked
    obtain ⟨scalars⟩ := scalar_code_checked t code.scalars checked.1
    exact ⟨⟨scalars, f, found, checked.2⟩⟩
  · simp at checked

inductive OperandBytes where
  | local (index : WordBytes)
  | literal (scalar : ScalarBytes)
  | erased
def OperandBytes.bytes : OperandBytes → List UInt8
  | .local w => 0 :: w.bytes
  | .literal s => 1 :: s.bytes
  | .erased => [2]
def OperandBytes.flat : OperandBytes → Array G
  | .local w => #[0, w.field, 0, 0, 0, 0]
  | .literal s => #[1] ++ s.flat
  | .erased => #[1, 4, 4, 4, 4, 4]
def OperandBytes.valid (locals : G) : OperandBytes → Prop
  | .local w => w.field.n < locals.n
  | .literal s => s.valid
  | .erased => True
instance (locals : G) (o : OperandBytes) : Decidable (o.valid locals) := by
  cases o <;> unfold OperandBytes.valid <;> infer_instance

theorem operand_flat_size (o : OperandBytes) : o.flat.size = 6 := by
  cases o <;> simp [OperandBytes.flat, scalar_flat_size]

/-- Unlike a raw UInt32 cast, genuine u32 metadata preserves natural ordering. -/
theorem u32_comparison_exact (a b : G) (ha : a.n < 2 ^ 32) (hb : b.n < 2 ^ 32) :
    a.val.toUInt32 < b.val.toUInt32 ↔ a.n < b.n := by
  simp only [UInt32.lt_iff_toNat_lt, UInt64.toNat_toUInt32]
  simp only [G.n, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

@[local simp] private theorem tag01 : (0 : G).val ≠ (1 : G).val := by decide
@[local simp] private theorem tag02 : (0 : G).val ≠ (2 : G).val := by decide
@[local simp] private theorem tag12 : (1 : G).val ≠ (2 : G).val := by decide

private theorem operand_dispatch (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals tag rest : G)
    (loaded : memLoad st 3 pointer.n = .ok #[0, tag, rest]) :
    evalBlock t (fuel + 1) checked.operandFn.body { st with map := #[pointer, locals] } =
      evalCtrl t (fuel + 1) (operandReaderBody code.scalars.reader code.scalars.scalar).ctrl
        { st with map := #[pointer, locals, tag, rest] } := by
  obtain ⟨_, body⟩ := operand_reader_checked checked.operandFn _ _ checked.operandChecked
  have first := byte_reader_call t fuel code.scalars.byteSelector code.scalars.reader 0
    { st with map := #[pointer, locals] } checked.scalars.byteFn checked.scalars.byteFunction
    checked.scalars.byteChecked pointer tag rest rfl loaded false
  rw [body, evalBlock]
  simp [operandReaderBody, dispatchBody, run_ops_list, first,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem local_guard_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 21) (index locals finish : G)
    (word : st.map[20]? = some index) (frame : st.map[1]? = some locals) (suffix : st.map[11]? = some finish)
    (wordRange : index.n < 2 ^ 32) (frameRange : locals.n < 2 ^ 32) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t fuel ⟨localGuardOps, .return 0 #[23, 20, 24, 24, 24, 24, 11]⟩ st =
        if index.n < locals.n then .error (.earlyReturn #[0, index, 0, 0, 0, 0, finish] after)
        else .error .assertFailed := by
  have iv := (Array.getElem?_eq_some_iff.mp word).2
  have lv := (Array.getElem?_eq_some_iff.mp frame).2
  have fv := (Array.getElem?_eq_some_iff.mp suffix).2
  have comparison := u32_comparison_exact index locals wordRange frameRange
  by_cases valid : index.n < locals.n
  · simp +arith [localGuardOps, evalBlock, run_ops_list, Aiur.Bytecode.Eval.evalOp,
      readIdxs, readIdx, pushMap, evalCtrl, size, iv, lv, fv,
      Array.getElem?_push, comparison, valid,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · refine ⟨st, rfl, rfl, ?_⟩
    simp +arith [localGuardOps, evalBlock, run_ops_list, Aiur.Bytecode.Eval.evalOp,
      readIdxs, readIdx, pushMap, size, iv, lv, comparison, valid, Array.getElem?_push,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete local-index branch, rejecting out-of-frame indices without
narrowing either the genuine index or the explicit u32 local count. -/
theorem checked_local_operand (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals finish : G) (w : WordBytes)
    (frameRange : locals.n < 2 ^ 32)
    (read : BytePrefix (bytecodeMemory st) pointer (0 :: w.bytes) finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 1) checked.operandFn.body { st with map := #[pointer, locals] } =
        if w.field.n < locals.n then .error (.earlyReturn #[0, w.field, 0, 0, 0, 0, finish] after)
        else .error .assertFailed := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  rw [operand_dispatch t code checked fuel st pointer locals 0 next tag]
  let start : EvalState := { st with map := #[pointer, locals, 0, next] }
  obtain ⟨registers, size, tail, value, words⟩ := inline_word_prefix t fuel code.scalars.byteSelector code.scalars.reader 3 start
    checked.scalars.byteFn checked.scalars.byteFunction checked.scalars.byteChecked next finish w rfl rest
  change runOps t (fuel + 1) (inlineWordOps code.scalars.reader 4 3) start 0 = _ at words
  let wordState : EvalState := { st with map := start.map ++ registers }
  have wordSize : wordState.map.size = 21 := by simp [wordState, start, size]
  have wordValue : wordState.map[20]? = some w.field := by
    simpa [wordState, start, Array.getElem?_append] using value
  have wordSuffix : wordState.map[11]? = some finish := by
    simpa [wordState, start, Array.getElem?_append] using tail
  have frame : wordState.map[1]? = some locals := by simp [wordState, start, Array.getElem?_append]
  obtain ⟨after, memory, io, guard⟩ := local_guard_eval t (fuel + 1) wordState wordSize
    w.field locals finish wordValue frame wordSuffix (word_field_bound w) frameRange
  refine ⟨after, memory, io, ?_⟩
  have branch : evalBlock t (fuel + 1) (localOperand code.scalars.reader).block start =
      if w.field.n < locals.n then .error (.earlyReturn #[0, w.field, 0, 0, 0, 0, finish] after)
      else .error .assertFailed := by
    simpa only [localOperand, ReturnSpec.block, evalBlock, run_ops_append, words, Except.bind, wordState] using guard
  dsimp only [start] at branch
  simp [operandReaderBody, dispatchBody, operandCases, evalCtrl, evalMatchArm, readIdx, branch]

theorem checked_literal_operand (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals finish : G) (s : ScalarBytes)
    (read : BytePrefix (bytecodeMemory st) pointer (1 :: s.bytes) finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 3) checked.operandFn.body { st with map := #[pointer, locals] } =
        if s.valid then .error (.earlyReturn (#[1] ++ (s.flat ++ #[finish])) after)
        else .error .assertFailed := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  rw [operand_dispatch t code checked (fuel + 2) st pointer locals 1 next tag]
  have call := checked_scalar_call t code.scalars checked.scalars fuel 3
    { st with map := #[pointer, locals, 1, next] } next finish s rfl rest false
  refine ⟨{ st with map := (#[pointer, locals, 1, next] ++ (s.flat ++ #[finish])).push 1 }, rfl, rfl, ?_⟩
  by_cases valid : s.valid
  · simp only [valid, ite_true] at call ⊢
    cases s <;> simp [operandReaderBody, dispatchBody, operandCases, literalOperand, ReturnSpec.block,
      evalCtrl, evalMatchArm, evalBlock, run_ops_list, Aiur.Bytecode.Eval.evalOp, call, ScalarBytes.flat,
      readIdx, readIdxs, pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [operandReaderBody, dispatchBody, operandCases, literalOperand, ReturnSpec.block,
      evalCtrl, evalMatchArm, evalBlock, run_ops_list, call, valid,
      readIdx, Bind.bind, Except.bind]

theorem checked_erased_operand (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals finish : G)
    (read : BytePrefix (bytecodeMemory st) pointer [2] finish) :
    evalBlock t (fuel + 1) checked.operandFn.body { st with map := #[pointer, locals] } =
      .error (.earlyReturn #[1, 4, 4, 4, 4, 4, finish]
        { st with map := #[pointer, locals, 2, finish, 1, 4, 4] }) := by
  obtain ⟨next, tag, rest⟩ := prefix_byte_load st read
  cases rest
  rw [operand_dispatch t code checked fuel st pointer locals 2 finish tag]
  simp [operandReaderBody, dispatchBody, operandCases, erasedOperand, ReturnSpec.block,
    evalCtrl, evalMatchArm, evalBlock, run_ops_list, Aiur.Bytecode.Eval.evalOp,
    readIdx, readIdxs, pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked_unsupported_operand (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals tag rest : G)
    (loaded : memLoad st 3 pointer.n = .ok #[0, tag, rest]) (unsupported : tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2) :
    evalBlock t (fuel + 1) checked.operandFn.body { st with map := #[pointer, locals] } = .error .assertFailed := by
  have t0 : (0 : G).val ≠ tag.val := fun equal => unsupported.1 (Subtype.ext equal.symm)
  have t1 : (1 : G).val ≠ tag.val := fun equal => unsupported.2.1 (Subtype.ext equal.symm)
  have t2 : (2 : G).val ≠ tag.val := fun equal => unsupported.2.2 (Subtype.ext equal.symm)
  rw [operand_dispatch t code checked fuel st pointer locals tag rest loaded]
  simp [operandReaderBody, dispatchBody, operandCases, unsupportedOperand, ReturnSpec.block,
    evalCtrl, evalMatchArm, evalDefaultBlock, evalBlock, run_ops_list, t0, t1, t2,
    Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete local/literal/erased leaf parsing. This does not allocate a list
cell or assume success of the instruction decoder that called it. -/
theorem checked_operand_reader (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (pointer locals finish : G) (o : OperandBytes)
    (frameRange : locals.n < 2 ^ 32) (read : BytePrefix (bytecodeMemory st) pointer o.bytes finish) :
    ∃ after, after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      evalBlock t (fuel + 3) checked.operandFn.body { st with map := #[pointer, locals] } =
        if o.valid locals then .error (.earlyReturn (o.flat ++ #[finish]) after) else .error .assertFailed := by
  cases o with
  | «local» w => simpa [OperandBytes.valid, OperandBytes.flat, Nat.add_assoc] using
      checked_local_operand t code checked (fuel + 2) st pointer locals finish w frameRange read
  | literal s => simpa only [OperandBytes.valid, OperandBytes.flat, Array.append_assoc] using
      checked_literal_operand t code checked fuel st pointer locals finish s read
  | erased =>
    refine ⟨{ st with map := #[pointer, locals, 2, finish, 1, 4, 4] }, rfl, rfl, ?_⟩
    simpa [OperandBytes.valid, OperandBytes.flat, Nat.add_assoc] using
      checked_erased_operand t code checked (fuel + 2) st pointer locals finish read

theorem checked_operand_call (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (indices : Array Nat) (pointer locals finish : G) (o : OperandBytes)
    (arguments : readIdxs st indices = .ok #[pointer, locals])
    (frameRange : locals.n < 2 ^ 32) (read : BytePrefix (bytecodeMemory st) pointer o.bytes finish)
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 4) (.call code.operand indices 7 unconstrained) st =
      if o.valid locals then .ok { st with map := st.map ++ (o.flat ++ #[finish]) } else .error .assertFailed := by
  obtain ⟨arity, _⟩ := operand_reader_checked checked.operandFn _ _ checked.operandChecked
  obtain ⟨after, memory, io, result⟩ := checked_operand_reader t code checked fuel st pointer locals finish o frameRange read
  have call := readonly_parser_call t (fuel + 3) code.operand st checked.operandFn checked.operandFunction
    indices #[pointer, locals] (o.flat ++ #[finish]) arguments arity (o.valid locals) after memory io result unconstrained
  simpa [operand_flat_size] using call

def atomOperand : Atom → Ix.Ixby.Operand
  | .bool b => .literal (.bool b)
  | .word w => .literal (.word32 w)
  | .field f => .literal (.field f)
  | .ext e => .literal (.extField e)
  | .erased => .erased
def OperandBytes.operand : OperandBytes → Ix.Ixby.Operand
  | .local w => .local w.field.n
  | .literal s => atomOperand s.atom
  | .erased => .erased

/-- Concrete six-field ICOperand layout. Local padding and scalar layouts
are checked; frame bounds are an admission obligation, not a property of bytes alone. -/
def decodeOperand : List G → Option Ix.Ixby.Operand
  | [tag, a, b, c, d, e] =>
    match tag.n with
    | 0 => if a.n < 2 ^ 32 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 then some (.local a.n) else none
    | 1 => atomOperand <$> decodeAtom [a, b, c, d, e]
    | _ => none
  | _ => none

theorem operand_flat_decoded (o : OperandBytes) (locals : G) (valid : o.valid locals) :
    decodeOperand o.flat.toList = some o.operand := by
  have n0 : (0 : G).n = 0 := by decide
  have n1 : (1 : G).n = 1 := by decide
  cases o with
  | «local» w =>
    simp [OperandBytes.flat, OperandBytes.operand, decodeOperand, n0]
    exact word_field_bound w
  | literal s =>
    have scalar := congrArg (Option.map atomOperand) (scalar_flat_decoded s valid)
    cases s <;> simpa [OperandBytes.flat, OperandBytes.operand, decodeOperand, n1, ScalarBytes.flat] using scalar
  | erased => decide

/-- Successful actual Calls produce the concrete representation of the
semantic operand while preserving all old reads/I/O and the unconsumed bytes. -/
theorem checked_operand_success (t : Bytecode.Toplevel) (code : OperandCode) (checked : CheckedOperands t code)
    (fuel : Nat) (st : EvalState) (indices : Array Nat) (pointer locals finish : G) (o : OperandBytes)
    (arguments : readIdxs st indices = .ok #[pointer, locals])
    (frameRange : locals.n < 2 ^ 32) (read : BytePrefix (bytecodeMemory st) pointer o.bytes finish)
    (valid : o.valid locals) (unconstrained : Bool) :
    let after : EvalState := { st with map := st.map ++ (o.flat ++ #[finish]) }
    Aiur.Bytecode.Eval.evalOp t (fuel + 4) (.call code.operand indices 7 unconstrained) st = .ok after ∧
      decodeOperand o.flat.toList = some o.operand ∧ after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  refine ⟨?_, operand_flat_decoded o locals valid, rfl, rfl⟩
  simpa only [valid, ite_true] using checked_operand_call t code checked fuel st indices pointer locals finish o
    arguments frameRange read unconstrained

open Objects.Admission in
/-- Composition at an identified operand prefix in successfully loaded advice.
Genuine bytes follow from the actual loader; the explicit u32 frame bound is
still supplied by the caller. Operand lists, instructions, and whole-program
decoding are not assumed. Failure carries no state, so no rollback is claimed. -/
theorem loaded_operand (t : Bytecode.Toplevel) (loaderCode : LoaderCode) (loader : CheckedLoader t loaderCode)
    (code : OperandCode) (checked : CheckedOperands t code)
    (loadFuel parseFuel : Nat) (st : EvalState) (channel : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (byteSpace : Objects.Store.bucketSize st 3 + values.length + 1 ≤ goldilocksModulus)
    (locals : G) (frameRange : locals.n < 2 ^ 32) (o : OperandBytes) (suffix : List UInt8)
    (bytes : adviceBytes values = o.bytes ++ suffix)
    (outputs : Array G) (loaded : EvalState)
    (executed : evalBlock t (loadFuel + values.length + 1) loader.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      .error (.earlyReturn outputs loaded)) :
    ∃ finish parsed, outputs = #[(storeAdvice st values).2] ∧
      ByteStream (bytecodeMemory loaded) finish suffix ∧
      evalBlock t (parseFuel + 3) checked.operandFn.body { loaded with map := #[(storeAdvice st values).2, locals] } =
        (if o.valid locals then .error (.earlyReturn (o.flat ++ #[finish]) parsed) else .error .assertFailed) ∧
      (o.valid locals → decodeOperand o.flat.toList = some o.operand ∧
        parsed.memory = loaded.memory ∧ parsed.ioBuffer = st.ioBuffer ∧
        ByteStream (bytecodeMemory parsed) finish suffix ∧
        (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad parsed width pointer = .ok flat)) := by
  obtain ⟨_, _, outputsEq, stream, io, _, _, preserved⟩ := checked_load_admission t loaderCode loader
    loadFuel st channel start limit values metadata available address lengthRange limitRange byteSpace outputs loaded executed
  obtain ⟨terminal, whole, nilRead⟩ := stream
  rw [bytes] at whole
  obtain ⟨finish, operandBytes, suffixBytes⟩ := byte_prefix_split whole
  have suffixStream : ByteStream (bytecodeMemory loaded) finish suffix := ⟨terminal, suffixBytes, nilRead⟩
  obtain ⟨parsed, memory, parserIo, parsedRun⟩ := checked_operand_reader t code checked parseFuel loaded
    (storeAdvice st values).2 locals finish o frameRange operandBytes
  refine ⟨finish, parsed, outputsEq, suffixStream, parsedRun, ?_⟩
  intro valid
  refine ⟨operand_flat_decoded o locals valid, memory, parserIo.trans io, ?_, ?_⟩
  · rw [bytecode_memory_congr parsed loaded memory]
    exact suffixStream
  · intro width pointer flat read
    simpa only [memLoad, memory] using preserved width pointer flat read

end
end
end Ix.Ixby.AiurBackend.Objects.Operands
