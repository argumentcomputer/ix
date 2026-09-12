module
public import Ix.Ixby.Aiur.Objects.Admission
import all Ix.Aiur.Goldilocks

/-! The actual `is_run` prefix through constructor-declaration admission.

The certificate binds only the initial sixty operations, not the remaining
function-table/input/machine code or its control. The theorem passes the exact
proved prefix state to that unchanged continuation. Genuine loaded bytes and
initial memory capacity remain explicit; compiler/hash/gadget/AIR refinement
and authenticated whole-program binding are separate obligations.
`Objects.CodeHeaders` extends this state through function-count admission and
proves the function/block header handoffs without certifying their later code.
-/

namespace Ix.Ixby.AiurBackend.Objects.ProgramPrefix

deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open Objects.Refinement Objects.Memory Objects.Store Objects.Table Objects.Parser
open Objects.Identity Objects.Equality Objects.Unique Objects.Declarations Objects.Admission

/-- The sixteen bytes preceding the constructor declarations. -/
structure HeaderBytes where
  magic : WordBytes
  revision : WordBytes
  entry : WordBytes
  constructors : WordBytes

def HeaderBytes.bytes (h : HeaderBytes) : List UInt8 :=
  h.magic.bytes ++ (h.revision.bytes ++ (h.entry.bytes ++ h.constructors.bytes))

def MagicValid (w : WordBytes) : Prop :=
  G.ofUInt8 w.a = 73 ∧ G.ofUInt8 w.b = 88 ∧ G.ofUInt8 w.c = 66 ∧ G.ofUInt8 w.d = 89
instance (w : WordBytes) : Decidable (MagicValid w) := by unfold MagicValid; infer_instance

def HeaderValid (h : HeaderBytes) : Prop :=
  MagicValid h.magic ∧ h.revision.field = 0 ∧ h.constructors.field.n ≤ 16
instance (h : HeaderBytes) : Decidable (HeaderValid h) := by unfold HeaderValid; infer_instance

theorem header_bytes_length (h : HeaderBytes) : h.bytes.length = 16 := by
  simp [HeaderBytes.bytes, WordBytes.bytes]

theorem byte_const_eq (byte : UInt8) (value : Nat) (range : value < 256) :
    G.ofUInt8 byte = G.ofNat value ↔ byte.toNat = value := by
  have fieldRange : value < goldilocksModulus := by change value < 18446744069414584321; omega
  constructor
  · intro same
    have exactValue := congrArg G.n same
    simpa only [byte_field_exact, field_of_nat_exact value fieldRange] using exactValue
  · intro same
    apply field_n_injective
    simp only [byte_field_exact, field_of_nat_exact value fieldRange, same]

theorem magic_valid_iff (w : WordBytes) : MagicValid w ↔ w.bytes = [73, 88, 66, 89] := by
  unfold MagicValid
  change (G.ofUInt8 w.a = G.ofNat 73 ∧ G.ofUInt8 w.b = G.ofNat 88 ∧
    G.ofUInt8 w.c = G.ofNat 66 ∧ G.ofUInt8 w.d = G.ofNat 89) ↔ _
  rw [byte_const_eq w.a 73 (by decide), byte_const_eq w.b 88 (by decide),
    byte_const_eq w.c 66 (by decide), byte_const_eq w.d 89 (by decide)]
  constructor
  · rintro ⟨a, b, c, d⟩
    have aEq : w.a = 73 := UInt8.toNat_inj.mp a
    have bEq : w.b = 88 := UInt8.toNat_inj.mp b
    have cEq : w.c = 66 := UInt8.toNat_inj.mp c
    have dEq : w.d = 89 := UInt8.toNat_inj.mp d
    simp [WordBytes.bytes, aEq, bEq, cEq, dEq]
  · intro bytes
    have fields : w.a = 73 ∧ w.b = 88 ∧ w.c = 66 ∧ w.d = 89 := by simpa [WordBytes.bytes] using bytes
    simp [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]

theorem word_zero_iff (w : WordBytes) : w.field = 0 ↔ w.bytes = [0, 0, 0, 0] := by
  have packed := (packed_word_exact (G.ofUInt8 w.a) (G.ofUInt8 w.b) (G.ofUInt8 w.c) (G.ofUInt8 w.d)
    (by simpa using w.a.toNat_lt) (by simpa using w.b.toNat_lt)
    (by simpa using w.c.toNat_lt) (by simpa using w.d.toNat_lt)).1
  change w.field.n = wordValue (G.ofUInt8 w.a) (G.ofUInt8 w.b) (G.ofUInt8 w.c) (G.ofUInt8 w.d) at packed
  simp only [wordValue, byte_field_exact] at packed
  constructor
  · intro zero
    have value := congrArg G.n zero
    change w.field.n = 0 at value
    have a : w.a.toNat = 0 := by omega
    have b : w.b.toNat = 0 := by omega
    have c : w.c.toNat = 0 := by omega
    have d : w.d.toNat = 0 := by omega
    have aEq : w.a = 0 := UInt8.toNat_inj.mp a
    have bEq : w.b = 0 := UInt8.toNat_inj.mp b
    have cEq : w.c = 0 := UInt8.toNat_inj.mp c
    have dEq : w.d = 0 := UInt8.toNat_inj.mp d
    simp [WordBytes.bytes, aEq, bEq, cEq, dEq]
  · intro zero
    have fields : w.a = 0 ∧ w.b = 0 ∧ w.c = 0 ∧ w.d = 0 := by simpa [WordBytes.bytes] using zero
    apply field_n_injective
    rw [packed]
    simp only [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2]
    decide

/-- Header acceptance refers to the exact IXBY magic, revision zero, and
natural constructor count, not a truncated comparison or a reduced word. -/
theorem header_valid_iff (h : HeaderBytes) : HeaderValid h ↔
    h.magic.bytes = [73, 88, 66, 89] ∧ h.revision.bytes = [0, 0, 0, 0] ∧
      natOfBytesLE h.constructors.bytes.toArray ≤ 16 := by
  simp only [HeaderValid, magic_valid_iff, word_zero_iff, word_field_codec]

theorem header_entry_codec (h : HeaderBytes) : h.entry.field.n = natOfBytesLE h.entry.bytes.toArray :=
  word_field_codec h.entry

def readExpectOps (reader pointer expected start : Nat) : Array Aiur.Bytecode.Op :=
  #[.call reader #[pointer] 2 false, .assertEq #[start] #[expected] (some "IxBy byte/tag mismatch")]

def magicOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  #[.const 89, .const 73] ++ readExpectOps reader 0 3 4 ++ #[.const 88] ++
    readExpectOps reader 5 6 7 ++ #[.const 66] ++ readExpectOps reader 8 9 10 ++ readExpectOps reader 11 2 12
def revisionGuard : Array Aiur.Bytecode.Op :=
  #[.const 0, .assertEq #[30] #[31] (some "IxBy wire revision")]
def constructorGuard : Array Aiur.Bytecode.Op :=
  #[.const 16, .const 1, .add 66 67, .u32LessThan 65 68, .const 1,
    .assertEq #[69] #[70] (some "IxBy constructor capacity")]
def headerOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  magicOps reader ++ inlineWordOps reader 14 13 ++ revisionGuard ++
    inlineWordOps reader 32 21 ++ inlineWordOps reader 49 39 ++ constructorGuard
def programPrefixOps (reader declarations : Nat) : Array Aiur.Bytecode.Op :=
  headerOps reader ++ #[.call declarations #[56, 65] 2 false]

theorem header_ops_size (reader : Nat) : (headerOps reader).size = 59 := by
  simp [headerOps, magicOps, readExpectOps, inlineWordOps, revisionGuard, constructorGuard]
theorem program_prefix_ops_size (reader declarations : Nat) : (programPrefixOps reader declarations).size = 60 := by
  simp [programPrefixOps, header_ops_size]

/-- Prefix-only certificate. The suffix operations and final control are
deliberately unrestricted; accepting them is not a whole-function certificate. -/
def checkProgramPrefix (f : Aiur.Bytecode.Function) (reader declarations : Nat) : Bool :=
  decide (f.layout.inputSize = 2 ∧
    f.body.ops.toList.take (programPrefixOps reader declarations).size = (programPrefixOps reader declarations).toList)

def remainingOps (f : Aiur.Bytecode.Function) (reader declarations : Nat) : Array Aiur.Bytecode.Op :=
  (f.body.ops.toList.drop (programPrefixOps reader declarations).size).toArray

theorem program_prefix_checked (f : Aiur.Bytecode.Function) (reader declarations : Nat)
    (checked : checkProgramPrefix f reader declarations = true) :
    f.layout.inputSize = 2 ∧ f.body.ops = programPrefixOps reader declarations ++ remainingOps f reader declarations := by
  obtain ⟨input, ops⟩ := of_decide_eq_true checked
  refine ⟨input, ?_⟩
  apply Array.toList_inj.mp
  have combined := List.take_append_drop (programPrefixOps reader declarations).size f.body.ops.toList
  rw [ops] at combined
  simpa only [Array.toList_append, remainingOps, List.toList_toArray] using combined.symm

structure ProgramCode where
  runner : Nat
  declarations : DeclarationCode

structure CheckedProgram (t : Bytecode.Toplevel) (code : ProgramCode) where
  declarations : Objects.Declarations.CheckedCode t code.declarations
  runFn : Aiur.Bytecode.Function
  runFunction : t.functions[code.runner]? = some runFn
  prefixChecked : checkProgramPrefix runFn code.declarations.reader code.declarations.self = true

def checkProgramCode (t : Bytecode.Toplevel) (code : ProgramCode) : Bool :=
  match t.functions[code.runner]? with
  | some runner => checkDeclarationCode t code.declarations &&
      checkProgramPrefix runner code.declarations.reader code.declarations.self
  | none => false

theorem program_code_checked (t : Bytecode.Toplevel) (code : ProgramCode)
    (checked : checkProgramCode t code = true) : Nonempty (CheckedProgram t code) := by
  unfold checkProgramCode at checked
  split at checked
  · rename_i runner found
    simp only [Bool.and_eq_true] at checked
    obtain ⟨declarations⟩ := declaration_code_checked t code.declarations checked.1
    exact ⟨⟨declarations, runner, found, checked.2⟩⟩
  · simp at checked

private theorem run_single (t : Bytecode.Toplevel) (fuel : Nat) (op : Aiur.Bytecode.Op) (st : EvalState) :
    runOps t fuel #[op] st 0 = Aiur.Bytecode.Eval.evalOp t fuel op st := by
  simp [run_ops_list, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases Aiur.Bytecode.Eval.evalOp t fuel op st <;> rfl

private theorem eval_block_append (t : Bytecode.Toplevel) (fuel : Nat)
    (left right : Array Aiur.Bytecode.Op) (ctrl : Aiur.Bytecode.Ctrl) (st : EvalState) :
    evalBlock t fuel ⟨left ++ right, ctrl⟩ st =
      (runOps t fuel left st 0).bind (fun next => evalBlock t fuel ⟨right, ctrl⟩ next) := by
  simp only [evalBlock, run_ops_append]
  cases runOps t fuel left st 0 <;> rfl

private theorem assert_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (left right : Nat) (a b : G) (first : st.map[left]? = some a) (second : st.map[right]? = some b)
    (message : Option String) :
    Aiur.Bytecode.Eval.evalOp t fuel (.assertEq #[left] #[right] message) st =
      if a = b then .ok st else .error .assertFailed := by
  have equal : a.val = b.val ↔ a = b := ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  simp [Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx, first, second,
    equal, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem read_expect_eval (t : Bytecode.Toplevel) (fuel reader selector pointerIdx expectedIdx : Nat)
    (st : EvalState) (byteFn : Aiur.Bytecode.Function) (function : t.functions[reader]? = some byteFn)
    (checked : checkByteReader byteFn selector = true) (pointer byte tail expected : G)
    (argument : st.map[pointerIdx]? = some pointer) (expectedArg : st.map[expectedIdx]? = some expected)
    (loaded : memLoad st 3 pointer.n = .ok #[0, byte, tail]) :
    runOps t (fuel + 1) (readExpectOps reader pointerIdx expectedIdx st.map.size) st 0 =
      if byte = expected then .ok { st with map := st.map ++ #[byte, tail] } else .error .assertFailed := by
  have called := byte_reader_call t fuel selector reader pointerIdx st byteFn function checked pointer byte tail argument loaded false
  have expectedBound := (Array.getElem?_eq_some_iff.mp expectedArg).1
  have asserted := assert_eval t (fuel + 1) { st with map := st.map ++ #[byte, tail] }
    st.map.size expectedIdx byte expected (by simp)
    (by simpa [Array.getElem?_append, expectedBound] using expectedArg) (some "IxBy byte/tag mismatch")
  change runOps t (fuel + 1) (#[.call reader #[pointerIdx] 2 false] ++
    #[.assertEq #[st.map.size] #[expectedIdx] (some "IxBy byte/tag mismatch")]) st 0 = _
  rw [run_ops_append, run_single, called]
  simpa only [Except.bind, run_single] using asserted

def magicRegisters (program input p1 p2 p3 finish : G) (w : WordBytes) : Array G :=
  #[program, input, 89, 73, G.ofUInt8 w.a, p1, 88, G.ofUInt8 w.b, p2,
    66, G.ofUInt8 w.c, p3, G.ofUInt8 w.d, finish]

/-- Exact magic checking, preserving input/program pointers and all memory/I/O.
The byte reader is resolved in the same checked program bundle. -/
theorem checked_magic_prefix (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input finish : G) (w : WordBytes)
    (bytesRead : BytePrefix (bytecodeMemory st) program w.bytes finish) :
    ∃ registers : Array G, registers.size = 14 ∧ registers[0]? = some program ∧
      registers[1]? = some input ∧ registers[13]? = some finish ∧
      runOps t (fuel + 1) (magicOps code.declarations.reader) { st with map := #[program, input] } 0 =
        if MagicValid w then .ok { st with map := registers } else .error .assertFailed := by
  obtain ⟨p1, ha, rest⟩ := byte_prefix_head bytesRead
  obtain ⟨p2, hb, rest⟩ := byte_prefix_head rest
  obtain ⟨p3, hc, rest⟩ := byte_prefix_head rest
  obtain ⟨p4, hd, rest⟩ := byte_prefix_head rest
  cases rest
  have la := raw_load st 3 program _ ha
  have lb := raw_load st 3 p1 _ hb
  have lc := raw_load st 3 p2 _ hc
  have ld := raw_load st 3 p3 _ hd
  let sa : EvalState := { st with map := #[program, input, 89, 73] }
  let ra : EvalState := { st with map := sa.map ++ #[G.ofUInt8 w.a, p1] }
  let sb := pushMap ra 88
  let rb : EvalState := { st with map := sb.map ++ #[G.ofUInt8 w.b, p2] }
  let sc := pushMap rb 66
  let rc : EvalState := { st with map := sc.map ++ #[G.ofUInt8 w.c, p3] }
  let rd : EvalState := { st with map := rc.map ++ #[G.ofUInt8 w.d, finish] }
  have constants : runOps t (fuel + 1) #[.const 89, .const 73] { st with map := #[program, input] } 0 = .ok sa := by
    simp [run_ops_list, Aiur.Bytecode.Eval.evalOp, pushMap, sa, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have aRun := read_expect_eval t fuel code.declarations.reader code.declarations.byteSelector 0 3 sa
    checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
    program (G.ofUInt8 w.a) p1 73 (by simp [sa]) (by simp [sa]) (by simpa [sa] using la)
  have bRun := read_expect_eval t fuel code.declarations.reader code.declarations.byteSelector 5 6 sb
    checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
    p1 (G.ofUInt8 w.b) p2 88 (by simp [sb, ra, sa, pushMap]) (by simp [sb, ra, sa, pushMap])
    (by simpa [sb, ra, sa, pushMap] using lb)
  have cRun := read_expect_eval t fuel code.declarations.reader code.declarations.byteSelector 8 9 sc
    checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
    p2 (G.ofUInt8 w.c) p3 66 (by simp [sc, rb, sb, ra, sa, pushMap]) (by simp [sc, rb, sb, ra, sa, pushMap])
    (by simpa [sc, rb, sb, ra, sa, pushMap] using lc)
  have dRun := read_expect_eval t fuel code.declarations.reader code.declarations.byteSelector 11 2 rc
    checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
    p3 (G.ofUInt8 w.d) finish 89 (by simp [rc, sc, rb, sb, ra, sa, pushMap]) (by simp [rc, sc, rb, sb, ra, sa, pushMap])
    (by simpa [rc, sc, rb, sb, ra, sa, pushMap] using ld)
  change runOps t (fuel + 1) (readExpectOps code.declarations.reader 0 3 4) sa 0 =
    (if G.ofUInt8 w.a = 73 then .ok ra else .error .assertFailed) at aRun
  change runOps t (fuel + 1) (readExpectOps code.declarations.reader 5 6 7) sb 0 =
    (if G.ofUInt8 w.b = 88 then .ok rb else .error .assertFailed) at bRun
  change runOps t (fuel + 1) (readExpectOps code.declarations.reader 8 9 10) sc 0 =
    (if G.ofUInt8 w.c = 66 then .ok rc else .error .assertFailed) at cRun
  change runOps t (fuel + 1) (readExpectOps code.declarations.reader 11 2 12) rc 0 =
    (if G.ofUInt8 w.d = 89 then .ok rd else .error .assertFailed) at dRun
  have c88 : Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.const 88) ra = .ok sb := by simp only [Aiur.Bytecode.Eval.evalOp, sb]
  have c66 : Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.const 66) rb = .ok sc := by simp only [Aiur.Bytecode.Eval.evalOp, sc]
  refine ⟨magicRegisters program input p1 p2 p3 finish w, by simp [magicRegisters],
    by simp [magicRegisters], by simp [magicRegisters], by simp [magicRegisters], ?_⟩
  by_cases a : G.ofUInt8 w.a = 73 <;> by_cases b : G.ofUInt8 w.b = 88 <;>
    by_cases c : G.ofUInt8 w.c = 66 <;> by_cases d : G.ofUInt8 w.d = 89 <;>
    simp only [magicOps, run_ops_append, constants, aRun, bRun, cRun, dRun, run_single, c88, c66,
      MagicValid, a, b, c, d, and_self, and_true, and_false, ite_true, ite_false, Except.bind]
  simp [rd, rc, sc, rb, sb, ra, sa, pushMap, magicRegisters]

private theorem revision_guard_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 31) (word : G) (revision : st.map[30]? = some word) :
    runOps t fuel revisionGuard st 0 =
      if word = 0 then .ok { st with map := st.map.push 0 } else .error .assertFailed := by
  have asserted := assert_eval t fuel (pushMap st 0) 30 31 word 0
    (by simpa [pushMap, Array.getElem_push, size] using revision)
    (by simp [pushMap, Array.getElem_push, size]) (some "IxBy wire revision")
  change runOps t fuel (#[.const 0] ++ #[.assertEq #[30] #[31] (some "IxBy wire revision")]) st 0 = _
  rw [run_ops_append, run_single]
  simpa only [Aiur.Bytecode.Eval.evalOp, Except.bind, run_single, pushMap] using asserted

private theorem constructor_guard_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 66) (word : G) (range : word.n < 2 ^ 32) (count : st.map[65]? = some word) :
    runOps t fuel constructorGuard st 0 = if word.n ≤ 16 then
      .ok { st with map := st.map ++ #[16, 1, 17, 1, 1] } else .error .assertFailed := by
  obtain ⟨_, countValue⟩ := Array.getElem?_eq_some_iff.mp count
  have added : (16 : G) + 1 = 17 := by decide
  have different : (0 : G).val ≠ (1 : G).val := by decide
  have comparison := field_u32_limit word range
  simp at comparison
  by_cases limit : word.n ≤ 16 <;>
    simp +arith [constructorGuard, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
      size, countValue, added, different, comparison, limit,
      Array.getElem?_push, Array.getElem_push, pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Array.toList_inj.mp
  simp [List.append_assoc]

/-- Live values at the constructor-reader call. Entry is a full u32; checking
it against the later function table is deliberately not part of this prefix. -/
structure PrefixRegisters (registers : Array G) (program input finish : G) (h : HeaderBytes) : Prop where
  size : registers.size = 71
  program : registers[0]? = some program
  input : registers[1]? = some input
  entry : registers[48]? = some h.entry.field
  count : registers[65]? = some h.constructors.field
  suffix : registers[56]? = some finish

/-- The actual sixteen-byte header and its guards. No constructor-capacity
premise is assumed: the compiled u32 check establishes it on success. -/
theorem checked_header_eval (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input finish : G) (h : HeaderBytes)
    (bytesRead : BytePrefix (bytecodeMemory st) program h.bytes finish) :
    ∃ registers, PrefixRegisters registers program input finish h ∧
      runOps t (fuel + 1) (headerOps code.declarations.reader) { st with map := #[program, input] } 0 =
        if HeaderValid h then .ok { st with map := registers } else .error .assertFailed := by
  obtain ⟨afterMagic, magicRead, wordsRead⟩ := byte_prefix_split bytesRead
  obtain ⟨afterRevision, revisionRead, wordsRead⟩ := byte_prefix_split wordsRead
  obtain ⟨afterEntry, entryRead, countRead⟩ := byte_prefix_split wordsRead
  obtain ⟨magicRegs, magicSize, magicProgram, magicInput, magicFinish, magicRun⟩ :=
    checked_magic_prefix t code checked fuel st program input afterMagic h.magic magicRead
  let magicState : EvalState := { st with map := magicRegs }
  obtain ⟨revisionRegs, revisionSize, revisionFinish, revisionValue, revisionRun⟩ :=
    inline_word_prefix t fuel code.declarations.byteSelector code.declarations.reader 13 magicState
      checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
      afterMagic afterRevision h.revision magicFinish revisionRead
  change runOps t (fuel + 1) (inlineWordOps code.declarations.reader magicRegs.size 13) magicState 0 = _ at revisionRun
  rw [magicSize] at revisionRun
  let revisionState : EvalState := { st with map := magicRegs ++ revisionRegs }
  have revisionStateSize : revisionState.map.size = 31 := by simp [revisionState, magicSize, revisionSize]
  have revisionArg : revisionState.map[30]? = some h.revision.field := by
    simpa [revisionState, Array.getElem?_append, magicSize] using revisionValue
  have revisionGuardRun := revision_guard_eval t (fuel + 1) revisionState revisionStateSize h.revision.field revisionArg
  let entryStart : EvalState := { st with map := revisionState.map.push 0 }
  have entryStartSize : entryStart.map.size = 32 := by simp [entryStart, revisionStateSize]
  have entryPointer : entryStart.map[21]? = some afterRevision := by
    simpa [entryStart, Array.getElem_push, Array.getElem?_push, revisionStateSize, revisionState,
      Array.getElem?_append, magicSize, revisionSize] using revisionFinish
  obtain ⟨entryRegs, entrySize, entryFinish, entryValue, entryRun⟩ :=
    inline_word_prefix t fuel code.declarations.byteSelector code.declarations.reader 21 entryStart
      checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
      afterRevision afterEntry h.entry entryPointer entryRead
  rw [entryStartSize] at entryRun
  let countStart : EvalState := { st with map := entryStart.map ++ entryRegs }
  have countStartSize : countStart.map.size = 49 := by simp [countStart, entryStartSize, entrySize]
  have countPointer : countStart.map[39]? = some afterEntry := by
    simpa [countStart, Array.getElem?_append, entryStartSize] using entryFinish
  obtain ⟨countRegs, countSize, countFinish, countValue, countRun⟩ :=
    inline_word_prefix t fuel code.declarations.byteSelector code.declarations.reader 39 countStart
      checked.declarations.byteFn checked.declarations.byteFunction checked.declarations.byteChecked
      afterEntry finish h.constructors countPointer countRead
  rw [countStartSize] at countRun
  let countState : EvalState := { st with map := countStart.map ++ countRegs }
  have countStateSize : countState.map.size = 66 := by simp [countState, countStartSize, countSize]
  have countArg : countState.map[65]? = some h.constructors.field := by
    simpa [countState, Array.getElem?_append, countStartSize] using countValue
  have countGuardRun := constructor_guard_eval t (fuel + 1) countState countStateSize h.constructors.field
    (word_field_bound h.constructors) countArg
  let registers := countState.map ++ #[16, 1, 17, 1, 1]
  refine ⟨registers, ?_, ?_⟩
  · refine ⟨by simp [registers, countStateSize], ?_, ?_, ?_, ?_, ?_⟩
    · simpa [registers, countState, countStart, entryStart, revisionState,
        Array.getElem?_append, Array.getElem?_push, magicSize, revisionSize, entrySize, countSize] using magicProgram
    · simpa [registers, countState, countStart, entryStart, revisionState,
        Array.getElem?_append, Array.getElem?_push, magicSize, revisionSize, entrySize, countSize] using magicInput
    · simpa [registers, countStateSize, countState, countStartSize, countStart, entryStartSize, entrySize, countSize,
        Array.getElem?_append] using entryValue
    · simpa [registers, countStateSize, Array.getElem?_append] using countArg
    · simpa [registers, countStateSize, countState, countStartSize, countSize, Array.getElem?_append] using countFinish
  · simp only [magicState, revisionState, entryStart, countStart, countState] at revisionRun revisionGuardRun entryRun countRun countGuardRun
    by_cases magic : MagicValid h.magic <;> by_cases revision : h.revision.field = 0 <;>
      by_cases count : h.constructors.field.n ≤ 16 <;>
      simp only [headerOps, run_ops_append, magicRun, revisionRun, revisionGuardRun, entryRun, countRun,
        countGuardRun, HeaderValid, magic, revision, count, and_self, and_true, and_false,
        ite_true, ite_false, Except.bind]
    rfl

/-- Exact state handed to the still-uncertified function-table continuation. -/
def admittedState (st : EvalState) (registers : Array G) (decls : List DeclarationBytes) (finish : G) : EvalState :=
  { (storeDeclarations st decls).1 with map := registers ++ #[(storeDeclarations st decls).2, finish] }

/-- Invalid magic, revision, or count rejects before the declaration call,
without any declaration bytes, allocation bound, or recursive fuel premise. -/
theorem checked_program_header_reject (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input finish : G) (h : HeaderBytes)
    (bytesRead : BytePrefix (bytecodeMemory st) program h.bytes finish) (invalid : ¬ HeaderValid h) :
    evalBlock t (fuel + 1) checked.runFn.body { st with map := #[program, input] } = .error .assertFailed := by
  obtain ⟨_, _, headerRun⟩ := checked_header_eval t code checked fuel st program input finish h bytesRead
  obtain ⟨_, body⟩ := program_prefix_checked checked.runFn _ _ checked.prefixChecked
  rw [if_neg invalid] at headerRun
  cases blockEq : checked.runFn.body with
  | mk ops ctrl =>
    simp only [blockEq] at body
    simp only [body, programPrefixOps, eval_block_append, run_ops_append, headerRun, Except.bind]

/-- The actual header and declaration call together. Capacity is derived from
the header check; the uniform initial bound covers at most sixteen cells plus
Nil, including content-deduplicated allocations. -/
theorem checked_program_prefix (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input declarationsStart finish : G) (h : HeaderBytes)
    (decls : List DeclarationBytes) (count : h.constructors.field.n = decls.length)
    (space : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (headerRead : BytePrefix (bytecodeMemory st) program h.bytes declarationsStart)
    (declarationsRead : BytePrefix (bytecodeMemory st) declarationsStart (decls.flatMap DeclarationBytes.bytes) finish) :
    ∃ registers, PrefixRegisters registers program input declarationsStart h ∧
      runOps t (fuel + decls.length + 3) (programPrefixOps code.declarations.reader code.declarations.self)
        { st with map := #[program, input] } 0 =
        if HeaderValid h ∧ Valid decls then .ok (admittedState st registers decls finish) else .error .assertFailed := by
  obtain ⟨registers, registerFacts, headerRun⟩ := checked_header_eval t code checked
    (fuel + decls.length + 2) st program input declarationsStart h headerRead
  refine ⟨registers, registerFacts, ?_⟩
  by_cases header : HeaderValid h
  · have capacity : decls.length ≤ 16 := by rw [← count]; exact header.2.2
    have tableSpace : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus := by omega
    have countField : h.constructors.field = G.ofNat decls.length := by
      apply field_n_injective
      rw [field_of_nat_exact _ (by change decls.length < 18446744069414584321; omega), count]
    have arguments : readIdxs { st with map := registers } #[56, 65] = .ok #[declarationsStart, G.ofNat decls.length] := by
      simp [readIdxs, readIdx, registerFacts.suffix, registerFacts.count, countField,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    have called := checked_declarations_call t code.declarations checked.declarations fuel { st with map := registers }
      decls capacity tableSpace declarationsStart finish declarationsRead #[56, 65] arguments false
    simp only [store_declarations_map] at called
    rw [if_pos header] at headerRun
    simp only [programPrefixOps, run_ops_append, headerRun, Except.bind, run_single, called,
      header, true_and, admittedState]
  · simp only [programPrefixOps, run_ops_append, headerRun, header, false_and, ite_false, Except.bind]

/-- Successful prefix admission supplies the ordered semantic constructor
table and exact live registers, while preserving I/O and all earlier reads. -/
theorem checked_program_table (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input declarationsStart finish : G) (h : HeaderBytes)
    (decls : List DeclarationBytes) (count : h.constructors.field.n = decls.length)
    (space : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (headerRead : BytePrefix (bytecodeMemory st) program h.bytes declarationsStart)
    (declarationsRead : BytePrefix (bytecodeMemory st) declarationsStart (decls.flatMap DeclarationBytes.bytes) finish)
    (after : EvalState)
    (executed : runOps t (fuel + decls.length + 3) (programPrefixOps code.declarations.reader code.declarations.self)
      { st with map := #[program, input] } 0 = .ok after) :
    HeaderValid h ∧ Valid decls ∧ decls.length ≤ 16 ∧
      after.map.size = 73 ∧ after.map[0]? = some program ∧ after.map[1]? = some input ∧
      after.map[48]? = some h.entry.field ∧ after.map[65]? = some h.constructors.field ∧
      after.map[71]? = some (storeDeclarations st decls).2 ∧ after.map[72]? = some finish ∧
      readTable (bytecodeMemory after) (storeDeclarations st decls).2.n decls.length =
        some (decls.map DeclarationBytes.declaration).toArray ∧
      after.ioBuffer = st.ioBuffer ∧ bucketSize after 13 ≤ bucketSize st 13 + decls.length + 1 ∧
      (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad after width pointer = .ok flat) := by
  obtain ⟨registers, facts, run⟩ := checked_program_prefix t code checked fuel st program input declarationsStart finish
    h decls count space headerRead declarationsRead
  rw [run] at executed
  split at executed
  · rename_i accepted
    have same := Except.ok.inj executed
    subst after
    have capacity : decls.length ≤ 16 := by rw [← count]; exact accepted.1.2.2
    refine ⟨accepted.1, accepted.2, capacity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [admittedState, facts.size]
    · simpa [admittedState, Array.getElem?_append, facts.size] using facts.program
    · simpa [admittedState, Array.getElem?_append, facts.size] using facts.input
    · simpa [admittedState, Array.getElem?_append, facts.size] using facts.entry
    · simpa [admittedState, Array.getElem?_append, facts.size] using facts.count
    · simp [admittedState, facts.size]
    · simp [admittedState, facts.size]
    · exact store_declarations_table st decls accepted.2 capacity (by omega)
    · exact store_declarations_io st decls
    · exact store_declarations_size st decls
    · intro width pointer flat read
      exact store_declarations_preserves st decls read
  · contradiction

/-- The prefix certificate is not whole-program acceptance: it either
rejects or passes the exact proved state to the original suffix and control. -/
theorem checked_program_continuation (t : Bytecode.Toplevel) (code : ProgramCode) (checked : CheckedProgram t code)
    (fuel : Nat) (st : EvalState) (program input declarationsStart finish : G) (h : HeaderBytes)
    (decls : List DeclarationBytes) (count : h.constructors.field.n = decls.length)
    (space : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (headerRead : BytePrefix (bytecodeMemory st) program h.bytes declarationsStart)
    (declarationsRead : BytePrefix (bytecodeMemory st) declarationsStart (decls.flatMap DeclarationBytes.bytes) finish) :
    ∃ registers, PrefixRegisters registers program input declarationsStart h ∧
      evalBlock t (fuel + decls.length + 3) checked.runFn.body { st with map := #[program, input] } =
        if HeaderValid h ∧ Valid decls then
          evalBlock t (fuel + decls.length + 3)
            ⟨remainingOps checked.runFn code.declarations.reader code.declarations.self, checked.runFn.body.ctrl⟩
            (admittedState st registers decls finish)
        else .error .assertFailed := by
  obtain ⟨registers, facts, prefixRun⟩ := checked_program_prefix t code checked fuel st program input declarationsStart finish
    h decls count space headerRead declarationsRead
  obtain ⟨_, body⟩ := program_prefix_checked checked.runFn _ _ checked.prefixChecked
  refine ⟨registers, facts, ?_⟩
  cases blockEq : checked.runFn.body with
  | mk ops ctrl =>
    simp only [blockEq] at body
    rw [body, eval_block_append, prefixRun]
    split <;> simp only [Except.bind]

/-- Every sixteen-byte prefix has this representation; grouping does not
exclude any malformed magic, revision, entry, or count bytes. -/
theorem group_header_bytes (bytes : List UInt8) (length : bytes.length = 16) :
    ∃ h : HeaderBytes, h.bytes = bytes := by
  obtain ⟨words, count, grouped⟩ := group_word_bytes 4 bytes (by omega)
  match words with
  | [] | [_] | [_, _] | [_, _, _] => simp_all
  | magic :: revision :: entry :: constructors :: rest =>
    have empty : rest = [] := by simpa using count
    subst rest
    refine ⟨⟨magic, revision, entry, constructors⟩, ?_⟩
    simpa [HeaderBytes.bytes] using grouped

/-- Successful checked advice loading supplies the genuine bytes for the
actual program prefix, not an assumed byte-range contract. Initial address,
metadata, byte-memory, and worst-case table-memory bounds remain explicit. -/
theorem loaded_program_prefix (t : Bytecode.Toplevel) (loaderCode : LoaderCode) (loader : CheckedLoader t loaderCode)
    (code : ProgramCode) (checked : CheckedProgram t code) (loadFuel parseFuel : Nat)
    (st : EvalState) (channel input : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (byteSpace : bucketSize st 3 + values.length + 1 ≤ goldilocksModulus)
    (h : HeaderBytes) (decls : List DeclarationBytes) (suffix : List UInt8)
    (bytes : adviceBytes values = h.bytes ++ (decls.flatMap DeclarationBytes.bytes ++ suffix))
    (count : h.constructors.field.n = decls.length)
    (tableSpace : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (outputs : Array G) (loaded : EvalState)
    (executed : evalBlock t (loadFuel + values.length + 1) loader.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      .error (.earlyReturn outputs loaded)) :
    ∃ declarationsStart finish registers,
      outputs = #[(storeAdvice st values).2] ∧
      PrefixRegisters registers (storeAdvice st values).2 input declarationsStart h ∧
      runOps t (parseFuel + decls.length + 3) (programPrefixOps code.declarations.reader code.declarations.self)
        { loaded with map := #[(storeAdvice st values).2, input] } 0 =
        (if HeaderValid h ∧ Valid decls then .ok (admittedState loaded registers decls finish) else .error .assertFailed) ∧
      (HeaderValid h ∧ Valid decls →
        decls.length ≤ 16 ∧
        ByteStream (bytecodeMemory (admittedState loaded registers decls finish)) finish suffix ∧
        readTable (bytecodeMemory (admittedState loaded registers decls finish)) (storeDeclarations loaded decls).2.n decls.length =
          some (decls.map DeclarationBytes.declaration).toArray ∧
        (admittedState loaded registers decls finish).ioBuffer = st.ioBuffer ∧
        (∀ width pointer flat, memLoad st width pointer = .ok flat →
          memLoad (admittedState loaded registers decls finish) width pointer = .ok flat)) := by
  obtain ⟨_, _, outputsEq, stream, io, _, other, preserved⟩ := checked_load_admission t loaderCode loader
    loadFuel st channel start limit values metadata available address lengthRange limitRange byteSpace outputs loaded executed
  obtain ⟨terminal, whole, nilRead⟩ := stream
  rw [bytes] at whole
  obtain ⟨declarationsStart, headerRead, rest⟩ := byte_prefix_split whole
  obtain ⟨finish, declarationsRead, suffixRead⟩ := byte_prefix_split rest
  have space : bucketSize loaded 13 + 17 ≤ goldilocksModulus := by
    rw [other 13 (by decide)]
    exact tableSpace
  obtain ⟨registers, facts, prefixRun⟩ := checked_program_prefix t code checked parseFuel loaded
    (storeAdvice st values).2 input declarationsStart finish h decls count space headerRead declarationsRead
  refine ⟨declarationsStart, finish, registers, outputsEq, facts, prefixRun, ?_⟩
  intro accepted
  have capacity : decls.length ≤ 16 := by rw [← count]; exact accepted.1.2.2
  refine ⟨capacity, ⟨terminal, store_declarations_prefix loaded decls suffixRead, ?_⟩,
    store_declarations_table loaded decls accepted.2 capacity (by omega),
    (store_declarations_io loaded decls).trans io, ?_⟩
  · have stored := store_declarations_preserves loaded decls (raw_load loaded 3 terminal _ nilRead)
    change bytecodeMemory (storeDeclarations loaded decls).1 3 terminal.n = some #[1, 1, 1]
    simp only [bytecodeMemory, stored]
  · intro width pointer flat read
    exact store_declarations_preserves loaded decls (preserved width pointer flat read)

end
end
end Ix.Ixby.AiurBackend.Objects.ProgramPrefix
