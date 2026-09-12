module
public import Ix.Ixby.Aiur.Objects.ProgramPrefix
import all Ix.Aiur.Goldilocks

/-! Actual function-count, function-header, and block-header admission.

These prefix certificates bind the next Call, but do not assume that it or
the remaining continuation succeeds. Instruction decoding, complete block and
function tables, whole-image validation, and authenticated program binding
remain separate obligations. All results concern the Lean bytecode evaluator,
not compiler, gadget, trace, or AIR correctness.
-/

namespace Ix.Ixby.AiurBackend.Objects.CodeHeaders

deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open Objects.Refinement Objects.Memory Objects.Store Objects.Table Objects.Parser
open Objects.Identity Objects.Equality Objects.Unique Objects.Declarations Objects.Admission Objects.ProgramPrefix

def upperOps (word start limit : Nat) (message : String) : Array Aiur.Bytecode.Op :=
  #[.const (G.ofNat limit), .const 1, .add start (start + 1), .u32LessThan word (start + 2),
    .const 1, .assertEq #[start + 3] #[start + 4] (some message)]

def nonzeroOps (word start : Nat) (message : String) : Array Aiur.Bytecode.Op :=
  #[.eqZero word, .const 0, .assertEq #[start] #[start + 1] (some message)]

/-- Cast-based comparisons are natural comparisons for genuine u32 words
and these small profile limits. -/
theorem u32_upper_exact (word : G) (range : word.n < 2 ^ 32) (limit : Nat) (small : limit ≤ 64) :
    word.val.toUInt32 < (G.ofNat limit + 1).val.toUInt32 ↔ word.n ≤ limit := by
  have wordExact : G.ofNat word.n = word := by
    apply field_n_injective
    exact field_of_nat_exact _ (by change word.n < 18446744069414584321; omega)
  simpa only [wordExact] using load_u32_limit word.n limit range (by omega)

private theorem upper_eval (t : Bytecode.Toplevel) (fuel idx start limit : Nat) (message : String)
    (st : EvalState) (size : st.map.size = start) (word : G)
    (argument : st.map[idx]? = some word) (range : word.n < 2 ^ 32) (small : limit ≤ 64) :
    runOps t fuel (upperOps idx start limit message) st 0 =
      if word.n ≤ limit then .ok { st with map := st.map ++ #[G.ofNat limit, 1, G.ofNat (limit + 1), 1, 1] }
      else .error .assertFailed := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp argument
  rw [size] at bound
  have before0 : idx ≠ start := by omega
  have before1 : idx ≠ start + 1 := by omega
  have before2 : idx ≠ start + 2 := by omega
  have added : G.ofNat limit + 1 = G.ofNat (limit + 1) := by
    change G.ofNat ((G.ofNat limit).n + 1) = _
    rw [field_of_nat_exact _ (by change limit < 18446744069414584321; omega)]
  have comparison := u32_upper_exact word range limit small
  rw [added] at comparison
  have different : (0 : G).val ≠ (1 : G).val := by decide
  simp at comparison
  by_cases accepted : word.n ≤ limit <;>
    simp +arith [upperOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
      size, found, bound, before0, before1, before2, added, different, comparison, accepted,
      Array.getElem?_push, Array.getElem_push, pushMap,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Array.toList_inj.mp
  simp [List.append_assoc]

private theorem nonzero_eval (t : Bytecode.Toplevel) (fuel idx start : Nat) (message : String)
    (st : EvalState) (size : st.map.size = start) (word : G) (argument : st.map[idx]? = some word) :
    runOps t fuel (nonzeroOps idx start message) st 0 =
      if word.n ≠ 0 then .ok { st with map := st.map ++ #[0, 0] } else .error .assertFailed := by
  have zero : word.val = 0 ↔ word.n = 0 :=
    ⟨fun h => congrArg UInt64.toNat h, fun h => UInt64.toNat_inj.mp (show word.val.toNat = (0 : UInt64).toNat from h)⟩
  have different : (1 : G).val ≠ (0 : G).val := by decide
  by_cases equal : word.n = 0 <;>
    simp +arith [nonzeroOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
      size, argument, zero, equal, different, Array.getElem?_push, pushMap,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact (Array.append_push (xs := st.map) (ys := #[0]) (a := 0)).symm

def functionCountOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  inlineWordOps reader 73 72 ++ upperOps 89 90 8 "IxBy function capacity" ++
    nonzeroOps 89 95 "IxBy empty program" ++ #[.const 0]

def programHeadersOps (reader declarations : Nat) : Array Aiur.Bytecode.Op :=
  programPrefixOps reader declarations ++ functionCountOps reader

structure FunctionHeaderBytes where
  arity : WordBytes
  entry : WordBytes
  blocks : WordBytes

def FunctionHeaderBytes.bytes (h : FunctionHeaderBytes) : List UInt8 :=
  h.arity.bytes ++ (h.entry.bytes ++ h.blocks.bytes)

def FunctionHeaderValid (h : FunctionHeaderBytes) : Prop :=
  h.arity.field.n ≤ 16 ∧ h.blocks.field.n ≤ 64 ∧ h.blocks.field.n ≠ 0
instance (h : FunctionHeaderBytes) : Decidable (FunctionHeaderValid h) := by
  unfold FunctionHeaderValid; infer_instance

def functionHeaderOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  inlineWordOps reader 3 0 ++ upperOps 19 20 16 "IxBy function arity capacity" ++
    upperOps 19 25 64 "IxBy function local capacity" ++ inlineWordOps reader 30 10 ++
    inlineWordOps reader 47 37 ++ upperOps 63 64 64 "IxBy block capacity" ++
    nonzeroOps 63 69 "IxBy empty function"

def blockHeaderOps (reader : Nat) : Array Aiur.Bytecode.Op :=
  inlineWordOps reader 3 0 ++ upperOps 19 20 64 "IxBy declared local capacity"

def functionCall (functions : Nat) : Aiur.Bytecode.Op := .call functions #[80, 89, 97] 2 false
def blockCall (blocks : Nat) : Aiur.Bytecode.Op := .call blocks #[54, 63, 2] 2 false
def instructionCall (instruction : Nat) : Aiur.Bytecode.Op := .call instruction #[10, 2, 19] 11 false

theorem function_count_ops_size (reader : Nat) : (functionCountOps reader).size = 23 := by
  simp [functionCountOps, inlineWordOps, upperOps, nonzeroOps]
theorem program_headers_ops_size (reader declarations : Nat) : (programHeadersOps reader declarations).size = 83 := by
  simp [programHeadersOps, program_prefix_ops_size, function_count_ops_size]
theorem function_header_ops_size (reader : Nat) : (functionHeaderOps reader).size = 60 := by
  simp [functionHeaderOps, inlineWordOps, upperOps, nonzeroOps]
theorem block_header_ops_size (reader : Nat) : (blockHeaderOps reader).size = 19 := by
  simp [blockHeaderOps, inlineWordOps, upperOps]
theorem function_header_bytes_length (h : FunctionHeaderBytes) : h.bytes.length = 12 := by
  simp [FunctionHeaderBytes.bytes, WordBytes.bytes]
theorem function_header_valid_iff (h : FunctionHeaderBytes) : FunctionHeaderValid h ↔
    natOfBytesLE h.arity.bytes.toArray ≤ 16 ∧
      1 ≤ natOfBytesLE h.blocks.bytes.toArray ∧ natOfBytesLE h.blocks.bytes.toArray ≤ 64 := by
  simp only [FunctionHeaderValid, word_field_codec]
  omega

def emptyListBranch (width : Nat) : Aiur.Bytecode.Block :=
  ⟨#[.const 1, .const 1, .store (#[3] ++ Array.replicate (width - 1) 4)], .return 0 #[5, 0]⟩
def listDispatch (width : Nat) (step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 1 #[(0, emptyListBranch width)] (some step)⟩

/-- Bind an operation prefix plus the exact next Call; all following
operations and control remain unrestricted. -/
def checkOpsPrefix (ops expected : Array Aiur.Bytecode.Op) : Bool :=
  decide (ops.toList.take expected.size = expected.toList)
def dropOps (ops : Array Aiur.Bytecode.Op) (count : Nat) : Array Aiur.Bytecode.Op :=
  (ops.toList.drop count).toArray

theorem ops_prefix_checked (ops expected : Array Aiur.Bytecode.Op) (checked : checkOpsPrefix ops expected = true) :
    ops = expected ++ dropOps ops expected.size := by
  have equal := of_decide_eq_true checked
  apply Array.toList_inj.mp
  have combined := List.take_append_drop expected.size ops.toList
  rw [equal] at combined
  simpa only [Array.toList_append, dropOps, List.toList_toArray] using combined.symm

def checkEmptyListBranch (branch : Aiur.Bytecode.Block) (width : Nat) : Bool :=
  match branch.ctrl with
  | .return selector outs => decide (branch.ops = (emptyListBranch width).ops ∧ selector = 0 ∧ outs = #[5, 0])
  | _ => false

theorem empty_list_branch_checked (branch : Aiur.Bytecode.Block) (width : Nat)
    (checked : checkEmptyListBranch branch width = true) : branch = emptyListBranch width := by
  unfold checkEmptyListBranch at checked
  split at checked
  · rename_i selector outs ctrl
    obtain ⟨ops, selected, outputs⟩ := of_decide_eq_true checked
    cases branch
    simp_all [emptyListBranch]
  · simp at checked

def checkListHeader (f : Aiur.Bytecode.Function) (width : Nat)
    (header : Array Aiur.Bytecode.Op) (next : Aiur.Bytecode.Op) : Bool :=
  match f.body.ctrl with
  | .match idx arms (some step) =>
    match arms.toList with
    | [(tag, branch)] => decide (f.layout.inputSize = 3 ∧ f.body.ops = #[] ∧ idx = 1 ∧ tag = 0) &&
        checkEmptyListBranch branch width && checkOpsPrefix step.ops (header ++ #[next])
    | _ => false
  | _ => false

structure ListHeaderShape (f : Aiur.Bytecode.Function) (width : Nat)
    (header : Array Aiur.Bytecode.Op) (next : Aiur.Bytecode.Op) where
  arity : f.layout.inputSize = 3
  step : Aiur.Bytecode.Block
  dispatch : f.body = listDispatch width step
  rest : Array Aiur.Bytecode.Op
  operations : step.ops = header ++ (#[next] ++ rest)

theorem list_header_checked (f : Aiur.Bytecode.Function) (width : Nat)
    (header : Array Aiur.Bytecode.Op) (next : Aiur.Bytecode.Op)
    (checked : checkListHeader f width header next = true) : Nonempty (ListHeaderShape f width header next) := by
  unfold checkListHeader at checked
  split at checked
  · rename_i idx arms step control
    split at checked
    · rename_i tag branch armsList
      simp only [Bool.and_eq_true] at checked
      obtain ⟨arity, ops, index, tagEq⟩ := of_decide_eq_true checked.1.1
      have branchEq := empty_list_branch_checked branch width checked.1.2
      have branches : arms = #[(0, emptyListBranch width)] := by
        apply Array.toList_inj.mp
        simpa only [tagEq, branchEq] using armsList
      refine ⟨⟨arity, step, ?_, dropOps step.ops (header ++ #[next]).size, ?_⟩⟩
      · cases body : f.body with
        | mk operations ctrl => simp_all [listDispatch]
      · simpa only [Array.append_assoc] using ops_prefix_checked step.ops (header ++ #[next]) checked.2
    · simp at checked
  · simp at checked

structure HeaderCode where
  program : ProgramCode
  functions : Nat
  blocks : Nat
  instruction : Nat

def checkProgramHeaders (f : Aiur.Bytecode.Function) (code : HeaderCode) : Bool :=
  checkOpsPrefix f.body.ops (programHeadersOps code.program.declarations.reader code.program.declarations.self ++ #[functionCall code.functions])

structure CheckedHeaders (t : Bytecode.Toplevel) (code : HeaderCode) where
  program : CheckedProgram t code.program
  programHeaders : checkProgramHeaders program.runFn code = true
  functionsFn : Aiur.Bytecode.Function
  functionsFound : t.functions[code.functions]? = some functionsFn
  functionsHeader : ListHeaderShape functionsFn 6 (functionHeaderOps code.program.declarations.reader) (blockCall code.blocks)
  blocksFn : Aiur.Bytecode.Function
  blocksFound : t.functions[code.blocks]? = some blocksFn
  blocksHeader : ListHeaderShape blocksFn 13 (blockHeaderOps code.program.declarations.reader) (instructionCall code.instruction)

/-- The instruction Call's index/arguments are bound, but its body is not
certified or executed by these header contracts. -/
def checkHeaderCode (t : Bytecode.Toplevel) (code : HeaderCode) : Bool :=
  match t.functions[code.program.runner]?, t.functions[code.functions]?, t.functions[code.blocks]? with
  | some runner, some functions, some blocks =>
    checkProgramCode t code.program && checkProgramHeaders runner code &&
      checkListHeader functions 6 (functionHeaderOps code.program.declarations.reader) (blockCall code.blocks) &&
      checkListHeader blocks 13 (blockHeaderOps code.program.declarations.reader) (instructionCall code.instruction)
  | _, _, _ => false

theorem header_code_checked (t : Bytecode.Toplevel) (code : HeaderCode)
    (checked : checkHeaderCode t code = true) : Nonempty (CheckedHeaders t code) := by
  unfold checkHeaderCode at checked
  split at checked
  · rename_i runner functions blocks runnerFound functionsFound blocksFound
    simp only [Bool.and_eq_true] at checked
    obtain ⟨program⟩ := program_code_checked t code.program checked.1.1.1
    have runnerEq : program.runFn = runner := Option.some.inj (program.runFunction.symm.trans runnerFound)
    obtain ⟨functionsHeader⟩ := list_header_checked functions 6 _ _ checked.1.2
    obtain ⟨blocksHeader⟩ := list_header_checked blocks 13 _ _ checked.2
    exact ⟨⟨program, by simpa only [runnerEq] using checked.1.1.2,
      functions, functionsFound, functionsHeader, blocks, blocksFound, blocksHeader⟩⟩
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

private theorem list_nonzero (t : Bytecode.Toplevel) (fuel width : Nat) (step : Aiur.Bytecode.Block)
    (st : EvalState) (pointer remaining self : G) (nonzero : remaining ≠ 0) :
    evalBlock t fuel (listDispatch width step) { st with map := #[pointer, remaining, self] } =
      evalBlock t fuel step { st with map := #[pointer, remaining, self] } := by
  have nonzeroVal : (0 : G).val ≠ remaining.val := fun eq => nonzero (Subtype.ext eq.symm)
  simp [listDispatch, evalBlock, run_ops_list, evalCtrl, evalMatchArm, evalDefaultBlock,
    readIdx, nonzeroVal, Pure.pure, Except.pure]

structure FunctionRegisters (registers : Array G) (pointer remaining self finish : G) (h : FunctionHeaderBytes) : Prop where
  size : registers.size = 71
  pointer : registers[0]? = some pointer
  remaining : registers[1]? = some remaining
  self : registers[2]? = some self
  arity : registers[19]? = some h.arity.field
  entry : registers[46]? = some h.entry.field
  blocks : registers[63]? = some h.blocks.field
  suffix : registers[54]? = some finish

/-- The twelve header bytes and all actual function-header guards, including
the redundant local-capacity check. No block bytes or table allocation premise
is needed; entry validation belongs to the later cross-table checker. -/
theorem checked_function_header (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (h : FunctionHeaderBytes)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer h.bytes finish) :
    ∃ registers, FunctionRegisters registers pointer remaining self finish h ∧
      runOps t (fuel + 1) (functionHeaderOps code.program.declarations.reader)
        { st with map := #[pointer, remaining, self] } 0 =
        if FunctionHeaderValid h then .ok { st with map := registers } else .error .assertFailed := by
  obtain ⟨afterArity, arityRead, rest⟩ := byte_prefix_split bytesRead
  obtain ⟨afterEntry, entryRead, countRead⟩ := byte_prefix_split rest
  let initial : EvalState := { st with map := #[pointer, remaining, self] }
  obtain ⟨arityRegs, aritySize, arityFinish, arityValue, arityRun⟩ := inline_word_prefix t fuel
    code.program.declarations.byteSelector code.program.declarations.reader 0 initial
    checked.program.declarations.byteFn checked.program.declarations.byteFunction checked.program.declarations.byteChecked
    pointer afterArity h.arity (by simp [initial]) arityRead
  change runOps t (fuel + 1) (inlineWordOps code.program.declarations.reader 3 0)
    { st with map := #[pointer, remaining, self] } 0 =
      .ok { st with map := #[pointer, remaining, self] ++ arityRegs } at arityRun
  let arityState : EvalState := { st with map := initial.map ++ arityRegs }
  have arityStateSize : arityState.map.size = 20 := by simp [arityState, initial, aritySize]
  have arityArg : arityState.map[19]? = some h.arity.field := by
    simpa [arityState, initial, Array.getElem?_append] using arityValue
  have arityGuard := upper_eval t (fuel + 1) 19 20 16 "IxBy function arity capacity"
    arityState arityStateSize h.arity.field arityArg (word_field_bound h.arity) (by decide)
  let localsState : EvalState := { st with map := arityState.map ++ #[G.ofNat 16, 1, G.ofNat (16 + 1), 1, 1] }
  have localsSize : localsState.map.size = 25 := by simp [localsState, arityStateSize]
  have localsArg : localsState.map[19]? = some h.arity.field := by
    simpa [localsState, Array.getElem?_append, arityStateSize] using arityArg
  have localsGuard := upper_eval t (fuel + 1) 19 25 64 "IxBy function local capacity"
    localsState localsSize h.arity.field localsArg (word_field_bound h.arity) (by decide)
  let entryStart : EvalState := { st with map := localsState.map ++ #[G.ofNat 64, 1, G.ofNat (64 + 1), 1, 1] }
  have entryStartSize : entryStart.map.size = 30 := by simp [entryStart, localsSize]
  have entryPointer : entryStart.map[10]? = some afterArity := by
    simpa [entryStart, localsState, arityState, initial, aritySize, Array.getElem?_append] using arityFinish
  obtain ⟨entryRegs, entrySize, entryFinish, entryValue, entryRun⟩ := inline_word_prefix t fuel
    code.program.declarations.byteSelector code.program.declarations.reader 10 entryStart
    checked.program.declarations.byteFn checked.program.declarations.byteFunction checked.program.declarations.byteChecked
    afterArity afterEntry h.entry entryPointer entryRead
  rw [entryStartSize] at entryRun
  let blocksStart : EvalState := { st with map := entryStart.map ++ entryRegs }
  have blocksStartSize : blocksStart.map.size = 47 := by simp [blocksStart, entryStartSize, entrySize]
  have blocksPointer : blocksStart.map[37]? = some afterEntry := by
    simpa [blocksStart, Array.getElem?_append, entryStartSize] using entryFinish
  obtain ⟨blockRegs, blockSize, blockFinish, blockValue, blockRun⟩ := inline_word_prefix t fuel
    code.program.declarations.byteSelector code.program.declarations.reader 37 blocksStart
    checked.program.declarations.byteFn checked.program.declarations.byteFunction checked.program.declarations.byteChecked
    afterEntry finish h.blocks blocksPointer countRead
  rw [blocksStartSize] at blockRun
  let blocksState : EvalState := { st with map := blocksStart.map ++ blockRegs }
  have blocksSize : blocksState.map.size = 64 := by simp [blocksState, blocksStartSize, blockSize]
  have blocksArg : blocksState.map[63]? = some h.blocks.field := by
    simpa [blocksState, Array.getElem?_append, blocksStartSize] using blockValue
  have blocksGuard := upper_eval t (fuel + 1) 63 64 64 "IxBy block capacity"
    blocksState blocksSize h.blocks.field blocksArg (word_field_bound h.blocks) (by decide)
  let nonzeroState : EvalState := { st with map := blocksState.map ++ #[G.ofNat 64, 1, G.ofNat (64 + 1), 1, 1] }
  have nonzeroSize : nonzeroState.map.size = 69 := by simp [nonzeroState, blocksSize]
  have nonzeroArg : nonzeroState.map[63]? = some h.blocks.field := by
    simpa [nonzeroState, Array.getElem?_append, blocksSize] using blocksArg
  have nonzeroGuard := nonzero_eval t (fuel + 1) 63 69 "IxBy empty function" nonzeroState nonzeroSize h.blocks.field nonzeroArg
  let registers := nonzeroState.map ++ #[0, 0]
  refine ⟨registers, ?_, ?_⟩
  · refine ⟨by simp [registers, nonzeroSize], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [registers, nonzeroState, blocksState, blocksStart, entryStart, localsState, arityState, initial, Array.getElem?_append]
    · simp [registers, nonzeroState, blocksState, blocksStart, entryStart, localsState, arityState, initial, Array.getElem?_append]
    · simp [registers, nonzeroState, blocksState, blocksStart, entryStart, localsState, arityState, initial, Array.getElem?_append]
    · simpa [registers, nonzeroState, blocksState, blocksStart, entryStart, localsState, arityState, initial,
        aritySize, entrySize, blockSize, Array.getElem?_append] using arityValue
    · simpa [registers, nonzeroState, blocksState, blocksStart, entryStartSize, entrySize, blockSize,
        Array.getElem?_append] using entryValue
    · simpa [registers, nonzeroState, blocksSize, Array.getElem?_append] using blocksArg
    · simpa [registers, nonzeroState, blocksState, blocksStartSize, blockSize, Array.getElem?_append] using blockFinish
  · simp only [initial, arityState, localsState, entryStart, blocksStart, blocksState, nonzeroState] at arityRun arityGuard localsGuard entryRun blockRun blocksGuard nonzeroGuard
    by_cases arity : h.arity.field.n ≤ 16
    · have locals : h.arity.field.n ≤ 64 := by omega
      by_cases blocks : h.blocks.field.n ≤ 64 <;> by_cases nonzero : h.blocks.field.n ≠ 0 <;>
        simp only [functionHeaderOps, run_ops_append, arityRun, arityGuard, localsGuard, entryRun, blockRun,
          blocksGuard, nonzeroGuard, FunctionHeaderValid, arity, locals, blocks, nonzero,
          and_self, and_false, true_and, false_and, ite_true, ite_false, Except.bind]
      simp only [registers, nonzeroState, blocksState, blocksStart, entryStart, localsState, arityState, initial]
    · simp only [functionHeaderOps, run_ops_append, arityRun, arityGuard, FunctionHeaderValid,
        arity, false_and, ite_false, Except.bind]

structure BlockRegisters (registers : Array G) (pointer remaining self finish : G) (locals : WordBytes) : Prop where
  size : registers.size = 25
  pointer : registers[0]? = some pointer
  remaining : registers[1]? = some remaining
  self : registers[2]? = some self
  locals : registers[19]? = some locals.field
  suffix : registers[10]? = some finish

/-- The actual four-byte local declaration and capacity check, before any
instruction byte is needed or the instruction decoder is called. -/
theorem checked_block_header (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (locals : WordBytes)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer locals.bytes finish) :
    ∃ registers, BlockRegisters registers pointer remaining self finish locals ∧
      runOps t (fuel + 1) (blockHeaderOps code.program.declarations.reader)
        { st with map := #[pointer, remaining, self] } 0 =
        if locals.field.n ≤ 64 then .ok { st with map := registers } else .error .assertFailed := by
  let initial : EvalState := { st with map := #[pointer, remaining, self] }
  obtain ⟨wordRegs, wordSize, wordFinish, wordValue, wordRun⟩ := inline_word_prefix t fuel
    code.program.declarations.byteSelector code.program.declarations.reader 0 initial
    checked.program.declarations.byteFn checked.program.declarations.byteFunction checked.program.declarations.byteChecked
    pointer finish locals (by simp [initial]) bytesRead
  change runOps t (fuel + 1) (inlineWordOps code.program.declarations.reader 3 0)
    { st with map := #[pointer, remaining, self] } 0 =
      .ok { st with map := #[pointer, remaining, self] ++ wordRegs } at wordRun
  let wordState : EvalState := { st with map := initial.map ++ wordRegs }
  have size : wordState.map.size = 20 := by simp [wordState, initial, wordSize]
  have argument : wordState.map[19]? = some locals.field := by simpa [wordState, initial, Array.getElem?_append] using wordValue
  have guarded := upper_eval t (fuel + 1) 19 20 64 "IxBy declared local capacity" wordState size
    locals.field argument (word_field_bound locals) (by decide)
  let registers := wordState.map ++ #[G.ofNat 64, 1, G.ofNat (64 + 1), 1, 1]
  refine ⟨registers, ?_, ?_⟩
  · refine ⟨by simp [registers, size], ?_, ?_, ?_, ?_, ?_⟩
    · simp [registers, wordState, initial, Array.getElem?_append]
    · simp [registers, wordState, initial, Array.getElem?_append]
    · simp [registers, wordState, initial, Array.getElem?_append]
    · simpa [registers, wordState, initial, wordSize, Array.getElem?_append] using wordValue
    · simpa [registers, wordState, initial, wordSize, Array.getElem?_append] using wordFinish
  · simp only [initial, wordState] at wordRun guarded
    simpa only [blockHeaderOps, run_ops_append, wordRun, Except.bind] using guarded

def ListHeaderShape.continuation {f : Aiur.Bytecode.Function} {width : Nat}
    {header : Array Aiur.Bytecode.Op} {next : Aiur.Bytecode.Op}
    (shape : ListHeaderShape f width header next) : Aiur.Bytecode.Block :=
  ⟨#[next] ++ shape.rest, shape.step.ctrl⟩

private theorem list_header_tail (t : Bytecode.Toplevel) (fuel width : Nat) (f : Aiur.Bytecode.Function)
    (header : Array Aiur.Bytecode.Op) (next : Aiur.Bytecode.Op) (shape : ListHeaderShape f width header next)
    (st : EvalState) (pointer remaining self : G) (nonzero : remaining ≠ 0)
    (accepted : Prop) [Decidable accepted] (registers : Array G)
    (executed : runOps t fuel header { st with map := #[pointer, remaining, self] } 0 =
      if accepted then .ok { st with map := registers } else .error .assertFailed) :
    evalBlock t fuel f.body { st with map := #[pointer, remaining, self] } =
      if accepted then evalBlock t fuel shape.continuation { st with map := registers } else .error .assertFailed := by
  rw [shape.dispatch, list_nonzero t fuel width shape.step st pointer remaining self nonzero]
  have operations := shape.operations
  cases stepEq : shape.step with
  | mk ops ctrl =>
    simp only [stepEq] at operations
    rw [operations, eval_block_append, executed]
    split <;> simp only [Except.bind, ListHeaderShape.continuation, stepEq]

/-- Valid headers pass their exact state to the original block Call and
remaining function-reader continuation. That continuation is not assumed to
parse blocks, recurse successfully, or return a valid function table. -/
theorem checked_function_continuation (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (h : FunctionHeaderBytes)
    (nonzero : remaining ≠ 0) (bytesRead : BytePrefix (bytecodeMemory st) pointer h.bytes finish) :
    ∃ registers, FunctionRegisters registers pointer remaining self finish h ∧
      evalBlock t (fuel + 1) checked.functionsFn.body { st with map := #[pointer, remaining, self] } =
        if FunctionHeaderValid h then
          evalBlock t (fuel + 1) checked.functionsHeader.continuation { st with map := registers }
        else .error .assertFailed := by
  obtain ⟨registers, facts, run⟩ := checked_function_header t code checked fuel st pointer remaining self finish h bytesRead
  exact ⟨registers, facts, list_header_tail t (fuel + 1) 6 checked.functionsFn _ _ checked.functionsHeader
    st pointer remaining self nonzero (FunctionHeaderValid h) registers run⟩

theorem checked_function_header_reject (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (h : FunctionHeaderBytes)
    (nonzero : remaining ≠ 0) (bytesRead : BytePrefix (bytecodeMemory st) pointer h.bytes finish)
    (invalid : ¬ FunctionHeaderValid h) :
    evalBlock t (fuel + 1) checked.functionsFn.body { st with map := #[pointer, remaining, self] } = .error .assertFailed := by
  obtain ⟨_, _, run⟩ := checked_function_continuation t code checked fuel st pointer remaining self finish h nonzero bytesRead
  simpa only [if_neg invalid] using run

/-- A block header passes locals and self unchanged to the exact instruction
Call; later instruction/recursive behavior remains outside this contract. -/
theorem checked_block_continuation (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (locals : WordBytes)
    (nonzero : remaining ≠ 0) (bytesRead : BytePrefix (bytecodeMemory st) pointer locals.bytes finish) :
    ∃ registers, BlockRegisters registers pointer remaining self finish locals ∧
      evalBlock t (fuel + 1) checked.blocksFn.body { st with map := #[pointer, remaining, self] } =
        if locals.field.n ≤ 64 then
          evalBlock t (fuel + 1) checked.blocksHeader.continuation { st with map := registers }
        else .error .assertFailed := by
  obtain ⟨registers, facts, run⟩ := checked_block_header t code checked fuel st pointer remaining self finish locals bytesRead
  exact ⟨registers, facts, list_header_tail t (fuel + 1) 13 checked.blocksFn _ _ checked.blocksHeader
    st pointer remaining self nonzero (locals.field.n ≤ 64) registers run⟩

theorem checked_block_header_reject (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (pointer remaining self finish : G) (locals : WordBytes)
    (nonzero : remaining ≠ 0) (bytesRead : BytePrefix (bytecodeMemory st) pointer locals.bytes finish)
    (invalid : ¬ locals.field.n ≤ 64) :
    evalBlock t (fuel + 1) checked.blocksFn.body { st with map := #[pointer, remaining, self] } = .error .assertFailed := by
  obtain ⟨_, _, run⟩ := checked_block_continuation t code checked fuel st pointer remaining self finish locals nonzero bytesRead
  simpa only [if_neg invalid] using run

def emptyListState (st : EvalState) (pointer self : G) (width : Nat) : EvalState :=
  { (memStore st (Array.replicate width 1)).1 with
    map := #[pointer, 0, self, 1, 1, G.ofNat (memStore st (Array.replicate width 1)).2] }

private theorem empty_list_eval (t : Bytecode.Toplevel) (fuel width : Nat) (step : Aiur.Bytecode.Block)
    (supported : width = 6 ∨ width = 13) (st : EvalState) (pointer self : G) :
    evalBlock t fuel (listDispatch width step) { st with map := #[pointer, 0, self] } =
      .error (.earlyReturn #[G.ofNat (memStore st (Array.replicate width 1)).2, pointer]
        (emptyListState st pointer self width)) := by
  rcases supported with widthEq | widthEq <;> subst width <;>
    simp [listDispatch, emptyListBranch, emptyListState, Array.replicate, evalBlock, run_ops_list,
      Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap, evalCtrl, evalMatchArm,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Both exact zero-count branches allocate their correctly padded Nil and
return the untouched byte pointer, without reading any bytes or using Call
fuel. The initial capacity bound prevents field-pointer wrap; deduplication
and the shared width-13 constructor/block bucket are permitted. -/
theorem checked_empty_list (t : Bytecode.Toplevel) (fuel width : Nat) (f : Aiur.Bytecode.Function)
    (header : Array Aiur.Bytecode.Op) (next : Aiur.Bytecode.Op) (shape : ListHeaderShape f width header next)
    (supported : width = 6 ∨ width = 13) (st : EvalState) (pointer self : G)
    (space : bucketSize st width + 1 ≤ goldilocksModulus) :
    evalBlock t fuel f.body { st with map := #[pointer, 0, self] } =
        .error (.earlyReturn #[G.ofNat (memStore st (Array.replicate width 1)).2, pointer]
          (emptyListState st pointer self width)) ∧
      memLoad (emptyListState st pointer self width) width (G.ofNat (memStore st (Array.replicate width 1)).2).n =
        .ok (Array.replicate width 1) ∧
      (emptyListState st pointer self width).ioBuffer = st.ioBuffer ∧
      bucketSize (emptyListState st pointer self width) width ≤ bucketSize st width + 1 ∧
      (∀ size address flat, memLoad st size address = .ok flat →
        memLoad (emptyListState st pointer self width) size address = .ok flat) := by
  have bounds := mem_store_bounds st (Array.replicate width 1)
  simp only [Array.size_replicate] at bounds
  refine ⟨by rw [shape.dispatch]; exact empty_list_eval t fuel width shape.step supported st pointer self,
    ?_, mem_store_io st _, bounds.2, fun _ _ _ read => mem_store_preserves st _ read⟩
  change memLoad (memStore st (Array.replicate width 1)).1 width
    (G.ofNat (memStore st (Array.replicate width 1)).2).n = .ok (Array.replicate width 1)
  simpa only [Array.size_replicate] using stored_field_pointer st (Array.replicate width 1) (by omega)

def FunctionCountValid (word : WordBytes) : Prop := word.field.n ≤ 8 ∧ word.field.n ≠ 0
instance (word : WordBytes) : Decidable (FunctionCountValid word) := by unfold FunctionCountValid; infer_instance

theorem function_count_valid_iff (word : WordBytes) : FunctionCountValid word ↔
    1 ≤ natOfBytesLE word.bytes.toArray ∧ natOfBytesLE word.bytes.toArray ≤ 8 := by
  simp only [FunctionCountValid, word_field_codec]
  omega

/-- The actual function-count read and both guards append exactly twenty-five
registers to the constructor-prefix state. Input/program/table/entry registers
are all retained; the next Call receives the exact suffix, count, and self zero. -/
theorem checked_function_count (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (size : st.map.size = 73) (pointer finish : G) (word : WordBytes)
    (argument : st.map[72]? = some pointer) (bytesRead : BytePrefix (bytecodeMemory st) pointer word.bytes finish) :
    ∃ extra : Array G, extra.size = 25 ∧ extra[7]? = some finish ∧ extra[16]? = some word.field ∧ extra[24]? = some 0 ∧
      runOps t (fuel + 1) (functionCountOps code.program.declarations.reader) st 0 =
        if FunctionCountValid word then .ok { st with map := st.map ++ extra } else .error .assertFailed := by
  obtain ⟨wordRegs, wordSize, wordFinish, wordValue, wordRun⟩ := inline_word_prefix t fuel
    code.program.declarations.byteSelector code.program.declarations.reader 72 st
    checked.program.declarations.byteFn checked.program.declarations.byteFunction checked.program.declarations.byteChecked
    pointer finish word argument bytesRead
  rw [size] at wordRun
  let wordState : EvalState := { st with map := st.map ++ wordRegs }
  have wordStateSize : wordState.map.size = 90 := by simp [wordState, size, wordSize]
  have wordArg : wordState.map[89]? = some word.field := by simpa [wordState, Array.getElem?_append, size] using wordValue
  have upperRun := upper_eval t (fuel + 1) 89 90 8 "IxBy function capacity" wordState wordStateSize
    word.field wordArg (word_field_bound word) (by decide)
  let nonzeroState : EvalState := { st with map := wordState.map ++ #[G.ofNat 8, 1, G.ofNat (8 + 1), 1, 1] }
  have nonzeroSize : nonzeroState.map.size = 95 := by simp [nonzeroState, wordStateSize]
  have nonzeroArg : nonzeroState.map[89]? = some word.field := by
    simpa [nonzeroState, Array.getElem?_append, wordStateSize] using wordArg
  have nonzeroRun := nonzero_eval t (fuel + 1) 89 95 "IxBy empty program" nonzeroState nonzeroSize word.field nonzeroArg
  let extra := (wordRegs ++ #[G.ofNat 8, 1, G.ofNat (8 + 1), 1, 1] ++ #[0, 0]).push 0
  refine ⟨extra, by simp [extra, wordSize], ?_, ?_, ?_, ?_⟩
  · simpa [extra, wordSize, Array.getElem_push, Array.getElem?_push, Array.getElem?_append] using wordFinish
  · simpa [extra, wordSize, Array.getElem_push, Array.getElem?_push, Array.getElem?_append] using wordValue
  · simp [extra, wordSize]
  · simp only [wordState, nonzeroState] at upperRun nonzeroRun
    by_cases upper : word.field.n ≤ 8 <;> by_cases nonzero : word.field.n ≠ 0 <;>
      simp only [functionCountOps, run_ops_append, wordRun, upperRun, nonzeroRun, run_single,
        Aiur.Bytecode.Eval.evalOp, FunctionCountValid, upper, nonzero, and_self, and_false, true_and, false_and,
        ite_true, ite_false, Except.bind]
    simp [nonzero, pushMap, extra, Array.append_assoc]

def headersContinuation (f : Aiur.Bytecode.Function) (code : HeaderCode) : Aiur.Bytecode.Block :=
  ⟨#[functionCall code.functions] ++ dropOps f.body.ops
    (programHeadersOps code.program.declarations.reader code.program.declarations.self ++ #[functionCall code.functions]).size,
    f.body.ctrl⟩

theorem program_headers_checked (f : Aiur.Bytecode.Function) (code : HeaderCode)
    (checked : checkProgramHeaders f code = true) :
    f.body.ops = programHeadersOps code.program.declarations.reader code.program.declarations.self ++
      (headersContinuation f code).ops := by
  simpa only [headersContinuation, Array.append_assoc] using ops_prefix_checked f.body.ops _ checked

def countState (st : EvalState) (registers extra : Array G) (decls : List DeclarationBytes) (declarationsEnd : G) : EvalState :=
  { admittedState st registers decls declarationsEnd with
    map := (admittedState st registers decls declarationsEnd).map ++ extra }

/-- The actual program prefix now derives both table-count bounds and passes
the exact state to the bound function-reader Call. It does not assume that
function parsing or any later whole-image check succeeds. -/
theorem checked_program_headers (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (program input declarationsStart declarationsEnd functionsStart : G)
    (h : HeaderBytes) (decls : List DeclarationBytes) (word : WordBytes)
    (count : h.constructors.field.n = decls.length) (space : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (headerRead : BytePrefix (bytecodeMemory st) program h.bytes declarationsStart)
    (declarationsRead : BytePrefix (bytecodeMemory st) declarationsStart (decls.flatMap DeclarationBytes.bytes) declarationsEnd)
    (countRead : BytePrefix (bytecodeMemory st) declarationsEnd word.bytes functionsStart) :
    ∃ registers extra, PrefixRegisters registers program input declarationsStart h ∧
      extra.size = 25 ∧ extra[7]? = some functionsStart ∧ extra[16]? = some word.field ∧ extra[24]? = some 0 ∧
      runOps t (fuel + decls.length + 3) (programHeadersOps code.program.declarations.reader code.program.declarations.self)
        { st with map := #[program, input] } 0 =
        (if HeaderValid h ∧ Valid decls ∧ FunctionCountValid word then
          .ok (countState st registers extra decls declarationsEnd) else .error .assertFailed) ∧
      evalBlock t (fuel + decls.length + 3) checked.program.runFn.body { st with map := #[program, input] } =
        (if HeaderValid h ∧ Valid decls ∧ FunctionCountValid word then
          evalBlock t (fuel + decls.length + 3) (headersContinuation checked.program.runFn code)
            (countState st registers extra decls declarationsEnd) else .error .assertFailed) := by
  obtain ⟨registers, facts, prefixRun⟩ := checked_program_prefix t code.program checked.program fuel st program input
    declarationsStart declarationsEnd h decls count space headerRead declarationsRead
  let admitted := admittedState st registers decls declarationsEnd
  have admittedSize : admitted.map.size = 73 := by simp [admitted, admittedState, facts.size]
  have countArg : admitted.map[72]? = some declarationsEnd := by simp [admitted, admittedState, facts.size]
  have preservedCount : BytePrefix (bytecodeMemory admitted) declarationsEnd word.bytes functionsStart :=
    store_declarations_prefix st decls countRead
  obtain ⟨extra, extraSize, extraFinish, extraValue, extraSelf, countRun⟩ := checked_function_count t code checked
    (fuel + decls.length + 2) admitted admittedSize declarationsEnd functionsStart word countArg preservedCount
  change runOps t (fuel + decls.length + 3) (functionCountOps code.program.declarations.reader)
    (admittedState st registers decls declarationsEnd) 0 =
      (if FunctionCountValid word then .ok (countState st registers extra decls declarationsEnd)
        else .error .assertFailed) at countRun
  have headersRun : runOps t (fuel + decls.length + 3)
      (programHeadersOps code.program.declarations.reader code.program.declarations.self)
      { st with map := #[program, input] } 0 =
      if HeaderValid h ∧ Valid decls ∧ FunctionCountValid word then
        .ok (countState st registers extra decls declarationsEnd) else .error .assertFailed := by
    by_cases prior : HeaderValid h ∧ Valid decls <;> by_cases countValid : FunctionCountValid word <;>
      simp only [programHeadersOps, run_ops_append, prefixRun, countRun, prior, countValid,
        and_self, and_true, and_false, ite_true, ite_false, Except.bind]
  refine ⟨registers, extra, facts, extraSize, extraFinish, extraValue, extraSelf, headersRun, ?_⟩
  have operations := program_headers_checked checked.program.runFn code checked.programHeaders
  cases bodyEq : checked.program.runFn.body with
  | mk ops ctrl =>
    simp only [bodyEq] at operations
    rw [operations, eval_block_append, headersRun]
    split <;> simp only [Except.bind, headersContinuation, bodyEq]

structure ProgramRegisters (registers : Array G) (program input functionsStart table : G)
    (h : HeaderBytes) (word : WordBytes) : Prop where
  size : registers.size = 98
  program : registers[0]? = some program
  input : registers[1]? = some input
  entry : registers[48]? = some h.entry.field
  constructors : registers[65]? = some h.constructors.field
  table : registers[71]? = some table
  suffix : registers[80]? = some functionsStart
  functions : registers[89]? = some word.field
  self : registers[97]? = some 0

theorem count_state_registers (st : EvalState) (registers extra : Array G) (decls : List DeclarationBytes)
    (program input declarationsStart declarationsEnd functionsStart : G) (h : HeaderBytes) (word : WordBytes)
    (facts : PrefixRegisters registers program input declarationsStart h) (extraSize : extra.size = 25)
    (suffix : extra[7]? = some functionsStart) (count : extra[16]? = some word.field) (self : extra[24]? = some 0) :
    ProgramRegisters (countState st registers extra decls declarationsEnd).map program input functionsStart
      (storeDeclarations st decls).2 h word := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [countState, admittedState, facts.size, extraSize]
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using facts.program
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using facts.input
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using facts.entry
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using facts.count
  · simp [countState, admittedState, Array.getElem?_append, facts.size]
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using suffix
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using count
  · simpa [countState, admittedState, Array.getElem?_append, facts.size] using self

/-- Exact arguments of the structurally bound function-reader Call. -/
theorem program_function_arguments (st : EvalState) (program input functionsStart table : G)
    (h : HeaderBytes) (word : WordBytes) (facts : ProgramRegisters st.map program input functionsStart table h word) :
    readIdxs st #[80, 89, 97] = .ok #[functionsStart, word.field, 0] := by
  simp [readIdxs, readIdx, facts.suffix, facts.functions, facts.self, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Successful execution derives both count bounds, preserves the constructor
table and its original wire order, and exposes the actual 98-register state. -/
theorem checked_program_headers_success (t : Bytecode.Toplevel) (code : HeaderCode) (checked : CheckedHeaders t code)
    (fuel : Nat) (st : EvalState) (program input declarationsStart declarationsEnd functionsStart : G)
    (h : HeaderBytes) (decls : List DeclarationBytes) (word : WordBytes)
    (count : h.constructors.field.n = decls.length) (space : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (headerRead : BytePrefix (bytecodeMemory st) program h.bytes declarationsStart)
    (declarationsRead : BytePrefix (bytecodeMemory st) declarationsStart (decls.flatMap DeclarationBytes.bytes) declarationsEnd)
    (countRead : BytePrefix (bytecodeMemory st) declarationsEnd word.bytes functionsStart)
    (after : EvalState)
    (executed : runOps t (fuel + decls.length + 3)
      (programHeadersOps code.program.declarations.reader code.program.declarations.self)
      { st with map := #[program, input] } 0 = .ok after) :
    HeaderValid h ∧ Valid decls ∧ decls.length ≤ 16 ∧ 1 ≤ word.field.n ∧ word.field.n ≤ 8 ∧
      ProgramRegisters after.map program input functionsStart (storeDeclarations st decls).2 h word ∧
      readTable (bytecodeMemory after) (storeDeclarations st decls).2.n decls.length =
        some (decls.map DeclarationBytes.declaration).toArray ∧
      after.ioBuffer = st.ioBuffer ∧ bucketSize after 13 ≤ bucketSize st 13 + decls.length + 1 ∧
      (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad after width pointer = .ok flat) := by
  obtain ⟨registers, extra, facts, size, suffix, value, self, run, _⟩ := checked_program_headers t code checked
    fuel st program input declarationsStart declarationsEnd functionsStart h decls word count space headerRead declarationsRead countRead
  rw [run] at executed
  split at executed
  · rename_i accepted
    have same := Except.ok.inj executed
    subst after
    have capacity : decls.length ≤ 16 := by rw [← count]; exact accepted.1.2.2
    have countBounds := accepted.2.2
    refine ⟨accepted.1, accepted.2.1, capacity, by unfold FunctionCountValid at countBounds; omega,
      countBounds.1, count_state_registers st registers extra decls program input declarationsStart declarationsEnd
        functionsStart h word facts size suffix value self, ?_, store_declarations_io st decls,
      store_declarations_size st decls, fun _ _ _ read => store_declarations_preserves st decls read⟩
    exact store_declarations_table st decls accepted.2.1 capacity (by omega)
  · contradiction

/-- No representation bias: every twelve-byte function header, including
unsupported arities/counts and arbitrary u32 entries, has this grouping. -/
theorem group_function_header_bytes (bytes : List UInt8) (length : bytes.length = 12) :
    ∃ h : FunctionHeaderBytes, h.bytes = bytes := by
  obtain ⟨words, count, grouped⟩ := group_word_bytes 3 bytes (by omega)
  match words with
  | [] | [_] | [_, _] => simp_all
  | arity :: entry :: blocks :: rest =>
    have empty : rest = [] := by simpa using count
    subst rest
    refine ⟨⟨arity, entry, blocks⟩, ?_⟩
    simpa [FunctionHeaderBytes.bytes] using grouped

/-- Checked advice loading supplies the genuine bytes for both program count
guards. The function-byte suffix is preserved, but is not assumed to decode
as a valid function table or canonical whole program. -/
theorem loaded_program_headers (t : Bytecode.Toplevel) (loaderCode : LoaderCode) (loader : CheckedLoader t loaderCode)
    (code : HeaderCode) (checked : CheckedHeaders t code) (loadFuel parseFuel : Nat)
    (st : EvalState) (channel input : G) (start limit : Nat) (values : List G)
    (metadata : st.ioBuffer.map[(channel, (#[0] : Array G))]? = some ⟨start, values.length⟩)
    (available : AdviceSlice st.ioBuffer channel start values)
    (address : start + values.length < goldilocksModulus)
    (lengthRange : values.length < 2 ^ 32) (limitRange : limit + 1 < 2 ^ 32)
    (byteSpace : bucketSize st 3 + values.length + 1 ≤ goldilocksModulus)
    (h : HeaderBytes) (decls : List DeclarationBytes) (word : WordBytes) (suffix : List UInt8)
    (bytes : adviceBytes values = h.bytes ++ (decls.flatMap DeclarationBytes.bytes ++ (word.bytes ++ suffix)))
    (count : h.constructors.field.n = decls.length) (tableSpace : bucketSize st 13 + 17 ≤ goldilocksModulus)
    (outputs : Array G) (loaded : EvalState)
    (executed : evalBlock t (loadFuel + values.length + 1) loader.loadFn.body { st with map := #[channel, G.ofNat limit] } =
      .error (.earlyReturn outputs loaded)) :
    ∃ declarationsEnd functionsStart registers extra,
      outputs = #[(storeAdvice st values).2] ∧
      ProgramRegisters (countState loaded registers extra decls declarationsEnd).map (storeAdvice st values).2 input
        functionsStart (storeDeclarations loaded decls).2 h word ∧
      runOps t (parseFuel + decls.length + 3)
        (programHeadersOps code.program.declarations.reader code.program.declarations.self)
        { loaded with map := #[(storeAdvice st values).2, input] } 0 =
        (if HeaderValid h ∧ Valid decls ∧ FunctionCountValid word then
          .ok (countState loaded registers extra decls declarationsEnd) else .error .assertFailed) ∧
      (HeaderValid h ∧ Valid decls ∧ FunctionCountValid word →
        decls.length ≤ 16 ∧ 1 ≤ word.field.n ∧ word.field.n ≤ 8 ∧
        ByteStream (bytecodeMemory (countState loaded registers extra decls declarationsEnd)) functionsStart suffix ∧
        readTable (bytecodeMemory (countState loaded registers extra decls declarationsEnd)) (storeDeclarations loaded decls).2.n decls.length =
          some (decls.map DeclarationBytes.declaration).toArray ∧
        (countState loaded registers extra decls declarationsEnd).ioBuffer = st.ioBuffer ∧
        (∀ width pointer flat, memLoad st width pointer = .ok flat →
          memLoad (countState loaded registers extra decls declarationsEnd) width pointer = .ok flat)) := by
  obtain ⟨_, _, outputsEq, stream, io, _, other, preserved⟩ := checked_load_admission t loaderCode loader
    loadFuel st channel start limit values metadata available address lengthRange limitRange byteSpace outputs loaded executed
  obtain ⟨terminal, whole, nilRead⟩ := stream
  rw [bytes] at whole
  obtain ⟨declarationsStart, headerRead, rest⟩ := byte_prefix_split whole
  obtain ⟨declarationsEnd, declarationsRead, rest⟩ := byte_prefix_split rest
  obtain ⟨functionsStart, countRead, suffixRead⟩ := byte_prefix_split rest
  have space : bucketSize loaded 13 + 17 ≤ goldilocksModulus := by
    rw [other 13 (by decide)]
    exact tableSpace
  obtain ⟨registers, extra, facts, size, finish, value, self, run, _⟩ := checked_program_headers t code checked parseFuel loaded
    (storeAdvice st values).2 input declarationsStart declarationsEnd functionsStart h decls word count space headerRead declarationsRead countRead
  refine ⟨declarationsEnd, functionsStart, registers, extra, outputsEq,
    count_state_registers loaded registers extra decls (storeAdvice st values).2 input declarationsStart declarationsEnd
      functionsStart h word facts size finish value self, run, ?_⟩
  intro accepted
  have capacity : decls.length ≤ 16 := by rw [← count]; exact accepted.1.2.2
  have countBounds := accepted.2.2
  refine ⟨capacity, by unfold FunctionCountValid at countBounds; omega, countBounds.1,
    ⟨terminal, store_declarations_prefix loaded decls suffixRead, ?_⟩,
    store_declarations_table loaded decls accepted.2.1 capacity (by omega),
    (store_declarations_io loaded decls).trans io, fun _ _ _ read => store_declarations_preserves loaded decls (preserved _ _ _ read)⟩
  have stored := store_declarations_preserves loaded decls (raw_load loaded 3 terminal _ nilRead)
  change bytecodeMemory (storeDeclarations loaded decls).1 3 terminal.n = some #[1, 1, 1]
  simp only [bytecodeMemory, stored]

end
end
end Ix.Ixby.AiurBackend.Objects.CodeHeaders
