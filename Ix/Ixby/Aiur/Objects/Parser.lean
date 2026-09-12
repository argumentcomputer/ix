module
public import Ix.Ixby.Aiur.Objects.Table
import all Ix.Aiur.Goldilocks

/-! Byte-stream and compiled-parser proof components.

Executable shape checks connect the proved bodies to actual bytecode without
assuming a general compiler-correctness theorem. The scalar reader contracts
and the zero-constructor parser path are proved here. `Objects/Identity.lean`
composes the inlined readers through the ten-limb identity parser.
`Objects/Equality.lean` and `Objects/Unique.lean` prove comparison and bounded
duplicate traversal. `Objects/Declarations.lean` composes the complete bounded
recursive parser. `Objects/Admission.lean` establishes genuine loaded bytes and
preserves table capacity under explicit metadata/address and storage bounds.
`Objects/ProgramPrefix.lean` certifies the actual header/count prefix through
the declaration call, handing its exact state to the remaining continuation.
Whole-program admission and commitment/compiler/gadget/AIR links remain open.

These are diagnostic proof components, not a production verification path.
-/

namespace Ix.Ixby.AiurBackend.Objects.Parser

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval
open Objects.Memory Objects.Refinement Objects.Store

-- Keep structural operation equality private to these diagnostic certificates.
deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

/-- An exact, range-safe byte prefix at field-valued pointers. The endpoint
is deliberately arbitrary: a parser must leave the following artifact bytes
unconsumed, not require a Nil after every declaration or u32. -/
inductive BytePrefix (memory : RawMemory) : G → List UInt8 → G → Prop where
  | nil (pointer : G) : BytePrefix memory pointer [] pointer
  | cons {pointer tail finish : G} {byte : UInt8} {bytes : List UInt8}
      (loaded : memory 3 pointer.n = some #[0, G.ofUInt8 byte, tail])
      (rest : BytePrefix memory tail bytes finish) :
      BytePrefix memory pointer (byte :: bytes) finish

theorem byte_prefix_append {memory : RawMemory} {pointer middle finish : G}
    {xs ys : List UInt8} (left : BytePrefix memory pointer xs middle)
    (right : BytePrefix memory middle ys finish) :
    BytePrefix memory pointer (xs ++ ys) finish := by
  induction left with
  | nil => exact right
  | cons loaded _ ih => exact .cons loaded (ih right)

theorem byte_prefix_store (st : EvalState) (stored : Array G) {pointer finish : G}
    {bytes : List UInt8} (bytesRead : BytePrefix (bytecodeMemory st) pointer bytes finish) :
    BytePrefix (bytecodeMemory (memStore st stored).1) pointer bytes finish := by
  induction bytesRead with
  | nil => exact .nil _
  | @cons pointer tail finish byte bytes loaded rest ih =>
    apply BytePrefix.cons (rest := ih)
    unfold bytecodeMemory at loaded ⊢
    cases actual : memLoad st 3 pointer.n with
    | error error => simp [actual] at loaded
    | ok flat =>
      simp only [actual, Option.some.injEq] at loaded
      subst flat
      simp [mem_store_preserves st stored actual]

/-- Actual allocation extends a byte prefix. The returned address must fit
Goldilocks before it is exposed as a field; content reuse is permitted. -/
theorem stored_byte_prefix (st : EvalState) (byte : UInt8) (tail finish : G)
    (bytes : List UInt8) (bytesRead : BytePrefix (bytecodeMemory st) tail bytes finish)
    (bounded : (memStore st #[0, G.ofUInt8 byte, tail]).2 < goldilocksModulus) :
    BytePrefix (bytecodeMemory (memStore st #[0, G.ofUInt8 byte, tail]).1)
      (.ofNat (memStore st #[0, G.ofUInt8 byte, tail]).2) (byte :: bytes) finish := by
  apply BytePrefix.cons (rest := byte_prefix_store st _ bytesRead)
  have loaded := stored_field_pointer st #[0, G.ofUInt8 byte, tail] bounded
  change memLoad (memStore st #[0, G.ofUInt8 byte, tail]).1 3
    (G.ofNat (memStore st #[0, G.ofUInt8 byte, tail]).2).n = .ok #[0, G.ofUInt8 byte, tail] at loaded
  simp [bytecodeMemory, loaded]

theorem byte_prefix_head {memory : RawMemory} {pointer finish : G}
    {byte : UInt8} {bytes : List UInt8} (bytesRead : BytePrefix memory pointer (byte :: bytes) finish) :
    ∃ tail, memory 3 pointer.n = some #[0, G.ofUInt8 byte, tail] ∧
      BytePrefix memory tail bytes finish := by
  cases bytesRead with
  | cons loaded rest => exact ⟨_, loaded, rest⟩

@[simp] theorem byte_field_exact (byte : UInt8) : (G.ofUInt8 byte).n = byte.toNat := by
  simp [G.ofUInt8, G.n]

/-- The post-lowering `ib_byte` body; selector bookkeeping is parametric. -/
def byteReaderBody (selector : Nat) : Aiur.Bytecode.Block :=
  ⟨#[.load 3 0], .match 1 #[(0, ⟨#[], .return selector #[2, 3]⟩)] none⟩

@[simp] theorem mem_load_map (st : EvalState) (map : Array G) (width pointer : Nat) :
    memLoad { st with map } width pointer = memLoad st width pointer := rfl

/-- Exact raw behavior, including the function-return sentinel. This lemma
intentionally allows any payload field: the reader itself does not range-check. -/
theorem byte_reader_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (st : EvalState)
    (pointer byte tail : G) (loaded : memLoad st 3 pointer.n = .ok #[0, byte, tail]) :
    evalBlock t fuel (byteReaderBody selector) { st with map := #[pointer] } =
      .error (.earlyReturn #[byte, tail] { st with map := #[pointer, 0, byte, tail] }) := by
  simp [byteReaderBody, evalBlock, runOps, Aiur.Bytecode.Eval.evalOp, readIdx, appendMap,
    evalCtrl, evalMatchArm, readIdxs, loaded, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Executable structural certificate for an actual compiled function.
This uses decidable equality, not an assumed lawful bytecode `BEq`. Layout
metadata ignored by the evaluator is not part of the semantic certificate. -/
def checkByteReader (f : Aiur.Bytecode.Function) (selector : Nat) : Bool :=
  match f.body.ctrl with
  | .match scrut cases none =>
    match cases.toList with
    | [(tag, branch)] =>
      match branch.ctrl with
      | .return found outs => decide (f.layout.inputSize = 1 ∧ f.body.ops = #[.load 3 0] ∧
          scrut = 1 ∧ tag = 0 ∧ branch.ops = #[] ∧ found = selector ∧ outs = #[2, 3])
      | _ => false
    | _ => false
  | _ => false

theorem byte_reader_checked (f : Aiur.Bytecode.Function) (selector : Nat)
    (checked : checkByteReader f selector = true) :
    f.layout.inputSize = 1 ∧ f.body = byteReaderBody selector := by
  unfold checkByteReader at checked
  split at checked
  · rename_i scrut cases ctrl
    split at checked
    · rename_i tag branch arms
      split at checked
      · rename_i found outs ret
        obtain ⟨input, ops, scrutEq, tagEq, empty, foundEq, outsEq⟩ := of_decide_eq_true checked
        have branches : cases = #[(tag, branch)] := Array.toList_inj.mp arms
        have shape : branch = ⟨#[], .return selector #[2, 3]⟩ := by
          cases branch
          simp_all
        refine ⟨input, ?_⟩
        cases f with
        | mk b layout entry constrained => cases b; simp_all [byteReaderBody]
      · simp at checked
    · simp at checked
  · simp at checked

/-- Actual Call semantics, with argument/output checks and register restoration.
The callee index is looked up in the same toplevel being evaluated. -/
theorem byte_reader_call (t : Bytecode.Toplevel) (fuel selector reader idx : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true)
    (pointer byte tail : G) (argument : st.map[idx]? = some pointer)
    (loaded : memLoad st 3 pointer.n = .ok #[0, byte, tail]) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call reader #[idx] 2 unconstrained) st =
      .ok { st with map := st.map ++ #[byte, tail] } := by
  obtain ⟨input, body⟩ := byte_reader_checked f selector checked
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  simp [Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx, argument, Bind.bind, Except.bind, Pure.pure, Except.pure,
    bound, found, input, body, byte_reader_eval t fuel selector st pointer byte tail loaded,
    appendMap, setIoBuffer]

/-- The exact association of the arithmetic emitted for `@ib_u32`. -/
def packedWord (a b c d : G) : G := a + (256 * b + (65536 * c + 16777216 * d))

/-- Standalone `ib_u32` after inlining `ib_word` and `b3_pack_w`. The same
arithmetic appears inlined in the declaration and identity readers. -/
def wordReaderBody (reader selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.call reader #[0] 2 false, .call reader #[2] 2 false,
    .call reader #[4] 2 false, .call reader #[6] 2 false,
    .const 256, .mul 9 3, .const 65536, .mul 11 5, .const 16777216, .mul 13 7,
    .add 12 14, .add 10 15, .add 1 16],
  ctrl := .return selector #[17, 8] }

theorem word_reader_eval (t : Bytecode.Toplevel) (fuel byteSelector wordSelector reader : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f byteSelector = true)
    (p0 p1 p2 p3 p4 a b c d : G)
    (ha : memLoad st 3 p0.n = .ok #[0, a, p1])
    (hb : memLoad st 3 p1.n = .ok #[0, b, p2])
    (hc : memLoad st 3 p2.n = .ok #[0, c, p3])
    (hd : memLoad st 3 p3.n = .ok #[0, d, p4]) :
    ∃ after, evalBlock t (fuel + 1) (wordReaderBody reader wordSelector) { st with map := #[p0] } =
      .error (.earlyReturn #[packedWord a b c d, p4] after) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨input, body⟩ := byte_reader_checked f byteSelector checked
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  simp [wordReaderBody, packedWord, evalBlock, runOps, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
    Bind.bind, Except.bind, Pure.pure, Except.pure, bound, found, input, body,
    byteReaderBody, ha, hb, hc, hd, appendMap, setIoBuffer, pushMap,
    evalCtrl, evalMatchArm]

private theorem mul_constant (weight : Nat) (byte : G) (bounded : byte.n < 256)
    (small : weight ≤ 16777216) :
    (G.ofNat weight * byte).n = weight * byte.n := by
  change (G.ofNat ((G.ofNat weight).n * byte.n)).n = _
  rw [field_of_nat_exact weight (by change weight < 18446744069414584321; omega)]
  apply field_of_nat_exact
  have := Nat.mul_le_mul small (Nat.le_of_lt bounded)
  change weight * byte.n < 18446744069414584321
  omega

private theorem add_bounded (a b : G) (bound : a.n + b.n < goldilocksModulus) :
    (a + b).n = a.n + b.n := field_of_nat_exact _ bound

/-- Four genuine bytes cannot wrap at any intermediate field multiplication
or addition, and their result retains all 32 bits. -/
theorem packed_word_exact (a b c d : G)
    (ha : a.n < 256) (hb : b.n < 256) (hc : c.n < 256) (hd : d.n < 256) :
    (packedWord a b c d).n = wordValue a b c d ∧ (packedWord a b c d).n < 2 ^ 32 := by
  have w1 : ((256 : G) * b).n = 256 * b.n := mul_constant 256 b hb (by decide)
  have w2 : ((65536 : G) * c).n = 65536 * c.n := mul_constant 65536 c hc (by decide)
  have w3 : ((16777216 : G) * d).n = 16777216 * d.n :=
    mul_constant 16777216 d hd (by decide)
  have s1 := add_bounded ((65536 : G) * c) (16777216 * d) (by
    rw [w2, w3]; change 65536 * c.n + 16777216 * d.n < 18446744069414584321; omega)
  have s2 := add_bounded ((256 : G) * b) (65536 * c + 16777216 * d) (by
    rw [w1, s1, w2, w3]
    change 256 * b.n + (65536 * c.n + 16777216 * d.n) < 18446744069414584321; omega)
  have s3 := add_bounded a (256 * b + (65536 * c + 16777216 * d)) (by
    rw [s2, w1, s1, w2, w3]
    change a.n + (256 * b.n + (65536 * c.n + 16777216 * d.n)) < 18446744069414584321; omega)
  simp only [packedWord, s3, s2, w1, s1, w2, w3, wordValue]
  omega

/-- Agreement with the existing codec's little-endian numeric interpretation;
this is not yet a theorem about the whole canonical program decoder. -/
theorem packed_word_codec (a b c d : UInt8) :
    (packedWord (G.ofUInt8 a) (G.ofUInt8 b) (G.ofUInt8 c) (G.ofUInt8 d)).n =
      Ix.Ixby.natOfBytesLE #[a, b, c, d] := by
  have exactWord := (packed_word_exact (G.ofUInt8 a) (G.ofUInt8 b) (G.ofUInt8 c) (G.ofUInt8 d)
    (by simpa using a.toNat_lt) (by simpa using b.toNat_lt)
    (by simpa using c.toNat_lt) (by simpa using d.toNat_lt)).1
  rw [exactWord]
  simp [wordValue, Ix.Ixby.natOfBytesLE]
  omega

/-- A successful actual byte range-check instruction establishes both byte
bounds without changing the state. The AIR lookup argument is separate. -/
theorem range_check_success (t : Bytecode.Toplevel) (fuel left right : Nat)
    (before after : EvalState)
    (executed : Aiur.Bytecode.Eval.evalOp t fuel (.u8RangeCheck left right) before = .ok after) :
    ∃ a b, readIdx before left = .ok a ∧ readIdx before right = .ok b ∧
      a.n < 256 ∧ b.n < 256 ∧ after = before := by
  cases first : readIdx before left with
  | error error => simp [Aiur.Bytecode.Eval.evalOp, first, Bind.bind, Except.bind] at executed
  | ok a =>
    cases second : readIdx before right with
    | error error => simp [Aiur.Bytecode.Eval.evalOp, first, second, Bind.bind, Except.bind] at executed
    | ok b =>
      simp only [Aiur.Bytecode.Eval.evalOp, first, second, Bind.bind, Except.bind] at executed
      split at executed
      · rename_i ranges
        have bounds : a.n < 256 ∧ b.n < 256 := by
          simpa [Bool.and_eq_true, UInt64.lt_iff_toNat_lt] using ranges
        exact ⟨a, b, rfl, rfl, bounds.1, bounds.2, (Except.ok.inj executed).symm⟩
      · simp at executed

def checkWordReader (f : Aiur.Bytecode.Function) (reader selector : Nat) : Bool :=
  match f.body.ctrl with
  | .return found outs => decide (f.layout.inputSize = 1 ∧
      f.body.ops = (wordReaderBody reader selector).ops ∧ found = selector ∧ outs = #[17, 8])
  | _ => false

theorem word_reader_checked (f : Aiur.Bytecode.Function) (reader selector : Nat)
    (checked : checkWordReader f reader selector = true) :
    f.layout.inputSize = 1 ∧ f.body = wordReaderBody reader selector := by
  unfold checkWordReader at checked
  split at checked
  · rename_i found outs ctrl
    obtain ⟨input, ops, foundEq, outsEq⟩ := of_decide_eq_true checked
    refine ⟨input, ?_⟩
    cases f with
    | mk b layout entry constrained => cases b; simp_all [wordReaderBody]
  · simp at checked

private theorem byte_prefix_load (st : EvalState) {pointer finish : G}
    {byte : UInt8} {bytes : List UInt8}
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (byte :: bytes) finish) :
    ∃ tail, memLoad st 3 pointer.n = .ok #[0, G.ofUInt8 byte, tail] ∧
      BytePrefix (bytecodeMemory st) tail bytes finish := by
  obtain ⟨tail, loaded, rest⟩ := byte_prefix_head bytesRead
  refine ⟨tail, ?_, rest⟩
  unfold bytecodeMemory at loaded
  cases actual : memLoad st 3 pointer.n with
  | error error => simp [actual] at loaded
  | ok flat => simpa [actual] using loaded

/-- A structurally checked bytecode u32 reader consumes exactly four certified
bytes and preserves the complete memory and I/O buffer. No end-of-stream or
fresh-allocation assumption is needed. -/
theorem checked_word_reader_prefix (t : Bytecode.Toplevel)
    (fuel byteSelector wordSelector reader : Nat) (st : EvalState) (byteFn wordFn : Aiur.Bytecode.Function)
    (function : t.functions[reader]? = some byteFn)
    (byteChecked : checkByteReader byteFn byteSelector = true)
    (wordChecked : checkWordReader wordFn reader wordSelector = true)
    (pointer finish : G) (a b c d : UInt8)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer [a, b, c, d] finish) :
    ∃ word after, evalBlock t (fuel + 1) wordFn.body { st with map := #[pointer] } =
      .error (.earlyReturn #[word, finish] after) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer ∧
      word.n = a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat ∧
      word.n < 2 ^ 32 := by
  obtain ⟨p1, ha, rest⟩ := byte_prefix_load st bytesRead
  obtain ⟨p2, hb, rest⟩ := byte_prefix_load st rest
  obtain ⟨p3, hc, rest⟩ := byte_prefix_load st rest
  obtain ⟨p4, hd, rest⟩ := byte_prefix_load st rest
  cases rest
  rw [(word_reader_checked wordFn reader wordSelector wordChecked).2]
  obtain ⟨after, executed, memory, io⟩ := word_reader_eval t fuel byteSelector wordSelector reader st
    byteFn function byteChecked pointer p1 p2 p3 finish _ _ _ _ ha hb hc hd
  refine ⟨_, after, executed, memory, io, ?_⟩
  have exactWord := packed_word_exact (G.ofUInt8 a) (G.ofUInt8 b) (G.ofUInt8 c) (G.ofUInt8 d)
    (by simpa using a.toNat_lt) (by simpa using b.toNat_lt)
    (by simpa using c.toNat_lt) (by simpa using d.toNat_lt)
  simpa [wordValue] using exactWord

open Ix.Ixby.AiurBackend.Objects.Table

/-- The zero-count branch emitted for `is_read_ctors`, including tag padding. -/
def emptyTableBranch (selector : Nat) : Aiur.Bytecode.Block := {
  ops := #[.const 1, .const 1, .store #[2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]],
  ctrl := .return selector #[4, 0] }

def emptyTableBody (selector : Nat) (otherwise : Option Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 1 #[(0, emptyTableBranch selector)] otherwise⟩

def tableNil : Array G := #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[simp] theorem mem_store_map (st : EvalState) (map flat : Array G) :
    memStore { st with map } flat = ({ (memStore st flat).1 with map }, (memStore st flat).2) := by
  unfold memStore
  dsimp only
  split <;> rfl

theorem empty_table_eval (t : Bytecode.Toplevel) (fuel selector : Nat)
    (otherwise : Option Aiur.Bytecode.Block) (st : EvalState) (pointer : G) :
    ∃ after, evalBlock t fuel (emptyTableBody selector otherwise) { st with map := #[pointer, 0] } =
      .error (.earlyReturn #[G.ofNat (memStore st tableNil).2, pointer] after) ∧
      after.memory = (memStore st tableNil).1.memory ∧ after.ioBuffer = st.ioBuffer := by
  have io : (memStore st tableNil).1.ioBuffer = st.ioBuffer := by
    unfold memStore
    dsimp only
    split <;> rfl
  simp [emptyTableBody, emptyTableBranch, tableNil, evalBlock, runOps,
    Aiur.Bytecode.Eval.evalOp, readIdx, readIdxs, pushMap, evalCtrl, evalMatchArm,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  simpa [tableNil] using io

theorem stored_empty_table (st : EvalState) :
    readTable (bytecodeMemory (memStore st tableNil).1) (memStore st tableNil).2 0 = some #[] := by
  have loaded := mem_store_load st tableNil
  change memLoad (memStore st tableNil).1 tableWidth (memStore st tableNil).2 = .ok tableNil at loaded
  have cell : declarationHeap (bytecodeMemory (memStore st tableNil).1) (memStore st tableNil).2 =
      some .nil := by
    unfold declarationHeap bytecodeMemory
    rw [loaded]
    rfl
  simp [readTable, readDeclarations, cell]

/-- Certificate for ONLY the zero-count parser path. The default/nonzero
branch is intentionally unconstrained and is not certified by this checker. -/
def checkEmptyTableParser (f : Aiur.Bytecode.Function) (selector : Nat) : Bool :=
  match f.body.ctrl with
  | .match scrut cases _ =>
    match cases.toList with
    | [(tag, branch)] =>
      match branch.ctrl with
      | .return found outs => decide (f.layout.inputSize = 2 ∧ f.body.ops = #[] ∧ scrut = 1 ∧
          tag = 0 ∧ branch.ops = (emptyTableBranch selector).ops ∧ found = selector ∧ outs = #[4, 0])
      | _ => false
    | _ => false
  | _ => false

theorem empty_parser_checked (f : Aiur.Bytecode.Function) (selector : Nat)
    (checked : checkEmptyTableParser f selector = true) :
    f.layout.inputSize = 2 ∧ ∃ otherwise, f.body = emptyTableBody selector otherwise := by
  unfold checkEmptyTableParser at checked
  split at checked
  · rename_i scrut cases otherwise ctrl
    split at checked
    · rename_i tag branch arms
      split at checked
      · rename_i found outs ret
        obtain ⟨input, ops, scrutEq, tagEq, branchOps, foundEq, outsEq⟩ := of_decide_eq_true checked
        have branches : cases = #[(tag, branch)] := Array.toList_inj.mp arms
        have shape : branch = emptyTableBranch selector := by
          cases branch
          simp_all [emptyTableBranch]
        refine ⟨input, otherwise, ?_⟩
        cases f with
        | mk b layout entry constrained => cases b; simp_all [emptyTableBody]
      · simp at checked
    · simp at checked
  · simp at checked

theorem bytecode_memory_congr (before after : EvalState) (equal : before.memory = after.memory) :
    bytecodeMemory before = bytecodeMemory after := by
  funext width pointer
  simp [bytecodeMemory, memLoad, equal]

/-- The checked zero-count parser establishes the concrete empty-table
relation at its actual field-valued output pointer. The input pointer is
returned unchanged, even if it is not a readable byte cell. -/
theorem checked_empty_parser_table (t : Bytecode.Toplevel) (fuel selector : Nat)
    (f : Aiur.Bytecode.Function) (checked : checkEmptyTableParser f selector = true)
    (st : EvalState) (pointer : G)
    (bounded : (memStore st tableNil).2 < goldilocksModulus) :
    ∃ after, evalBlock t fuel f.body { st with map := #[pointer, 0] } =
      .error (.earlyReturn #[G.ofNat (memStore st tableNil).2, pointer] after) ∧
      readTable (bytecodeMemory after) (G.ofNat (memStore st tableNil).2).n 0 = some #[] ∧
      bytecodeMemory after = bytecodeMemory (memStore st tableNil).1 ∧
      after.ioBuffer = st.ioBuffer := by
  obtain ⟨_, otherwise, shape⟩ := empty_parser_checked f selector checked
  rw [shape]
  obtain ⟨after, executed, memory, io⟩ := empty_table_eval t fuel selector otherwise st pointer
  have same := bytecode_memory_congr after (memStore st tableNil).1 memory
  refine ⟨after, executed, ?_, same, io⟩
  rw [same, field_of_nat_exact _ bounded]
  exact stored_empty_table st

/-- The induction step at the final Cons store: retain the recursively read
table in forward order and add a fresh semantic name. `Objects.Declarations`
establishes these premises through the actual bounded nonzero parser path. -/
theorem stored_declaration_table (st : EvalState) (flat : Array G)
    (width : flat.size = tableWidth) (declaration : Ix.Ixby.CtorDecl)
    (tail count : Nat) (table : Array Ix.Ixby.CtorDecl)
    (decoded : decodeDeclCell flat = some (.cons declaration tail))
    (read : readTable (bytecodeMemory st) tail count = some table)
    (fresh : declaration.id ∉ table.toList.map Ix.Ixby.CtorDecl.id)
    (capacity : count + 1 ≤ Ix.Ixby.AiurBackend.objectsProfile.limits.constructors) :
    readTable (bytecodeMemory (memStore st flat).1) (memStore st flat).2 (count + 1) =
      some (#[declaration] ++ table) := by
  unfold readTable at read
  split at read
  · simp at read
  · obtain ⟨decls, tailRead, read⟩ := Option.bind_eq_some_iff.mp read
    split at read
    · rename_i unique
      cases Option.some.inj read
      have nextRead := store_preserves_declarations st flat tailRead
      have loaded := mem_store_load st flat
      rw [width] at loaded
      have cell : declarationHeap (bytecodeMemory (memStore st flat).1) (memStore st flat).2 =
          some (.cons declaration tail) := by
        unfold declarationHeap bytecodeMemory
        rw [loaded]
        exact decoded
      have uniqueCons : ((declaration :: decls).map Ix.Ixby.CtorDecl.id).Nodup := by
        simpa using (show declaration.id ∉ decls.map Ix.Ixby.CtorDecl.id ∧
          (decls.map Ix.Ixby.CtorDecl.id).Nodup from ⟨by simpa using fresh, unique⟩)
      simp [readTable, readDeclarations, cell, nextRead, Nat.not_lt.mpr capacity]
      simpa using uniqueCons
    · simp at read

end
end
end Ix.Ixby.AiurBackend.Objects.Parser
