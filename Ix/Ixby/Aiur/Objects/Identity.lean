module
public import Ix.Ixby.Aiur.Objects.Parser
import all Ix.Aiur.Goldilocks

/-! Compiled ten-limb constructor-identity reader contracts.

The production compiler inlines ten u32 readers into `is_read_id`. These
proofs cover the emitted operations with their actual register offsets and
Call semantics, including the complete 256-bit digest and u32 member/tag.
Executable structural certificates bind the proved shape to a compiled body;
they are not a general source-compiler correctness theorem.

Input byte ranges are explicit in `BytePrefix`. `Objects/Admission.lean`
establishes that premise for checked advice loading under explicit bounds.
Comparison and bounded duplicate traversal are proved
in `Objects/Equality.lean` and `Objects/Unique.lean`; `Objects/Declarations.lean`
composes the complete bounded declaration parser. `Objects/ProgramPrefix.lean`
derives constructor capacity from the actual header check and composes that
parser call. Whole-program binding and compiler/hash/gadget/AIR links remain open.
This module does not change the interpreter or the production proof path.
-/

namespace Ix.Ixby.AiurBackend.Objects.Identity

-- Diagnostic structural equality stays private to this certificate.
deriving instance DecidableEq for Aiur.Bytecode.Op

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval
open Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Memory

/-- Relate actual indexed operation execution to sequential list composition. -/
theorem run_ops_list (t : Bytecode.Toplevel) (fuel : Nat) (ops : Array Aiur.Bytecode.Op)
    (st : EvalState) (i : Nat) :
    runOps t fuel ops st i =
      (ops.toList.drop i).foldlM (fun state op => Aiur.Bytecode.Eval.evalOp t fuel op state) st := by
  rw [runOps]
  split
  · rename_i bound
    rw [List.drop_eq_getElem_cons (by simpa using bound)]
    simp only [List.foldlM_cons, Array.getElem_toList]
    cases executed : Aiur.Bytecode.Eval.evalOp t fuel ops[i] st with
    | error error => rfl
    | ok next => exact run_ops_list t fuel ops next (i + 1)
  · rename_i bound
    rw [List.drop_eq_nil_of_le (show ops.toList.length ≤ i from Nat.le_of_not_gt bound)]
    rfl
termination_by ops.size - i

/-- Appending bytecode operations composes success and propagates all errors. -/
theorem run_ops_append (t : Bytecode.Toplevel) (fuel : Nat) (left right : Array Aiur.Bytecode.Op)
    (st : EvalState) :
    runOps t fuel (left ++ right) st 0 =
      (runOps t fuel left st 0).bind (fun next => runOps t fuel right next 0) := by
  simp only [run_ops_list, List.drop_zero, Array.toList_append, List.foldlM_append]
  rfl

/-- Inlined u32 operations with an arbitrary input register and fresh-register
base. One word appends exactly seventeen registers. -/
def inlineWordOps (reader start pointer : Nat) : Array Aiur.Bytecode.Op :=
  #[.call reader #[pointer] 2 false, .call reader #[start + 1] 2 false,
    .call reader #[start + 3] 2 false, .call reader #[start + 5] 2 false,
    .const 256, .mul (start + 8) (start + 2), .const 65536, .mul (start + 10) (start + 4),
    .const 16777216, .mul (start + 12) (start + 6), .add (start + 11) (start + 13),
    .add (start + 9) (start + 14), .add start (start + 15)]

/-- Complete intermediate registers in the compiler's actual evaluation order. -/
def wordRegisters (p1 p2 p3 p4 a b c d : G) : Array G :=
  #[a, p1, b, p2, c, p3, d, p4, 256, 256 * b, 65536, 65536 * c,
    16777216, 16777216 * d, 65536 * c + 16777216 * d,
    256 * b + (65536 * c + 16777216 * d), packedWord a b c d]

/-- Raw evaluator behavior, including non-byte payloads. Range safety is
established separately for genuine bytes, not inferred from a successful read. -/
theorem inline_word_eval (t : Bytecode.Toplevel) (fuel selector reader idx : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true)
    (p0 p1 p2 p3 p4 a b c d : G) (argument : st.map[idx]? = some p0)
    (ha : memLoad st 3 p0.n = .ok #[0, a, p1])
    (hb : memLoad st 3 p1.n = .ok #[0, b, p2])
    (hc : memLoad st 3 p2.n = .ok #[0, c, p3])
    (hd : memLoad st 3 p3.n = .ok #[0, d, p4]) :
    runOps t (fuel + 1) (inlineWordOps reader st.map.size idx) st 0 =
      .ok { st with map := st.map ++ wordRegisters p1 p2 p3 p4 a b c d } := by
  obtain ⟨input, body⟩ := byte_reader_checked f selector checked
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  simp +arith [inlineWordOps, wordRegisters, packedWord, runOps, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
    Bind.bind, Except.bind, Pure.pure, Except.pure, bound, found, input, body,
    evalBlock, byteReaderBody, evalCtrl, evalMatchArm,
    ha, hb, hc, hd, argument, appendMap, setIoBuffer, pushMap,
    Array.getElem?_append, Array.append_assoc]

/-- Split a consumed prefix without imposing an end-of-stream condition. -/
theorem byte_prefix_split {memory : RawMemory} {pointer finish : G}
    {xs ys : List UInt8} (read : BytePrefix memory pointer (xs ++ ys) finish) :
    ∃ middle, BytePrefix memory pointer xs middle ∧ BytePrefix memory middle ys finish := by
  induction xs generalizing pointer with
  | nil => exact ⟨pointer, .nil _, read⟩
  | cons byte bytes ih =>
    obtain ⟨tail, loaded, rest⟩ := byte_prefix_head read
    obtain ⟨middle, first, last⟩ := ih rest
    exact ⟨middle, .cons loaded first, last⟩

/-- Four genuine bytes, in wire order. This carries ranges by construction. -/
structure WordBytes where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8

def WordBytes.bytes (w : WordBytes) : List UInt8 := [w.a, w.b, w.c, w.d]
def WordBytes.field (w : WordBytes) : G :=
  packedWord (G.ofUInt8 w.a) (G.ofUInt8 w.b) (G.ofUInt8 w.c) (G.ofUInt8 w.d)

theorem word_field_bound (w : WordBytes) : w.field.n < 2 ^ 32 :=
  (packed_word_exact _ _ _ _ (by simpa using w.a.toNat_lt) (by simpa using w.b.toNat_lt)
    (by simpa using w.c.toNat_lt) (by simpa using w.d.toNat_lt)).2

theorem word_field_codec (w : WordBytes) : w.field.n = Ix.Ixby.natOfBytesLE w.bytes.toArray :=
  packed_word_codec w.a w.b w.c w.d

private theorem prefix_load (st : EvalState) {pointer finish : G}
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

/-- Range-safe inlined word read, preserving every preexisting register and
all memory/I/O, with exact positions for the word and suffix. -/
theorem inline_word_prefix (t : Bytecode.Toplevel) (fuel selector reader idx : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true) (pointer finish : G) (w : WordBytes)
    (argument : st.map[idx]? = some pointer)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer w.bytes finish) :
    ∃ registers : Array G, registers.size = 17 ∧ registers[7]? = some finish ∧
      registers[16]? = some w.field ∧
      runOps t (fuel + 1) (inlineWordOps reader st.map.size idx) st 0 =
        .ok { st with map := st.map ++ registers } := by
  obtain ⟨p1, ha, rest⟩ := prefix_load st bytesRead
  obtain ⟨p2, hb, rest⟩ := prefix_load st rest
  obtain ⟨p3, hc, rest⟩ := prefix_load st rest
  obtain ⟨p4, hd, rest⟩ := prefix_load st rest
  cases rest
  exact ⟨wordRegisters p1 p2 p3 finish _ _ _ _, rfl, rfl, rfl,
    inline_word_eval t fuel selector reader idx st f function checked _ _ _ _ _ _ _ _ _
      argument ha hb hc hd⟩

/-- Sequential inlined readers, matching the compiler's seventeen-register stride. -/
def wordsOps (reader : Nat) : Nat → Nat → Nat → Array Aiur.Bytecode.Op
  | _, _, 0 => #[]
  | start, pointer, count + 1 =>
    inlineWordOps reader start pointer ++ wordsOps reader (start + 17) (start + 7) count

def wordIndices : Nat → Nat → Array Nat
  | _, 0 => #[]
  | start, count + 1 => #[start + 16] ++ wordIndices (start + 17) count

def finishIndex : Nat → Nat → Nat → Nat
  | _, pointer, 0 => pointer
  | start, _, count + 1 => finishIndex (start + 17) (start + 7) count

theorem word_indices_bound (start count : Nat) :
    ∀ i ∈ wordIndices start count, start ≤ i ∧ i < start + 17 * count := by
  induction count generalizing start with
  | zero => simp [wordIndices]
  | succ count ih =>
    intro i member
    simp only [wordIndices, Array.mem_append, Array.mem_singleton] at member
    rcases member with head | tail
    · omega
    · have := ih (start + 17) i tail
      omega

theorem read_idxs_single (st : EvalState) (idx : Nat) (value : G)
    (found : st.map[idx]? = some value) : readIdxs st #[idx] = .ok #[value] := by
  simp [readIdxs, readIdx, found, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem read_idxs_acc (st : EvalState) (indices : List Nat) (acc : Array G) :
    indices.foldlM (fun acc idx => do pure (acc.push (← readIdx st idx))) acc =
      (indices.foldlM (fun (acc : Array G) idx => do pure (acc.push (← readIdx st idx))) #[]).bind
        (fun out => .ok (acc ++ out)) := by
  induction indices generalizing acc with
  | nil => simp [List.foldlM_nil, Except.bind, Pure.pure, Except.pure]
  | cons idx indices ih =>
    simp only [List.foldlM_cons]
    cases found : readIdx st idx with
    | error error => rfl
    | ok value =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Array.push_empty] at ih ⊢
      rw [ih (acc.push value), ih #[value]]
      split <;> simp_all only [← Array.append_assoc, Array.append_singleton]

theorem read_idxs_append (st : EvalState) (left right : Array Nat) :
    readIdxs st (left ++ right) =
      (readIdxs st left).bind (fun a => (readIdxs st right).bind (fun b => .ok (a ++ b))) := by
  simp only [readIdxs, ← Array.foldlM_toList, Array.toList_append, List.foldlM_append]
  cases left.toList.foldlM (fun (acc : Array G) idx => do pure (acc.push (← readIdx st idx))) #[] with
  | error error => rfl
  | ok values => exact read_idxs_acc st right.toList values

/-- Compositional contract for any number of inlined word readers. The full
state is retained except for the explicitly appended temporary registers. -/
theorem words_prefix (t : Bytecode.Toplevel) (fuel selector reader : Nat)
    (f : Aiur.Bytecode.Function) (function : t.functions[reader]? = some f)
    (checked : checkByteReader f selector = true) (words : List WordBytes)
    (st : EvalState) (idx : Nat) (pointer finish : G)
    (argument : st.map[idx]? = some pointer)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (words.flatMap WordBytes.bytes) finish) :
    ∃ registers : Array G,
      runOps t (fuel + 1) (wordsOps reader st.map.size idx words.length) st 0 =
        .ok { st with map := st.map ++ registers } ∧
      registers.size = 17 * words.length ∧
      readIdxs { st with map := st.map ++ registers } (wordIndices st.map.size words.length) =
        .ok (words.map WordBytes.field).toArray ∧
      (st.map ++ registers)[finishIndex st.map.size idx words.length]? = some finish := by
  induction words generalizing st idx pointer with
  | nil =>
    cases bytesRead
    exact ⟨#[], by simp [wordsOps, runOps], rfl,
      by simp [wordIndices, readIdxs, Pure.pure, Except.pure], by simpa [finishIndex] using argument⟩
  | cons word words ih =>
    obtain ⟨middle, first, rest⟩ := byte_prefix_split bytesRead
    obtain ⟨head, sizeHead, tailHead, valueHead, firstRun⟩ :=
      inline_word_prefix t fuel selector reader idx st f function checked pointer middle word argument first
    let next : EvalState := { st with map := st.map ++ head }
    have nextSize : next.map.size = st.map.size + 17 := by simp [next, sizeHead]
    have nextArg : next.map[st.map.size + 7]? = some middle := by
      simpa +arith [next, Array.getElem?_append] using tailHead
    obtain ⟨tail, restRun, sizeTail, valuesTail, finishTail⟩ :=
      ih next (st.map.size + 7) middle nextArg rest
    refine ⟨head ++ tail, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, wordsOps, run_ops_append, firstRun, Except.bind]
      simpa only [next, nextSize, Array.append_assoc] using restRun
    · simp +arith [sizeHead, sizeTail, Nat.mul_add]
    · have kept : (st.map ++ (head ++ tail))[st.map.size + 16]? = some word.field := by
        simpa +arith [Array.getElem?_append, sizeHead] using valueHead
      rw [List.length_cons, wordIndices, read_idxs_append,
        read_idxs_single _ _ _ kept]
      simp only [Except.bind]
      have tailRead : readIdxs { st with map := st.map ++ (head ++ tail) }
          (wordIndices (st.map.size + 17) words.length) = .ok (words.map WordBytes.field).toArray := by
        simpa only [next, nextSize, Array.append_assoc] using valuesTail
      rw [tailRead]
      simp
    · simpa only [List.length_cons, finishIndex, next, nextSize, Array.append_assoc] using finishTail

/-- Exact 130-operation body emitted for the ten-limb identity reader. -/
def idReaderBody (reader selector : Nat) : Aiur.Bytecode.Block := {
  ops := wordsOps reader 1 0 10,
  ctrl := .return selector (wordIndices 1 10 ++ #[finishIndex 1 0 10]) }

/-- Structural certificate: all operations, callee indices, arity, selector,
and eleven output registers are checked. Nonsemantic layout data is ignored. -/
def checkIdReader (f : Aiur.Bytecode.Function) (reader selector : Nat) : Bool :=
  match f.body.ctrl with
  | .return found outs => decide (f.layout.inputSize = 1 ∧
      f.body.ops = (idReaderBody reader selector).ops ∧ found = selector ∧
      outs = wordIndices 1 10 ++ #[finishIndex 1 0 10])
  | _ => false

theorem id_reader_checked (f : Aiur.Bytecode.Function) (reader selector : Nat)
    (checked : checkIdReader f reader selector = true) :
    f.layout.inputSize = 1 ∧ f.body = idReaderBody reader selector := by
  unfold checkIdReader at checked
  split at checked
  · rename_i found outs ctrl
    obtain ⟨input, ops, foundEq, outsEq⟩ := of_decide_eq_true checked
    refine ⟨input, ?_⟩
    cases f with
    | mk b layout entry constrained => cases b; simp_all [idReaderBody]
  · simp at checked

/-- The checked body consumes exactly ten words and returns the unmodified,
full-field suffix pointer. No extra load or Nil is required at that endpoint. -/
theorem checked_id_reader_prefix (t : Bytecode.Toplevel)
    (fuel byteSelector idSelector reader : Nat) (st : EvalState)
    (byteFn idFn : Aiur.Bytecode.Function) (function : t.functions[reader]? = some byteFn)
    (byteChecked : checkByteReader byteFn byteSelector = true)
    (idChecked : checkIdReader idFn reader idSelector = true)
    (words : List WordBytes) (length : words.length = 10) (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (words.flatMap WordBytes.bytes) finish) :
    ∃ after, evalBlock t (fuel + 1) idFn.body { st with map := #[pointer] } =
      .error (.earlyReturn ((words.map WordBytes.field).toArray ++ #[finish]) after) ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨registers, executed, _, values, final⟩ :=
    words_prefix t fuel byteSelector reader byteFn function byteChecked words
      { st with map := #[pointer] } 0 pointer finish rfl bytesRead
  simp only [length] at executed values final
  change runOps t (fuel + 1) (wordsOps reader 1 0 10) { st with map := #[pointer] } 0 =
    .ok { st with map := #[pointer] ++ registers } at executed
  change readIdxs { st with map := #[pointer] ++ registers } (wordIndices 1 10) =
    .ok (words.map WordBytes.field).toArray at values
  change (#[pointer] ++ registers)[finishIndex 1 0 10]? = some finish at final
  rw [(id_reader_checked idFn reader idSelector idChecked).2]
  simp only [idReaderBody, evalBlock, executed, evalCtrl, read_idxs_append, values,
    read_idxs_single { st with map := #[pointer] ++ registers } _ _ final, Except.bind]
  exact ⟨_, rfl, rfl, rfl⟩

theorem word_bytes_length (words : List WordBytes) :
    (words.flatMap WordBytes.bytes).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word words ih => simp +arith [WordBytes.bytes, ih, Nat.mul_add]

/-- Grouping into words excludes no byte sequence of the required length. -/
theorem group_word_bytes (count : Nat) (bytes : List UInt8) (length : bytes.length = 4 * count) :
    ∃ words : List WordBytes, words.length = count ∧ words.flatMap WordBytes.bytes = bytes := by
  induction count generalizing bytes with
  | zero =>
    have empty : bytes = [] := by simpa using length
    subst bytes
    exact ⟨[], rfl, rfl⟩
  | succ count ih =>
    match bytes with
    | [] | [_] | [_, _] | [_, _, _] => simp_all +arith
    | a :: b :: c :: d :: rest =>
      obtain ⟨words, countEq, bytesEq⟩ := ih rest (by simpa +arith [Nat.mul_add] using length)
      refine ⟨⟨a, b, c, d⟩ :: words, by simp [countEq], ?_⟩
      simp [WordBytes.bytes, bytesEq]

theorem word_bytes_prepend (word : WordBytes) (rest : List UInt8) :
    Ix.Ixby.natOfBytesLE (word.bytes ++ rest).toArray =
      word.field.n + 2 ^ 32 * Ix.Ixby.natOfBytesLE rest.toArray := by
  rw [word_field_codec]
  simp [Ix.Ixby.natOfBytesLE, WordBytes.bytes]
  omega

open Ix.Ixby.AiurBackend.Objects.Table

/-- Packing little-endian u32 limbs agrees with the existing byte codec,
using natural arithmetic without digest truncation or field reduction. -/
theorem words_digest_exact (words : List WordBytes) :
    packLimbs (words.map (fun word => word.field.n)) =
      Ix.Ixby.natOfBytesLE (words.flatMap WordBytes.bytes).toArray := by
  induction words with
  | nil => simp [packLimbs, Ix.Ixby.natOfBytesLE]
  | cons word words ih =>
    simp only [List.map_cons, packLimbs, List.flatMap_cons, word_bytes_prepend, ih, limbBase]

set_option maxHeartbeats 1000000 in
/-- The ten range-safe output limbs decode to the complete semantic name.
The digest bound is derived from the eight u32 bounds, not assumed. -/
theorem decode_id_words (a b c d e f g h member tag : WordBytes) :
    ∃ id : Ix.Ixby.CtorId,
      decodeId [a.field, b.field, c.field, d.field, e.field, f.field, g.field, h.field,
        member.field, tag.field] = some id ∧
      id.block.val = Ix.Ixby.natOfBytesLE ([a, b, c, d, e, f, g, h].flatMap WordBytes.bytes).toArray ∧
      id.member = Ix.Ixby.natOfBytesLE member.bytes.toArray ∧
      id.tag = Ix.Ixby.natOfBytesLE tag.bytes.toArray := by
  have digestBound : packLimbs [a.field.n, b.field.n, c.field.n, d.field.n, e.field.n, f.field.n,
      g.field.n, h.field.n] < 2 ^ 256 := by
    have bound := pack_limbs_bound (limbs := [a, b, c, d, e, f, g, h].map (fun word => word.field.n)) (by
        intro limb mem
        obtain ⟨word, _, rfl⟩ := List.mem_map.mp mem
        exact word_field_bound word)
    simpa [limbBase] using bound
  refine ⟨⟨⟨_, digestBound⟩, member.field.n, tag.field.n⟩, ?_, ?_,
    word_field_codec member, word_field_codec tag⟩
  · have ranges (word : WordBytes) : word.field.n < 4294967296 := word_field_bound word
    simp [decodeId, limbBase, ranges, digestBound]
  · exact words_digest_exact [a, b, c, d, e, f, g, h]

/-- End-to-end identity-reader component: actual bytecode execution, checked
semantic decoding, exact digest/member/tag, and memory/I/O preservation.
This is not yet a theorem about admission or the whole program decoder. -/
theorem checked_id_reader_sound (t : Bytecode.Toplevel)
    (fuel byteSelector idSelector reader : Nat) (st : EvalState)
    (byteFn idFn : Aiur.Bytecode.Function) (function : t.functions[reader]? = some byteFn)
    (byteChecked : checkByteReader byteFn byteSelector = true)
    (idChecked : checkIdReader idFn reader idSelector = true)
    (a b c d e f g h member tag : WordBytes) (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer
      ([a, b, c, d, e, f, g, h, member, tag].flatMap WordBytes.bytes) finish) :
    ∃ (id : Ix.Ixby.CtorId) (after : EvalState),
      evalBlock t (fuel + 1) idFn.body { st with map := #[pointer] } =
        .error (.earlyReturn #[a.field, b.field, c.field, d.field, e.field, f.field,
          g.field, h.field, member.field, tag.field, finish] after) ∧
      decodeId [a.field, b.field, c.field, d.field, e.field, f.field, g.field, h.field,
        member.field, tag.field] = some id ∧
      id.block.val = Ix.Ixby.natOfBytesLE ([a, b, c, d, e, f, g, h].flatMap WordBytes.bytes).toArray ∧
      id.member = Ix.Ixby.natOfBytesLE member.bytes.toArray ∧
      id.tag = Ix.Ixby.natOfBytesLE tag.bytes.toArray ∧
      after.memory = st.memory ∧ after.ioBuffer = st.ioBuffer := by
  obtain ⟨after, executed, memory, io⟩ := checked_id_reader_prefix t fuel byteSelector idSelector reader st
    byteFn idFn function byteChecked idChecked [a, b, c, d, e, f, g, h, member, tag] rfl pointer finish bytesRead
  obtain ⟨id, decoded, block, memberEq, tagEq⟩ := decode_id_words a b c d e f g h member tag
  exact ⟨id, after, executed, decoded, block, memberEq, tagEq, memory, io⟩

/-- The actual Call boundary checks arity/output size and restores the caller's
registers. Both constraint flags have the same Lean evaluation semantics;
this does not assert that an unconstrained call supplies an AIR relation. -/
theorem checked_id_reader_call (t : Bytecode.Toplevel)
    (fuel byteSelector idSelector reader idReader idx : Nat) (st : EvalState)
    (byteFn idFn : Aiur.Bytecode.Function) (byteFunction : t.functions[reader]? = some byteFn)
    (idFunction : t.functions[idReader]? = some idFn)
    (byteChecked : checkByteReader byteFn byteSelector = true)
    (idChecked : checkIdReader idFn reader idSelector = true)
    (words : List WordBytes) (length : words.length = 10) (pointer finish : G)
    (argument : st.map[idx]? = some pointer)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (words.flatMap WordBytes.bytes) finish)
    (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 2) (.call idReader #[idx] 11 unconstrained) st =
      .ok { st with map := st.map ++ ((words.map WordBytes.field).toArray ++ #[finish]) } := by
  obtain ⟨after, executed, memory, io⟩ := checked_id_reader_prefix t fuel byteSelector idSelector reader st
    byteFn idFn byteFunction byteChecked idChecked words length pointer finish bytesRead
  have input := (id_reader_checked idFn reader idSelector idChecked).1
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp idFunction
  simp [Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx, argument, Bind.bind, Except.bind,
    Pure.pure, Except.pure, bound, found, input, executed, memory, io, length,
    appendMap, setIoBuffer]

end
end
end Ix.Ixby.AiurBackend.Objects.Identity
