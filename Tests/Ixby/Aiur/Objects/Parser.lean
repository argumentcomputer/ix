module
import Ix.Ixby.Aiur.Objects.Parser
import Ix.Ixby.Aiur.Objects.Identity
import Ix.Ixby.Aiur.Objects.Unique
import Ix.Ixby.Aiur.Objects.Declarations
import Ix.Ixby.Aiur.Objects.Admission
import Ix.Ixby.Aiur.Objects.ProgramPrefix
import Ix.Ixby.Aiur.Objects.CodeHeaders
import Ix.Ixby.Aiur.Objects.Operands
import Ix.Ixby.Aiur.Objects
import Ix.Aiur.Compiler

/-! Structural certificate and bytecode-contract tests. Forged byte cells and
mutated functions are diagnostic fixtures, not production advice or new keys.
The zero-count certificate remains deliberately partial; the separate full
declaration and advice-loader certificates check both branches and their
required callees. Forged natural metadata tests document Lean evaluator
premises, not claims about native execution or the AIR's range constraints.
The program-prefix certificate binds only the first sixty operations; positive
suffix/control mutations deliberately test that limited boundary. Code-header
certificates extend the program count checks and cover function/block headers,
not instruction decoding or complete function-table admission. Separate full
scalar/leaf-operand certificates cover canonical fields, concrete value layouts,
frame guards and loader composition, not operand lists or whole instructions. -/

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

private abbrev Check := String × Bool

private def function (compiled : Aiur.CompiledToplevel) (name : Lean.Name) :
    Except String (Nat × Aiur.Bytecode.Function) := do
  let some index := compiled.getFuncIdx name | throw s!"missing function {name}"
  let some f := compiled.bytecode.functions[index]? | throw s!"missing index {index}"
  return (index, f)

private def snapshot (compiled : Aiur.CompiledToplevel) (name : Lean.Name)
    (args : Array Aiur.G) (initial : EvalState) (fuel := 8) :
    Except String (Array Aiur.G × EvalState) := do
  let (_, f) ← function compiled name
  unless f.layout.inputSize == args.size do throw "input arity"
  match evalBlock compiled.bytecode fuel f.body { initial with map := args } with
  | .ok (flat, state) | .error (.earlyReturn flat state) => return (flat, state)
  | .error error => throw (reprStr error)

private def initial : EvalState := {
  map := #[123, 456],
  ioBuffer := (default : Aiur.IOBuffer).extend 7 #[8, 9] #[10, 11, 12] }

private def memoryView (state : EvalState) : Array (Nat × Array (Array Aiur.G)) :=
  state.memory.pairs.map fun (width, bucket) => (width, bucket.pairs.map Prod.fst)
private def sameIo (before after : EvalState) : Bool :=
  before.ioBuffer.data.toList == after.ioBuffer.data.toList &&
    before.ioBuffer.map.toList == after.ioBuffer.map.toList
private def unchanged (before after : EvalState) : Bool :=
  memoryView before == memoryView after && sameIo before after
private def preservesReads (before after : EvalState) : Bool :=
  before.memory.pairs.all fun (width, bucket) =>
    bucket.pairs.toList.zipIdx.all fun ((flat, _), pointer) =>
      match memLoad after width pointer with | .ok found => found == flat | _ => false

private def storePrefix (st : EvalState) (bytes : Array Aiur.G) (tail : Aiur.G) : EvalState × Aiur.G :=
  bytes.foldr (fun byte state =>
    let next := memStore state.1 #[0, byte, state.2]
    (next.1, .ofNat next.2)) (st, tail)
private def storeStream (st : EvalState) (bytes : Array Aiur.G) : EvalState × Aiur.G :=
  let (st, pointer) := memStore st #[1, 1, 1]
  storePrefix st bytes (.ofNat pointer)

private def success (result : Except String (Array Aiur.G × EvalState))
    (out : Array Aiur.G) (before : EvalState) : Bool :=
  match result with | .ok (actual, after) => actual == out && unchanged before after | _ => false
private def failed (result : Except String (Array Aiur.G × EvalState))
    (error : BytecodeError) : Bool :=
  match result with | .error actual => actual == reprStr error | _ => false

private def certificateChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (reader, byte) ← function compiled `ib_byte
  let (_, word) ← function compiled `ib_u32
  let (_, identity) ← function compiled `is_read_id
  let (_, parser) ← function compiled `is_read_ctors
  let byteBody := byteReaderBody 0
  let wordBody := wordReaderBody reader 0
  let identityBody := idReaderBody reader 0
  let byteBranch : Aiur.Bytecode.Block := ⟨#[], .return 0 #[2, 3]⟩
  let nonzero : Aiur.Bytecode.Block := ⟨#[], .return 0 #[0]⟩
  let baseOnly := { parser with body := emptyTableBody 0 (some nonzero) }
  let mut checks : List Check := [
    ("full compiled byte-reader certificate", checkByteReader byte 0),
    ("full compiled u32-reader certificate", checkWordReader word reader 0),
    ("full compiled identity-reader certificate", checkIdReader identity reader 0),
    ("full compiled zero-count parser certificate", checkEmptyTableParser parser 0),
    ("byte certificate rejects wrong input arity", !checkByteReader
      { byte with layout := { byte.layout with inputSize := 2 } } 0),
    ("byte certificate rejects extra operation", !checkByteReader
      { byte with body := { byteBody with ops := byteBody.ops.push (.const 0) } } 0),
    ("byte certificate rejects wrong load width", !checkByteReader
      { byte with body := { byteBody with ops := #[.load 4 0] } } 0),
    ("byte certificate rejects wrong pointer register", !checkByteReader
      { byte with body := { byteBody with ops := #[.load 3 1] } } 0),
    ("byte certificate rejects wrong tag register", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 2 #[(0, byteBranch)] none⟩ } 0),
    ("byte certificate rejects Nil branch", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 1 #[(1, byteBranch)] none⟩ } 0),
    ("byte certificate rejects added fallback", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 1 #[(0, byteBranch)] (some byteBranch)⟩ } 0),
    ("byte certificate rejects added match arm", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 1 #[(0, byteBranch), (1, byteBranch)] none⟩ } 0),
    ("byte certificate rejects yield instead of return", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 1 #[(0, ⟨#[], .yield 0 #[2, 3]⟩)] none⟩ } 0),
    ("byte certificate rejects swapped outputs", !checkByteReader { byte with body :=
      ⟨#[.load 3 0], .match 1 #[(0, ⟨#[], .return 0 #[3, 2]⟩)] none⟩ } 0),
    ("byte selector is explicit", checkByteReader { byte with body := byteReaderBody 7 } 7 &&
      !checkByteReader { byte with body := byteReaderBody 7 } 0),
    ("nonsemantic layout metadata is ignored", checkByteReader { byte with
      layout := { byte.layout with auxiliaries := 999, lookups := 888 }, constrained := false } 0),
    ("u32 certificate rejects wrong callee", !checkWordReader word (reader + 1) 0),
    ("u32 certificate rejects wrong input arity", !checkWordReader
      { word with layout := { word.layout with inputSize := 2 } } reader 0),
    ("u32 certificate rejects swapped outputs", !checkWordReader
      { word with body := { wordBody with ctrl := .return 0 #[8, 17] } } reader 0),
    ("u32 certificate rejects yield", !checkWordReader
      { word with body := { wordBody with ctrl := .yield 0 #[17, 8] } } reader 0),
    ("identity certificate rejects wrong input arity", !checkIdReader
      { identity with layout := { identity.layout with inputSize := 2 } } reader 0),
    ("identity certificate rejects wrong byte callee", !checkIdReader identity (reader + 1) 0),
    ("identity certificate rejects short body", !checkIdReader
      { identity with body := { identityBody with ops := wordBody.ops } } reader 0),
    ("identity certificate rejects added operation", !checkIdReader
      { identity with body := { identityBody with ops := identityBody.ops.push (.const 0) } } reader 0),
    ("identity certificate rejects missing suffix output", !checkIdReader
      { identity with body := { identityBody with ctrl := .return 0 (wordIndices 1 10) } } reader 0),
    ("identity certificate rejects yield", !checkIdReader { identity with body :=
      { identityBody with ctrl := .yield 0 (wordIndices 1 10 ++ #[finishIndex 1 0 10]) } } reader 0),
    ("identity selector is explicit", checkIdReader
      { identity with body := idReaderBody reader 7 } reader 7 && !checkIdReader identity reader 7),
    ("zero-count certificate rejects wrong arity", !checkEmptyTableParser
      { parser with layout := { parser.layout with inputSize := 1 } } 0),
    ("zero-count certificate rejects leading operation", !checkEmptyTableParser
      { parser with body := { parser.body with ops := #[.const 0] } } 0),
    ("zero-count certificate does not certify the default branch", checkEmptyTableParser baseOnly 0),
    ("uncertified nonzero branch can return a non-table", match evalBlock compiled.bytecode 0
      baseOnly.body { initial with map := #[42, 1] } with
      | .error (.earlyReturn flat after) => flat == #[42] && (readTable (bytecodeMemory after) 42 1).isNone
      | _ => false)]
  for i in [:wordBody.ops.size] do
    checks := checks ++ [(s!"u32 certificate binds operation {i}", !checkWordReader
      { word with body := { wordBody with ops := wordBody.ops.set! i (.const 0) } } reader 0)]
  for i in [:identityBody.ops.size] do
    checks := checks ++ [(s!"identity certificate binds operation {i}", !checkIdReader
      { identity with body := { identityBody with ops := identityBody.ops.set! i (.const 0) } } reader 0)]
  for i in [:11] do
    let indices := wordIndices 1 10 ++ #[finishIndex 1 0 10]
    checks := checks ++ [(s!"identity certificate binds output {i}", !checkIdReader { identity with body :=
      { identityBody with ctrl := .return 0 (indices.set! i 0) } } reader 0)]
  for i in [:13] do
    let indices : Array Nat := #[2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
    let branch := { emptyTableBranch 0 with ops := #[.const 1, .const 1, .store (indices.set! i 0)] }
    checks := checks ++ [(s!"zero-count certificate binds Nil store operand {i}", !checkEmptyTableParser
      { parser with body := ⟨#[], .match 1 #[(0, branch)] none⟩ } 0)]
  return checks

private def byteChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (reader, _) ← function compiled `ib_byte
  let mut checks : List Check := []
  let tail : Aiur.G := .ofNat (2 ^ 32 + 19)
  for n in [:256] do
    let (st, pointer) := storePrefix initial #[.ofNat n] tail
    checks := checks ++ [(s!"compiled byte {n} with untouched memory/io and full tail",
      success (snapshot compiled `ib_byte #[pointer] st 0) #[.ofNat n, tail] st)]
  for n in [0, 127, 255] do
    for unconstrained in [false, true] do
      let (st, pointer) := storePrefix initial #[.ofNat n] tail
      let caller := { st with map := #[99, pointer, 101] }
      let result := Aiur.Bytecode.Eval.evalOp compiled.bytecode 1 (.call reader #[1] 2 unconstrained) caller
      checks := checks ++ [(s!"actual byte Call restores caller registers {n}/{unconstrained}",
        match result with
        | .ok after => after.map == #[99, pointer, 101, .ofNat n, tail] && unchanged caller after
        | _ => false)]
  for n in [256, 65536, 2 ^ 32, goldilocksModulus - 1] do
    let byte : Aiur.G := .ofNat n
    let (st, pointer) := storePrefix initial #[byte] tail
    let checked := Aiur.Bytecode.Eval.evalOp compiled.bytecode 0 (.u8RangeCheck 0 1)
      { initial with map := #[byte, 0] }
    checks := checks ++ [(s!"raw byte reader does not establish range {n}",
      success (snapshot compiled `ib_byte #[pointer] st) #[byte, tail] st),
      (s!"actual range instruction rejects forged byte {n}",
        match checked with | .error .u8RangeCheckFailed => true | _ => false)]
  for (label, flat, error) in [
      ("Nil", #[1, 1, 1], BytecodeError.unreachableAfterLayout),
      ("unknown tag", #[2, 17, 0], .unreachableAfterLayout),
      ("short width", #[0, 17], .invalidPointer 3 0),
      ("long width", #[0, 17, 0, 0], .invalidPointer 3 0)] do
    let (st, pointer) := memStore initial flat
    checks := checks ++ [("compiled byte rejects " ++ label,
      failed (snapshot compiled `ib_byte #[.ofNat pointer] st) error)]
  let (st, _) := storeStream initial #[17]
  checks := checks ++ [("byte pointer is not narrowed to u32",
    failed (snapshot compiled `ib_byte #[.ofNat (2 ^ 32 + 1)] st) (.invalidPointer 3 (2 ^ 32 + 1)))]
  for (a, b, valid) in [(0, 0, true), (255, 255, true), (255, 0, true), (0, 256, false)] do
    let before := { initial with map := #[.ofNat a, .ofNat b] }
    let result := Aiur.Bytecode.Eval.evalOp compiled.bytecode 0 (.u8RangeCheck 0 1) before
    checks := checks ++ [(s!"paired range check {a}/{b}", match result with
      | .ok after => valid && after.map == before.map && unchanged before after
      | .error .u8RangeCheckFailed => !valid | _ => false)]
  return checks

private def wordChecks (compiled : Aiur.CompiledToplevel) : List Check := Id.run do
  let mut checks := []
  let samples := [0, 1, 255, 256, 65535, 65536, 2 ^ 24 - 1, 2 ^ 24, 0x12345678, 2 ^ 31, 2 ^ 32 - 1] ++
    (List.range 32).map (2 ^ ·)
  for n in samples do
    let (suffix, finish) := storeStream initial #[90, 91, 92]
    let (st, pointer) := storePrefix suffix ((bytesLE 4 n).map Aiur.G.ofUInt8) finish
    checks := checks ++ [(s!"compiled u32 {n} exact value/suffix/memory/io",
      success (snapshot compiled `ib_u32 #[pointer] st 1) #[.ofNat n, finish] st)]
  for length in [:4] do
    let (st, pointer) := storeStream initial (Array.replicate length 0)
    checks := checks ++ [(s!"compiled u32 rejects {length}-byte truncation",
      failed (snapshot compiled `ib_u32 #[pointer] st) .unreachableAfterLayout)]
  let (st, pointer) := storeStream initial #[1, 2, 3, 4]
  checks := checks ++ [("u32 needs fuel for byte calls", failed (snapshot compiled `ib_u32 #[pointer] st 0) .outOfFuel)]
  let tail : Aiur.G := .ofNat (goldilocksModulus - 1)
  let (st, pointer) := storePrefix initial #[255, 255, 255, 255] tail
  checks := checks ++ [("u32 does not read or narrow its returned suffix",
    success (snapshot compiled `ib_u32 #[pointer] st) #[.ofNat (2 ^ 32 - 1), tail] st)]
  let (st, pointer) := storePrefix initial #[.ofNat (goldilocksModulus - 1), 1, 0, 0] tail
  checks := checks ++ [("forged non-byte can wrap to a plausible u32: range premise is essential",
    success (snapshot compiled `ib_u32 #[pointer] st) #[255, tail] st)]
  return checks

private def identityBytes (words : Array Nat) : Array UInt8 :=
  words.foldl (fun out word => out ++ bytesLE 4 word) #[]

private def identityAgreement (compiled : Aiur.CompiledToplevel) (words : Array Nat) : Bool :=
  let bytes := identityBytes words
  let (suffix, finish) := storeStream initial #[90, 91, 92]
  let (st, pointer) := storePrefix suffix (bytes.map Aiur.G.ofUInt8) finish
  let wire := #[200, 201] ++ bytes ++ #[90, 91, 92]
  match snapshot compiled `is_read_id #[pointer] st 1,
      Codec.Internal.readCtorId.run { bytes := wire, offset := 2, nodes := 13 } with
  | .ok (out, after), .ok (name, remaining) =>
    out == (words.map Aiur.G.ofNat) ++ #[finish] && unchanged st after &&
      decodeId (out.extract 0 10).toList == some name && remaining.offset == 42 &&
      remaining.nodes == 13 && remaining.bytes == wire
  | _, _ => false

private def identityChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (identity, identityFn) ← function compiled `is_read_id
  let (reader, byteFn) ← function compiled `ib_byte
  let baseline := #[0x01020304, 0x05060708, 0x11121314, 0x15161718, 0x21222324,
    0x25262728, 0x31323334, 0x35363738, 0x41424344, 0x45464748]
  let bytes := identityBytes baseline
  let payload := bytes.map Aiur.G.ofUInt8
  let mut checks : List Check := [
    ("identity full asymmetric digest/member/tag matches the byte codec", identityAgreement compiled baseline),
    ("identity all zero limbs match the byte codec", identityAgreement compiled (Array.replicate 10 0)),
    ("identity all maximum limbs retain 256-bit digest and u32 member/tag",
      identityAgreement compiled (Array.replicate 10 (2 ^ 32 - 1)))]
  let samples := [0, 1, 255, 256, 65535, 65536, 2 ^ 24 - 1, 2 ^ 24, 0x12345678, 2 ^ 31, 2 ^ 32 - 1] ++
    (List.range 32).map (2 ^ ·)
  for limb in [:10] do
    for n in samples do
      checks := checks ++ [(s!"identity limb {limb}/{n} exact codec/suffix/memory/io",
        identityAgreement compiled (baseline.set! limb n))]
  for length in [:40] do
    let (st, pointer) := storeStream initial (payload.extract 0 length)
    checks := checks ++ [(s!"identity rejects {length}-byte truncation",
      failed (snapshot compiled `is_read_id #[pointer] st 1) .unreachableAfterLayout)]
  let (suffix, finish) := storeStream initial #[90, 91, 92]
  for position in [:40] do
    let (after, next) := storePrefix suffix (payload.extract (position + 1) 40) finish
    let (malformed, bad) := memStore after #[2, payload.getD position 0, next]
    let (st, pointer) := storePrefix malformed (payload.extract 0 position) (.ofNat bad)
    checks := checks ++ [(s!"identity rejects malformed byte tag at {position}",
      failed (snapshot compiled `is_read_id #[pointer] st 1) .unreachableAfterLayout)]
  let large : Aiur.G := .ofNat (goldilocksModulus - 1)
  for position in [:39] do
    let (st, pointer) := storePrefix initial (payload.extract 0 (position + 1)) large
    checks := checks ++ [(s!"identity rejects unreadable intermediate pointer after byte {position}",
      failed (snapshot compiled `is_read_id #[pointer] st 1) (.invalidPointer 3 large.n))]
  for n in [2 ^ 32 + 9, goldilocksModulus - 1] do
    let tail : Aiur.G := .ofNat n
    let (st, pointer) := storePrefix initial payload tail
    checks := checks ++ [(s!"identity returns unreadable full-field suffix {n} without loading it",
      success (snapshot compiled `is_read_id #[pointer] st 1) ((baseline.map Aiur.G.ofNat) ++ #[tail]) st)]
  let (st, pointer) := storePrefix suffix payload finish
  checks := checks ++ [
    ("identity body needs fuel for byte calls", failed (snapshot compiled `is_read_id #[pointer] st 0) .outOfFuel),
    ("identity input pointer is not narrowed", failed (snapshot compiled `is_read_id #[large] st 1)
      (.invalidPointer 3 large.n))]
  let caller := { st with map := #[99, 100, pointer, 102] }
  for unconstrained in [false, true] do
    checks := checks ++ [(s!"actual identity Call restores all caller registers/{unconstrained}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 2 (.call identity #[2] 11 unconstrained) caller with
      | .ok after => after.map == caller.map ++ ((baseline.map Aiur.G.ofNat) ++ #[finish]) && unchanged caller after
      | _ => false)]
  for (label, fuel, args, outputs, error) in [
      ("nested-call fuel", 1, #[2], 11, BytecodeError.outOfFuel),
      ("input arity", 2, #[], 11, .arityMismatch identity),
      ("missing argument register", 2, #[4], 11, .invalidValIdx 4),
      ("short output arity", 2, #[2], 10, .callOutputSizeMismatch),
      ("long output arity", 2, #[2], 12, .callOutputSizeMismatch)] do
    checks := checks ++ [("identity Call rejects " ++ label,
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call identity args outputs false) caller with
      | .error actual => reprStr actual == reprStr error | _ => false)]
  for limb in [:10] do
    let forged := (Array.replicate 40 (0 : Aiur.G)).set! (limb * 4 + 3) 256
    let (st, pointer) := storePrefix initial forged finish
    checks := checks ++ [(s!"identity raw non-byte can exceed u32 at limb {limb}",
      match snapshot compiled `is_read_id #[pointer] st 1 with
      | .ok (out, after) => out[limb]? == some (.ofNat (2 ^ 32)) &&
        (decodeId (out.extract 0 10).toList).isNone && unchanged st after
      | _ => false)]
  let forged := (Array.replicate 40 (0 : Aiur.G)).set! 0 large |>.set! 1 1
  let (st, pointer) := storePrefix initial forged finish
  checks := checks ++ [("identity non-byte can wrap into a decodable name: byte premise is essential",
    match snapshot compiled `is_read_id #[pointer] st 1 with
    | .ok (out, after) => out[0]? == some 255 && (decodeId (out.extract 0 10).toList).isSome && unchanged st after
    | _ => false)]
  let fakeByte := { byteFn with body := (⟨#[.const 0], .return 0 #[1, 0]⟩ : Aiur.Bytecode.Block) }
  let fake := { compiled with bytecode := { compiled.bytecode with
    functions := compiled.bytecode.functions.set! reader fakeByte } }
  let (st, pointer) := storePrefix initial payload finish
  checks := checks ++ [("identity certificate also requires its actual byte callee certificate",
    checkIdReader identityFn reader 0 && !checkByteReader fakeByte 0 &&
      success (snapshot fake `is_read_id #[pointer] st 1) ((Array.replicate 10 0) ++ #[pointer]) st)]
  return checks

private def comparisonChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (comparer, cmp) ← function compiled `is_id_eq
  let body := idEqBody 0
  let mut checks : List Check := [
    ("full compiled ID-comparator certificate", checkIdEq cmp 0),
    ("comparator certificate rejects input arity", !checkIdEq { cmp with layout := { cmp.layout with inputSize := 19 } } 0),
    ("comparator certificate rejects wrong return register", !checkIdEq
      { cmp with body := { body with ctrl := .return 0 #[47] } } 0),
    ("comparator certificate rejects extra return register", !checkIdEq
      { cmp with body := { body with ctrl := .return 0 #[48, 48] } } 0),
    ("comparator certificate rejects yield", !checkIdEq { cmp with body := { body with ctrl := .yield 0 #[48] } } 0),
    ("comparator certificate rejects wrong selector", !checkIdEq cmp 1),
    ("comparator selectors are parametric", checkIdEq { cmp with body := idEqBody 7 } 7),
    ("comparator certificate rejects extra operation", !checkIdEq
      { cmp with body := { body with ops := body.ops.push (.const 0) } } 0)]
  for i in [:body.ops.size] do
    checks := checks ++ [(s!"comparator certificate binds operation {i}", !checkIdEq
      { cmp with body := { body with ops := body.ops.set! i (.const 0) } } 0)]
  for baseline in [0, 1, 2 ^ 32 - 1, goldilocksModulus - 1] do
    let left : Array Aiur.G := Array.replicate 10 (.ofNat baseline)
    checks := checks ++ [(s!"comparator equal all-limb value {baseline}",
      success (snapshot compiled `is_id_eq (left ++ left) initial 0) #[1] initial)]
    for limb in [:10] do
      let other : Aiur.G := if baseline == 0 then 1 else 0
      let right := left.set! limb other
      for (a, b, direction) in [(left, right, "forward"), (right, left, "reverse")] do
        checks := checks ++ [(s!"comparator distinguishes limb {limb}/{baseline}/{direction}",
          success (snapshot compiled `is_id_eq (a ++ b) initial 0) #[0] initial)]
  let maximum : Array Aiur.G := Array.replicate 10 (.ofNat (2 ^ 32 - 1))
  checks := checks ++ [("all 256 digest bits and maximum member/tag decode exactly",
    match decodeId maximum.toList with
    | some id => id.block.val == 2 ^ 256 - 1 && id.member == 2 ^ 32 - 1 && id.tag == 2 ^ 32 - 1
    | none => false)]
  for limb in [:10] do
    let forged := maximum.set! limb (.ofNat (2 ^ 32))
    checks := checks ++ [(s!"raw comparator does not supply semantic limb range {limb}",
      (decodeId forged.toList).isNone && success (snapshot compiled `is_id_eq (forged ++ forged) initial 0) #[1] initial)]
  let caller := { initial with map := #[123] ++ maximum ++ maximum ++ #[456] }
  let args := (Array.range 20).map (· + 1)
  for flag in [false, true] do
    checks := checks ++ [(s!"comparator Call preserves all caller registers and memory/io/{flag}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 1 (.call comparer args 1 flag) caller with
      | .ok after => after.map == caller.map.push 1 && unchanged caller after
      | _ => false)]
  for (label, fuel, arguments, outputs, error) in [
      ("fuel", 0, args, 1, BytecodeError.outOfFuel),
      ("input arity", 1, #[1], 1, .arityMismatch comparer),
      ("missing register", 1, (args.set! 0 99), 1, .invalidValIdx 99),
      ("output arity", 1, args, 0, .callOutputSizeMismatch)] do
    checks := checks ++ [("comparator Call rejects " ++ label,
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call comparer arguments outputs false) caller with
      | .error actual => reprStr actual == reprStr error | _ => false)]
  return checks

private def testRawId (n : Nat) : RawId :=
  ⟨.ofNat n, 17, 29, 31, 43, 59, 61, 73, 83, 97⟩

private def storeDeclarations (st : EvalState) (decls : Array RawDecl) : EvalState × Aiur.G :=
  let (st, pointer) := memStore st tableNil
  decls.foldr (fun decl state =>
    let next := memStore state.1 (decl.cell state.2)
    (next.1, .ofNat next.2)) (st, .ofNat pointer)

private def uniqueFixture (zero step : Aiur.Bytecode.Block) : Aiur.Bytecode.Block :=
  ⟨#[], .match 11 #[(0, zero)] (some (uniqueNonzero step))⟩

private def uniquenessChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let (comparer, cmp) ← function compiled `is_id_eq
  let (self, unique) ← function compiled `is_unique_id
  let body := uniqueBody comparer self 0 1
  let zero := uniqueZero 0
  let step := uniqueStep comparer self 1
  let accepts := fun b => checkUnique { unique with body := b } comparer self 0 1
  let mut checks : List Check := [
    ("full compiled uniqueness certificate", checkUnique unique comparer self 0 1),
    ("uniqueness certificate binds comparison index", !checkUnique unique (comparer + 1) self 0 1),
    ("uniqueness certificate binds recursion index", !checkUnique unique comparer (self + 1) 0 1),
    ("uniqueness certificate binds both selectors", !checkUnique unique comparer self 1 1 &&
      !checkUnique unique comparer self 0 0),
    ("uniqueness certificate rejects input arity", !checkUnique
      { unique with layout := { unique.layout with inputSize := 11 } } comparer self 0 1),
    ("uniqueness certificate ignores nonsemantic layout metadata", checkUnique
      { unique with layout := { unique.layout with auxiliaries := 999 }, constrained := false } comparer self 0 1),
    ("uniqueness certificate rejects extra root operation", !accepts { body with ops := #[.const 0] }),
    ("uniqueness certificate rejects wrong counter register", !accepts
      ⟨#[], .match 10 #[(0, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects wrong zero tag", !accepts
      ⟨#[], .match 11 #[(1, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects added zero arm", !accepts
      ⟨#[], .match 11 #[(0, zero), (1, zero)] (some (uniqueNonzero step))⟩),
    ("uniqueness certificate rejects missing recursive branch", !accepts ⟨#[], .match 11 #[(0, zero)] none⟩),
    ("uniqueness certificate binds Cons tag register", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 13 #[(0, uniqueTagless step)] none⟩)⟩),
    ("uniqueness certificate rejects a Nil recursion arm", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(1, uniqueTagless step)] none⟩)⟩),
    ("uniqueness certificate rejects extra Cons fallback", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, uniqueTagless step)] (some step)⟩)⟩),
    ("uniqueness certificate binds tagless-constructor match", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, ⟨#[], .match 14 #[] (some step)⟩)] none⟩)⟩),
    ("uniqueness certificate rejects a tagless-constructor case", !accepts ⟨#[], .match 11 #[(0, zero)]
      (some ⟨#[.load 13 10], .match 12 #[(0, ⟨#[], .match 13 #[(0, step)] (some step)⟩)] none⟩)⟩),
    ("uniqueness certificate rejects yielding base", !accepts (uniqueFixture { zero with ctrl := .yield 0 #[] } step)),
    ("uniqueness certificate rejects yielding step", !accepts (uniqueFixture zero { step with ctrl := .yield 1 #[] })),
    ("uniqueness certificate rejects extra output", !accepts (uniqueFixture zero { step with ctrl := .return 1 #[0] }))]
  for i in [:zero.ops.size] do
    checks := checks ++ [(s!"uniqueness certificate binds base operation {i}",
      !accepts (uniqueFixture { zero with ops := zero.ops.set! i (.const 0) } step))]
  for i in [:step.ops.size] do
    -- The existing const-zero operation is replaced with a distinct constant.
    checks := checks ++ [(s!"uniqueness certificate binds recursive operation {i}",
      !accepts (uniqueFixture zero { step with ops := step.ops.set! i (.const 999) }))]
  for i in [:compareArgs.size] do
    let changed := step.ops.set! 0 (.call comparer (compareArgs.set! i 99) 1 false)
    checks := checks ++ [(s!"uniqueness certificate binds comparator argument {i}",
      !accepts (uniqueFixture zero { step with ops := changed }))]
  for i in [:recurseArgs.size] do
    let changed := step.ops.set! 5 (.call self (recurseArgs.set! i 99) 0 false)
    checks := checks ++ [(s!"uniqueness certificate binds recursive argument {i}",
      !accepts (uniqueFixture zero { step with ops := changed }))]
  let needle := testRawId 999
  let populated := (memStore (memStore initial #[101, 102, 103]).1 (Array.replicate 13 999)).1
  for count in [:17] do
    let decls : Array RawDecl := (Array.range count).map fun i => ⟨testRawId (i + 1), .ofNat (i % 8)⟩
    let (st, pointer) := storeDeclarations populated decls
    checks := checks ++ [(s!"fresh semantic ID across exact bounded table length {count}",
      (readTable (bytecodeMemory st) pointer.n count).isSome &&
      success (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat count]) st (count + 1)) #[] st)]
    for i in [:count] do
      let duplicate := testRawId (i + 1)
      checks := checks ++ [(s!"duplicate rejection at position {i} of {count}",
        failed (snapshot compiled `is_unique_id (duplicate.flat ++ #[pointer, .ofNat count]) st (count + 1)) .assertFailed)]
    if count > 0 then
      checks := checks ++ [(s!"uniqueness rejects too-small count for table length {count}",
        failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat (count - 1)]) st (count + 1)) .assertFailed)]
    checks := checks ++ [(s!"uniqueness rejects too-large count for table length {count}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, .ofNat (count + 1)]) st (count + 2))
        .unreachableAfterLayout)]
  for i in [:13] do
    let (st, pointer) := memStore initial (tableNil.set! i 0)
    checks := checks ++ [(s!"uniqueness checks terminal Nil padding field {i}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat pointer, 0]) st 0) .assertFailed)]
  let (st, pointer) := storeDeclarations populated #[⟨testRawId 1, 3⟩, ⟨testRawId 2, 7⟩]
  let caller := { st with map := #[9999] ++ needle.flat ++ #[pointer, 2, 8888] }
  let arguments := (Array.range 12).map (· + 1)
  for flag in [false, true] do
    checks := checks ++ [(s!"uniqueness Call returns exact original caller state/{flag}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 4 (.call self arguments 0 flag) caller with
      | .ok after => after.map == caller.map && unchanged caller after | _ => false)]
  for (label, fuel, args, outputs, error) in [
      ("input arity", 4, #[1], 0, BytecodeError.arityMismatch self),
      ("missing argument register", 4, (arguments.set! 0 99), 0, .invalidValIdx 99),
      ("output arity", 4, arguments, 1, .callOutputSizeMismatch),
      ("fuel", 1, arguments, 0, .outOfFuel)] do
    checks := checks ++ [("uniqueness Call rejects " ++ label,
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call self args outputs false) caller with
      | .error actual => reprStr actual == reprStr error | _ => false)]
  for n in [2 ^ 32 + pointer.n, goldilocksModulus - 1] do
    checks := checks ++ [(s!"uniqueness never narrows table pointer {n}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat n, 2]) st 3) (.invalidPointer 13 n))]
  for count in [0, 1] do
    checks := checks ++ [(s!"insufficient uniqueness fuel {count}",
      failed (snapshot compiled `is_unique_id (needle.flat ++ #[pointer, 2]) st count) .outOfFuel)]
  let (nilState, nilPtr) := storeDeclarations initial #[]
  checks := checks ++ [("empty uniqueness body needs no call fuel",
    success (snapshot compiled `is_unique_id (needle.flat ++ #[nilPtr, 0]) nilState 0) #[] nilState)]
  let (badTagState, badTagPtr) := memStore nilState ((RawDecl.cell ⟨testRawId 1, 1⟩ nilPtr).set! 0 2)
  checks := checks ++ [("uniqueness rejects unknown list tag",
    failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat badTagPtr, 1]) badTagState 2) .unreachableAfterLayout)]
  let invalid : RawId := { testRawId 1 with h := .ofNat (2 ^ 32) }
  let (rawState, rawPtr) := storeDeclarations initial #[⟨invalid, 0⟩]
  checks := checks ++ [("raw uniqueness does not establish semantic limb bounds",
    (readTable (bytecodeMemory rawState) rawPtr.n 1).isNone &&
      success (snapshot compiled `is_unique_id (needle.flat ++ #[rawPtr, 1]) rawState 2) #[] rawState),
    ("raw uniqueness still rejects equal out-of-range limbs",
      failed (snapshot compiled `is_unique_id (invalid.flat ++ #[rawPtr, 1]) rawState 2) .assertFailed)]
  let (cycleState, cyclePtr) := memStore initial (RawDecl.cell ⟨testRawId 1, 0⟩ 0)
  checks := checks ++ [("finite count rejects a cyclic raw spine at the terminal check",
    failed (snapshot compiled `is_unique_id (needle.flat ++ #[.ofNat cyclePtr, 3]) cycleState 4) .assertFailed)]
  let fakeCmp := { cmp with body := (⟨#[.const 0], .return 0 #[20]⟩ : Aiur.Bytecode.Block) }
  let fake := { compiled with bytecode := { compiled.bytecode with
    functions := compiled.bytecode.functions.set! comparer fakeCmp } }
  checks := checks ++ [("uniqueness body also requires its actual comparator certificate",
    checkUnique unique comparer self 0 1 && !checkIdEq fakeCmp 0 &&
    success (snapshot fake `is_unique_id ((testRawId 1).flat ++ #[pointer, 2]) st 3) #[] st)]
  return checks

private def emptyChecks (compiled : Aiur.CompiledToplevel) : List Check := Id.run do
  let mut checks := []
  let populated := (memStore (memStore initial (Array.replicate 13 2)).1 tableNil).1
  for (label, st) in [("fresh", initial), ("deduplicated", populated)] do
    for n in [0, 2 ^ 32 + 7, goldilocksModulus - 1] do
      let (before, pointer) := storeStream st #[90, 91, 92]
      let arg : Aiur.G := if n == 0 then pointer else .ofNat n
      let result := snapshot compiled `is_read_ctors #[arg, 0] before 0
      checks := checks ++ [(s!"zero parser {label}/{n} establishes Nil and preserves all prior reads",
        match result with
        | .ok (out, after) => out.size == 2 && out[1]? == some arg &&
          readTable (bytecodeMemory after) (out.getD 0 0).n 0 == some #[] &&
          out[0]? == some (.ofNat (memStore before tableNil).2) && preservesReads before after && sameIo before after
        | _ => false)]
  return checks

private def declarationCode (compiled : Aiur.CompiledToplevel) : Except String DeclarationCode := do
  let (reader, _) ← function compiled `ib_byte
  let (identity, _) ← function compiled `is_read_id
  let (comparer, _) ← function compiled `is_id_eq
  let (unique, _) ← function compiled `is_unique_id
  let (self, _) ← function compiled `is_read_ctors
  return { reader, identity, comparer, unique, self }

private def declarationCertificates (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let code ← declarationCode compiled
  let (_, parser) ← function compiled `is_read_ctors
  let zero := emptyTableBranch 0
  let step := declarationsStep code.reader code.identity code.unique code.self 1
  let body := declarationsBody code.reader code.identity code.unique code.self 0 1
  let fixture := fun zero step => (⟨#[], .match 1 #[(0, zero)] (some step)⟩ : Aiur.Bytecode.Block)
  let accepts := fun body => checkDeclarations { parser with body } code.reader code.identity code.unique code.self 0 1
  let mut checks : List Check := [
    ("complete compiled declaration reader certificate", accepts parser.body),
    ("complete declaration code links every actual callee", checkDeclarationCode compiled.bytecode code),
    ("complete declaration certificate rejects input arity", !checkDeclarations
      { parser with layout := { parser.layout with inputSize := 3 } } code.reader code.identity code.unique code.self 0 1),
    ("complete declaration certificate ignores nonsemantic metadata", checkDeclarations
      { parser with layout := { parser.layout with auxiliaries := 999, lookups := 888 }, constrained := false }
      code.reader code.identity code.unique code.self 0 1),
    ("declaration certificate rejects root operations", !accepts { body with ops := #[.const 0] }),
    ("declaration certificate binds counter register", !accepts ⟨#[], .match 0 #[(0, zero)] (some step)⟩),
    ("declaration certificate binds zero tag", !accepts ⟨#[], .match 1 #[(1, zero)] (some step)⟩),
    ("declaration certificate rejects extra zero arm", !accepts ⟨#[], .match 1 #[(0, zero), (1, zero)] (some step)⟩),
    ("declaration certificate rejects missing zero arm", !accepts ⟨#[], .match 1 #[] (some step)⟩),
    ("declaration certificate rejects missing recursive branch", !accepts ⟨#[], .match 1 #[(0, zero)] none⟩),
    ("declaration certificate rejects yielding zero branch", !accepts (fixture { zero with ctrl := .yield 0 #[4, 0] } step)),
    ("declaration certificate rejects yielding recursive branch", !accepts (fixture zero { step with ctrl := .yield 1 #[42, 38] })),
    ("declaration certificate binds zero outputs", !accepts (fixture { zero with ctrl := .return 0 #[0, 4] } step)),
    ("declaration certificate binds recursive outputs", !accepts (fixture zero { step with ctrl := .return 1 #[38, 42] })),
    ("declaration certificate rejects extra recursive output", !accepts (fixture zero { step with ctrl := .return 1 #[42, 38, 0] })),
    ("declaration certificate binds zero selector", !accepts (fixture { zero with ctrl := .return 1 #[4, 0] } step)),
    ("declaration certificate binds recursive selector", !accepts (fixture zero { step with ctrl := .return 0 #[42, 38] })),
    ("declaration certificate rejects extra step operation", !accepts (fixture zero { step with ops := step.ops.push (.const 0) })),
    ("zero-only certificate is not a full parser certificate", checkEmptyTableParser
      { parser with body := emptyTableBody 0 (some ⟨#[], .return 1 #[0, 1]⟩) } 0 &&
      !accepts (emptyTableBody 0 (some ⟨#[], .return 1 #[0, 1]⟩))),
    ("declaration selectors are explicit parameters", checkDeclarations
      { parser with body := declarationsBody code.reader code.identity code.unique code.self 7 8 }
      code.reader code.identity code.unique code.self 7 8)]
  for i in [:zero.ops.size] do
    checks := checks ++ [(s!"declaration certificate binds zero operation {i}",
      !accepts (fixture { zero with ops := zero.ops.set! i (.const 999) } step))]
  for i in [:step.ops.size] do
    checks := checks ++ [(s!"declaration certificate binds recursive operation {i}",
      !accepts (fixture zero { step with ops := step.ops.set! i (.const 999) }))]
  for i in [:2] do
    checks := checks ++ [(s!"declaration certificate binds recursive Call argument {i}", !accepts (fixture zero
      { step with ops := step.ops.set! 22 (.call code.self (#[20, 36].set! i 99) 2 false) }))]
  for i in [:uniquenessArgs.size] do
    checks := checks ++ [(s!"declaration certificate binds unique Call argument {i}", !accepts (fixture zero
      { step with ops := step.ops.set! 25 (.call code.unique (uniquenessArgs.set! i 99) 0 false) }))]
  let storeArgs := #[41, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 29, 37]
  for i in [:storeArgs.size] do
    checks := checks ++ [(s!"declaration certificate binds Cons store argument {i}", !accepts (fixture zero
      { step with ops := step.ops.set! 27 (.store (storeArgs.set! i 99)) }))]
  for (label, index) in [("byte", code.reader), ("identity", code.identity), ("comparer", code.comparer),
      ("uniqueness", code.unique), ("recursive parser", code.self)] do
    let some callee := compiled.bytecode.functions[index]? | throw "missing certified callee"
    let changed := { callee with body := { callee.body with ops := callee.body.ops.push (.const 999) } }
    let bad := { compiled.bytecode with functions := compiled.bytecode.functions.set! index changed }
    checks := checks ++ [(s!"declaration bundle rejects changed {label} callee", !checkDeclarationCode bad code)]
  let missing := compiled.bytecode.functions.size
  for (label, changed) in [("byte", { code with reader := missing }), ("identity", { code with identity := missing }),
      ("comparer", { code with comparer := missing }), ("unique", { code with unique := missing }),
      ("parser", { code with self := missing })] do
    checks := checks ++ [(s!"declaration bundle rejects missing {label} callee", !checkDeclarationCode compiled.bytecode changed)]
  return checks

private def wordBytes (n : Nat) : WordBytes :=
  ⟨.ofNat n, .ofNat (n / 256), .ofNat (n / 65536), .ofNat (n / 16777216)⟩

private def wireDeclaration (n fields : Nat) : DeclarationBytes := {
  a := wordBytes 0x01020304, b := wordBytes 0x05060708, c := wordBytes 0x11121314,
  d := wordBytes 0x15161718, e := wordBytes 0x21222324, f := wordBytes 0x25262728,
  g := wordBytes 0x31323334, h := wordBytes (2 ^ 32 - 1),
  member := wordBytes (0x41424340 + n), tag := wordBytes (0x45464740 + n), fields := wordBytes fields }

private def wireDeclarations (count : Nat) : List DeclarationBytes :=
  (List.range count).map fun i => wireDeclaration i (if i % 2 == 0 then 0 else 16)

private def declarationPayload (decls : List DeclarationBytes) : Array Aiur.G :=
  (decls.flatMap DeclarationBytes.bytes).toArray.map Aiur.G.ofUInt8

private def declarationAgreement (compiled : Aiur.CompiledToplevel) (base : EvalState)
    (decls : List DeclarationBytes) (finish : Aiur.G) : Bool :=
  let (st, pointer) := storePrefix base (declarationPayload decls) finish
  let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations st decls
  let bytes := #[200, 201] ++ bytesLE 4 decls.length ++ (decls.flatMap DeclarationBytes.bytes).toArray ++ #[90, 91, 92]
  let decoder : Codec.Internal.Decoder (Array CtorDecl) := Codec.Internal.readVector 16 do
    let id ← Codec.Internal.readCtorId
    let fields ← Codec.Internal.readCount 16
    return ⟨id, fields⟩
  match snapshot compiled `is_read_ctors #[pointer, .ofNat decls.length] st (decls.length + 2),
      decoder.run { bytes, offset := 2, nodes := 13 } with
  | .ok (out, after), .ok (table, remaining) =>
    out == #[expected.2, finish] && table == (decls.map DeclarationBytes.declaration).toArray &&
      readTable (bytecodeMemory after) expected.2.n decls.length == some table &&
      memoryView after == memoryView expected.1 && preservesReads st after && sameIo st after &&
      Ix.Ixby.AiurBackend.Objects.Store.bucketSize after 13 ≤ Ix.Ixby.AiurBackend.Objects.Store.bucketSize st 13 + decls.length + 1 &&
      remaining.bytes == bytes && remaining.offset == 6 + 44 * decls.length && remaining.nodes == 13
  | _, _ => false

private def declarationSuccessChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let populated := (memStore (memStore initial #[101, 102, 103]).1 (Array.replicate 13 999)).1
  let (suffix, finish) := storeStream populated #[90, 91, 92]
  let mut checks := []
  for count in [:17] do
    let decls := wireDeclarations count
    checks := checks ++ [(s!"{label} declaration prefix {count}: exact codec/order/stores/suffix/state",
      declarationAgreement compiled suffix decls finish),
      (s!"{label} declaration prefix {count}: unreadable full-field suffix is not loaded",
        declarationAgreement compiled populated decls (.ofNat (goldilocksModulus - 1)))]
  return checks

private def declarationChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let code ← declarationCode compiled
  let mut checks : List Check := []
  let decls := wireDeclarations 16
  let (suffix, finish) := storeStream initial #[90, 91, 92]
  for fields in [:17] do
    checks := checks ++ [(s!"declaration parser accepts exact supported arity {fields}",
      declarationAgreement compiled suffix [wireDeclaration 0 fields] finish)]
  let baseline := wireDeclaration 0 0
  let variants := [
    { baseline with a := wordBytes 0 }, { baseline with b := wordBytes 0 },
    { baseline with c := wordBytes 0 }, { baseline with d := wordBytes 0 },
    { baseline with e := wordBytes 0 }, { baseline with f := wordBytes 0 },
    { baseline with g := wordBytes 0 }, { baseline with h := wordBytes 0 },
    { baseline with member := wordBytes 0 }, { baseline with tag := wordBytes 0 }]
  for (different, limb) in variants.zipIdx do
    checks := checks ++ [(s!"declaration parser retains distinct semantic ID limb {limb}",
      declarationAgreement compiled suffix [baseline, different] finish)]
  let zero := wordBytes 0
  let high := wordBytes (2 ^ 32 - 1)
  let smallest : DeclarationBytes := ⟨zero, zero, zero, zero, zero, zero, zero, zero, zero, zero, zero⟩
  let largest : DeclarationBytes := ⟨high, high, high, high, high, high, high, high, high, high, wordBytes 16⟩
  checks := checks ++ [("declaration parser retains complete zero and maximal 256-bit identities",
    declarationAgreement compiled suffix [smallest, largest] finish)]
  for count in [1:17] do
    let sample := wireDeclarations count
    for position in [:count] do
      for fields in [17, 2 ^ 32 - 1] do
        let changed := sample.toArray.modify position (fun d => { d with fields := wordBytes fields })
        let (st, pointer) := storePrefix suffix (declarationPayload changed.toList) finish
        checks := checks ++ [(s!"declaration arity {fields} rejected at {position}/{count}",
          failed (snapshot compiled `is_read_ctors #[pointer, .ofNat count] st (count + 2)) .assertFailed)]
  for first in [:16] do
    for second in [first + 1:16] do
      let original := decls.toArray
      let changed := original.modify second (fun d => { original.getD first (wireDeclaration 0 0) with fields := d.fields })
      let (st, pointer) := storePrefix suffix (declarationPayload changed.toList) finish
      checks := checks ++ [(s!"semantic duplicate rejected at pair {first}/{second}, independent of field count",
        failed (snapshot compiled `is_read_ctors #[pointer, 16] st 18) .assertFailed)]
  let sample := wireDeclarations 3
  let payload := declarationPayload sample
  for length in [:payload.size] do
    let (st, pointer) := storeStream initial (payload.extract 0 length)
    checks := checks ++ [(s!"declaration parser rejects {length}/132-byte truncation",
      failed (snapshot compiled `is_read_ctors #[pointer, 3] st 5) .unreachableAfterLayout)]
  for position in [:payload.size] do
    let (tailState, tail) := storePrefix suffix (payload.extract (position + 1) payload.size) finish
    let (badState, bad) := memStore tailState #[2, payload.getD position 0, tail]
    let (st, pointer) := storePrefix badState (payload.extract 0 position) (.ofNat bad)
    checks := checks ++ [(s!"declaration parser rejects malformed byte tag at {position}/132",
      failed (snapshot compiled `is_read_ctors #[pointer, 3] st 5) .unreachableAfterLayout)]
  for count in [0, 1, 3, 16] do
    let sample := wireDeclarations count
    let stored := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations suffix sample
    let (st, pointer) := storePrefix stored.1 (declarationPayload sample) finish
    checks := checks ++ [(s!"declaration parser reuses every existing table cell at length {count}",
      match snapshot compiled `is_read_ctors #[pointer, .ofNat count] st (count + 2) with
      | .ok (out, after) => out == #[stored.2, finish] && unchanged st after
      | _ => false)]
    let caller := { st with map := #[999, pointer, .ofNat count, 888] }
    for flag in [false, true] do
      checks := checks ++ [(s!"declaration Call preserves caller registers/memory/io {count}/{flag}",
        match Aiur.Bytecode.Eval.evalOp compiled.bytecode (count + 3) (.call code.self #[1, 2] 2 flag) caller with
        | .ok after => after.map == caller.map ++ #[stored.2, finish] && unchanged caller after | _ => false)]
  let (st, pointer) := storePrefix suffix (declarationPayload sample) finish
  let caller := { st with map := #[999, pointer, 3, 888] }
  let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations st sample
  for flag in [false, true] do
    checks := checks ++ [(s!"declaration Call performs exact new stores/{flag}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 6 (.call code.self #[1, 2] 2 flag) caller with
      | .ok after => after.map == caller.map ++ #[expected.2, finish] && memoryView after == memoryView expected.1 &&
          preservesReads caller after && sameIo caller after
      | _ => false)]
  for (label, fuel, args, outputs, error) in [
      ("input arity", 6, #[1], 2, BytecodeError.arityMismatch code.self),
      ("missing argument", 6, #[1, 99], 2, .invalidValIdx 99),
      ("output arity", 6, #[1, 2], 1, .callOutputSizeMismatch),
      ("no call fuel", 0, #[1, 2], 2, .outOfFuel),
      ("insufficient nested fuel", 1, #[1, 2], 2, .outOfFuel)] do
    checks := checks ++ [("declaration Call rejects " ++ label,
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call code.self args outputs false) caller with
      | .error actual => reprStr actual == reprStr error | _ => false)]
  for fuel in [0, 1, 2] do
    checks := checks ++ [(s!"declaration body rejects insufficient call depth {fuel}",
      failed (snapshot compiled `is_read_ctors #[pointer, 3] st fuel) .outOfFuel)]
  checks := checks ++ [("declaration input pointer is never narrowed to u32",
    failed (snapshot compiled `is_read_ctors #[.ofNat (2 ^ 32 + pointer.n), 3] st 5) (.invalidPointer 3 (2 ^ 32 + pointer.n)))]
  let tooMany := wireDeclarations 17
  let (largeState, largePointer) := storePrefix suffix (declarationPayload tooMany) finish
  checks := checks ++ [("constructor-count admission is separate from this parser body",
    match snapshot compiled `is_read_ctors #[largePointer, 17] largeState 19 with
    | .ok (out, after) => out[1]? == some finish && (readTable (bytecodeMemory after) (out.getD 0 0).n 17).isNone
    | _ => false)]
  let forged := (declarationPayload [wireDeclaration 0 0]).set! 40 (.ofNat (2 ^ 32))
  let (rawState, rawPointer) := storePrefix suffix forged finish
  checks := checks ++ [("genuine-byte admission is essential: forged arity wraps the u32 comparison",
    match snapshot compiled `is_read_ctors #[rawPointer, 1] rawState 3 with
    | .ok (out, after) => out[1]? == some finish && (readTable (bytecodeMemory after) (out.getD 0 0).n 1).isNone
    | _ => false)]
  let (_, cmp) ← function compiled `is_id_eq
  let fakeCmp := { cmp with body := (⟨#[.const 0], .return 0 #[20]⟩ : Aiur.Bytecode.Block) }
  let fake := { compiled with bytecode := { compiled.bytecode with functions := compiled.bytecode.functions.set! code.comparer fakeCmp } }
  let duplicate := [wireDeclaration 0 0, wireDeclaration 0 16]
  let (dupState, dupPointer) := storePrefix suffix (declarationPayload duplicate) finish
  checks := checks ++ [("full parser code certificate must include its actual comparator",
    !checkDeclarationCode fake.bytecode code &&
      match snapshot fake `is_read_ctors #[dupPointer, 2] dupState 4 with
      | .ok (out, after) => out[1]? == some finish && (readTable (bytecodeMemory after) (out.getD 0 0).n 2).isNone
      | _ => false)]
  return checks

private def loaderCode (compiled : Aiur.CompiledToplevel) : Except String LoaderCode := do
  let (reader, _) ← function compiled `ib_read_advice
  let (loader, _) ← function compiled `ib_load
  return { reader, loader }

private def loaderCertificates (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
  let code ← loaderCode compiled
  let (_, reader) ← function compiled `ib_read_advice
  let (_, loader) ← function compiled `ib_load
  let zero := adviceZero 0
  let step := adviceStep code.reader 1
  let body := adviceBody code.reader 0 1
  let loadBlock := loadBody code.reader 0
  let fixture := fun zero step => (⟨#[], .match 2 #[(0, zero)] (some step)⟩ : Aiur.Bytecode.Block)
  let accepts := fun body => checkAdviceReader { reader with body } code.reader 0 1
  let loadAccepts := fun body => checkLoader { loader with body } code.reader 0
  let mut checks : List Check := [
    ("complete compiled advice-reader certificate", accepts reader.body),
    ("complete compiled loader certificate", loadAccepts loader.body),
    ("loader bundle links its actual recursive reader", checkLoaderCode compiled.bytecode code),
    ("advice certificate rejects wrong arity", !checkAdviceReader
      { reader with layout := { reader.layout with inputSize := 2 } } code.reader 0 1),
    ("loader certificate rejects wrong arity", !checkLoader
      { loader with layout := { loader.layout with inputSize := 3 } } code.reader 0),
    ("advice certificate ignores evaluator-irrelevant metadata", checkAdviceReader
      { reader with layout := { reader.layout with auxiliaries := 999, lookups := 888 }, constrained := false } code.reader 0 1),
    ("loader certificate ignores evaluator-irrelevant metadata", checkLoader
      { loader with layout := { loader.layout with auxiliaries := 999, lookups := 888 }, constrained := false } code.reader 0),
    ("advice certificate binds root operations", !accepts { body with ops := #[.const 0] }),
    ("advice certificate binds counter", !accepts ⟨#[], .match 1 #[(0, zero)] (some step)⟩),
    ("advice certificate binds zero tag", !accepts ⟨#[], .match 2 #[(1, zero)] (some step)⟩),
    ("advice certificate rejects extra arm", !accepts ⟨#[], .match 2 #[(0, zero), (1, zero)] (some step)⟩),
    ("advice certificate rejects missing zero arm", !accepts ⟨#[], .match 2 #[] (some step)⟩),
    ("advice certificate rejects missing recursive branch", !accepts ⟨#[], .match 2 #[(0, zero)] none⟩),
    ("advice certificate rejects zero yield", !accepts (fixture { zero with ctrl := .yield 0 #[5] } step)),
    ("advice certificate rejects recursive yield", !accepts (fixture zero { step with ctrl := .yield 1 #[11] })),
    ("advice certificate binds zero output", !accepts (fixture { zero with ctrl := .return 0 #[4] } step)),
    ("advice certificate binds recursive output", !accepts (fixture zero { step with ctrl := .return 1 #[9] })),
    ("advice certificate rejects extra zero output", !accepts (fixture { zero with ctrl := .return 0 #[5, 0] } step)),
    ("advice certificate rejects extra recursive output", !accepts (fixture zero { step with ctrl := .return 1 #[11, 0] })),
    ("advice certificate binds zero selector", !accepts (fixture { zero with ctrl := .return 1 #[5] } step)),
    ("advice certificate binds recursive selector", !accepts (fixture zero { step with ctrl := .return 0 #[11] })),
    ("advice certificate rejects extra zero op", !accepts (fixture { zero with ops := zero.ops.push (.const 0) } step)),
    ("advice certificate rejects extra recursive op", !accepts (fixture zero { step with ops := step.ops.push (.const 0) })),
    ("advice selectors are explicit parameters", checkAdviceReader
      { reader with body := adviceBody code.reader 7 8 } code.reader 7 8),
    ("loader selector is an explicit parameter", checkLoader { loader with body := loadBody code.reader 9 } code.reader 9),
    ("loader certificate rejects yield", !loadAccepts { loadBlock with ctrl := .yield 0 #[9] }),
    ("loader certificate binds output", !loadAccepts { loadBlock with ctrl := .return 0 #[4] }),
    ("loader certificate rejects extra output", !loadAccepts { loadBlock with ctrl := .return 0 #[9, 0] }),
    ("loader certificate binds selector", !loadAccepts { loadBlock with ctrl := .return 1 #[9] }),
    ("loader certificate rejects extra operation", !loadAccepts { loadBlock with ops := loadBlock.ops.push (.const 0) })]
  for i in [:zero.ops.size] do
    checks := checks ++ [(s!"advice certificate binds zero operation {i}",
      !accepts (fixture { zero with ops := zero.ops.set! i (.const 999) } step))]
  for i in [:step.ops.size] do
    checks := checks ++ [(s!"advice certificate binds recursive operation {i}",
      !accepts (fixture zero { step with ops := step.ops.set! i (.const 999) }))]
  for i in [:loadBlock.ops.size] do
    checks := checks ++ [(s!"loader certificate binds operation {i}", !loadAccepts { loadBlock with ops := loadBlock.ops.set! i (.const 999) })]
  for i in [:3] do
    checks := checks ++ [
      (s!"advice certificate binds Nil store argument {i}", !accepts (fixture
        { zero with ops := zero.ops.set! 2 (.store (#[3, 4, 4].set! i 99)) } step)),
      (s!"advice certificate binds recursive Call argument {i}", !accepts (fixture zero
        { step with ops := step.ops.set! 7 (.call code.reader (#[0, 6, 8].set! i 99) 1 false) })),
      (s!"advice certificate binds Cons store argument {i}", !accepts (fixture zero
        { step with ops := step.ops.set! 9 (.store (#[10, 3, 9].set! i 99)) })),
      (s!"loader certificate binds reader Call argument {i}", !loadAccepts
        { loadBlock with ops := loadBlock.ops.set! 7 (.call code.reader (#[0, 3, 4].set! i 99) 1 false) })]
  for (label, op) in [
      ("I/O channel", Aiur.Bytecode.Op.ioRead 2 1 1), ("I/O address", .ioRead 0 2 1),
      ("I/O width", .ioRead 0 1 2)] do
    checks := checks ++ [("advice certificate binds " ++ label, !accepts (fixture zero { step with ops := step.ops.set! 0 op }))]
  for (label, index, op) in [
      ("range-check payload", 2, Aiur.Bytecode.Op.u8RangeCheck 4 4),
      ("range-check padding", 2, .u8RangeCheck 3 3),
      ("recursive callee", 7, .call code.loader #[0, 6, 8] 1 false),
      ("recursive output size", 7, .call code.reader #[0, 6, 8] 2 false),
      ("recursive constraint flag", 7, .call code.reader #[0, 6, 8] 1 true)] do
    checks := checks ++ [("advice certificate binds " ++ label,
      !accepts (fixture zero { step with ops := step.ops.set! index op }))]
  for (label, index, op) in [
      ("metadata channel", 1, Aiur.Bytecode.Op.ioGetInfo 1 #[2]),
      ("metadata key", 1, .ioGetInfo 0 #[1]),
      ("length comparison", 4, .u32LessThan 6 4),
      ("assertion message", 6, .assertEq #[7] #[8] (some "changed")),
      ("callee", 7, .call code.loader #[0, 3, 4] 1 false),
      ("output size", 7, .call code.reader #[0, 3, 4] 2 false),
      ("constraint flag", 7, .call code.reader #[0, 3, 4] 1 true)] do
    checks := checks ++ [("loader certificate binds " ++ label, !loadAccepts { loadBlock with ops := loadBlock.ops.set! index op })]
  for (label, index) in [("reader", code.reader), ("loader", code.loader)] do
    let some f := compiled.bytecode.functions[index]? | throw "missing loader bundle callee"
    let changed := { f with body := { f.body with ops := f.body.ops.push (.const 999) } }
    checks := checks ++ [("loader bundle rejects changed " ++ label, !checkLoaderCode
      { compiled.bytecode with functions := compiled.bytecode.functions.set! index changed } code)]
  for changed in [{ code with reader := compiled.bytecode.functions.size }, { code with loader := compiled.bytecode.functions.size }] do
    checks := checks ++ [("loader bundle rejects missing function", !checkLoaderCode compiled.bytecode changed)]
  return checks

private def streamMatches (st : EvalState) (pointer : Aiur.G) : List Aiur.G → Bool
  | [] => match memLoad st 3 pointer.n with | .ok cell => cell == #[1, 1, 1] | _ => false
  | value :: values =>
    match memLoad st 3 pointer.n with
    | .ok cell => match cell.toList with
      | [tag, head, tail] => tag == 0 && head == value && streamMatches st tail values
      | _ => false
    | _ => false

private def skipStream (st : EvalState) (pointer : Aiur.G) : Nat → Option Aiur.G
  | 0 => some pointer
  | count + 1 => do
    let .ok cell := memLoad st 3 pointer.n | none
    let [tag, _, tail] := cell.toList | none
    if tag == 0 then skipStream st tail count else none

private def rawAdvice (st : EvalState) (channel : Aiur.G) (start length : Nat) (values : Array Aiur.G) : EvalState :=
  { st with ioBuffer := {
      data := st.ioBuffer.data.insert channel values,
      map := st.ioBuffer.map.insert (channel, #[0]) ⟨start, length⟩ } }

private def loadAgreement (compiled : Aiur.CompiledToplevel) (base : EvalState) (channel : Aiur.G)
    (values : Array Aiur.G) (limit : Nat) : Bool := Id.run do
  -- Both unread parts deliberately contain non-bytes; only the registered
  -- slice is admitted. Same-channel and other-channel prior data is retained.
  let before := base.ioBuffer.extend channel #[88] #[256, .ofNat (goldilocksModulus - 1)]
  let ready := { base with ioBuffer := (before.extend channel #[0] values).extend channel #[99] #[65536] }
  let start := (before.data.getD channel #[]).size
  let expected := Ix.Ixby.AiurBackend.Objects.Admission.storeAdvice ready values.toList
  match snapshot compiled `ib_load #[channel, .ofNat limit] ready (values.size + 1) with
  | .error _ => return false
  | .ok (out, after) =>
    return out == #[expected.2] && memoryView after == memoryView expected.1 &&
      after.map == loadRegisters channel start values.size limit ++ #[expected.2] &&
      streamMatches after expected.2 values.toList && preservesReads ready after && sameIo ready after &&
      Ix.Ixby.AiurBackend.Objects.Store.bucketSize after 3 ≤ Ix.Ixby.AiurBackend.Objects.Store.bucketSize ready 3 + values.size + 1 &&
      [0, 1, 5, 13, 17].all (fun width => Ix.Ixby.AiurBackend.Objects.Store.bucketSize after width == Ix.Ixby.AiurBackend.Objects.Store.bucketSize ready width)

private def loaderSuccessChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let populated := (memStore (memStore (memStore initial #[123, 234, 345]).1
    (Array.replicate 13 777)).1 (Array.replicate 5 888)).1
  let mut checks : List Check := []
  for channel in [(0 : Aiur.G), 1, .ofNat (goldilocksModulus - 1)] do
    for n in [0, 1, 2, 3, 16, 17, 255, 256, 257, 704] do
      let values := (Array.range n).map (fun i => Aiur.G.ofNat (i % 256))
      for limit in [n, n + 1] do
        checks := checks ++ [(s!"{label} loader slice/channel{channel.n}/length{n}/limit{limit}: exact stores/bytes/registers/resources",
          loadAgreement compiled populated channel values limit)]
  for byte in [:256] do
    checks := checks ++ [(s!"{label} loader admits exact byte {byte}", loadAgreement compiled populated 0 #[.ofNat byte] 1)]
  for n in [0, 1, 3, 16, 257] do
    let values := (Array.range n).map (fun i => Aiur.G.ofNat (i % 2))
    let ready := rawAdvice populated 0 0 n values
    let first := snapshot compiled `ib_load #[0, .ofNat n] ready (n + 1)
    checks := checks ++ [(s!"{label} loader reparsing deduplicates all cells/{n}", match first with
      | .ok (out, after) => success (snapshot compiled `ib_load #[0, .ofNat n] after (n + 1)) out after
      | _ => false)]
  return checks

private def loaderFailureChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let code ← loaderCode compiled
  let values := (Array.range 33).map (fun i => Aiur.G.ofNat i)
  let mut checks : List Check := []
  for position in [:values.size] do
    for invalid in [256, 65536, 2 ^ 32, goldilocksModulus - 1] do
      let ready := rawAdvice initial 0 0 values.size (values.set! position (.ofNat invalid))
      checks := checks ++ [(s!"{label} loader rejects non-byte {invalid} at {position}",
        failed (snapshot compiled `ib_load #[0, .ofNat values.size] ready (values.size + 1)) .u8RangeCheckFailed)]
  for length in [:values.size] do
    let ready := rawAdvice initial 0 0 values.size (values.extract 0 length)
    checks := checks ++ [(s!"{label} loader rejects truncated arena at {length}",
      failed (snapshot compiled `ib_load #[0, .ofNat values.size] ready (values.size + 1)) .ioReadOoB)]
  for n in [1, 16, 65535, 2 ^ 32 - 1] do
    checks := checks ++ [(s!"{label} length guard rejects before any arena access or Call fuel/{n}",
      failed (snapshot compiled `ib_load #[0, .ofNat (n - 1)] (rawAdvice initial 0 0 n #[]) 0) .assertFailed)]
  checks := checks ++ [
    (s!"{label} loader rejects missing metadata", failed (snapshot compiled `ib_load #[0, 1] initial 1) .ioKeyNotFound),
    (s!"{label} loader does not borrow another channel's metadata", failed
      (snapshot compiled `ib_load #[1, 1] (rawAdvice initial 0 0 1 #[7]) 1) .ioKeyNotFound),
    (s!"{label} invalid next field fails without tail availability or Call fuel", failed
      (snapshot compiled `ib_read_advice #[0, 0, 2] (rawAdvice initial 0 0 2 #[256]) 0) .u8RangeCheckFailed),
    (s!"{label} zero reader touches no advice and needs no Call fuel",
      match snapshot compiled `ib_read_advice #[0, .ofNat (goldilocksModulus - 1), 0] initial 0 with
      | .ok (out, after) => out.size == 1 && streamMatches after (out.getD 0 0) [] && sameIo initial after
      | _ => false)]
  for n in [0, 1, 8] do
    let ready := rawAdvice initial 0 0 n (Array.replicate n 7)
    checks := checks ++ [
      (s!"{label} loader minimum body fuel/{n}", (snapshot compiled `ib_load #[0, .ofNat n] ready (n + 1)).isOk),
      (s!"{label} loader insufficient body fuel/{n}", failed (snapshot compiled `ib_load #[0, .ofNat n] ready n) .outOfFuel)]
  for idx in [2 ^ 32, goldilocksModulus - 1] do
    checks := checks ++ [(s!"{label} I/O address is not narrowed to UInt32/{idx}", failed
      (snapshot compiled `ib_load #[0, 1] (rawAdvice initial 0 idx 1 #[7]) 2) .ioReadOoB)]
  for (start, length, limit, expected) in [
      (goldilocksModulus, 1, 1, [7]), (0, goldilocksModulus, 0, []), (0, goldilocksModulus + 1, 1, [7])] do
    let ready := rawAdvice initial 0 start length #[7]
    checks := checks ++ [(s!"{label} forged natural metadata demonstrates field-wrap premise/{start}/{length}",
      match snapshot compiled `ib_load #[0, .ofNat limit] ready 2 with
      | .ok (out, after) => out.size == 1 && streamMatches after (out.getD 0 0) (expected.map Aiur.G.ofNat)
      | _ => false)]
  checks := checks ++ [
    (s!"{label} non-u32 length can pass the guard then fail I/O", failed
      (snapshot compiled `ib_load #[0, 0] (rawAdvice initial 0 0 (2 ^ 32) #[]) 1) .ioReadOoB),
    (s!"{label} UInt32 limit-plus-one wrap rejects even zero bytes", failed
      (snapshot compiled `ib_load #[0, .ofNat (2 ^ 32 - 1)] (rawAdvice initial 0 0 0 #[]) 1) .assertFailed)]
  let caller := { rawAdvice initial 0 0 3 #[0, 127, 255] with map := #[999, 0, 3, 888] }
  let expected := Ix.Ixby.AiurBackend.Objects.Admission.storeAdvice caller [0, 127, 255]
  for flag in [false, true] do
    checks := checks ++ [(s!"{label} loader Call preserves exact caller registers/{flag}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode 5 (.call code.loader #[1, 2] 1 flag) caller with
      | .ok after => after.map == caller.map ++ #[expected.2] && memoryView after == memoryView expected.1 &&
        streamMatches after expected.2 [0, 127, 255] && preservesReads caller after && sameIo caller after
      | _ => false)]
  for (desc, fuel, args, outputs, error) in [
      ("arity", 5, #[1], 1, BytecodeError.arityMismatch code.loader),
      ("missing argument", 5, #[1, 99], 1, .invalidValIdx 99),
      ("output arity", 5, #[1, 2], 2, .callOutputSizeMismatch),
      ("no fuel", 0, #[1, 2], 1, .outOfFuel),
      ("insufficient nested fuel", 4, #[1, 2], 1, .outOfFuel)] do
    checks := checks ++ [(s!"{label} loader Call rejects {desc}",
      match Aiur.Bytecode.Eval.evalOp compiled.bytecode fuel (.call code.loader args outputs false) caller with
      | .error actual => reprStr actual == reprStr error
      | _ => false)]
  return checks

private def loadedDeclarationChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let suffix : Array Aiur.G := #[90, 91, 92]
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    let raw := declarationPayload decls ++ suffix
    let ready := rawAdvice initial 0 0 raw.size raw
    checks := checks ++ [(s!"{label} actual loader supplies declaration prefix/{count}",
      match snapshot compiled `ib_load #[0, .ofNat raw.size] ready (raw.size + 1) with
      | .ok (loadOut, loaded) =>
        let pointer := loadOut.getD 0 0
        let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations loaded decls
        match skipStream loaded pointer (44 * count), snapshot compiled `is_read_ctors #[pointer, .ofNat count] loaded (count + 2) with
        | some finish, .ok (out, parsed) =>
          out == #[expected.2, finish] && streamMatches parsed finish suffix.toList &&
          readTable (bytecodeMemory parsed) expected.2.n count == some (decls.map DeclarationBytes.declaration).toArray &&
          memoryView parsed == memoryView expected.1 && preservesReads ready parsed && sameIo ready parsed &&
          Ix.Ixby.AiurBackend.Objects.Store.bucketSize loaded 13 == Ix.Ixby.AiurBackend.Objects.Store.bucketSize ready 13
        | _, _ => false
      | _ => false)]
  for position in [:16] do
    for (desc, decls) in [
        ("unsupported arity", (wireDeclarations 16).set position (wireDeclaration position 17)),
        ("duplicate full ID", (wireDeclarations 16).set position (wireDeclaration ((position + 1) % 16) 16))] do
      let raw := declarationPayload decls ++ suffix
      let ready := rawAdvice initial 0 0 raw.size raw
      checks := checks ++ [(s!"{label} loaded declaration rejects {desc} at {position}",
        match snapshot compiled `ib_load #[0, .ofNat raw.size] ready (raw.size + 1) with
        | .ok (out, loaded) => failed (snapshot compiled `is_read_ctors #[out.getD 0 0, 16] loaded 18) .assertFailed
        | _ => false)]
  let forged := (declarationPayload [wireDeclaration 0 0]).set! 40 (.ofNat (2 ^ 32))
  checks := checks ++ [(s!"{label} loader closes the forged non-byte arity counterexample", failed
    (snapshot compiled `ib_load #[0, 44] (rawAdvice initial 0 0 44 forged) 45) .u8RangeCheckFailed)]
  return checks

namespace ProgramPrefixTests
open Ix.Ixby.AiurBackend.Objects.ProgramPrefix

private def code (compiled : Aiur.CompiledToplevel) : Except String ProgramCode := do
  let (runner, _) ← function compiled `is_run
  return { runner, declarations := ← declarationCode compiled }

private def wireHeader (entry count : Nat) (revision := 0) : HeaderBytes :=
  ⟨⟨73, 88, 66, 89⟩, wordBytes revision, wordBytes entry, wordBytes count⟩

private def payload (h : HeaderBytes) (decls : List DeclarationBytes) : Array Aiur.G :=
  h.bytes.toArray.map Aiur.G.ofUInt8 ++ declarationPayload decls

/-- Run the actual compiled sixty operations, not the certificate's model. -/
private def prefixSnapshot (compiled : Aiur.CompiledToplevel) (st : EvalState)
    (program input : Aiur.G) (fuel : Nat) : Except String (Array Aiur.G × EvalState) := do
  let (_, runner) ← function compiled `is_run
  match runOps compiled.bytecode fuel (runner.body.ops.toList.take 60).toArray { st with map := #[program, input] } 0 with
  | .ok after => return (#[after.map.getD 48 0, after.map.getD 65 0, after.map.getD 71 0,
      after.map.getD 72 0, after.map.getD 0 0, after.map.getD 1 0], after)
  | .error error => throw (reprStr error)

private def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let pc ← code compiled
  let (_, runner) ← function compiled `is_run
  let accepts := fun f => checkProgramPrefix f pc.declarations.reader pc.declarations.self
  let prefixBody := programPrefixOps pc.declarations.reader pc.declarations.self
  let mut checks : List Check := [
    (s!"{label} actual program prefix certificate", accepts runner),
    (s!"{label} program bundle resolves all six actual functions", checkProgramCode compiled.bytecode pc),
    (s!"{label} prefix is exactly sixty operations", prefixBody.size == 60),
    (s!"{label} prefix binds input arity", !accepts { runner with layout := { runner.layout with inputSize := 1 } }),
    (s!"{label} prefix accepts evaluator-irrelevant metadata", accepts { runner with
      layout := { runner.layout with lookups := 777, auxiliaries := 888 }, constrained := false }),
    (s!"{label} prefix does not certify final control", accepts { runner with body := { runner.body with ctrl := .return 0 #[0] } }),
    (s!"{label} prefix allows an empty continuation", accepts { runner with body := ⟨prefixBody, .return 0 #[0]⟩ }),
    (s!"{label} prefix binds byte callee", !checkProgramPrefix runner (pc.declarations.reader + 1) pc.declarations.self),
    (s!"{label} prefix binds declaration callee", !checkProgramPrefix runner pc.declarations.reader (pc.declarations.self + 1)),
    (s!"{label} prefix bundle rejects missing runner", !checkProgramCode compiled.bytecode { pc with runner := compiled.bytecode.functions.size })]
  for i in [:60] do
    checks := checks ++ [
      (s!"{label} prefix binds operation/{i}", !accepts { runner with body := { runner.body with ops := runner.body.ops.set! i (.const 1234567) } }),
      (s!"{label} prefix rejects short body/{i}", !accepts { runner with body := { runner.body with ops := (prefixBody.toList.take i).toArray } })]
    match prefixBody.getD i (.const 0) with
    | .call callee args outputs flag =>
      for (desc, op) in [("callee", .call (callee + 1) args outputs flag),
          ("arguments", .call callee (args.set! 0 1) outputs flag),
          ("outputs", .call callee args (outputs + 1) flag), ("flag", .call callee args outputs (!flag))] do
        checks := checks ++ [(s!"{label} prefix binds call {desc}/{i}",
          !accepts { runner with body := { runner.body with ops := runner.body.ops.set! i op } })]
    | _ => pure ()
  for i in [60:runner.body.ops.size] do
    checks := checks ++ [(s!"{label} prefix deliberately leaves suffix operation/{i} unrestricted",
      accepts { runner with body := { runner.body with ops := runner.body.ops.set! i (.const 1234567) } })]
  for name in [`is_run, `ib_byte, `is_read_id, `is_id_eq, `is_unique_id, `is_read_ctors] do
    let (index, f) ← function compiled name
    let changed := { f with body := { f.body with ops := #[.const 1234567] } }
    let bad := { compiled.bytecode with functions := compiled.bytecode.functions.set! index changed }
    checks := checks ++ [(s!"{label} prefix bundle binds actual function/{name}", !checkProgramCode bad pc)]
  let missing := compiled.bytecode.functions.size
  for (desc, changed) in [("byte", { pc.declarations with reader := missing }),
      ("identity", { pc.declarations with identity := missing }), ("comparer", { pc.declarations with comparer := missing }),
      ("unique", { pc.declarations with unique := missing }), ("declarations", { pc.declarations with self := missing })] do
    checks := checks ++ [(s!"{label} prefix bundle rejects missing/{desc}",
      !checkProgramCode compiled.bytecode { pc with declarations := changed })]
  let h := wireHeader (2 ^ 32 - 1) 0
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (2 ^ 32 + 19)
  let (st, pointer) := storePrefix initial (payload h []) finish
  let table := (Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations st []).2
  let postlude := { runner with body := (⟨prefixBody ++ #[.const 77], .return 0 #[48, 65, 71, 72, 0, 1, 73]⟩ : Aiur.Bytecode.Block) }
  let postProgram := { compiled with bytecode := { compiled.bytecode with functions := compiled.bytecode.functions.set! pc.runner postlude } }
  let badTail := { runner with body := (⟨prefixBody ++ #[.assertEq #[0] #[1] none], .return 0 #[0]⟩ : Aiur.Bytecode.Block) }
  let badProgram := { compiled with bytecode := { compiled.bytecode with functions := compiled.bytecode.functions.set! pc.runner badTail } }
  checks := checks ++ [
    (s!"{label} unrestricted continuation receives exact entry/count/table/suffix/program/input", accepts postlude &&
      match snapshot postProgram `is_run #[pointer, input] st 3 with
      | .ok (out, after) => out == #[h.entry.field, 0, table, finish, pointer, input, 77] && after.map.size == 74
      | _ => false),
    (s!"{label} certified prefix does not imply continuation success", accepts badTail &&
      failed (snapshot badProgram `is_run #[pointer, input] st 3) .assertFailed)]
  return checks

private def agreement (compiled : Aiur.CompiledToplevel) (base : EvalState) (h : HeaderBytes)
    (decls : List DeclarationBytes) (finish input : Aiur.G) : Bool :=
  let (st, pointer) := storePrefix base (payload h decls) finish
  let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations st decls
  let bytes := #[200, 201] ++ h.bytes.toArray ++ (decls.flatMap DeclarationBytes.bytes).toArray ++ #[90, 91, 92]
  let decoder : Codec.Internal.Decoder (Nat × Array CtorDecl) := do
    Codec.Internal.readHeader "IXBY"
    let entry ← Codec.Internal.readU32
    let table ← Codec.Internal.readVector 16 do
      let id ← Codec.Internal.readCtorId
      let fields ← Codec.Internal.readCount 16
      return ⟨id, fields⟩
    return (entry, table)
  match prefixSnapshot compiled st pointer input (decls.length + 3), decoder.run { bytes, offset := 2, nodes := 13 } with
  | .ok (out, after), .ok ((entry, table), rest) =>
    out == #[h.entry.field, h.constructors.field, expected.2, finish, pointer, input] && after.map.size == 73 &&
      entry == h.entry.field.n && table == (decls.map DeclarationBytes.declaration).toArray &&
      readTable (bytecodeMemory after) expected.2.n decls.length == some table &&
      memoryView after == memoryView expected.1 && preservesReads st after && sameIo st after &&
      Ix.Ixby.AiurBackend.Objects.Store.bucketSize after 13 ≤ Ix.Ixby.AiurBackend.Objects.Store.bucketSize st 13 + decls.length + 1 &&
      rest.offset == 18 + 44 * decls.length && rest.nodes == 13 && rest.bytes == bytes
  | _, _ => false

private def successChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    for entry in [0, 1, 2 ^ 31, 2 ^ 32 - 1] do
      checks := checks ++ [(s!"{label} program header/table exact state and codec/{count}/{entry}",
        agreement compiled initial (wireHeader entry count) decls finish input)]
    let existing := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations initial decls
    checks := checks ++ [(s!"{label} header/table handles content-deduplicated stores/{count}",
      agreement compiled existing.1 (wireHeader 7 count) decls finish input)]
  for bit in [:32] do
    checks := checks ++ [(s!"{label} entry retains bit/{bit}", agreement compiled initial (wireHeader (2 ^ bit) 0) [] finish input)]
  for value in [0, 2 ^ 32 + 7, goldilocksModulus - 1] do
    checks := checks ++ [(s!"{label} full-field input and suffix preserved/{value}",
      agreement compiled initial (wireHeader 0 1) (wireDeclarations 1) (.ofNat value) (.ofNat value))]
  return checks

private def failureChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let base := payload (wireHeader 0 0) []
  let mut checks : List Check := []
  for position in [:4] do
    for value in [:256] do
      let changed := base.set! position (.ofNat value)
      let (st, pointer) := storePrefix initial changed finish
      checks := checks ++ [(s!"{label} exact magic byte/{position}/{value}",
        if base.getD position 0 == Aiur.G.ofNat value then (prefixSnapshot compiled st pointer input 3).isOk
        else failed (snapshot compiled `is_run #[pointer, input] st 1) .assertFailed)]
  for revision in (List.range 32).map (2 ^ ·) ++ [2 ^ 32 - 1] do
    let (st, pointer) := storePrefix initial (payload (wireHeader 0 0 revision) []) finish
    checks := checks ++ [(s!"{label} nonzero revision rejects before declaration call/{revision}",
      failed (snapshot compiled `is_run #[pointer, input] st 1) .assertFailed)]
  for count in [17, 18, 255, 256, 65535, 65536, 2 ^ 31, 2 ^ 32 - 1] do
    let (st, pointer) := storePrefix initial (payload (wireHeader 0 count) []) finish
    checks := checks ++ [(s!"{label} oversized constructor count rejects before unreadable suffix/{count}",
      failed (snapshot compiled `is_run #[pointer, input] st 1) .assertFailed)]
  for position in [:16] do
    let (shortState, shortPointer) := storeStream initial (base.extract 0 position)
    let (tailState, tail) := storePrefix initial (base.extract (position + 1) base.size) finish
    let (badState, bad) := memStore tailState #[2, base.getD position 0, tail]
    let (st, pointer) := storePrefix badState (base.extract 0 position) (.ofNat bad)
    checks := checks ++ [
      (s!"{label} header rejects truncation/{position}", failed (prefixSnapshot compiled shortState shortPointer input 3) .unreachableAfterLayout),
      (s!"{label} header rejects malformed byte tag/{position}", failed (prefixSnapshot compiled st pointer input 3) .unreachableAfterLayout)]
  for position in [:16] do
    for (desc, decls) in [("arity", (wireDeclarations 16).set position (wireDeclaration position 17)),
        ("duplicate", (wireDeclarations 16).set position (wireDeclaration ((position + 1) % 16) 16))] do
      let (st, pointer) := storePrefix initial (payload (wireHeader 0 16) decls) finish
      checks := checks ++ [(s!"{label} header/declarations reject {desc}/{position}",
        failed (prefixSnapshot compiled st pointer input 19) .assertFailed)]
  for count in [1, 3, 16] do
    let (st, pointer) := storePrefix initial (payload (wireHeader 0 count) (wireDeclarations count)) finish
    checks := checks ++ [
      (s!"{label} prefix minimum nested call fuel/{count}", (prefixSnapshot compiled st pointer input (count + 2)).isOk),
      (s!"{label} prefix rejects insufficient nested call fuel/{count}", failed (prefixSnapshot compiled st pointer input (count + 1)) .outOfFuel)]
  let (st, pointer) := storeStream initial (base ++ #[0, 0, 0, 0])
  checks := checks ++ [
    (s!"{label} valid prefix does not admit missing function table", (prefixSnapshot compiled st pointer input 3).isOk &&
      failed (snapshot compiled `is_run #[pointer, input] st 3) .assertFailed),
    (s!"{label} header program pointer is not narrowed to u32", failed
      (prefixSnapshot compiled st (.ofNat (2 ^ 32 + pointer.n)) input 3) (.invalidPointer 3 (2 ^ 32 + pointer.n))),
    (s!"{label} header byte call requires fuel", failed (prefixSnapshot compiled st pointer input 0) .outOfFuel)]
  return checks

private def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let suffix : Array Aiur.G := #[90, 91, 92]
  let mut checks : List Check := []
  for count in [:17] do
    let h := wireHeader (2 ^ 32 - 1) count
    let decls := wireDeclarations count
    let raw := payload h decls ++ suffix
    let ready := rawAdvice initial 0 2 raw.size (#[256, 65536] ++ raw)
    checks := checks ++ [(s!"{label} actual loader to program prefix/{count}",
      match snapshot compiled `ib_load #[0, .ofNat raw.size] ready (raw.size + 1) with
      | .ok (loadedOut, loaded) =>
        let pointer := loadedOut.getD 0 0
        let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations loaded decls
        match skipStream loaded pointer (16 + 44 * count), prefixSnapshot compiled loaded pointer input (count + 3) with
        | some finish, .ok (out, after) =>
          out == #[h.entry.field, .ofNat count, expected.2, finish, pointer, input] && after.map.size == 73 &&
            readTable (bytecodeMemory after) expected.2.n count == some (decls.map DeclarationBytes.declaration).toArray &&
            memoryView after == memoryView expected.1 && streamMatches after finish suffix.toList &&
            preservesReads ready after && sameIo ready after &&
            Ix.Ixby.AiurBackend.Objects.Store.bucketSize loaded 13 == Ix.Ixby.AiurBackend.Objects.Store.bucketSize ready 13
        | _, _ => false
      | _ => false)]
  for (desc, raw) in [("magic", (payload (wireHeader 0 0) []).set! 0 0),
      ("revision", payload (wireHeader 0 0 1) []), ("count", payload (wireHeader 0 17) []),
      ("arity", payload (wireHeader 0 1) [wireDeclaration 0 17]),
      ("duplicate", payload (wireHeader 0 2) [wireDeclaration 0 0, wireDeclaration 0 16])] do
    let ready := rawAdvice initial 0 0 raw.size raw
    checks := checks ++ [(s!"{label} loaded program rejects/{desc}",
      match snapshot compiled `ib_load #[0, .ofNat raw.size] ready (raw.size + 1) with
      | .ok (out, loaded) => failed (prefixSnapshot compiled loaded (out.getD 0 0) input 5) .assertFailed
      | _ => false)]
  for position in [:16] do
    let forged := (payload (wireHeader 0 0) []).set! position (.ofNat (2 ^ 32))
    checks := checks ++ [(s!"{label} loader rejects non-byte header field/{position}", failed
      (snapshot compiled `ib_load #[0, 16] (rawAdvice initial 0 0 16 forged) 17) .u8RangeCheckFailed)]
  return checks

end ProgramPrefixTests

namespace CodeHeaderTests
open Ix.Ixby.AiurBackend.Objects.CodeHeaders

private def code (compiled : Aiur.CompiledToplevel) : Except String HeaderCode := do
  let program ← ProgramPrefixTests.code compiled
  let (functions, _) ← function compiled `is_read_functions
  let (blocks, _) ← function compiled `is_read_blocks
  let (instruction, _) ← function compiled `is_read_instr
  return { program, functions, blocks, instruction }

private def stepOf (f : Aiur.Bytecode.Function) : Except String Aiur.Bytecode.Block :=
  match f.body.ctrl with
  | .match _ _ (some step) => .ok step
  | _ => .error "missing nonzero branch"

private def withStep (f : Aiur.Bytecode.Function) (step : Aiur.Bytecode.Block) : Aiur.Bytecode.Function :=
  match f.body.ctrl with
  | .match index arms _ => { f with body := { f.body with ctrl := .match index arms (some step) } }
  | _ => f

/-- Observe only actual compiled operations, never substitute model op arrays. -/
private def observe (compiled : Aiur.CompiledToplevel) (name : Lean.Name) (count : Nat)
    (args : Array Aiur.G) (outputs : Array Nat) (st : EvalState) (fuel := 1) :
    Except String (Array Aiur.G × EvalState) := do
  let (_, f) ← function compiled name
  let body ← if name == `is_run then pure f.body else stepOf f
  match runOps compiled.bytecode fuel (body.ops.toList.take count).toArray { st with map := args } 0 with
  | .error error => throw (reprStr error)
  | .ok after =>
    match readIdxs after outputs with
    | .ok out => return (out, after)
    | .error error => throw (reprStr error)

private def wireFunction (arity entry blocks : Nat) : FunctionHeaderBytes :=
  ⟨wordBytes arity, wordBytes entry, wordBytes blocks⟩

private def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let hc ← code compiled
  let (_, runner) ← function compiled `is_run
  let (_, functions) ← function compiled `is_read_functions
  let (_, blocks) ← function compiled `is_read_blocks
  let (_, instruction) ← function compiled `is_read_instr
  let functionStep ← stepOf functions
  let blockStep ← stepOf blocks
  let byte := hc.program.declarations.reader
  let mut checks : List Check := [
    (s!"{label} complete code-header prefix bundle", checkHeaderCode compiled.bytecode hc),
    (s!"{label} program count prefix and next function Call", checkProgramHeaders runner hc),
    (s!"{label} function header, zero branch, and next block Call", checkListHeader functions 6 (functionHeaderOps byte) (blockCall hc.blocks)),
    (s!"{label} block header, zero branch, and next instruction Call", checkListHeader blocks 13 (blockHeaderOps byte) (instructionCall hc.instruction)),
    (s!"{label} program header prefix has eighty-three operations", (programHeadersOps byte hc.program.declarations.self).size == 83),
    (s!"{label} function header prefix has sixty operations", (functionHeaderOps byte).size == 60),
    (s!"{label} block header prefix has nineteen operations", (blockHeaderOps byte).size == 19)]
  for i in [:84] do
    checks := checks ++ [
      (s!"{label} code-header program certificate binds op/{i}", !checkProgramHeaders
        { runner with body := { runner.body with ops := runner.body.ops.set! i (.const 1234567) } } hc),
      (s!"{label} code-header program rejects short prefix/{i}", !checkProgramHeaders
        { runner with body := { runner.body with ops := (runner.body.ops.toList.take i).toArray } } hc)]
  for i in [84:runner.body.ops.size] do
    checks := checks ++ [(s!"{label} code-header program leaves later op/{i} unrestricted", checkProgramHeaders
      { runner with body := { runner.body with ops := runner.body.ops.set! i (.const 1234567) } } hc)]
  checks := checks ++ [(s!"{label} code-header program leaves final control unrestricted", checkProgramHeaders
    { runner with body := { runner.body with ctrl := .return 0 #[0] } } hc)]
  for (desc, f, step, width, headOps, next) in [
      ("function", functions, functionStep, 6, functionHeaderOps byte, blockCall hc.blocks),
      ("block", blocks, blockStep, 13, blockHeaderOps byte, instructionCall hc.instruction)] do
    let accepts := fun f => checkListHeader f width headOps next
    let certifiedSize := headOps.size + 1
    for i in [:certifiedSize] do
      checks := checks ++ [
        (s!"{label} {desc} header binds op/{i}", !accepts (withStep f { step with ops := step.ops.set! i (.const 1234567) })),
        (s!"{label} {desc} header rejects short prefix/{i}", !accepts (withStep f { step with ops := (step.ops.toList.take i).toArray }))]
      match step.ops.getD i (.const 0) with
      | .call callee args outputs flag =>
        for (change, op) in [("callee", .call (callee + 1) args outputs flag),
            ("argument", .call callee (args.set! 0 1) outputs flag),
            ("outputs", .call callee args (outputs + 1) flag), ("flag", .call callee args outputs (!flag))] do
          checks := checks ++ [(s!"{label} {desc} header binds Call {change}/{i}",
            !accepts (withStep f { step with ops := step.ops.set! i op }))]
      | _ => pure ()
    for i in [certifiedSize:step.ops.size] do
      checks := checks ++ [(s!"{label} {desc} header leaves later op/{i} unrestricted",
        accepts (withStep f { step with ops := step.ops.set! i (.const 1234567) }))]
    let zero := emptyListBranch width
    for i in [:3] do
      let badZero := { zero with ops := zero.ops.set! i (.const 1234567) }
      checks := checks ++ [(s!"{label} {desc} zero branch binds operation/{i}", !accepts { f with body :=
        ⟨#[], .match 1 #[(0, badZero)] (some step)⟩ })]
    let indices := #[3] ++ Array.replicate (width - 1) 4
    for i in [:width] do
      let badZero := { zero with ops := #[.const 1, .const 1, .store (indices.set! i 0)] }
      checks := checks ++ [(s!"{label} {desc} zero branch binds Nil padding/{i}", !accepts { f with body :=
        ⟨#[], .match 1 #[(0, badZero)] (some step)⟩ })]
    checks := checks ++ [
      (s!"{label} {desc} header binds input arity", !accepts { f with layout := { f.layout with inputSize := 2 } }),
      (s!"{label} {desc} header ignores irrelevant layout", accepts { f with
        layout := { f.layout with lookups := 777, auxiliaries := 888 }, constrained := false }),
      (s!"{label} {desc} header binds root ops", !accepts { f with body := { f.body with ops := #[.const 0] } }),
      (s!"{label} {desc} header binds dispatch counter", !accepts { f with body := ⟨#[], .match 2 #[(0, zero)] (some step)⟩ }),
      (s!"{label} {desc} header binds zero tag", !accepts { f with body := ⟨#[], .match 1 #[(1, zero)] (some step)⟩ }),
      (s!"{label} {desc} header rejects extra branch", !accepts { f with body := ⟨#[], .match 1 #[(0, zero), (1, zero)] (some step)⟩ }),
      (s!"{label} {desc} header requires default branch", !accepts { f with body := ⟨#[], .match 1 #[(0, zero)] none⟩ }),
      (s!"{label} {desc} header binds zero return", !accepts { f with body := ⟨#[], .match 1
        #[(0, { zero with ctrl := .return 1 #[0, 5] })] (some step)⟩ }),
      (s!"{label} {desc} header rejects zero yield", !accepts { f with body := ⟨#[], .match 1
        #[(0, { zero with ctrl := .yield 0 #[5, 0] })] (some step)⟩ }),
      (s!"{label} {desc} header does not certify step control", accepts (withStep f { step with ctrl := .return 0 #[0] }))]
  for name in [`is_run, `ib_byte, `is_read_id, `is_id_eq, `is_unique_id, `is_read_ctors, `is_read_functions, `is_read_blocks] do
    let (index, f) ← function compiled name
    let bad := { compiled.bytecode with functions := compiled.bytecode.functions.set! index { f with body := { f.body with ops := #[.const 1234567] } } }
    checks := checks ++ [(s!"{label} code-header bundle binds function/{name}", !checkHeaderCode bad hc)]
  let missing := compiled.bytecode.functions.size
  for (desc, changed) in [("functions", { hc with functions := missing }), ("blocks", { hc with blocks := missing })] do
    checks := checks ++ [(s!"{label} code-header bundle rejects missing/{desc}", !checkHeaderCode compiled.bytecode changed)]
  let arbitraryInstruction := { instruction with body := (⟨#[.const 77], .return 0 (Array.replicate 10 3 ++ #[0])⟩ : Aiur.Bytecode.Block) }
  let changedInstruction := { compiled.bytecode with functions := compiled.bytecode.functions.set! hc.instruction arbitraryInstruction }
  checks := checks ++ [(s!"{label} instruction body is explicitly outside the header certificate", checkHeaderCode changedInstruction hc)]
  let detachedBlocks := withStep blocks { blockStep with ops := blockStep.ops.set! 19 (instructionCall missing) }
  let detached := { compiled.bytecode with functions := compiled.bytecode.functions.set! hc.blocks detachedBlocks }
  checks := checks ++ [(s!"{label} instruction Call is bound but its target lookup is not certified",
    checkHeaderCode detached { hc with instruction := missing })]
  return checks

private def functionAgreement (compiled : Aiur.CompiledToplevel) (h : FunctionHeaderBytes)
    (remaining self finish : Aiur.G) : Bool :=
  let raw := h.bytes.toArray.map Aiur.G.ofUInt8
  let (st, pointer) := storePrefix initial raw finish
  let bytes := #[200, 201] ++ h.bytes.toArray ++ #[90, 91, 92]
  let decoder : Codec.Internal.Decoder (Nat × Nat × Nat) := do
    let arity ← Codec.Internal.readCount 16
    let entry ← Codec.Internal.readU32
    let blocks ← Codec.Internal.readCount 64
    return (arity, entry, blocks)
  match observe compiled `is_read_functions 60 #[pointer, remaining, self] #[0, 1, 2, 19, 46, 63, 54] st,
      decoder.run { bytes, offset := 2, nodes := 13 } with
  | .ok (out, after), .ok ((arity, entry, blocks), rest) =>
    out == #[pointer, remaining, self, h.arity.field, h.entry.field, h.blocks.field, finish] && after.map.size == 71 &&
      unchanged st after && arity == h.arity.field.n && entry == h.entry.field.n && blocks == h.blocks.field.n &&
      blocks != 0 && rest.offset == 14 && rest.nodes == 13 && rest.bytes == bytes
  | _, _ => false

private def headerChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let full : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let mut checks : List Check := []
  for arity in [:17] do
    for blocks in [1:65] do
      checks := checks ++ [(s!"{label} function header exact state and codec/{arity}/{blocks}",
        functionAgreement compiled (wireFunction arity (2 ^ 32 - 1) blocks) full full finish)]
  for bit in [:32] do
    checks := checks ++ [(s!"{label} function entry retains bit/{bit}",
      functionAgreement compiled (wireFunction 16 (2 ^ bit) 64) 1 full finish)]
  for arity in [17, 18, 64, 65, 255, 256, 65536, 2 ^ 31, 2 ^ 32 - 1] do
    let (st, pointer) := storePrefix initial ((wordBytes arity).bytes.toArray.map Aiur.G.ofUInt8) finish
    checks := checks ++ [(s!"{label} function arity rejects before entry/block bytes/{arity}",
      failed (snapshot compiled `is_read_functions #[pointer, full, full] st 1) .assertFailed)]
  for arity in [:17] do
    for blocks in [0, 65, 66, 255, 256, 65536, 2 ^ 31, 2 ^ 32 - 1] do
      let h := wireFunction arity (2 ^ 32 - 1) blocks
      let (st, pointer) := storePrefix initial (h.bytes.toArray.map Aiur.G.ofUInt8) finish
      checks := checks ++ [(s!"{label} invalid block count rejects before block Call/{arity}/{blocks}",
        failed (snapshot compiled `is_read_functions #[pointer, full, full] st 1) .assertFailed)]
  for locals in [:65] do
    for self in [0, 2 ^ 32 + 7, goldilocksModulus - 1] do
      let word := wordBytes locals
      let (st, pointer) := storePrefix initial (word.bytes.toArray.map Aiur.G.ofUInt8) finish
      checks := checks ++ [(s!"{label} block local header exact state/{locals}/{self}",
        match observe compiled `is_read_blocks 19 #[pointer, full, .ofNat self] #[0, 1, 2, 19, 10] st with
        | .ok (out, after) => out == #[pointer, full, .ofNat self, word.field, finish] && after.map.size == 25 && unchanged st after
        | _ => false)]
  for locals in [65, 66, 255, 256, 65536, 2 ^ 31, 2 ^ 32 - 1] do
    let (st, pointer) := storePrefix initial ((wordBytes locals).bytes.toArray.map Aiur.G.ofUInt8) finish
    checks := checks ++ [(s!"{label} local count rejects before instruction Call/{locals}",
      failed (snapshot compiled `is_read_blocks #[pointer, full, full] st 1) .assertFailed)]
  for (name, length, raw, outputs) in [
      (`is_read_functions, 60, (wireFunction 16 0 64).bytes.toArray.map Aiur.G.ofUInt8, #[19, 46, 63, 54]),
      (`is_read_blocks, 19, (wordBytes 64).bytes.toArray.map Aiur.G.ofUInt8, #[19, 10])] do
    for position in [:raw.size] do
      let (shortState, shortPointer) := storeStream initial (raw.extract 0 position)
      let (tailState, tail) := storePrefix initial (raw.extract (position + 1) raw.size) finish
      let (badState, bad) := memStore tailState #[2, raw.getD position 0, tail]
      let (st, pointer) := storePrefix badState (raw.extract 0 position) (.ofNat bad)
      checks := checks ++ [
        (s!"{label} {name} header rejects truncation/{position}", failed (observe compiled name length #[shortPointer, 1, full] outputs shortState) .unreachableAfterLayout),
        (s!"{label} {name} header rejects byte tag/{position}", failed (observe compiled name length #[pointer, 1, full] outputs st) .unreachableAfterLayout)]
    let (st, pointer) := storePrefix initial raw finish
    checks := checks ++ [
      (s!"{label} {name} header requires byte Call fuel", failed (observe compiled name length #[pointer, 1, full] outputs st 0) .outOfFuel),
      (s!"{label} {name} header does not narrow program pointer", failed
        (observe compiled name length #[.ofNat (2 ^ 32 + pointer.n), 1, full] outputs st) (.invalidPointer 3 (2 ^ 32 + pointer.n)))]
  for (name, length, raw, fieldIndex, expected) in [
      (`is_read_functions, 60, ((wireFunction 0 0 1).bytes.toArray.map Aiur.G.ofUInt8).set! 0 (.ofNat (2 ^ 32)), 19, 2 ^ 32),
      (`is_read_functions, 60, ((wireFunction 0 0 1).bytes.toArray.map Aiur.G.ofUInt8).set! 8 (.ofNat (2 ^ 32 + 1)), 63, 2 ^ 32 + 1),
      (`is_read_blocks, 19, #[.ofNat (2 ^ 32), 0, 0, 0], 19, 2 ^ 32)] do
    let (st, pointer) := storePrefix initial raw finish
    checks := checks ++ [
      (s!"{label} non-byte fixture shows {name}/{fieldIndex} UInt32 premise", match observe compiled name length #[pointer, 1, full] #[fieldIndex] st with
        | .ok (out, _) => out == #[.ofNat expected]
        | _ => false),
      (s!"{label} actual loader rejects forged {name}/{fieldIndex} header", failed
        (snapshot compiled `ib_load #[0, .ofNat raw.size] (rawAdvice initial 0 0 raw.size raw) (raw.size + 1)) .u8RangeCheckFailed)]
  return checks

private def zeroChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let mut checks : List Check := []
  for (name, width) in [(`is_read_functions, 6), (`is_read_blocks, 13)] do
    for pointer in [0, 2 ^ 32 + 19, goldilocksModulus - 1] do
      for self in [0, 2 ^ 32 + 7, goldilocksModulus - 1] do
        let flat : Array Aiur.G := Array.replicate width 1
        let (occupied, _) := memStore initial (Array.replicate width 99)
        let expected := memStore occupied flat
        for (desc, base) in [("new", occupied), ("dedup", expected.1)] do
          let stored := memStore base flat
          checks := checks ++ [(s!"{label} exact {name} Nil/{desc}/{pointer}/{self}",
            match snapshot compiled name #[.ofNat pointer, 0, .ofNat self] base 0 with
            | .ok (out, after) => out == #[.ofNat stored.2, .ofNat pointer] &&
                after.map == #[.ofNat pointer, 0, .ofNat self, 1, 1, .ofNat stored.2] &&
                memoryView after == memoryView stored.1 && (match memLoad after width stored.2 with | .ok found => found == flat | _ => false) &&
                preservesReads base after && sameIo base after &&
                Ix.Ixby.AiurBackend.Objects.Store.bucketSize after width ≤ Ix.Ixby.AiurBackend.Objects.Store.bucketSize base width + 1
            | _ => false)]
  let ctors := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations initial []
  checks := checks ++ [(s!"{label} empty block list reuses the constructor Nil cell in width thirteen",
    match snapshot compiled `is_read_blocks #[.ofNat (goldilocksModulus - 1), 0, 0] ctors.1 0 with
    | .ok (out, after) => out[0]? == some ctors.2 && unchanged ctors.1 after &&
        readTable (bytecodeMemory after) ctors.2.n 0 == some #[]
    | _ => false)]
  return checks

private def programChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let outputs := #[0, 1, 48, 65, 71, 80, 89, 97]
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    let h := ProgramPrefixTests.wireHeader (2 ^ 32 - 1) count
    for functions in [:10] do
      let raw := ProgramPrefixTests.payload h decls ++ (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8
      let (st, pointer) := storePrefix initial raw finish
      let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations st decls
      checks := checks ++ [(s!"{label} composed constructor/function-count prefix/{count}/{functions}",
        if functions == 0 || functions > 8 then failed (snapshot compiled `is_run #[pointer, input] st (count + 3)) .assertFailed
        else match observe compiled `is_run 83 #[pointer, input] outputs st (count + 3) with
        | .ok (out, after) => out == #[pointer, input, h.entry.field, .ofNat count, expected.2, finish, .ofNat functions, 0] &&
            after.map.size == 98 && memoryView after == memoryView expected.1 && sameIo st after && preservesReads st after &&
            readTable (bytecodeMemory after) expected.2.n count == some (decls.map DeclarationBytes.declaration).toArray
        | _ => false)]
  for functions in [10, 16, 17, 255, 256, 65536, 2 ^ 31, 2 ^ 32 - 1] do
    let raw := ProgramPrefixTests.payload (ProgramPrefixTests.wireHeader 0 0) [] ++
      (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8
    let (st, pointer) := storePrefix initial raw finish
    checks := checks ++ [(s!"{label} program rejects high function count before Call/{functions}",
      failed (snapshot compiled `is_run #[pointer, input] st 1) .assertFailed)]
  let prefixBytes := ProgramPrefixTests.payload (ProgramPrefixTests.wireHeader 0 1) (wireDeclarations 1)
  let countBytes := (wordBytes 8).bytes.toArray.map Aiur.G.ofUInt8
  for position in [:4] do
    let (shortState, shortPointer) := storeStream initial (prefixBytes ++ countBytes.extract 0 position)
    let (tailState, tail) := storePrefix initial (countBytes.extract (position + 1) 4) finish
    let (badState, bad) := memStore tailState #[2, countBytes.getD position 0, tail]
    let (st, pointer) := storePrefix badState (prefixBytes ++ countBytes.extract 0 position) (.ofNat bad)
    checks := checks ++ [
      (s!"{label} program function count rejects truncation/{position}", failed
        (observe compiled `is_run 83 #[shortPointer, input] outputs shortState 4) .unreachableAfterLayout),
      (s!"{label} program function count rejects byte tag/{position}", failed
        (observe compiled `is_run 83 #[pointer, input] outputs st 4) .unreachableAfterLayout)]
  let good := ProgramPrefixTests.payload (ProgramPrefixTests.wireHeader 0 0) [] ++ #[1, 0, 0, 0]
  let (st, pointer) := storePrefix initial good finish
  checks := checks ++ [(s!"{label} admitted count does not establish any function bytes",
    (observe compiled `is_run 83 #[pointer, input] outputs st 1).isOk &&
      failed (snapshot compiled `is_run #[pointer, input] st 3) (.invalidPointer 3 finish.n))]
  let forged := good.set! 16 (.ofNat (2 ^ 32 + 1))
  let (st, pointer) := storePrefix initial forged finish
  checks := checks ++ [
    (s!"{label} non-byte function-count fixture can pass the UInt32 guard", match observe compiled `is_run 83 #[pointer, input] #[89] st 1 with
      | .ok (out, _) => out == #[.ofNat (2 ^ 32 + 1)]
      | _ => false),
    (s!"{label} actual loader closes non-byte function-count fixture", failed
      (snapshot compiled `ib_load #[0, 20] (rawAdvice initial 0 0 20 forged) 21) .u8RangeCheckFailed)]
  return checks

private def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let suffix : Array Aiur.G := #[90, 91, 92]
  let outputs := #[0, 1, 48, 65, 71, 80, 89, 97]
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    let h := ProgramPrefixTests.wireHeader (2 ^ 32 - 1) count
    for functions in [1, 8] do
      let raw := ProgramPrefixTests.payload h decls ++ (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8 ++ suffix
      let ready := rawAdvice initial 0 2 raw.size (#[256, 65536] ++ raw)
      checks := checks ++ [(s!"{label} actual loader to both program count guards/{count}/{functions}",
        match snapshot compiled `ib_load #[0, .ofNat raw.size] ready (raw.size + 1) with
        | .ok (loadedOut, loaded) =>
          let pointer := loadedOut.getD 0 0
          let expected := Ix.Ixby.AiurBackend.Objects.Declarations.storeDeclarations loaded decls
          match skipStream loaded pointer (20 + 44 * count), observe compiled `is_run 83 #[pointer, input] outputs loaded (count + 3) with
          | some finish, .ok (out, after) =>
            out == #[pointer, input, h.entry.field, .ofNat count, expected.2, finish, .ofNat functions, 0] &&
              after.map.size == 98 && memoryView after == memoryView expected.1 && preservesReads ready after && sameIo ready after &&
              streamMatches after finish suffix.toList &&
              readTable (bytecodeMemory after) expected.2.n count == some (decls.map DeclarationBytes.declaration).toArray
          | _, _ => false
        | _ => false)]
  for functions in [0, 9, 2 ^ 32 - 1] do
    let raw := ProgramPrefixTests.payload (ProgramPrefixTests.wireHeader 0 0) [] ++
      (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8 ++ suffix
    checks := checks ++ [(s!"{label} loaded program rejects function count/{functions}",
      match snapshot compiled `ib_load #[0, .ofNat raw.size] (rawAdvice initial 0 0 raw.size raw) (raw.size + 1) with
      | .ok (out, loaded) => failed (snapshot compiled `is_run #[out.getD 0 0, input] loaded 1) .assertFailed
      | _ => false)]
  for (arity, blocks, valid) in [(0, 1, true), (16, 64, true), (17, 1, false), (16, 0, false), (16, 65, false)] do
    let h := wireFunction arity (2 ^ 32 - 1) blocks
    let raw := h.bytes.toArray.map Aiur.G.ofUInt8 ++ suffix
    checks := checks ++ [(s!"{label} loaded function header/{arity}/{blocks}",
      match snapshot compiled `ib_load #[0, .ofNat raw.size] (rawAdvice initial 0 0 raw.size raw) (raw.size + 1) with
      | .ok (out, loaded) =>
        let pointer := out.getD 0 0
        if valid then match skipStream loaded pointer 12,
            observe compiled `is_read_functions 60 #[pointer, 1, input] #[19, 46, 63, 54] loaded with
          | some finish, .ok (out, after) => out == #[h.arity.field, h.entry.field, h.blocks.field, finish] &&
              unchanged loaded after && streamMatches after finish suffix.toList
          | _, _ => false
        else failed (snapshot compiled `is_read_functions #[pointer, 1, input] loaded 1) .assertFailed
      | _ => false)]
  for (name, prefixBytes, fieldBytes) in [
      ("function count", ProgramPrefixTests.payload (ProgramPrefixTests.wireHeader 0 0) [], (wordBytes 1).bytes.toArray.map Aiur.G.ofUInt8),
      ("function header", #[], (wireFunction 0 0 1).bytes.toArray.map Aiur.G.ofUInt8),
      ("block header", #[], (wordBytes 64).bytes.toArray.map Aiur.G.ofUInt8)] do
    for position in [:fieldBytes.size] do
      let raw := prefixBytes ++ fieldBytes.set! position (.ofNat (2 ^ 32))
      checks := checks ++ [(s!"{label} loader rejects non-byte {name}/{position}", failed
        (snapshot compiled `ib_load #[0, .ofNat raw.size] (rawAdvice initial 0 0 raw.size raw) (raw.size + 1)) .u8RangeCheckFailed)]
  return checks

private def continuationChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let hc ← code compiled
  let (_, functions) ← function compiled `is_read_functions
  let (_, blocks) ← function compiled `is_read_blocks
  let (_, instruction) ← function compiled `is_read_instr
  let fs ← stepOf functions
  let bs ← stepOf blocks
  let fakeInstruction := { instruction with body := (⟨#[.const 77], .return 0 (Array.replicate 10 3 ++ #[0])⟩ : Aiur.Bytecode.Block) }
  let controlledBlock := withStep blocks { bs with ops := (bs.ops.toList.take 20).toArray, ctrl := .return 0 #[2, 35] }
  let controlledFunction := withStep functions { fs with
    ops := (fs.ops.toList.take 61).toArray ++ #[.const 88]
    ctrl := .return 0 #[19, 46, 63, 54, 2, 71, 72, 73] }
  let replaced := compiled.bytecode.functions.set! hc.instruction fakeInstruction |>.set! hc.blocks controlledBlock |>.set! hc.functions controlledFunction
  let changed := { compiled with bytecode := { compiled.bytecode with functions := replaced } }
  let self : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let h := wireFunction 16 (2 ^ 32 - 1) 1
  let (blockState, blockPointer) := storePrefix initial ((wordBytes 64).bytes.toArray.map Aiur.G.ofUInt8) finish
  let (st, pointer) := storePrefix blockState (h.bytes.toArray.map Aiur.G.ofUInt8) blockPointer
  let missing := compiled.bytecode.functions.size
  let detachedBlock := withStep blocks { bs with ops := bs.ops.set! 19 (instructionCall missing) }
  let detached := { compiled with bytecode := { compiled.bytecode with functions := compiled.bytecode.functions.set! hc.blocks detachedBlock } }
  return [
    (s!"{label} header certificates permit arbitrary downstream implementations", checkHeaderCode changed.bytecode hc),
    (s!"{label} function continuation receives exact header and actual block Call outputs",
      match snapshot changed `is_read_functions #[pointer, 1, self] st 3 with
      | .ok (out, after) => out == #[h.arity.field, h.entry.field, h.blocks.field, blockPointer, self, self, finish, 88] &&
          after.map.size == 74 && unchanged st after
      | _ => false),
    (s!"{label} block continuation receives exact self and actual instruction suffix",
      success (snapshot changed `is_read_blocks #[blockPointer, 1, self] blockState 2) #[self, finish] blockState),
    (s!"{label} header certificate does not imply next instruction Call success",
      checkHeaderCode detached.bytecode { hc with instruction := missing } &&
        failed (snapshot detached `is_read_blocks #[blockPointer, 1, self] blockState 2) (.invalidFunIdx missing))]

end CodeHeaderTests

namespace ScalarOperandTests

open Ix.Ixby.AiurBackend.Objects.Scalars Ix.Ixby.AiurBackend.Objects.Operands

private def fieldBytes (n : Nat) : FieldBytes :=
  ⟨.ofNat n, .ofNat (n / 256), .ofNat (n / 65536), .ofNat (n / 16777216),
    .ofNat (n / 4294967296), .ofNat (n / 1099511627776), .ofNat (n / 281474976710656),
    .ofNat (n / 72057594037927936)⟩

private def code (compiled : Aiur.CompiledToplevel) : Except String OperandCode := do
  let (reader, _) ← function compiled `ib_byte
  let (field, _) ← function compiled `ib_field
  let (scalar, _) ← function compiled `ib_scalar
  let (operand, _) ← function compiled `ic_read_operand
  return ⟨⟨reader, field, scalar, 0⟩, operand⟩

/-- Mutate every certified operation/return slot and dispatch edge. This is
test-only traversal, never a compiler or evaluator modification. -/
private def mutations : Nat → Aiur.Bytecode.Block → Array (String × Aiur.Bytecode.Block)
  | 0, _ => #[]
  | depth + 1, b => Id.run do
    let mut out := #[("control form", { b with ctrl := .return 99 #[] })]
    for idx in [:b.ops.size] do
      out := out.push (s!"op/{idx}", { b with ops := b.ops.set! idx (.const (.ofNat (2 ^ 32 + 123))) })
      out := out.push (s!"short ops/{idx}", { b with ops := b.ops.extract 0 idx })
      if let .call callee args size flag := b.ops.getD idx (.const 0) then
        for (label, op) in [("callee", Aiur.Bytecode.Op.call (callee + 1) args size flag),
            ("output count", .call callee args (size + 1) flag),
            ("flag", .call callee args size (!flag)), ("extra argument", .call callee (args.push 0) size flag)] do
          out := out.push (s!"call/{idx}/{label}", { b with ops := b.ops.set! idx op })
        for arg in [:args.size] do
          let changed := Aiur.Bytecode.Op.call callee (args.set! arg (args[arg]! + 1)) size flag
          out := out.push (s!"call/{idx}/arg/{arg}", { b with ops := b.ops.set! idx changed })
    out := out.push ("extra op", { b with ops := b.ops.push (.const 0) })
    match b.ctrl with
    | .return selector outputs =>
      out := out.push ("return selector", { b with ctrl := .return (selector + 1) outputs })
      out := out.push ("yield", { b with ctrl := .yield selector outputs })
      out := out.push ("extra return", { b with ctrl := .return selector (outputs.push 0) })
      for idx in [:outputs.size] do
        out := out.push (s!"return/{idx}", { b with ctrl := .return selector (outputs.set! idx (outputs[idx]! + 1)) })
        out := out.push (s!"short return/{idx}", { b with ctrl := .return selector (outputs.extract 0 idx) })
    | .match idx cases fallback =>
      out := out.push ("scrutinee", { b with ctrl := .match (idx + 1) cases fallback })
      out := out.push ("no fallback", { b with ctrl := .match idx cases none })
      for arm in [:cases.size] do
        let (tag, branch) := cases.getD arm (0, ⟨#[], .return 0 #[]⟩)
        out := out.push (s!"tag/{arm}", { b with ctrl := .match idx (cases.set! arm (tag + 99, branch)) fallback })
        out := out.push (s!"short arms/{arm}", { b with ctrl := .match idx (cases.extract 0 arm) fallback })
        out := out.push (s!"extra arm/{arm}", { b with ctrl := .match idx (cases.push (tag, branch)) fallback })
        for (label, changed) in mutations depth branch do
          out := out.push (s!"arm/{arm}/{label}", { b with ctrl := .match idx (cases.set! arm (tag, changed)) fallback })
      if let some branch := fallback then
        for (label, changed) in mutations depth branch do
          out := out.push (s!"fallback/{label}", { b with ctrl := .match idx cases (some changed) })
    | _ => pure ()
    return out

private def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let c ← code compiled
  let (_, byteFn) ← function compiled `ib_byte
  let (_, fieldFn) ← function compiled `ib_field
  let (_, scalarFn) ← function compiled `ib_scalar
  let (_, operandFn) ← function compiled `ic_read_operand
  let mut checks := [(s!"{label} complete scalar/operand same-toplevel certificate", checkOperandCode compiled.bytecode c)]
  for (name, f, accepts) in [
      ("field", fieldFn, fun f => checkFieldReader f c.scalars.reader),
      ("scalar", scalarFn, fun f => checkScalarReader f c.scalars.reader c.scalars.field),
      ("operand", operandFn, fun f => checkOperandReader f c.scalars.reader c.scalars.scalar)] do
    let metadata := { f with constrained := f.constrained.not, layout := { f.layout with auxiliaries := 999, lookups := 888 } }
    checks := checks ++ [(s!"{label} {name} full body certificate", accepts f),
      (s!"{label} {name} wrong input arity", !accepts { f with layout := { f.layout with inputSize := f.layout.inputSize + 1 } }),
      (s!"{label} {name} evaluator-irrelevant metadata", accepts metadata)]
    for (path, body) in mutations 3 f.body do
      checks := checks ++ [(s!"{label} {name} certificate binds {path}", !accepts { f with body })]
  for (name, idx, f) in [("byte", c.scalars.reader, byteFn), ("field", c.scalars.field, fieldFn),
      ("scalar", c.scalars.scalar, scalarFn), ("operand", c.operand, operandFn)] do
    let broken := { f with body := (⟨#[], .return 0 #[]⟩ : Aiur.Bytecode.Block) }
    let changed := { compiled.bytecode with functions := compiled.bytecode.functions.set! idx broken }
    checks := checks ++ [(s!"{label} bundle binds {name} implementation", !checkOperandCode changed c),
      (s!"{label} bundle resolves {name} target", !checkOperandCode
        { compiled.bytecode with functions := compiled.bytecode.functions.extract 0 idx } c)]
  let (instruction, f) ← function compiled `is_read_instr
  let broken := { f with body := (⟨#[], .return 0 #[]⟩ : Aiur.Bytecode.Block) }
  checks := checks ++ [(s!"{label} leaf certificate does not validate instructions", checkOperandCode
    { compiled.bytecode with functions := compiled.bytecode.functions.set! instruction broken } c)]
  return checks

private def scalarCodec (s : ScalarBytes) : Bool :=
  match Codec.Internal.decode 64 0 s.bytes.toArray (Codec.Internal.readScalar objectsProfile) with
  | .ok value => decide s.valid && Value.scalar value == s.atom.decode
  | .error .nonCanonical => !decide s.valid
  | _ => false

private def scalarFixture (compiled : Aiur.CompiledToplevel) (label : String) (s : ScalarBytes) : Check :=
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let (st, pointer) := storePrefix initial (s.bytes.toArray.map Aiur.G.ofUInt8) finish
  let result := snapshot compiled `ib_scalar #[pointer] st 2
  (label, scalarCodec s && if s.valid then
    success result (s.flat ++ #[finish]) st && decodeAtom s.flat.toList == some s.atom
    else failed result .assertFailed)

private def fields : List Nat := [0, 1, 255, 256, 65535, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63,
  goldilocksModulus - 2, goldilocksModulus - 1, goldilocksModulus, goldilocksModulus + 1, 2 ^ 64 - 1]
private def scalars : List ScalarBytes :=
  [.boolean 0, .boolean 1, .boolean 2, .boolean 255, .word (wordBytes 0), .word (wordBytes (2 ^ 32 - 1))] ++
    fields.map (fun n => .field (fieldBytes n)) ++
    fields.flatMap (fun a => fields.map (fun b => .extension (fieldBytes a) (fieldBytes b)))

private def scalarChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let mut checks := scalars.zipIdx.map fun (s, idx) => scalarFixture compiled s!"{label} scalar codec/layout/{idx}" s
  for byte in [:256] do
    checks := checks ++ [scalarFixture compiled s!"{label} Boolean byte/{byte}" (.boolean (.ofNat byte))]
  for pos in [:4] do
    for byte in [:256] do
      checks := checks ++ [scalarFixture compiled s!"{label} Word literal byte/{pos}/{byte}" (.word (wordBytes (byte * 256 ^ pos)))]
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  for pos in [:8] do
    for byte in [:256] do
      let n := if pos < 4 then goldilocksModulus - 1 + byte * 256 ^ pos
        else goldilocksModulus - 1 - (255 - byte) * 256 ^ pos
      let w := fieldBytes n
      let (st, pointer) := storePrefix initial (w.bytes.toArray.map Aiur.G.ofUInt8) finish
      let actual := snapshot compiled `ib_field #[pointer] st 1
      checks := checks ++ [(s!"{label} field canonical boundary byte/{pos}/{byte}",
        n == natOfBytesLE w.bytes.toArray && w.value == n &&
          if n < goldilocksModulus then success actual #[.ofNat n, finish] st else failed actual .assertFailed)]
  for tag in [4:256] do
    let (st, pointer) := storePrefix initial #[.ofNat tag] finish
    checks := checks ++ [(s!"{label} unsupported scalar stops before payload/{tag}",
      failed (snapshot compiled `ib_scalar #[pointer] st 1) .assertFailed)]
  return checks

private def operandFixture (compiled : Aiur.CompiledToplevel) (label : String) (locals : Aiur.G) (o : OperandBytes) : Check :=
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let (st, pointer) := storePrefix initial (o.bytes.toArray.map Aiur.G.ofUInt8) finish
  let result := snapshot compiled `ic_read_operand #[pointer, locals] st 3
  let codec := Codec.Internal.decode 64 0 o.bytes.toArray (Codec.Internal.readOperand objectsProfile)
  (label, if o.valid locals then success result (o.flat ++ #[finish]) st &&
      decodeOperand o.flat.toList == some o.operand && (match codec with | .ok actual => actual == o.operand | _ => false)
    else failed result .assertFailed)

private def operandChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let mut checks := []
  for locals in [:65] do
    for index in [0, locals - 1, locals, locals + 1, 2 ^ 32 - 1] do
      checks := checks ++ [operandFixture compiled s!"{label} local frame boundary/{locals}/{index}" (.ofNat locals) (.local (wordBytes index))]
  for index in [:256] do
    checks := checks ++ [operandFixture compiled s!"{label} local index byte/{index}" 64 (.local (wordBytes index))]
  for locals in [2 ^ 31, 2 ^ 32 - 1] do
    for index in [0, 64, locals - 1, locals, 2 ^ 32 - 1] do
      checks := checks ++ [operandFixture compiled s!"{label} full u32 local/index/{locals}/{index}" (.ofNat locals) (.local (wordBytes index))]
  for locals in [0, 64, goldilocksModulus - 1] do
    checks := checks ++ [operandFixture compiled s!"{label} erased operand/full local field/{locals}" (.ofNat locals) .erased]
    for (s, idx) in scalars.zipIdx do
      checks := checks ++ [operandFixture compiled s!"{label} literal operand/full local field/{locals}/{idx}" (.ofNat locals) (.literal s)]
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  for tag in [3:256] do
    let (st, pointer) := storePrefix initial #[.ofNat tag] finish
    checks := checks ++ [(s!"{label} unsupported operand stops before payload/{tag}",
      failed (snapshot compiled `ic_read_operand #[pointer, 64] st 1) .assertFailed)]
  return checks

private structure ReaderCase where
  name : Lean.Name
  bytes : List UInt8
  extraArgs : Array Aiur.G
  flat : Array Aiur.G
  fuel : Nat

private def readerCases : List ReaderCase :=
  let field := fieldBytes (goldilocksModulus - 1)
  let scalarCases : List (ScalarBytes × Nat) := [(.boolean 1, 1), (.word (wordBytes (2 ^ 32 - 1)), 1),
    (.field field, 2), (.extension field (fieldBytes (goldilocksModulus - 2)), 2)]
  [⟨`ib_field, field.bytes, #[], #[field.field], 1⟩] ++
    scalarCases.map (fun (s, fuel) => ⟨`ib_scalar, s.bytes, #[], s.flat, fuel⟩) ++
    [⟨`ic_read_operand, (OperandBytes.local (wordBytes 63)).bytes, #[64],
      (OperandBytes.local (wordBytes 63)).flat, 1⟩,
     ⟨`ic_read_operand, [2], #[64], OperandBytes.erased.flat, 1⟩] ++
    scalarCases.map (fun (s, fuel) => ⟨`ic_read_operand, (OperandBytes.literal s).bytes, #[64],
      (OperandBytes.literal s).flat, fuel + 1⟩)

private def opFailed (actual : Except BytecodeError EvalState) (error : BytecodeError) : Bool :=
  match actual with | .error found => reprStr found == reprStr error | _ => false

private def failureChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
  let mut checks := []
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  for (c, idx) in readerCases.zipIdx do
    let (callee, _) ← function compiled c.name
    let bytes := c.bytes.toArray.map Aiur.G.ofUInt8
    let (st, pointer) := storePrefix initial bytes finish
    let args := #[pointer] ++ c.extraArgs
    let outputs := c.flat ++ #[finish]
    let caller := { st with map := #[99] ++ args ++ #[101] }
    let indices := (List.range args.size).toArray.map (· + 1)
    checks := checks ++ [
      (s!"{label} leaf minimum body fuel/{idx}", success (snapshot compiled c.name args st c.fuel) outputs st),
      (s!"{label} leaf insufficient body fuel/{idx}", failed (snapshot compiled c.name args st (c.fuel - 1)) .outOfFuel),
      (s!"{label} leaf Call insufficient fuel/{idx}", opFailed
        (Aiur.Bytecode.Eval.evalOp compiled.bytecode c.fuel (.call callee indices outputs.size false) caller) .outOfFuel),
      (s!"{label} leaf Call input arity/{idx}", opFailed
        (Aiur.Bytecode.Eval.evalOp compiled.bytecode (c.fuel + 1) (.call callee (indices.push 0) outputs.size false) caller)
        (.arityMismatch callee)),
      (s!"{label} leaf Call argument register/{idx}", opFailed
        (Aiur.Bytecode.Eval.evalOp compiled.bytecode (c.fuel + 1) (.call callee (indices.set! 0 99) outputs.size false) caller)
        (.invalidValIdx 99))]
    for size in [outputs.size - 1, outputs.size + 1] do
      checks := checks ++ [(s!"{label} leaf Call output arity/{idx}/{size}", opFailed
        (Aiur.Bytecode.Eval.evalOp compiled.bytecode (c.fuel + 1) (.call callee indices size false) caller)
        .callOutputSizeMismatch)]
    for flag in [false, true] do
      checks := checks ++ [(s!"{label} leaf actual Call exact caller append/{idx}/{flag}",
        match Aiur.Bytecode.Eval.evalOp compiled.bytecode (c.fuel + 1) (.call callee indices outputs.size flag) caller with
        | .ok after => after.map == caller.map ++ outputs && unchanged caller after
        | _ => false)]
    for pos in [:bytes.size] do
      let beforeBytes := bytes.extract 0 pos
      let (short, shortPointer) := storeStream initial beforeBytes
      let (bad, badPointer) := memStore initial #[2, bytes.getD pos 0, finish]
      let (malformed, malformedPointer) := storePrefix bad beforeBytes (.ofNat badPointer)
      let (dangling, danglingPointer) := storePrefix initial beforeBytes finish
      checks := checks ++ [
        (s!"{label} leaf truncated byte/{idx}/{pos}", failed
          (snapshot compiled c.name (#[shortPointer] ++ c.extraArgs) short c.fuel) .unreachableAfterLayout),
        (s!"{label} leaf malformed Cons/{idx}/{pos}", failed
          (snapshot compiled c.name (#[malformedPointer] ++ c.extraArgs) malformed c.fuel) .unreachableAfterLayout),
        (s!"{label} leaf dangling full-field pointer/{idx}/{pos}", failed
          (snapshot compiled c.name (#[danglingPointer] ++ c.extraArgs) dangling c.fuel) (.invalidPointer 3 finish.n))]
      for nonByte in [256, goldilocksModulus - 1] do
        let forged := bytes.set! pos (.ofNat nonByte)
        let ready := rawAdvice initial 4 0 forged.size forged
        checks := checks ++ [(s!"{label} loader rejects non-byte leaf position/{idx}/{pos}/{nonByte}",
          failed (snapshot compiled `ib_load #[4, .ofNat forged.size] ready (forged.size + 1)) .u8RangeCheckFailed)]
  -- These deliberately forged memory fixtures document why the genuine-byte
  -- premise matters. They are not admissible advice or native/AIR claims.
  let index : Aiur.G := .ofNat (2 ^ 32 + 1)
  let (localState, localPointer) := storePrefix initial #[0, index, 0, 0, 0] finish
  let (wordState, wordPointer) := storePrefix initial #[1, 1, 256, 0, 0, 0] finish
  let (fieldState, fieldPointer) := storePrefix initial #[256, 0, 0, 0, 0, 0, 0, 0] finish
  checks := checks ++ [
    (s!"{label} forged local can pass UInt32 guard but is not a decoded operand",
      success (snapshot compiled `ic_read_operand #[localPointer, 2] localState 1) #[0, index, 0, 0, 0, 0, finish] localState &&
        (decodeOperand [0, index, 0, 0, 0, 0]).isNone),
    (s!"{label} forged Word literal passes raw reader but fails representation",
      success (snapshot compiled `ic_read_operand #[wordPointer, 64] wordState 2) #[1, 1, 256, 0, 0, 0, finish] wordState &&
        (decodeOperand [1, 1, 256, 0, 0, 0]).isNone),
    (s!"{label} raw field packing does not establish genuine bytes",
      success (snapshot compiled `ib_field #[fieldPointer] fieldState 1) #[256, finish] fieldState)]
  return checks

private def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let operands : List OperandBytes := [.local (wordBytes 0), .local (wordBytes 63), .local (wordBytes 64), .erased,
    .literal (.boolean 0), .literal (.boolean 1), .literal (.boolean 2), .literal (.word (wordBytes (2 ^ 32 - 1))),
    .literal (.field (fieldBytes (goldilocksModulus - 1))), .literal (.field (fieldBytes goldilocksModulus)),
    .literal (.extension (fieldBytes (goldilocksModulus - 1)) (fieldBytes (goldilocksModulus - 2))),
    .literal (.extension (fieldBytes 1) (fieldBytes goldilocksModulus))]
  let mut checks := []
  for locals in [0, 64] do
    for (o, idx) in operands.zipIdx do
      let values := (o.bytes ++ [255, 254]).toArray.map Aiur.G.ofUInt8
      let base := (storeStream initial #[17, 18]).1
      let ready := rawAdvice base 4 2 values.size (#[256, .ofNat (goldilocksModulus - 1)] ++ values ++ #[65536])
      checks := checks ++ [(s!"{label} actual loaded operand with untouched suffix/{locals}/{idx}",
        match snapshot compiled `ib_load #[4, .ofNat values.size] ready (values.size + 1) with
        | .ok (out, loaded) => out.size == 1 && sameIo ready loaded && preservesReads ready loaded &&
          streamMatches loaded (out.getD 0 0) values.toList &&
          (match skipStream loaded (out.getD 0 0) o.bytes.length with
          | some finish =>
            let result := snapshot compiled `ic_read_operand #[out.getD 0 0, .ofNat locals] loaded 3
            if o.valid (.ofNat locals) then
              match result with
              | .ok (actual, after) => actual == o.flat ++ #[finish] && unchanged loaded after &&
                sameIo ready after && preservesReads ready after && streamMatches after finish [255, 254] &&
                decodeOperand (actual.extract 0 6).toList == some o.operand
              | _ => false
            else failed result .assertFailed
          | none => false)
        | _ => false)]
  return checks

private def layoutChecks : List Check := Id.run do
  let mut checks := []
  for (label, flat, pads) in [
      ("local", #[0, 7, 0, 0, 0, 0], [2, 3, 4, 5]),
      ("Boolean", #[1, 0, 1, 0, 0, 0], [3, 4, 5]),
      ("field", #[1, 2, 17, 0, 0, 0], [3, 4, 5]),
      ("extension", #[1, 3, 17, 18, 0, 0], [4, 5]),
      ("erased", #[1, 4, 4, 4, 4, 4], [2, 3, 4, 5])] do
    checks := checks ++ [(s!"operand layout accepted/{label}", (decodeOperand flat.toList).isSome),
      (s!"operand layout extra field/{label}", (decodeOperand (flat.push 0).toList).isNone)]
    for pos in [:6] do
      checks := checks ++ [(s!"operand layout short/{label}/{pos}", (decodeOperand (flat.extract 0 pos).toList).isNone)]
    for pos in pads do
      checks := checks ++ [(s!"operand layout padding/{label}/{pos}",
        (decodeOperand (flat.set! pos (flat.getD pos 0 + 1)).toList).isNone)]
  for pos in [2:6] do
    checks := checks ++ [(s!"operand Word byte range/{pos}",
      (decodeOperand ((#[1, 1, 255, 255, 255, 255] : Array Aiur.G).set! pos 256).toList).isNone)]
  for tag in [2, 3, 4, 255, goldilocksModulus - 1] do
    checks := checks ++ [(s!"operand outer tag/{tag}", (decodeOperand [.ofNat tag, 0, 0, 0, 0, 0]).isNone)]
  checks := checks ++ [
    ("operand Boolean noncanonical payload", (decodeOperand [1, 0, 2, 0, 0, 0]).isNone),
    ("operand scalar unsupported tag", (decodeOperand [1, 5, 0, 0, 0, 0]).isNone),
    ("operand full-field local index is not narrowed", (decodeOperand [0, .ofNat (2 ^ 32), 0, 0, 0, 0]).isNone)]
  return checks

end ScalarOperandTests

public def suite : IO UInt32 := do
  IO.println "IxBy bytecode parser proof components"
  let result : Except String (List Check) := do
    let source ← objectsToplevel
    let compiled ← source.compile
    let pruned ← (source.prune [`ib_load, `ib_u32, `is_run]).compile
    let (_, byte) ← function pruned `ib_byte
    let (reader, _) ← function pruned `ib_byte
    let (_, word) ← function pruned `ib_u32
    let (_, identity) ← function pruned `is_read_id
    let (_, parser) ← function pruned `is_read_ctors
    let (comparer, cmp) ← function pruned `is_id_eq
    let (self, unique) ← function pruned `is_unique_id
    let shapes ← certificateChecks compiled
    let bytes ← byteChecks compiled
    let identities ← identityChecks compiled
    let comparisons ← comparisonChecks compiled
    let uniqueness ← uniquenessChecks compiled
    let declarations ← declarationCertificates compiled
    let declarationRuntime ← declarationChecks compiled
    let prunedCode ← declarationCode pruned
    let loaders ← loaderCertificates compiled
    let loaderFailures ← loaderFailureChecks compiled "full"
    let prunedFailures ← loaderFailureChecks pruned "pruned"
    let prunedLoader ← loaderCode pruned
    let programCertificates ← ProgramPrefixTests.certificates compiled "full"
    let prunedProgramCertificates ← ProgramPrefixTests.certificates pruned "pruned"
    let headerCertificates ← CodeHeaderTests.certificates compiled "full"
    let prunedHeaderCertificates ← CodeHeaderTests.certificates pruned "pruned"
    let headerContinuations ← CodeHeaderTests.continuationChecks compiled "full"
    let prunedHeaderContinuations ← CodeHeaderTests.continuationChecks pruned "pruned"
    let scalarCertificates ← ScalarOperandTests.certificates compiled "full"
    let prunedScalarCertificates ← ScalarOperandTests.certificates pruned "pruned"
    let scalarFailures ← ScalarOperandTests.failureChecks compiled "full"
    let prunedScalarFailures ← ScalarOperandTests.failureChecks pruned "pruned"
    return shapes ++ bytes ++ wordChecks compiled ++ identities ++ comparisons ++ uniqueness ++ emptyChecks compiled ++
      declarations ++ declarationRuntime ++ declarationSuccessChecks compiled "full" ++ declarationSuccessChecks pruned "pruned" ++
      loaders ++ loaderFailures ++ prunedFailures ++ loaderSuccessChecks compiled "full" ++ loaderSuccessChecks pruned "pruned" ++
      loadedDeclarationChecks compiled "full" ++ loadedDeclarationChecks pruned "pruned" ++
      programCertificates ++ prunedProgramCertificates ++
      ProgramPrefixTests.successChecks compiled "full" ++ ProgramPrefixTests.successChecks pruned "pruned" ++
      ProgramPrefixTests.failureChecks compiled "full" ++ ProgramPrefixTests.failureChecks pruned "pruned" ++
      ProgramPrefixTests.loadedChecks compiled "full" ++ ProgramPrefixTests.loadedChecks pruned "pruned" ++
      headerCertificates ++ prunedHeaderCertificates ++
      CodeHeaderTests.headerChecks compiled "full" ++ CodeHeaderTests.headerChecks pruned "pruned" ++
      CodeHeaderTests.zeroChecks compiled "full" ++ CodeHeaderTests.zeroChecks pruned "pruned" ++
      CodeHeaderTests.programChecks compiled "full" ++ CodeHeaderTests.programChecks pruned "pruned" ++
      CodeHeaderTests.loadedChecks compiled "full" ++ CodeHeaderTests.loadedChecks pruned "pruned" ++
      headerContinuations ++ prunedHeaderContinuations ++ scalarCertificates ++ prunedScalarCertificates ++
      ScalarOperandTests.scalarChecks compiled "full" ++ ScalarOperandTests.scalarChecks pruned "pruned" ++
      ScalarOperandTests.operandChecks compiled "full" ++ ScalarOperandTests.operandChecks pruned "pruned" ++
      scalarFailures ++ prunedScalarFailures ++ ScalarOperandTests.layoutChecks ++
      ScalarOperandTests.loadedChecks compiled "full" ++ ScalarOperandTests.loadedChecks pruned "pruned" ++ [
      ("pruned byte-reader certificate", checkByteReader byte 0),
      ("pruned u32-reader certificate with relocated callee", checkWordReader word reader 0),
      ("pruned identity-reader certificate with relocated callee", checkIdReader identity reader 0),
      ("pruned zero-count parser certificate", checkEmptyTableParser parser 0),
      ("pruned comparator certificate", checkIdEq cmp 0),
      ("pruned uniqueness certificate with both relocated callees", checkUnique unique comparer self 0 1),
      ("pruned complete declaration code certificate with all relocated callees", checkDeclarationCode pruned.bytecode prunedCode),
      ("pruned loader bundle with both relocated functions", checkLoaderCode pruned.bytecode prunedLoader)]
  let .ok checks := result
    | IO.eprintln (match result with | .error error => error | _ => "unexpected result"); return 1
  let mut failed := 0
  for (label, ok) in checks do
    if ok then IO.println s!"  ✓ {label}"
    else failed := failed + 1; IO.eprintln s!"  ✗ {label}"
  IO.println s!"{checks.length - failed}/{checks.length} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Aiur.Objects.Parser
