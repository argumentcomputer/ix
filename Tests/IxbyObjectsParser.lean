module
import Ix.Ixby.Aiur.ObjectsParser
import Ix.Ixby.Aiur.ObjectsIdentity
import Ix.Ixby.Aiur.Objects
import Ix.Aiur.Compiler

/-! Structural certificate and bytecode-contract tests. Forged byte cells and
mutated functions are diagnostic fixtures, not production advice or new keys.
The zero-count certificate deliberately does not certify the recursive branch. -/

namespace Tests.IxbyObjectsParser

open Ix.Ixby Ix.Ixby.AiurBackend
open ObjectsMemory ObjectsTable ObjectsParser
open ObjectsIdentity
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

public def suite : IO UInt32 := do
  IO.println "IxBy bytecode parser proof components"
  let result : Except String (List Check) := do
    let source ← objectsToplevel
    let compiled ← source.compile
    let pruned ← (source.prune [`ib_u32, `is_read_ctors]).compile
    let (_, byte) ← function pruned `ib_byte
    let (reader, _) ← function pruned `ib_byte
    let (_, word) ← function pruned `ib_u32
    let (_, identity) ← function pruned `is_read_id
    let (_, parser) ← function pruned `is_read_ctors
    let shapes ← certificateChecks compiled
    let bytes ← byteChecks compiled
    let identities ← identityChecks compiled
    return shapes ++ bytes ++ wordChecks compiled ++ identities ++ emptyChecks compiled ++ [
      ("pruned byte-reader certificate", checkByteReader byte 0),
      ("pruned u32-reader certificate with relocated callee", checkWordReader word reader 0),
      ("pruned identity-reader certificate with relocated callee", checkIdReader identity reader 0),
      ("pruned zero-count parser certificate", checkEmptyTableParser parser 0)]
  let .ok checks := result
    | IO.eprintln (match result with | .error error => error | _ => "unexpected result"); return 1
  let mut failed := 0
  for (label, ok) in checks do
    if ok then IO.println s!"  ✓ {label}"
    else failed := failed + 1; IO.eprintln s!"  ✗ {label}"
  IO.println s!"{checks.length - failed}/{checks.length} checks passed"
  return if failed == 0 then 0 else 1

end Tests.IxbyObjectsParser
