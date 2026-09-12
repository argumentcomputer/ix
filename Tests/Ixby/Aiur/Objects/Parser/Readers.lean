module
public import Tests.Ixby.Aiur.Objects.Parser.Common

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

public def certificateChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

public def byteChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

public def wordChecks (compiled : Aiur.CompiledToplevel) : List Check := Id.run do
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

public def emptyChecks (compiled : Aiur.CompiledToplevel) : List Check := Id.run do
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

end Tests.Ixby.Aiur.Objects.Parser
