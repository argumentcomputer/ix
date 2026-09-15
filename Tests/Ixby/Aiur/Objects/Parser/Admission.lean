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

public def loaderCode (compiled : Aiur.CompiledToplevel) : Except String LoaderCode := do
  let (reader, _) ← function compiled `ib_read_advice
  let (loader, _) ← function compiled `ib_load
  return { reader, loader }

public def loaderCertificates (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

public def loaderSuccessChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def loaderFailureChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

public def loadedDeclarationChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

end Tests.Ixby.Aiur.Objects.Parser
