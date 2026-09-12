module
public import Tests.Ixby.Aiur.Objects.Parser.ProgramPrefix

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

namespace CodeHeaders
open Ix.Ixby.AiurBackend.Objects.CodeHeaders

private def code (compiled : Aiur.CompiledToplevel) : Except String HeaderCode := do
  let program ← ProgramPrefix.code compiled
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

public def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

public def headerChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def zeroChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def programChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let finish : Aiur.G := .ofNat (goldilocksModulus - 2)
  let outputs := #[0, 1, 48, 65, 71, 80, 89, 97]
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    let h := ProgramPrefix.wireHeader (2 ^ 32 - 1) count
    for functions in [:10] do
      let raw := ProgramPrefix.payload h decls ++ (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8
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
    let raw := ProgramPrefix.payload (ProgramPrefix.wireHeader 0 0) [] ++
      (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8
    let (st, pointer) := storePrefix initial raw finish
    checks := checks ++ [(s!"{label} program rejects high function count before Call/{functions}",
      failed (snapshot compiled `is_run #[pointer, input] st 1) .assertFailed)]
  let prefixBytes := ProgramPrefix.payload (ProgramPrefix.wireHeader 0 1) (wireDeclarations 1)
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
  let good := ProgramPrefix.payload (ProgramPrefix.wireHeader 0 0) [] ++ #[1, 0, 0, 0]
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

public def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
  let input : Aiur.G := .ofNat (goldilocksModulus - 1)
  let suffix : Array Aiur.G := #[90, 91, 92]
  let outputs := #[0, 1, 48, 65, 71, 80, 89, 97]
  let mut checks : List Check := []
  for count in [:17] do
    let decls := wireDeclarations count
    let h := ProgramPrefix.wireHeader (2 ^ 32 - 1) count
    for functions in [1, 8] do
      let raw := ProgramPrefix.payload h decls ++ (wordBytes functions).bytes.toArray.map Aiur.G.ofUInt8 ++ suffix
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
    let raw := ProgramPrefix.payload (ProgramPrefix.wireHeader 0 0) [] ++
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
      ("function count", ProgramPrefix.payload (ProgramPrefix.wireHeader 0 0) [], (wordBytes 1).bytes.toArray.map Aiur.G.ofUInt8),
      ("function header", #[], (wireFunction 0 0 1).bytes.toArray.map Aiur.G.ofUInt8),
      ("block header", #[], (wordBytes 64).bytes.toArray.map Aiur.G.ofUInt8)] do
    for position in [:fieldBytes.size] do
      let raw := prefixBytes ++ fieldBytes.set! position (.ofNat (2 ^ 32))
      checks := checks ++ [(s!"{label} loader rejects non-byte {name}/{position}", failed
        (snapshot compiled `ib_load #[0, .ofNat raw.size] (rawAdvice initial 0 0 raw.size raw) (raw.size + 1)) .u8RangeCheckFailed)]
  return checks

public def continuationChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

end CodeHeaders

end Tests.Ixby.Aiur.Objects.Parser
