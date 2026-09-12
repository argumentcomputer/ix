module
public import Tests.Ixby.Aiur.Objects.Parser.Declarations

namespace Tests.Ixby.Aiur.Objects.Parser

open Ix.Ixby Ix.Ixby.AiurBackend
open Ix.Ixby.AiurBackend.Objects.Memory Ix.Ixby.AiurBackend.Objects.Table Ix.Ixby.AiurBackend.Objects.Parser
open Ix.Ixby.AiurBackend.Objects.Identity
open Ix.Ixby.AiurBackend.Objects.Equality Ix.Ixby.AiurBackend.Objects.Unique
open Ix.Ixby.AiurBackend.Objects.Declarations
open Ix.Ixby.AiurBackend.Objects.Admission
open Aiur.Bytecode.Eval

namespace ProgramPrefix
open Ix.Ixby.AiurBackend.Objects.ProgramPrefix

public def code (compiled : Aiur.CompiledToplevel) : Except String ProgramCode := do
  let (runner, _) ← function compiled `is_run
  return { runner, declarations := ← declarationCode compiled }

public def wireHeader (entry count : Nat) (revision := 0) : HeaderBytes :=
  ⟨⟨73, 88, 66, 89⟩, wordBytes revision, wordBytes entry, wordBytes count⟩

public def payload (h : HeaderBytes) (decls : List DeclarationBytes) : Array Aiur.G :=
  h.bytes.toArray.map Aiur.G.ofUInt8 ++ declarationPayload decls

/-- Run the actual compiled sixty operations, not the certificate's model. -/
private def prefixSnapshot (compiled : Aiur.CompiledToplevel) (st : EvalState)
    (program input : Aiur.G) (fuel : Nat) : Except String (Array Aiur.G × EvalState) := do
  let (_, runner) ← function compiled `is_run
  match runOps compiled.bytecode fuel (runner.body.ops.toList.take 60).toArray { st with map := #[program, input] } 0 with
  | .ok after => return (#[after.map.getD 48 0, after.map.getD 65 0, after.map.getD 71 0,
      after.map.getD 72 0, after.map.getD 0 0, after.map.getD 1 0], after)
  | .error error => throw (reprStr error)

public def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

public def successChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def failureChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

end ProgramPrefix

end Tests.Ixby.Aiur.Objects.Parser
