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

namespace Operands

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

public def certificates (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

public def scalarChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def operandChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def failureChecks (compiled : Aiur.CompiledToplevel) (label : String) : Except String (List Check) := do
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

public def loadedChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def layoutChecks : IO (List Check) := do
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

end Operands

end Tests.Ixby.Aiur.Objects.Parser
