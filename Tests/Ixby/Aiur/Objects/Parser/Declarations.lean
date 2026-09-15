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

public def declarationCode (compiled : Aiur.CompiledToplevel) : Except String DeclarationCode := do
  let (reader, _) ← function compiled `ib_byte
  let (identity, _) ← function compiled `is_read_id
  let (comparer, _) ← function compiled `is_id_eq
  let (unique, _) ← function compiled `is_unique_id
  let (self, _) ← function compiled `is_read_ctors
  return { reader, identity, comparer, unique, self }

public def declarationCertificates (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

public def declarationSuccessChecks (compiled : Aiur.CompiledToplevel) (label : String) : List Check := Id.run do
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

public def declarationChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

end Tests.Ixby.Aiur.Objects.Parser
