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

public def identityChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

public def comparisonChecks (compiled : Aiur.CompiledToplevel) : Except String (List Check) := do
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

end Tests.Ixby.Aiur.Objects.Parser
