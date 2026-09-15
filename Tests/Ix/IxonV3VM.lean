module
public import Tests.Ix.IxonV3
public import Tests.Aiur.Common
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.Resource.Claim
public import Tests.Ix.ResourceAddressed

public section
namespace Tests.IxonV3

def codecEntrypoints := ⟦
  pub fn ixon_expr_decode() {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    let (_, rest) = get_expr(bytes);
    assert_eq!(load(rest), ListNode.Nil, "trailing expression bytes");
  }

  pub fn ixon_const_decode() {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    let (_, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil, "trailing constant bytes");
  }

  pub fn ixon_expr_codec() {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    let (expr, rest) = get_expr(bytes);
    assert_eq!(load(rest), ListNode.Nil, "trailing expression bytes");
    let encoded = put_expr(load(expr), store(ListNode.Nil));
    assert_eq!(bytes, encoded, "VM expression bytes differ");
  }

  pub fn ixon_const_codec() {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil, "trailing constant bytes");
    let encoded = put_constant(constant, store(ListNode.Nil));
    assert_eq!(bytes, encoded, "VM constant bytes differ");
  }
⟧

def codecToplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← IxVM.core.merge IxVM.byteStream
  let vm ← vm.merge IxVM.ixon
  let vm ← vm.merge IxVM.ixonSerialize
  let vm ← vm.merge IxVM.ixonDeserialize
  let vm ← vm.merge codecEntrypoints
  return vm.prune [`ixon_expr_codec, `ixon_const_codec,
    `ixon_expr_decode, `ixon_const_decode]

def codecBuffer (bytes : ByteArray) : Aiur.IOBuffer :=
  (default : Aiur.IOBuffer).extend 0 #[0] (bytes.data.map .ofUInt8)

def checkVMBytes (env : AiurTestEnv) (name : String) (bytes : ByteArray)
    (accept : Bool) (fnName : Lean.Name := `ixon_expr_codec) : IO Nat := do
  let some index := env.compiled.getFuncIdx fnName
    | throw <| IO.userError "missing VM codec entrypoint"
  let buffer := codecBuffer bytes
  let executed := env.compiled.bytecode.execute index #[] buffer
  match executed with
  | .ok (out, io, _) =>
    unless accept && out.isEmpty && io == buffer do
      throw <| IO.userError s!"{name}: VM unexpectedly accepted or changed output"
  | .error e =>
    if accept then throw <| IO.userError s!"{name}: VM execution failed: {e}"
  let (interpreted, state) := Aiur.runFunction env.decls (.mk fnName) [] buffer
  match interpreted with
  | .ok value =>
    let flattened := Aiur.flattenValue env.decls (fun g => env.compiled.getFuncIdx g.toName) value
    unless accept && flattened.isEmpty && state.ioBuffer == buffer do
      throw <| IO.userError s!"{name}: source interpretation unexpectedly accepted or changed output"
  | .error e =>
    if accept then throw <| IO.userError s!"{name}: source interpretation failed: {e}"
  return 2

/-- Every counted decoding path accepts one complete element and rejects a
short stream when the count is two or the largest canonical UInt64. Each
truncated stream supplies one element, then ends. The decode-only entrypoints
ensure rejection happens before reserialization. -/
def runCountTruncations (env : AiurTestEnv) : IO Nat := do
  let mut checks := 0
  for count in [1, 2, (2 ^ 64 - 1 : Nat)] do
    let large := count > 2
    let accept := count == 1
    let suffix : Array UInt8 := if large then Array.replicate 8 0xff else #[]
    let tag0 : ByteArray := .mk ((if large then #[0x87] else #[count.toUInt8]) ++ suffix)
    let tag4 (flag : UInt8) : ByteArray :=
      .mk (#[flag * 16 + (if large then 15 else count.toUInt8)] ++ suffix)
    let finish (bytes tail : ByteArray) := if accept then bytes ++ tail else bytes
    let countLabel := if large then "max-u64" else toString count
    for (label, bytes) in [
        ("ref-universes", tag4 2 ++ .mk #[0, 0]),
        ("rec-universes", tag4 3 ++ .mk #[0, 0]),
        ("app-arguments", tag4 7 ++ .mk #[0x10, 0x10]),
        ("lambda-binders", finish (tag4 8 ++ .mk #[0x07, 0x00]) (.mk #[0x10])),
        ("forall-binders", finish (tag4 9 ++ .mk #[0x17, 0x00]) (.mk #[0x10]))] do
      checks := checks + (← checkVMBytes env s!"{label}-{countLabel}"
        bytes accept `ixon_expr_decode)
    let axiomPrefix : ByteArray := .mk #[0xd2, 0, 0, 0]
    for (label, bytes) in [
        ("sharing", finish (axiomPrefix ++ tag0 ++ .mk #[0x10]) (.mk #[0, 0])),
        ("references", finish (axiomPrefix ++ .mk #[0] ++ tag0 ++
          .mk (Array.replicate 32 0)) (.mk #[0])),
        ("universes", axiomPrefix ++ .mk #[0, 0] ++ tag0 ++ .mk #[0]),
        ("recursor-rules", finish (.mk #[0xd1, 0, 0, 0, 0, 0, 0, 0] ++
          tag0 ++ .mk #[0, 0x10]) (.mk #[0, 0, 0])),
        ("constructors", finish (.mk #[0xc1, 1, 0, 0, 0, 0, 0] ++
          tag0 ++ .mk #[0, 0, 0, 0, 0, 0]) (.mk #[0, 0, 0])),
        ("mutual-members", finish (tag4 12 ++ .mk #[0, 0x06, 0x05, 0x00, 0x10])
          (.mk #[0, 0, 0]))] do
      checks := checks + (← checkVMBytes env s!"{label}-{countLabel}"
        bytes accept `ixon_const_decode)
  return checks

def replaceClaimBytes (witness : IxVM.ClaimHarness.ClaimWitness) (bytes : ByteArray) :
    IxVM.ClaimHarness.ClaimWitness :=
  let key := IxVM.ClaimHarness.packedDigestKey (Address.blake3 bytes)
  { witness with
    input := key
    inputIOBuffer := witness.inputIOBuffer.extend 0 key (bytes.data.map .ofUInt8) }

def checkVMClaim (env : AiurTestEnv) (label : String)
    (witness : IxVM.ClaimHarness.ClaimWitness) (accept : Bool) : IO Nat := do
  let index := env.compiled.getFuncIdx witness.funcName |>.get!
  let executed := env.compiled.bytecode.execute index witness.input witness.inputIOBuffer
  match executed with
  | .ok (out, io, _) =>
    unless accept && out.isEmpty && io == witness.inputIOBuffer do
      throw <| IO.userError s!"{label}: VM claim unexpectedly accepted or changed output"
  | .error e =>
    if accept then throw <| IO.userError s!"{label}: VM claim execution failed: {e}"
  match env.compiled.bytecode.executeIxVM index witness.input witness.inputIOBuffer with
  | .ok (out, io, counts) =>
    let .ok (expectedOut, expectedIO, expectedCounts) := executed
      | throw <| IO.userError s!"{label}: generated VM accepted a rejected claim"
    unless accept && out == expectedOut && io == expectedIO &&
        counts.size == expectedCounts.size &&
        (counts.zip expectedCounts).all (fun (actual, expected) =>
          actual.uniqueRows == expected.uniqueRows && actual.totalHits == expected.totalHits) do
      throw <| IO.userError s!"{label}: generated VM output or query counts differ"
  | .error e =>
    if accept then throw <| IO.userError s!"{label}: generated VM claim execution failed: {e}"
  let name := Aiur.Global.mk witness.funcName
  let inputTypes := match env.decls.getByKey name with
    | some (.function f) => f.inputs.map (·.2)
    | _ => []
  let inputs := Aiur.unflattenInputs env.decls witness.input inputTypes
  match Aiur.runFunction env.decls name inputs witness.inputIOBuffer with
  | (.ok _, state) =>
    unless accept && state.ioBuffer == witness.inputIOBuffer do
      throw <| IO.userError s!"{label}: claim interpreter unexpectedly accepted"
  | (.error e, _) =>
    if accept then throw <| IO.userError s!"{label}: claim interpretation failed: {e}"
  return 3

def runVMClaims : IO Nat := do
  let vm ← IO.ofExcept (AiurTestEnv.build IxVM.ixVM)
  let (base, unit) := Tests.ResourceAddressed.unitEnv
  let constant := Tests.ResourceAddressed.identity unit
  let (env, target) := Tests.ResourceAddressed.store base constant
  let env := { env with anonHints := env.anonHints.insert target .opaque }
  let some tree := IxVM.ClaimHarness.envCanonicalTree env
    | throw <| IO.userError "VM claim fixture has no tree"
  let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert tree.root tree
  let mut checks := 0
  for claim in [Ix.Claim.check target none, .checkEnv tree.root none,
      .reveal target (.defn none none none
        (some (Address.blake3 (Ixon.runPut (Ixon.putExpr
          (.all Tests.ResourceAddressed.linearLocal .localShared (.ref 0 #[]) (.ref 0 #[])))))) none),
      .contains tree.root target] do
    let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim trees)
    checks := checks + (← checkVMClaim vm "v3 claim" witness true)
    let bytes := Ix.Claim.ser claim
    for bad in [bytes.push 0, bytes.set! 1 2, bytes.set! 2 255,
        bytes.extract 0 (bytes.size - 1)] do
      checks := checks + (← checkVMClaim vm "invalid v3 claim"
        (replaceClaimBytes witness bad) false)
  -- Erased typing deliberately accepts a resource-invalid body. The
  -- validator byte keeps that fact separate from resource admission.
  let (escaping, target) := Tests.ResourceAddressed.store base
    (Tests.ResourceAddressed.identity unit Tests.ResourceAddressed.linearLocal .shared)
  let escaping := { escaping with anonHints := escaping.anonHints.insert target .opaque }
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness escaping (.check target none))
  checks := checks + (← checkVMClaim vm "explicit erased typing" witness true)
  unless (Ix.Resource.validate escaping {}).toOption.isNone do
    throw <| IO.userError "escaping fixture passed native resource validation"
  -- Resource claims have a native validator, and must fail explicitly at
  -- the circuit boundary rather than accepting a host validation result.
  let profile : Ix.Resource.Profile := {}
  let claim ← IO.ofExcept (Ix.Resource.makeClaim env profile)
  let profileAddr ← IO.ofExcept profile.address
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim trees
    (({} : Std.HashMap Address ByteArray).insert profileAddr profile.bytes))
  checks := checks + (← checkVMClaim vm "unsupported circuit resource validator" witness false)
  -- The positive proof uses the valid annotated target from the original env.
  let validTarget := Tests.ResourceAddressed.store base constant |>.2
  let checkWitness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env (.check validTarget none))
  let index := vm.compiled.getFuncIdx checkWitness.funcName |>.get!
  let (claim, proof, _) ← IO.ofExcept
    (vm.aiurSystem.prove index checkWitness.input checkWitness.inputIOBuffer)
  IO.ofExcept (vm.aiurSystem.verify claim (Aiur.Proof.ofBytes proof.toBytes))
  return checks + 1

def runVM : IO Nat := do
  let env ← IO.ofExcept (AiurTestEnv.build codecToplevel)
  let mut checks := 0
  let file ← IO.FS.readFile "Tests/Fixtures/ixon-v3/expressions.txt"
  let mut cases := modeCases.map fun (name, _, bytes) => (name, bytes)
  for (name, _) in fixtures do
    let some line := (file.splitOn "\n").find? (·.startsWith (name ++ " "))
      | throw <| IO.userError s!"missing fixture {name}"
    let some hex := (line.splitOn " ")[1]?
      | throw <| IO.userError s!"missing fixture bytes {name}"
    let bytes ← IO.ofExcept (parseHex hex.toList)
    cases := cases ++ [(name, ByteArray.mk bytes.toArray)]
  for (name, bytes) in cases do
    checks := checks + (← checkVMBytes env name bytes true)
    checks := checks + (← checkVMBytes env s!"{name}-trailing" (bytes.push 0) false)
    for n in [:bytes.size] do
      checks := checks + (← checkVMBytes env s!"{name}-truncated-{n}" (bytes.extract 0 n) false)
  for bytes in malformed do
    checks := checks + (← checkVMBytes env "malformed" bytes false)
  checks := checks + (← runCountTruncations env)
  for code in [16:256] do
    for bytes in #[ByteArray.mk #[0x81, code.toUInt8, 0x00, 0x10],
        ByteArray.mk #[0xA0, code.toUInt8, 0x00, 0x10, 0x10]] do
      checks := checks + (← checkVMBytes env "reserved-binder-bits" bytes false)
  for code in [64:256] do
    checks := checks + (← checkVMBytes env "reserved-forall-bits"
      (.mk #[0x91, code.toUInt8, 0x00, 0x10]) false)
  -- Independently authored declaration bytes cover the six unchanged headers.
  for hex in [
      "d006050010000000",
      "d101050102030400010310000000",
      "d2010500000000",
      "d3020500000000",
      "c101000502030001010501020300000000"] do
    let bytes ← IO.ofExcept (parseHex hex.toList)
    let bytes := ByteArray.mk bytes.toArray
    checks := checks + (← checkVMBytes env "declaration" bytes true `ixon_const_codec)
    checks := checks + (← checkVMBytes env "declaration-trailing" (bytes.push 0) false `ixon_const_codec)
    for n in [:bytes.size] do
      checks := checks + (← checkVMBytes env "declaration-truncated" (bytes.extract 0 n) false `ixon_const_codec)
  -- Exercise the proof pipeline for an explicit scoped-borrow representation.
  let bytes := ByteArray.mk #[0xA2, 0x0e, 0x00, 0x41, 0x02, 0x11, 0x10]
  let index := env.compiled.getFuncIdx `ixon_expr_codec |>.get!
  let (claim, proof, _) ← IO.ofExcept (env.aiurSystem.prove index #[] (codecBuffer bytes))
  let proof := Aiur.Proof.ofBytes proof.toBytes
  IO.ofExcept (env.aiurSystem.verify claim proof)
  -- Execute and prove the actual production claim boundary as well.
  return checks + 2 + (← runVMClaims)

end Tests.IxonV3
