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
  let vm ← Aiur.Library.core.merge Aiur.Library.byteStream
  let vm ← vm.merge IxVM.ixon
  let vm ← vm.merge IxVM.ixonSerialize
  let vm ← vm.merge IxVM.ixonDeserialize
  let vm ← vm.merge codecEntrypoints
  return vm.prune [`ixon_expr_codec, `ixon_const_codec,
    `ixon_expr_decode, `ixon_const_decode]

def codecBuffer (bytes : ByteArray) : Aiur.IOBuffer :=
  (default : Aiur.IOBuffer).extend 0 #[0] (bytes.data.map .ofUInt8)

/-- Check acceptance, empty output, and an unchanged I/O buffer on each interpreter.
Production claims also run through the generated Rust VM with query-count parity. -/
def checkVM (env : AiurTestEnv) (label : String) (fnName : Lean.Name)
    (input : Array Aiur.G) (buffer : Aiur.IOBuffer) (accept : Bool)
    (generated : Bool := false) : IO Nat := do
  let some index := env.compiled.getFuncIdx fnName
    | throw <| IO.userError s!"{label}: missing VM entrypoint {fnName}"
  let executed := env.compiled.bytecode.execute index input buffer
  match executed with
  | .ok (out, io, _) =>
    unless accept && out.isEmpty && io == buffer do
      throw <| IO.userError s!"{label}: VM unexpectedly accepted or changed output"
  | .error e =>
    if accept then throw <| IO.userError s!"{label}: VM execution failed: {e}"
  if generated then
    match env.compiled.bytecode.executeIxVM index input buffer with
    | .ok (out, io, counts) =>
      let .ok (expectedOut, expectedIO, expectedCounts) := executed
        | throw <| IO.userError s!"{label}: generated VM accepted a rejected input"
      unless accept && out == expectedOut && io == expectedIO &&
          counts.size == expectedCounts.size &&
          (counts.zip expectedCounts).all (fun (actual, expected) =>
            actual.uniqueRows == expected.uniqueRows && actual.totalHits == expected.totalHits) do
        throw <| IO.userError s!"{label}: generated VM output or query counts differ"
    | .error e =>
      if accept then throw <| IO.userError s!"{label}: generated VM execution failed: {e}"
  let name := Aiur.Global.mk fnName
  let some (.function function) := env.decls.getByKey name
    | throw <| IO.userError s!"{label}: missing source entrypoint {fnName}"
  let inputs := Aiur.unflattenInputs env.decls input (function.inputs.map (·.2))
  let (interpreted, state) := Aiur.runFunction env.decls name inputs buffer
  match interpreted with
  | .ok value =>
    let flattened := Aiur.flattenValue env.decls (fun g => env.compiled.getFuncIdx g.toName) value
    unless accept && flattened.isEmpty && state.ioBuffer == buffer do
      throw <| IO.userError s!"{label}: source interpretation unexpectedly accepted or changed output"
  | .error e =>
    if accept then throw <| IO.userError s!"{label}: source interpretation failed: {e}"
  return if generated then 3 else 2

def checkVMBytes (env : AiurTestEnv) (name : String) (bytes : ByteArray)
    (accept : Bool) (fnName : Lean.Name := `ixon_expr_codec) : IO Nat :=
  checkVM env name fnName #[] (codecBuffer bytes) accept

def checkVMEncoding (env : AiurTestEnv) (name : String) (bytes : ByteArray)
    (fnName : Lean.Name := `ixon_expr_codec) : IO Nat := do
  let mut checks ← checkVMBytes env name bytes true fnName
  checks := checks + (← checkVMBytes env s!"{name}-trailing" (bytes.push 0) false fnName)
  for n in [:bytes.size] do
    checks := checks + (← checkVMBytes env s!"{name}-truncated-{n}" (bytes.extract 0 n) false fnName)
  return checks

def checkVMProof (env : AiurTestEnv) (fnName : Lean.Name)
    (input : Array Aiur.G) (buffer : Aiur.IOBuffer) : IO Unit := do
  let index := env.compiled.getFuncIdx fnName |>.get!
  let (claim, proof, _) ← IO.ofExcept (env.aiurSystem.prove index input buffer)
  IO.ofExcept (env.aiurSystem.verify claim (Aiur.Proof.ofBytes proof.toBytes))

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
    (witness : IxVM.ClaimHarness.ClaimWitness) (accept : Bool) : IO Nat :=
  checkVM env label witness.funcName witness.input witness.inputIOBuffer accept (generated := true)

def runVMClaims : IO Nat := do
  let vm ← IO.ofExcept (AiurTestEnv.build IxVM.ixVM)
  let (base, unit) := Tests.ResourceAddressed.unitEnv
  let constant := Tests.ResourceAddressed.identity unit
  let (env, validTarget) := Tests.ResourceAddressed.store base constant
  let env := { env with anonHints := env.anonHints.insert validTarget .opaque }
  let some tree := IxVM.ClaimHarness.envCanonicalTree env
    | throw <| IO.userError "VM claim fixture has no tree"
  let trees := ({} : Std.HashMap Address Ix.AssumptionTree).insert tree.root tree
  let mut checks := 0
  let revealedType := Address.blake3 (Ixon.runPut (Ixon.putExpr
    (.all Tests.ResourceAddressed.linearLocal .localShared (.ref 0 #[]) (.ref 0 #[]))))
  for (name, claim) in [
      ("check", Ix.Claim.check validTarget none),
      ("check-env", .checkEnv tree.root none),
      ("reveal", .reveal validTarget (.defn none none none (some revealedType) none)),
      ("contains", .contains tree.root validTarget)] do
    let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim trees)
    checks := checks + (← checkVMClaim vm name witness true)
    let bytes := Ix.Claim.ser claim
    for (mutation, bad) in [
        ("trailing", bytes.push 0), ("legacy-version", bytes.set! 1 2),
        ("wrong-validator", bytes.set! 2 255), ("truncated", bytes.extract 0 (bytes.size - 1))] do
      checks := checks + (← checkVMClaim vm s!"{name}-{mutation}"
        (replaceClaimBytes witness bad) false)
  -- Erased typing deliberately accepts a resource-invalid body. The
  -- validator byte keeps that fact separate from resource admission.
  let (escaping, escapingTarget) := Tests.ResourceAddressed.store base
    (Tests.ResourceAddressed.identity unit Tests.ResourceAddressed.linearLocal .shared)
  let escaping := { escaping with anonHints := escaping.anonHints.insert escapingTarget .opaque }
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness escaping (.check escapingTarget none))
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
  let checkWitness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env (.check validTarget none))
  checkVMProof vm checkWitness.funcName checkWitness.input checkWitness.inputIOBuffer
  return checks + 1

def runVM (cases : List ExprCase) : IO Nat := do
  let env ← IO.ofExcept (AiurTestEnv.build codecToplevel)
  let mut checks := 0
  for test in cases do
    checks := checks + (← checkVMEncoding env test.name test.bytes)
  for (name, bytes) in rejectedExprCases do
    checks := checks + (← checkVMBytes env name bytes false)
  checks := checks + (← runCountTruncations env)
  -- Independently authored declaration bytes cover the six unchanged headers.
  for (name, hex) in [
      ("definition", "d006050010000000"),
      ("recursor", "d101050102030400010310000000"),
      ("axiom", "d2010500000000"),
      ("quotient", "d3020500000000"),
      ("mutual", "c101000502030001010501020300000000")] do
    let some bytes := bytesOfHex hex
      | throw <| IO.userError s!"invalid declaration fixture hex: {name}"
    checks := checks + (← checkVMEncoding env name bytes `ixon_const_codec)
  -- Exercise the proof pipeline for an explicit scoped-borrow representation.
  let bytes := ByteArray.mk #[0xA2, 0x0e, 0x00, 0x41, 0x02, 0x11, 0x10]
  checkVMProof env `ixon_expr_codec #[] (codecBuffer bytes)
  -- Execute and prove the actual production claim boundary as well.
  return checks + 2 + (← runVMClaims)

end Tests.IxonV3
