import IxCCTests.Aiur.WireFixtures

namespace IxCCTests.Aiur.WireRun

open IxCC.Aiur.Wire
open IxCC.Ixon
open IxCCTests.Aiur.WireFixtures
open _root_.IxCC.Vendor.Aiur (G gSize)
open _root_.IxCC.Vendor.Aiur.Bytecode

private def rejected (result : Except String α) (part : String) : Bool :=
  match result with
  | .ok _ => false
  | .error message => message.contains part

private def frameOp (payload : ByteArray) : ByteArray :=
  expectedHeader ++ bytes [1, 1] ++ payload ++ bytes [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def frameCtrl (payload : ByteArray) : ByteArray :=
  expectedHeader ++ bytes [1, 0] ++ payload ++ bytes [0, 0, 0, 0, 0, 0, 0, 0, 0]

private def withFunction (value : Function) : Toplevel :=
  { corpus with functions := corpus.functions.set! 0 value }

private def identityVariants : List (String × Toplevel) := Id.run do
  let fn := corpus.functions[0]!
  let circuit := corpus.circuits[0]!
  let changeCircuit := fun value => { corpus with circuits := corpus.circuits.set! 0 value }
  return [
    ("function order", { corpus with functions := corpus.functions.reverse }),
    ("memory order", { corpus with memorySizes := corpus.memorySizes.reverse }),
    ("memory size", { corpus with memorySizes := corpus.memorySizes.set! 1 2 }),
    ("entry flag", withFunction { fn with entry := true }),
    ("constrained flag", withFunction { fn with constrained := true }),
    ("input size", withFunction { fn with layout := { fn.layout with inputSize := 8 } }),
    ("selectors", withFunction { fn with layout := { fn.layout with selectors := 9 } }),
    ("auxiliaries", withFunction { fn with layout := { fn.layout with auxiliaries := 10 } }),
    ("lookups", withFunction { fn with layout := { fn.layout with lookups := 11 } }),
    ("opcode order", withFunction { fn with body := { fn.body with ops := fn.body.ops.reverse } }),
    ("hint call flag", withFunction { fn with body := { fn.body with
      ops := fn.body.ops.set! 5 (.call 3 #[1, 128] 2 false) } }),
    ("circuit order", { corpus with circuits := corpus.circuits.reverse }),
    ("circuit name", changeCircuit { circuit with name := "α" }),
    ("circuit members", changeCircuit { circuit with members := #[0, 1, 1] }),
    ("circuit input", changeCircuit { circuit with layout := { circuit.layout with inputSize := 12 } }),
    ("circuit selectors", changeCircuit { circuit with layout := { circuit.layout with selectors := 13 } }),
    ("circuit auxiliaries", changeCircuit { circuit with layout := { circuit.layout with auxiliaries := 14 } }),
    ("circuit lookups", changeCircuit { circuit with layout := { circuit.layout with lookups := 15 } }),
    ("component order", { corpus with callComponents := #[⟨0, false⟩, ⟨0, true⟩] }),
    ("component rank", { corpus with callComponents := #[⟨1, true⟩, ⟨0, true⟩] }),
    ("ranked fallback", { corpus with callComponents := #[] })]

def run : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test := fun label condition => do
    unless condition do throw (IO.userError s!"Aiur wire regression failed: {label}")
    count.modify (· + 1)
  test "fixed domain and revision" (header == expectedHeader)
  test "complete opcode inventory" (opcodes.length == 34)
  for (name, op, expected) in opcodes do
    test s!"{name} independent spelling" (opBytes op == bytes expected)
    test s!"{name} bounded reader" (match runGet (getOp {}) (bytes expected) with
      | .ok actual => actual == op | .error _ => false)
  for (name, value, expected) in fixtures do
    test s!"{name} golden preimage" (preimage value == expected)
    test s!"{name} checked encoder" ((encodeChecked {} value).isOk)
    test s!"{name} strict decode" (match decode {} expected with
      | .ok actual => preimage actual == expected | .error _ => false)
    test s!"{name} addressed component ingress" ((ingest {} {} expected (address value)).isOk)
  let largest := G.ofNat (gSize.toNat - 1)
  test "field p minus one bytes" (fieldBytes largest == bytes [0, 0, 0, 0, 255, 255, 255, 255])
  test "field p minus one roundtrip" (match runGet getField (fieldBytes largest) with
    | .ok value => value == largest | .error _ => false)
  test "reject field p" (rejected (runGet getField (bytes [1, 0, 0, 0, 255, 255, 255, 255])) "noncanonical")
  test "reject field all ones" (rejected (runGet getField (bytes [255, 255, 255, 255, 255, 255, 255, 255])) "noncanonical")
  let wide : Op := .eqZero (2 ^ 80)
  test "large natural is not truncated" (opBytes wide == bytes [4, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8])
  test "large natural decoded exactly" (match runGet (getOp {}) (opBytes wide) with
    | .ok (.eqZero value) => value == 2 ^ 80 | _ => false)
  test "none versus empty assertion string" (opBytes (.assertEq #[] #[] none) != opBytes (.assertEq #[] #[] (some "")))
  test "none versus empty debug values" (opBytes (.debug "" none) != opBytes (.debug "" (some #[])))
  test "return versus yield" (ctrlBytes (.return 0 #[]) != ctrlBytes (.yield 0 #[]))
  for (name, invalid, message) in [
      ("unknown opcode", frameOp (bytes [34]), "invalid tag"),
      ("unknown control", frameCtrl (bytes [4]), "invalid tag"),
      ("invalid Boolean", frameOp (bytes [5, 0, 0, 0, 2]), "boolean"),
      ("invalid option", frameOp (bytes [26, 0, 2]), "invalid tag"),
      ("invalid UTF-8", frameOp (bytes [26, 1, 255, 0]), "UTF-8"),
      ("nonminimal natural", frameOp (bytes [4, 128, 0]), "canonical"),
      ("nonminimal count", expectedHeader ++ bytes [128, 0, 0, 0, 0], "canonical"),
      ("field modulus", frameOp (bytes [0, 1, 0, 0, 0, 255, 255, 255, 255]), "noncanonical"),
      ("huge sequence", expectedHeader ++ bytes [128, 128, 128, 128, 128, 128, 128, 128, 128, 2], "sequence"),
      ("huge blob", frameOp (bytes [26, 128, 128, 128, 128, 128, 128, 128, 128, 128, 2]), "blob"),
      ("trailing byte", counterExpected.push 0, "trailing"),
      ("truncated field", frameOp (bytes [0]) |>.extract 0 (expectedHeader.size + 3), "EOF") ] do
    test name (rejected (decode {} invalid) message)
  test "wrong domain" ((decode {} (counterExpected.set! 0 0)).isOk.not)
  test "wrong revision" ((decode {} (counterExpected.set! 20 0)).isOk.not)
  for cut in [:counterExpected.size] do
    test s!"truncation {cut}" ((decode {} (counterExpected.extract 0 cut)).isOk.not)
  test "input byte limit" (rejected (decode { maxBytes := counterExpected.size - 1 } counterExpected) "byte limit")
  test "sequence budget" (rejected (decode { maxSequence := 0 } counterExpected) "sequence")
  test "natural width budget" (rejected (decode { maxNatBytes := 1 } (frameOp (opBytes wide))) "recursion limit")
  test "blob budget" (rejected (decode { maxBlobBytes := 0 } counterExpected) "blob")
  test "control depth budget" (rejected (decode { maxDepth := 1 } counterExpected) "depth")
  test "exact control depth" ((decode { maxDepth := 2 } counterExpected).isOk)
  test "empty artifact at depth zero" ((decode { maxDepth := 0 } (preimage empty)).isOk)
  test "encoder byte limit" ((encodeChecked { maxBytes := 1 } counter).isOk.not)
  test "encoder representation limit" ((encodeChecked { maxDepth := 1 } counter).isOk.not)
  test "wrong claimed root" (rejected (decodeAddressed {} counterExpected (Address.replicate 0)) "root mismatch")
  test "unit counter recognized" ((UnitCounter.find? 0 counter.functions[0]!).isSome)
  let unrankedMutual := { rankedMutual with callComponents := #[⟨0, false⟩, ⟨0, false⟩] }
  test "unranked mutual rejected" (rejected (checkComponents {} unrankedMutual) "invalid static")
  test "invalid components remain serializable" ((decode {} (preimage unrankedMutual)).isOk)
  test "invalid components rejected at ingress" ((ingest {} {} (preimage unrankedMutual) (address unrankedMutual)).isOk.not)
  test "missing component entry" ((checkComponents {} { counter with callComponents := #[⟨0, false⟩, ⟨0, true⟩] }).isOk.not)
  test "out of range component order" ((checkComponents {} { counter with callComponents := #[⟨1, false⟩] }).isOk.not)
  let fn := counter.functions[0]!
  let giantInput := { counter with functions := #[{ fn with layout := { fn.layout with inputSize := 2 ^ 200 } }] }
  let giantOutput := { counter with functions := #[{ fn with body :=
    ⟨#[.load (2 ^ 200) 0, .call 0 #[0] 1 false], .return 0 #[0]⟩ }] }
  test "huge input rejected before allocation" (rejected (checkComponents {} giantInput) "resource limit")
  test "huge output rejected before allocation" (rejected (checkComponents {} giantOutput) "resource limit")
  test "component work budget" ((checkComponents { maxWork := 0 } counter).isOk.not)
  test "component candidate budget" ((checkComponents { maxCandidates := 0 } counter).isOk.not)
  test "component function budget" ((checkComponents { maxFunctions := 0 } counter).isOk.not)
  test "component depth budget" ((checkComponents { maxDepth := 1 } counter).isOk.not)
  test "empty certificate selects ranked fallback" ((checkComponents { maxValues := 0 } { giantInput with callComponents := #[] }).isOk)
  for (label, changed) in identityVariants do
    test s!"{label} changes bytes" (preimage changed != corpusExpected)
    test s!"{label} changes fixture root" (address changed != address corpus)
  IO.println s!"aiur-wire-tests-ok: {← count.get} assertions, 34 opcodes, 4 complete golden fixtures"

def emit (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, value, _) in fixtures do
    IO.FS.writeBinFile (directory / (name ++ ".bin")) (preimage value)
    IO.println s!"{name} {(preimage value).size} {address value}"

end IxCCTests.Aiur.WireRun
