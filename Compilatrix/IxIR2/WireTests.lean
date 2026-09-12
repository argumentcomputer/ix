import Compilatrix.IxIR2.WireFixtures

/-! Executed wire regressions: strict malformed input, explicit capacity
edges, every identity-bearing layer, stale roots and metadata/ownership
rejection. These run through the same public ingress used by persisted files. -/

namespace Compilatrix.IxIR2.Wire.Examples

open Lean Compilatrix.Ixon Compilatrix.IxIR

def splice (bytes : ByteArray) (offset count : Nat) (replacement : ByteArray) : ByteArray :=
  bytes.extract 0 offset ++ replacement ++ bytes.extract (offset + count) bytes.size

private def changeMain (artifact : Artifact) (change : Function → Function) : Artifact :=
  { artifact with program := { artifact.program with main := change artifact.program.main } }

private def changeBlock (artifact : Artifact) (index : Nat) (change : Block → Block) : Artifact :=
  changeMain artifact fun fn => { fn with blocks := fn.blocks.set! index (change fn.blocks[index]!) }

private def changeSchema (artifact : Artifact) (change : Schema → Schema) : Artifact :=
  { artifact with schemas := artifact.schemas.set! 0 (change artifact.schemas[0]!) }

private def changeLeaf (artifact : Artifact) (change : Validate.ScalarLeafFact → Validate.ScalarLeafFact) : Artifact :=
  { artifact with scalarLeaves := artifact.scalarLeaves.set! 0 (change artifact.scalarLeaves[0]!) }

def identityMutations : List (String × Artifact) :=
  let a := allSyntax
  [ ("semantics-version", { a with policy := { a.policy with semantics := "ixir2-semantics/next" } })
  , ("validator-version", { a with policy := { a.policy with validator := "ownership/next" } })
  , ("lowering-version", { a with policy := { a.policy with lowering := "lowering/next" } })
  , ("pass-version", { a with policy := { a.policy with passes := #["pass-a/2", "pass-b/1"] } })
  , ("pass-order", { a with policy := { a.policy with passes := a.policy.passes.reverse } })
  , ("layout-abi", { a with policy := { a.policy with layout := "fixture-layout/2" } })
  , ("credit-policy", { a with policy := { a.policy with credits := .suspendedCallsV1 } })
  , ("extern-policy", { a with policy := { a.policy with allowExtern := false } })
  , ("dependency-role", { a with dependencies := a.dependencies.set! 0 ⟨"different-role", a.dependencies[0]!.root⟩ })
  , ("dependency-root", { a with dependencies := a.dependencies.set! 0 ⟨a.dependencies[0]!.role, Address.replicate 0x33⟩ })
  , ("dependency-order", { a with dependencies := a.dependencies.reverse })
  , ("layout-key", { a with layouts := a.layouts.set! 0 { layoutA with identity := Address.replicate 0x34 } })
  , ("layout-preimage", { a with layouts := a.layouts.set! 0 { layoutA with preimage := layoutA.preimage.push 0 } })
  , ("layout-order", { a with layouts := a.layouts.reverse })
  , ("schema-world", changeSchema a fun s => { s with world := .shared })
  , ("schema-constructor-block", changeSchema a fun s => { s with constructor := { s.constructor with block := Address.replicate 0x35 } })
  , ("schema-inductive-index", changeSchema a fun s => { s with constructor := { s.constructor with indIdx := 1 } })
  , ("schema-constructor-index", changeSchema a fun s => { s with constructor := { s.constructor with cidx := 2 } })
  , ("schema-layout", changeSchema a fun s => { s with definition := { s.definition with layout := layoutB.identity } })
  , ("schema-fields", changeSchema a fun s => { s with definition := { s.definition with fields := #[.shared] } })
  , ("schema-order", { a with schemas := a.schemas.reverse })
  , ("fact-owner", changeLeaf a fun f => { f with owner := .declaration symbolB })
  , ("fact-block", changeLeaf a fun f => { f with block := 1 })
  , ("fact-value", changeLeaf a fun f => { f with value := 3 })
  , ("fact-constructor", changeLeaf a fun f => { f with cid := cidB })
  , ("fact-order", { a with scalarLeaves := a.scalarLeaves.reverse })
  , ("declaration-key", { a with program := { a.program with declarations := (Address.replicate 0x36, a.program.declarations.head!.2) :: a.program.declarations.tail } })
  , ("declaration-body", { a with program := { a.program with declarations := (symbolA, .fn (scalarFunction (.nat 99))) :: a.program.declarations.tail } })
  , ("extern-arity", { a with program := { a.program with declarations := a.program.declarations.take 2 ++ [(externSymbol, .extern 3)] } })
  , ("declaration-order", { a with program := { a.program with declarations := a.program.declarations.reverse } })
  , ("parameter-world", changeMain a fun f => { f with signature := { f.signature with params := #[⟨.shared, .owned⟩, ⟨.shared, .borrowed⟩] } })
  , ("parameter-passing", changeMain a fun f => { f with signature := { f.signature with params := #[⟨.unique, .borrowed⟩, ⟨.shared, .borrowed⟩] } })
  , ("result-world", changeMain a fun f => { f with signature := { f.signature with result := .unique } })
  , ("pap-entry", changeMain a fun f => { f with signature := { f.signature with papSafe := false } })
  , ("block-order", changeMain a fun f => { f with blocks := f.blocks.reverse })
  , ("value-capability", changeBlock a 0 fun b => { b with valueParams := b.valueParams.set! 0 (.owned .unique) })
  , ("borrow-lender", changeBlock a 0 fun b => { b with valueParams := b.valueParams.set! 4 (.borrowed .shared (.value 2)) })
  , ("credit-presence", changeBlock a 0 fun b => { b with creditParams := b.creditParams.set! 0 (.optional layoutA.identity) })
  , ("credit-layout", changeBlock a 0 fun b => { b with creditParams := b.creditParams.set! 0 (.required layoutB.identity) })
  , ("instruction-order", changeBlock a 0 fun b => { b with instructions := b.instructions.reverse })
  , ("instruction-operand", changeBlock a 0 fun b => { b with instructions := b.instructions.set! 0 (.move (.reg 2)) })
  , ("allocation-world", changeBlock a 0 fun b => { b with instructions := b.instructions.set! 1 (.alloc .shared cidA #[.reg 0, .lit (.nat 0), .erased]) })
  , ("allocation-credit", changeBlock a 0 fun b => { b with instructions := b.instructions.set! 2 (.allocWith 3 .shared cidB #[.lit (.str "λ🙂\n"), .reg 3]) })
  , ("call-reference", changeBlock a 0 fun b => { b with instructions := b.instructions.set! 11 (.call symbolB #[.reg 12, .erased]) })
  , ("edge-target", changeBlock a 0 fun b => { b with terminator := .jump { edgeA with target := 2 } })
  , ("edge-values", changeBlock a 0 fun b => { b with terminator := .jump { edgeA with values := edgeA.values.reverse } })
  , ("edge-credits", changeBlock a 0 fun b => { b with terminator := .jump { edgeA with credits := edgeA.credits.reverse } })
  , ("switch-order", changeBlock a 1 fun b => { b with terminator := .switchValue (.reg 0) #[⟨cidB, edgeB⟩, ⟨cidA, edgeA⟩] (some ⟨edgeB, edgeA⟩) })
  , ("nat-peel", changeBlock a 1 fun b => { b with terminator := .switchValue (.reg 0) #[⟨cidA, edgeA⟩, ⟨cidB, edgeB⟩] none })
  , ("terminator", changeBlock a 0 fun b => { b with terminator := .ret .erased })
  , ("utf8-literal", changeBlock a 3 fun b => { b with terminator := .ret (.lit (.str "é")) }) ]

def checkIdentityMutations : Except String (Array Json) := do
  let original := allSyntax
  let mut results := #[]
  for (name, changed) in identityMutations do
    let encoded ← changed.encodeChecked {}
    need (changed != original && encoded.bytes != original.preimage && changed.address != original.address)
      s!"identity omitted {name}"
    let decoded ← Artifact.decodeAddressed {} encoded.bytes changed.address
    need (decoded.artifact == changed) s!"mutation roundtrip failed: {name}"
    need (!(Artifact.decodeAddressed {} encoded.bytes original.address).isOk) s!"stale root accepted: {name}"
    results := results.push (Json.mkObj [("name", toJson name), ("root", toJson changed.address.toHex)])
  return results

structure Boundary where
  name : String
  bytes : ByteArray
  limits : Bounded.Limits := {}
  /-- `syntax`, `address` or `ingress`: the boundary actually exercised. -/
  stage : String := "syntax"
  accepts : Bool := false
  expectedRoot : Option Address := none

def Boundary.root (boundary : Boundary) : Address :=
  boundary.expectedRoot.getD (Address.blake3 boundary.bytes)

def Boundary.check (boundary : Boundary) : Except String Json := do
  let result := match boundary.stage with
    | "syntax" => (Artifact.decodePreimage boundary.limits boundary.bytes).isOk
    | "address" => (Artifact.decodeAddressed boundary.limits boundary.bytes boundary.root).isOk
    | "ingress" => (Artifact.ingest boundary.limits {} boundary.bytes boundary.root).isOk
    | _ => false
  need (result == boundary.accepts) s!"wrong {boundary.stage} boundary: {boundary.name}"
  return Json.mkObj [
    ("name", toJson boundary.name), ("binary", toJson s!"boundary-{boundary.name}.bin"),
    ("bytes", toJson boundary.bytes.size), ("digest", toJson (Address.blake3 boundary.bytes).toHex),
    ("root", toJson boundary.root.toHex), ("stage", toJson boundary.stage), ("accepts", toJson boundary.accepts),
    ("limits", Json.mkObj [("maxBytes", toJson boundary.limits.maxBytes),
      ("maxNatBytes", toJson boundary.limits.maxNatBytes), ("maxSequence", toJson boundary.limits.maxSequence),
      ("maxBlobBytes", toJson boundary.limits.maxBlobBytes)])]

private def syntaxCase (name : String) (bytes : ByteArray) : Boundary := { name, bytes }
private def typed (name : String) (artifact : Artifact) : Boundary :=
  { name, bytes := artifact.preimage, stage := "ingress" }

def syntaxBoundaries : Array Boundary := Id.run do
  let bytes := scalarArtifact.preimage
  let stringBytes := (scalarArtifact (.str "é")).preimage
  let param := changeMain scalarArtifact fun f =>
    { f with signature := { f.signature with params := #[⟨.shared, .borrowed⟩] } }
  let borrow := changeBlock scalarArtifact 0 fun b =>
    { b with valueParams := #[.borrowed .shared (.value 0)] }
  let credit := changeBlock scalarArtifact 0 fun b => { b with creditParams := #[.required layoutA.identity] }
  let instr := changeBlock scalarArtifact 0 fun b => { b with instructions := #[.move .erased] }
  let peel := changeBlock scalarArtifact 0 fun b => { b with terminator := .switchValue .erased #[] none }
  let call := changeBlock scalarArtifact 0 fun b => { b with terminator := .tailCall symbolA #[] }
  let decl := { scalarArtifact with program := { scalarArtifact.program with declarations := [(symbolA, .extern 0)] } }
  let blockStart := fun a : Artifact => a.preimage.size - (blockBytes a.program.main.blocks[0]!).size
  let mut result := #[
    syntaxCase "empty" ByteArray.empty,
    syntaxCase "domain-only" Artifact.addressDomain,
    syntaxCase "wrong-domain" (bytes.set! 0 0),
    syntaxCase "wrong-version" (bytes.set! (Artifact.addressDomain.size - 2) 0x32),
    syntaxCase "missing-nul" (splice bytes (Artifact.addressDomain.size - 1) 1 ByteArray.empty),
    syntaxCase "trailing" (bytes.push 0),
    syntaxCase "nonminimal-count" (splice bytes (bytes.size - 12) 1 (ByteArray.mk #[128, 0])),
    syntaxCase "nonminimal-natural" (splice bytes (bytes.size - 1) 1 (ByteArray.mk #[170, 0])),
    syntaxCase "natural-width" (splice bytes (bytes.size - 1) 1 (Encoding.nat (2 ^ 448))),
    syntaxCase "unterminated-natural" (splice bytes (bytes.size - 1) 1 (ByteArray.mk (Array.replicate 64 128))),
    syntaxCase "huge-sequence" (splice bytes (bytes.size - 8) 1 (Encoding.nat (2 ^ 400))),
    syntaxCase "huge-blob" (splice bytes Artifact.addressDomain.size 1 (Encoding.nat (2 ^ 400))),
    syntaxCase "invalid-utf8" (stringBytes.set! (stringBytes.size - 1) 255),
    syntaxCase "overlong-utf8" (splice stringBytes (stringBytes.size - 2) 2 (ByteArray.mk #[192, 128])),
    syntaxCase "ownership-tag" (bytes.set! (bytes.size - 10) 2),
    syntaxCase "boolean-tag" (bytes.set! (bytes.size - 9) 2),
    syntaxCase "terminator-tag" (bytes.set! (bytes.size - 4) 6),
    syntaxCase "atom-tag" (bytes.set! (bytes.size - 3) 3),
    syntaxCase "literal-tag" (bytes.set! (bytes.size - 2) 2),
    syntaxCase "parameter-passing-tag" (param.preimage.set! (param.preimage.size - (functionBytes param.program.main).size + 2) 2),
    syntaxCase "capability-tag" (borrow.preimage.set! (blockStart borrow + 1) 3),
    syntaxCase "borrow-lender-tag" (borrow.preimage.set! (blockStart borrow + 3) 2),
    syntaxCase "credit-capability-tag" (credit.preimage.set! (blockStart credit + 2) 2),
    syntaxCase "instruction-tag" (instr.preimage.set! (blockStart instr + 3) 16),
    syntaxCase "nat-peel-tag" (peel.preimage.set! (peel.preimage.size - 1) 2),
    syntaxCase "short-address" (splice call.preimage (call.preimage.size - 2) 1 ByteArray.empty),
    syntaxCase "declaration-tag" (decl.preimage.set! (decl.preimage.size - (programBytes decl.program).size + 33) 2),
    syntaxCase "credit-policy-tag" (bytes.set! (Artifact.addressDomain.size + (policyBytes scalarArtifact.policy).size - 2) 2)]
  let full := allSyntax
  let factStart := full.preimage.size - (programBytes full.program).size - (scalarLeafArrayBytes full.scalarLeaves).size
  result := result.push (syntaxCase "fact-owner-tag" (full.preimage.set! (factStart + 1) 2))
  return result

def resourceBoundaries : Array Boundary := Id.run do
  let small := scalarArtifact.preimage
  let number := (scalarArtifact (.nat (2 ^ 64))).preimage
  let flat := (changeBlock scalarArtifact 0 fun b => { b with instructions := Array.replicate 4096 (.move .erased) }).preimage
  let blob := { scalarArtifact with layouts := #[⟨Address.replicate 0x44, ByteArray.mk (Array.replicate 1000 0)⟩] }.preimage
  let utf8 := { scalarArtifact with policy := { fixturePolicy with lowering := String.ofList (List.replicate 20 'é') } }.preimage
  return #[
    { name := "bytes-exact", bytes := small, limits := { maxBytes := small.size }, accepts := true },
    { name := "bytes-short", bytes := small, limits := { maxBytes := small.size - 1 } },
    { name := "nat-u64-plus-exact", bytes := number, limits := { maxNatBytes := 10 }, accepts := true },
    { name := "nat-u64-plus-short", bytes := number, limits := { maxNatBytes := 9 } },
    { name := "nat-zero-width", bytes := small, limits := { maxNatBytes := 0 } },
    { name := "sequence-exact", bytes := flat, limits := { maxSequence := 4096 }, accepts := true },
    { name := "sequence-short", bytes := flat, limits := { maxSequence := 4095 } },
    { name := "blob-exact", bytes := blob, limits := { maxBlobBytes := 1000 }, accepts := true },
    { name := "blob-short", bytes := blob, limits := { maxBlobBytes := 999 } },
    { name := "utf8-bytes-exact", bytes := utf8, limits := { maxBlobBytes := 40 }, accepts := true },
    { name := "utf8-bytes-short", bytes := utf8, limits := { maxBlobBytes := 39 } }]

def ingressBoundaries : Array Boundary :=
  let a := coherent
  #[ typed "unknown-semantics" { a with policy := { a.policy with semantics := "next" } },
    typed "unknown-validator" { a with policy := { a.policy with validator := "next" } },
    typed "duplicate-dependency" { a with dependencies := a.dependencies.push ⟨"source", Address.replicate 0x55⟩ },
    typed "empty-dependency-role" { a with dependencies := #[⟨"", symbolA⟩] },
    typed "duplicate-layout" { a with layouts := a.layouts.push layoutA },
    typed "duplicate-schema" { a with schemas := a.schemas.push a.schemas[0]! },
    typed "wrong-layout-hash" { a with layouts := a.layouts.set! 0 { layoutA with preimage := layoutA.preimage.push 0 } },
    typed "missing-schema-layout" (changeSchema a fun s => { s with definition := { s.definition with layout := Address.replicate 0x66 } }),
    typed "missing-credit-layout" (changeBlock a 0 fun b => { b with creditParams := #[.required (Address.replicate 0x66)] }),
    typed "invalid-register" (changeBlock a 0 fun b => { b with terminator := .ret (.reg 99) }),
    typed "stale-scalar-fact" { a with scalarLeaves := #[⟨.main, 99, 0, cidA⟩] },
    typed "duplicate-declaration" { a with program := { a.program with declarations := [(symbolA, .fn (scalarFunction (.nat 1))), (symbolA, .fn (scalarFunction (.nat 2)))] } },
    typed "missing-callee" (changeBlock a 0 fun b => { b with instructions := #[.call symbolA #[]] }),
    typed "extern-disabled" { a with program := { a.program with declarations := [(externSymbol, .extern 0)] } },
    { name := "stale-root", bytes := a.preimage, stage := "address", expectedRoot := some symbolA }]

def boundaries (cases : Array Case) : Array Boundary :=
  let selected := cases.find? (fun c => c.name == "map-hot-reuse")
  let wrongCredit := selected.toArray.map fun c => typed "downgraded-credit-policy"
    { c.artifact with policy := { c.artifact.policy with credits := .callLocalV0 } }
  syntaxBoundaries ++ resourceBoundaries ++ ingressBoundaries ++ wrongCredit

/-- A retained scalar fact must name a real function block, including when
the fact is unused by the body. An extern entry cannot supply that owner. -/
def checkScalarFactOwners : Except String Unit := do
  let declared := { coherent with
    program := { coherent.program with declarations := [(symbolA, .fn (scalarFunction (.nat 1)))] }
    scalarLeaves := #[⟨.declaration symbolA, 0, 0, cidA⟩] }
  need (declared.check {}).isOk "valid declaration scalar-fact owner rejected"
  let missing := { declared with program := coherent.program }
  need (!(missing.check {}).isOk) "missing declaration scalar-fact owner accepted"
  let external := { declared with
    policy := { declared.policy with allowExtern := true }
    program := { declared.program with declarations := [(symbolA, .extern 0)] } }
  need (!(external.check {}).isOk) "extern scalar-fact owner accepted"
  let outside := { declared with scalarLeaves := #[⟨.declaration symbolA, 1, 0, cidA⟩] }
  need (!(outside.check {}).isOk) "out-of-bounds declaration scalar-fact block accepted"

def checkTruncations (cases : Array Case) : Except String Nat := do
  let mut count := 0
  for c in cases do
    for size in [:c.bytes.size] do
      need (!(Artifact.decodePreimage {} (c.bytes.extract 0 size)).isOk)
        s!"proper prefix accepted: {c.name} at {size}"
      count := count + 1
  return count

/- This vector freezes the complete minimal program tail independently of
the record/constructor serializers and guards the mutation offsets above. -/
#guard (scalarArtifact.preimage.extract (scalarArtifact.preimage.size - 12) scalarArtifact.preimage.size) ==
  ByteArray.mk #[0, 0, 1, 0, 1, 0, 0, 0, 3, 1, 0, 42]
#guard atomBytes (.lit (.nat (2 ^ 64))) ==
  ByteArray.mk #[1, 0, 128, 128, 128, 128, 128, 128, 128, 128, 128, 2]

end Compilatrix.IxIR2.Wire.Examples
