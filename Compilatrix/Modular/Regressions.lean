import Compilatrix.Modular.Fixtures

/-! Adversarial evidence, exact policy boundaries, and dependency integrity. -/

namespace Compilatrix.Modular.Regressions

open Ixon IxIR

private def reject (name : String) (result : Except String α) : Except String (String × String) :=
  match result with
  | .error reason => .ok (name, reason)
  | .ok _ => .error s!"regression {name} unexpectedly accepted malformed input"

private def changeRecord (records : List (String × Record)) (name : String)
    (change : Record → Record) : List (String × Record) :=
  records.map fun entry => if entry.1 == name then (name, change entry.2) else entry

private def changeInput (inputs : List Input) (name : String)
    (change : Input → Input) : List Input :=
  inputs.map fun input => if input.name == name then change input else input

def run (fixture : Fixtures.Case) (built : Built Fixtures.policy) :
    Except String (List (String × String)) := do
  let limits := Fixtures.limits
  let policy := Fixtures.policy
  let inputs := fixture.inputs
  let records := built.units.map (fun unit => (unit.input.name, unit.record))
  let some (_, leaf) := records.find? (fun entry => entry.1 == "leaf") | throw "missing regression leaf"
  let some leafUnit := built.units.find? (fun unit => unit.input.name == "leaf") | throw "missing checked leaf"
  let bytes ← Wire.encodeRecord limits leaf
  let store ← Wire.encodeStore limits records
  let mut results := []
  results := (← reject "truncated-record" (Wire.decodeRecord limits (bytes.extract 0 (bytes.size - 1)))) :: results
  results := (← reject "trailing-record-bytes" (Wire.decodeRecord limits (bytes.push 0))) :: results
  results := (← reject "record-byte-limit" (Wire.decodeRecord
    { limits with record := { limits.record with maxBytes := bytes.size - 1 } } bytes)) :: results
  results := (← reject "store-byte-limit" (Wire.decodeStore { limits with maxBytes := store.size - 1 } store)) :: results
  results := (← reject "store-duplicate-unit" (Wire.encodeStore limits (records ++ records.take 1))) :: results
  results := (← reject "store-trailing-bytes" (Wire.decodeStore limits (store.push 0))) :: results
  results := (← reject "record-version" (Wire.decodeRecord limits (bytes.set! 0 0))) :: results
  let oversized := Wire.recordDomain ++ Encoding.blob leaf.query ++
    Encoding.nat (limits.record.maxSequence + 1)
  results := (← reject "oversized-declaration-count" (Wire.decodeRecord limits oversized)) :: results
  let longNatural := Wire.recordDomain ++ ByteArray.mk (Array.replicate 65 128)
  results := (← reject "overlong-natural" (Wire.decodeRecord limits longNatural)) :: results
  let deep := (List.range (limits.maxExprDepth + 1)).foldl
    (fun body _ => IxIR0.Expr.lam .many body) .erased
  let deepRecord := { leaf with output := [(leafUnit.input.constants.head!.1, .defn .shared deep)] }
  results := (← reject "expression-depth" (Wire.decodeRecord limits (Wire.recordBytes deepRecord))) :: results
  results := (← reject "typed-expression-depth" (checkUnit limits policy leafUnit.input [] deepRecord)) :: results
  let badOutput := changeRecord records "leaf" fun record =>
    { record with output := record.output.map (fun entry => (entry.1, .defn .shared (.lit (.nat 999)))) }
  results := (← reject "forged-erasure-output" (restore limits policy inputs badOutput)) :: results
  results := (← reject "omitted-coverage" (restore limits policy inputs
    (changeRecord records "leaf" fun record => { record with order := [] }))) :: results
  results := (← reject "duplicate-coverage" (restore limits policy inputs
    (changeRecord records "leaf" fun record => { record with order := record.order ++ record.order }))) :: results
  results := (← reject "forged-query" (restore limits policy inputs
    (changeRecord records "leaf" fun record => { record with query := record.query.push 0 }))) :: results
  results := (← reject "checker-policy" (restore limits { policy with validateFuel := policy.validateFuel + 1 }
    inputs records)) :: results
  results := (← reject "stale-source-dependency" (restore limits policy (← Fixtures.editCase true).inputs records)) :: results
  results := (← reject "stale-literal-premise" (restore limits policy (← Fixtures.blobEditCase).inputs records)) :: results
  let reordered := changeInput inputs "root" fun input => { input with imports := input.imports.reverse }
  results := (← reject "stale-import-interface-order" (restore limits policy reordered records)) :: results
  let wrongMode := changeInput inputs "leaf" fun input => { input with
    constants := input.constants.map fun (address, constant) =>
      (address, { constant with info := match constant.info with
        | .defn definition => .defn { definition with kind := .thm }
        | info => info }) }
  results := (← reject "source-mode-address-mismatch" (build limits policy wrongMode)) :: results
  let missing := changeInput inputs "dependent" fun input => { input with imports := [] }
  results := (← reject "undeclared-source-dependency" (build limits policy missing)) :: results
  let cyclic := changeInput inputs "leaf" fun input => { input with imports := ["root"] }
  results := (← reject "cross-unit-cycle" (build limits policy cyclic)) :: results
  results := (← reject "missing-unit" (build limits policy (inputs.filter (·.name != "leaf")))) :: results
  results := (← reject "duplicate-owned-constant" (build limits policy
    (inputs ++ [{ leafUnit.input with name := "duplicate" }]))) :: results
  results := (← reject "aggregate-unit-limit" (build { limits with maxUnits := inputs.length - 1 } policy inputs)) :: results
  results := (← reject "aggregate-candidate-limit" (build { limits with maxCandidates := 3 } policy inputs)) :: results
  results := (← reject "aggregate-work-limit" (build { limits with maxCertificateWork := 0 } policy inputs)) :: results
  results := (← reject "aggregate-import-limit" (build { limits with maxImportBindings := 1 } policy inputs)) :: results
  results := (← reject "unit-candidate-limit" (build limits
    { policy with unit := { policy.unit with maxCertificateCandidates := 0 } } inputs)) :: results
  results := (← reject "checked-cache-record-limit" (build
    { limits with record := { limits.record with maxBytes := 0 } } policy inputs built.cache)) :: results
  results := (← reject "checked-cache-byte-limit" (build
    { limits with maxBytes := 0 } policy inputs built.cache)) :: results
  results := (← reject "checked-cache-depth-limit" (build
    { limits with maxExprDepth := 0 } policy inputs built.cache)) :: results
  let mutualFixture ← Fixtures.mutualCase
  let some group := mutualFixture.inputs.find? (fun input => input.imports.isEmpty)
    | throw "missing member-only unit"
  ensure ((candidates group.constants).isEmpty && proofObligations group.constants == 2)
    "member-only regression does not exercise two executable members"
  results := (← reject "member-only-unit-obligation-limit" (build limits
    { policy with unit := { policy.unit with maxCertificateCandidates := 1 } } [group])) :: results
  results := (← reject "member-only-unit-attempt-limit" (build limits
    { policy with unit := { policy.unit with maxCertificateValidationAttempts := 0 } } [group])) :: results
  results := (← reject "member-only-unit-work-limit" (build limits
    { policy with unit := { policy.unit with maxCertificateSourceNodeWork := 0 } } [group])) :: results
  results := (← reject "member-only-aggregate-work-limit" (build
    { limits with maxCertificateWork := 0 } policy [group])) :: results
  results := (← reject "member-aggregate-obligation-limit" (build
    { limits with maxCandidates := 4 } policy mutualFixture.inputs)) :: results
  let wrongTarget := { leafUnit.context with
    declarations := leafUnit.context.declarations.map (fun entry => (entry.1, .defn .shared (.lit (.nat 999)))) }
  results := (← reject "incompatible-imported-target" (leafUnit.context.extension wrongTarget)) :: results
  let wrongBlob := { leafUnit.context with
    blobs := leafUnit.context.blobs.map (fun entry => (entry.1, .natB 999)) }
  results := (← reject "incompatible-imported-literal" (leafUnit.context.extension wrongBlob)) :: results
  let wrongNat := { leafUnit.context with natBlock := some (Address.replicate 1) }
  results := (← reject "incompatible-Nat-identity" (leafUnit.context.extension wrongNat)) :: results
  -- Exact inclusive boundaries still accept the complete record and program.
  let _ ← Wire.decodeRecord { limits with record := { limits.record with maxBytes := bytes.size } } bytes
  let _ ← Wire.decodeStore { limits with maxBytes := store.size } store
  let _ ← build { limits with maxUnits := inputs.length, maxCandidates := 4 } policy inputs
  let _ ← build { limits with maxCandidates := 5 } policy mutualFixture.inputs
  let memberPolicy := { policy with unit := { policy.unit with
    maxCertificateCandidates := 2
    maxCertificateValidationAttempts := proofAttempts group.constants
    maxCertificateSourceNodeWork := proofWork group.constants group.constants } }
  let _ ← build limits memberPolicy [group]
  return results.reverse

end Compilatrix.Modular.Regressions
