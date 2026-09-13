import Compilatrix.Modular.Fixtures
import Compilatrix.Tools.Check

/-! Canonical-address reuse must not bypass current context, usage, resource,
or record checks. Compare complete fresh/prepared results and exact failures. -/

namespace Compilatrix.Modular.PreparationTests

open Lean Ixon Compilatrix.Tools.Check

private def ioCheck := @Compilatrix.Tools.Check.checked

private def contextView (context : Context) :=
  (context.constants, context.blobs, context.declarations, context.natBlock)

private def unitView {policy} (unit : CheckedUnit policy) :=
  (unit.input, unit.interfaces, contextView unit.context, unit.record)

private def sameResult [BEq α] : Except String α → Except String α → Bool
  | .ok first, .ok second => first == second
  | .error first, .error second => first == second
  | _, _ => false

private def resultJson (name kind : String) (accepted : Bool)
    (result : Except String α) : IO Json := do
  need (result.toOption.isSome == accepted) s!"{name}: wrong admission result"
  return Json.mkObj [("name", toJson name), ("kind", toJson kind),
    ("accepted", toJson accepted), ("reason", toJson (match result with | .ok _ => "" | .error error => error))]

private def recordCase {limits policy input imports} (name : String)
    (prepared : Preparation limits policy input imports) (record : Record) (accepted : Bool) : IO Json := do
  let fresh := checkUnit limits policy input imports record
  let reused := checkUnitPrepared limits policy input imports prepared record
  need (sameResult (fresh.map unitView) (reused.map unitView)) s!"{name}: prepared record checking differs"
  resultJson name "record" accepted fresh

private def preparationCase (name : String) (limits : Limits) (policy : Policy) (input : Input)
    (known : Option (PLift (AddressEvidence input.constants))) (accepted : Bool) : IO Json := do
  let fresh := prepare limits policy input []
  let reused := prepareChecked limits policy input [] known
  need (sameResult (fresh.map contextView) (reused.map (fun value => contextView value.context)))
    s!"{name}: canonical reuse changed preparation"
  resultJson name "preparation" accepted fresh

private def lookupCase {policy} (name : String) (cache : Cache policy) (input : Input)
    (hit : Bool) : IO Json := do
  need ((cache.addressEvidence? input).isSome == hit) s!"{name}: wrong canonical-address reuse"
  return Json.mkObj [("name", toJson name), ("kind", toJson "address-lookup"), ("hit", toJson hit)]

def run : IO Json := do
  let limits := Fixtures.limits
  let policy := Fixtures.policy
  let fixture ← ioCheck (Fixtures.editCase false)
  let built ← ioCheck (build limits policy fixture.inputs)
  let some leaf := built.units.find? (·.input.name == "leaf")
    | throw (IO.userError "missing preparation regression leaf")
  let known := built.cache.addressEvidence? leaf.input
  need known.isSome "checked source lost canonical-address evidence"
  let prepared ← ioCheck (prepareChecked limits policy leaf.input [] known)
  let mut cases := []
  for unit in built.units do
    let imports ← ioCheck (unit.input.imports.mapM fun name =>
      match built.units.find? (·.input.name == name) with
      | some imported => .ok imported
      | none => .error "missing preparation regression import")
    let completed ← ioCheck (prepareChecked limits policy unit.input imports
      (built.cache.addressEvidence? unit.input))
    cases := (← recordCase s!"accepted-{unit.input.name}" completed unit.record true) :: cases
    cases := (← lookupCase s!"unchanged-{unit.input.name}" built.cache unit.input true) :: cases
  for (name, record) in [
      ("changed-query", { leaf.record with query := leaf.query.push 0 }),
      ("changed-output", { leaf.record with output := leaf.output.map fun entry =>
        (entry.1, IxIR0.Decl.defn .shared (.lit (.nat 999))) }),
      ("missing-coverage", { leaf.record with order := [] }),
      ("duplicate-coverage", { leaf.record with order := leaf.order ++ leaf.order })] do
    cases := (← recordCase name prepared record false) :: cases
  let deep := (List.range (limits.maxExprDepth + 1)).foldl
    (fun body _ => IxIR0.Expr.lam .many body) .erased
  cases := (← recordCase "deep-record" prepared
    { leaf.record with output := [(leaf.input.constants.head!.1, .defn .shared deep)] } false) :: cases
  let recordSize ← ioCheck (leaf.record.preflight limits)
  let recordLimits := { limits with record := { limits.record with maxBytes := recordSize - 1 } }
  let bounded ← ioCheck (prepareChecked recordLimits policy leaf.input [] known)
  cases := (← recordCase "record-limit-after-preparation" bounded leaf.record false) :: cases

  let changedBody := { leaf.input with constants := leaf.input.constants.map fun (address, constant) =>
    (address, { constant with info := (Fixtures.definition (.nat 999)).info }) }
  let changedRefs := { leaf.input with constants := leaf.input.constants.map fun (address, constant) =>
    (address, { constant with refs := constant.refs.push (Address.replicate 0x99) }) }
  let changedSharing := { leaf.input with constants := leaf.input.constants.map fun (address, constant) =>
    (address, { constant with sharing := constant.sharing.push (.nat 999) }) }
  for (name, changed) in [("same-key-changed-body", changedBody),
      ("same-key-changed-refs", changedRefs), ("same-key-changed-sharing", changedSharing)] do
    cases := (← lookupCase name built.cache changed false) :: cases
    cases := (← preparationCase name limits policy changed (built.cache.addressEvidence? changed) false) :: cases
  let literalEdit ← ioCheck Fixtures.blobEditCase
  for input in literalEdit.inputs do
    cases := (← lookupCase s!"literal-edit-{input.name}" built.cache input true) :: cases
  let changedLeaf ← present (literalEdit.inputs.find? (·.name == "leaf")) "missing literal-edit leaf"
  let changedPreparation ← ioCheck (prepareChecked limits policy changedLeaf []
    (built.cache.addressEvidence? changedLeaf))
  cases := (← recordCase "literal-edit-stale-record" changedPreparation leaf.record false) :: cases
  let sourceEdit ← ioCheck (Fixtures.editCase true)
  for input in sourceEdit.inputs do
    cases := (← lookupCase s!"source-edit-{input.name}" built.cache input (input.name == "unaffected")) :: cases

  cases := (← preparationCase "known-address-current-input" limits policy leaf.input known true) :: cases
  cases := (← preparationCase "known-address-empty-name" limits policy { leaf.input with name := "" } known false) :: cases
  cases := (← preparationCase "known-address-missing-literal" limits policy
    { leaf.input with blobs := [] } known false) :: cases
  cases := (← preparationCase "known-address-missing-import" limits policy
    { leaf.input with imports := ["absent"] } known false) :: cases
  cases := (← preparationCase "known-address-usage-fuel" limits { policy with checkFuel := 0 }
    leaf.input known false) :: cases
  cases := (← preparationCase "known-address-candidate-limit" limits
    { policy with unit := { policy.unit with maxCertificateCandidates := 0 } } leaf.input known false) :: cases
  cases := (← preparationCase "known-address-import-limit" { limits with maxImportBindings := 0 }
    policy leaf.input known false) :: cases
  cases := (← preparationCase "known-address-input-byte-limit"
    { limits with record := { limits.record with maxBlobBytes := leaf.input.bytes.size - 1 } }
    policy leaf.input known false) :: cases
  let repeated : Input := { leaf.input with constants := leaf.input.constants ++ leaf.input.constants }
  let repeatedEvidence : AddressEvidence repeated.constants := by
    intro entry member
    rcases List.mem_append.mp member with first | second
    · exact leaf.addresses entry first
    · exact leaf.addresses entry second
  cases := (← preparationCase "known-address-duplicate-ownership" limits policy repeated
    (some ⟨repeatedEvidence⟩) false) :: cases
  let changed ← ioCheck (build limits policy literalEdit.inputs built.cache)
  need (changed.observations.all fun entry => entry.action ==
    if entry.name == "unaffected" then .reused else .produced) "canonical reuse bypassed literal invalidation"
  let cold ← ioCheck (build limits policy literalEdit.inputs)
  need (changed.units.map unitView == cold.units.map unitView) "literal-edit reuse differs from cold evidence"
  let ordered := cases.reverse
  IO.println s!"source preparation checks ok: {ordered.length} exact result and reuse cases"
  return Json.mkObj [("cases", toJson ordered), ("literal_edit_matches_cold", toJson true)]

end Compilatrix.Modular.PreparationTests
