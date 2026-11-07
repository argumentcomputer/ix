import IxCCTests.Corpus.Build
import IxCC.Src.Table.Cert

/- Genuine retained producer bytes. Only sidecar field names are adapted;
   no declaration, contract, theorem, profile byte, or address is rewritten. -/
open Lean System IxCC

namespace IxCCTests.Own.AnnotatedFixture

def need (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def field (j : Json) (key : String) : IO Json := IO.ofExcept (j.getObjVal? key)

/-- Historical cb68 only: no profile and no actual checked claim. This is
not the current corpus paired-key protocol, whose parser is unchanged. -/
def legacyPlainEmpty (raw : Json) : IO Unit := do
  need (!(raw.getObjVal? "resourceProfile").isOk)
    "stripped plain source unexpectedly carries a resource profile"
  match raw.getObjVal? "resourceChecked" with
  | .error _ => pure ()
  | .ok pairs => do
    let values ← IO.ofExcept pairs.getArr?
    need values.isEmpty "stripped plain source has nonempty orphan resourceChecked"

def normalizedResource (raw : Json) : IO Json := do
  let profile ← field raw "resourceProfile"
  let pairs ← IO.ofExcept (← field raw "resourceChecked").getArr?
  let pairs ← pairs.mapM fun q => do
    return Json.mkObj [
      ("definition", ← field q "definition"),
      ("definition_address", ← field q "definitionAddress"),
      ("equation", ← field q "equation"),
      ("equation_address", ← field q "equationAddress"),
      ("profile", ← field q "profile"),
      ("contracts", ← field q "contracts")]
  return Json.mkObj [("resource_profile", profile), ("resource_checked", .arr pairs)]

def run (ixe sidecar checkedLog : FilePath) : IO Unit := do
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile sidecar))
  need ((← IO.ofExcept (← field raw "format").getStr?) == "ix/compile-equations/1") "producer sidecar format"
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv (← IO.FS.readBinFile ixe))
  need ((← IO.ofExcept (← field raw "root").getStr?) == toString env.root) "actual Merkle root"
  let normalized ← normalizedResource raw
  let some context ← IO.ofExcept (Src.Hints.resourceOfJson normalized)
    | throw (IO.userError "missing genuine producer resource context")
  let profile ← IO.ofExcept (Src.Resource.Profile.ofBytes context.bytes)
  need (profile.steps == 100000 && profile.depth == 256) "original100k/depth256 required"
  need (toString context.address == "5e387038c267c42212fa9c62ddbac9d062eb3354f79ade3fb57ee9a3ddac09b9") "historical effective core profile identity"
  need (context.pairs.length == 1) "one genuinely checked annotated equation"
  let verified ← IO.ofExcept (IxCCTests.Corpus.verifiedPairs
    (← IO.FS.readFile checkedLog) (toString context.address))
  need (verified.length == context.pairs.length) "complete check-equations receipt count"
  for (v, q) in verified.zip context.pairs do
    need (v.definitionAddress == toString q.definition && v.equationAddress == toString q.equation)
      "check-equations receipt must match actual sidecar addresses"
  let original ← IO.ofExcept (Src.Ingress.ofEnv env #[])
  let p := { original with known := Src.Pinned.known original, resource := some context }
  IO.ofExcept (Src.Resource.validate p)
  let mut proposals : Array Src.Proposal := #[]
  for (definition, equation) in profile.equations do
    proposals := proposals.push { kind := .eqn, subject := definition, theorem? := some equation }
  let (table, _, stats) := Src.Table.build {} p proposals
  for q in context.pairs do
    let some f := p.lookup q.definition | throw (IO.userError "actual subject absent")
    let some thm := p.lookup q.equation | throw (IO.userError "actual theorem absent")
    need (toString q.definition == "3206312baf22a918e3c0c1deaa5dce1031f03b1ce823d155ac1659a4febaa40a") "actual len identity"
    need (toString q.equation == "81199f3ff47c8e5442a4ad4d0f8aa970c8d8627c505cada21a0d8a33d3f9c97f") "actual len.eq_def identity"
    let entry ← IO.ofExcept (Src.Table.checkEqn p f thm)
    match entry with
    | .eqn actual (.lam binder _ body) =>
      need (actual == thm && binder.contract.uses == .erased && body.mentions f)
        "genuine recursive RHS retains erased header"
    | _ => throw (IO.userError "expected genuine annotated recursive lambda")
    need (stats.eqnAccepted.contains f) "producer table accepted annotated equation"
    need (!(Src.Table.ofCert {} p {}).isOk) "omitted checked equation must refuse"
    need (!(Src.Table.checkEqn { p with resource := none } f thm).isOk) "absent context must refuse"
    need (!(Src.Resource.validate { p with resource := some { context with
      pairs := context.pairs.map fun r => { r with equation := r.definition } } }).isOk)
      "changed equation address must refuse"
    need (!(Src.Resource.validate { p with resource := some { context with address := q.definition } }).isOk)
      "changed profile address must refuse"
    need (!(Src.Table.checkCsimp p f f thm).isOk) "resource-bound csimp must refuse"
  IO.ofExcept (Src.Resource.selected p table)
  IO.ofExcept (Src.Table.validate {} { p with table })
  let replayed ← IO.ofExcept (Src.Table.ofCert {} p (Src.Table.TableCert.ofTable table))
  IO.ofExcept (Src.Resource.selected p replayed)
  need (Src.Table.TableCert.ofTable replayed == Src.Table.TableCert.ofTable table)
    "producer/certificate table selections coincide"
  IO.println s!"PASS: authentic cb68d94c OS04 bytes; declarations={p.size}; original100k/depth256; one genuine recursive checked pair; table/certificate selection; five refusal controls"
  IO.println "Scope: historical-producer structural consumer boundary only; no selected-producer admission, execution-order adequacy, native result, or final refreeze claim."

end IxCCTests.Own.AnnotatedFixture
