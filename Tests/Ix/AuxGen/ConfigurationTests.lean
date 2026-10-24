import LSpec
import Ix.AuxGen.Configuration

namespace Tests.Ix.AuxGen.ConfigurationTests
open LSpec _root_.Ix _root_.Ix.AuxGen
open _root_.Ix.AuxGen.Configuration

private def need (ok : Bool) (why : String) : Except String Unit := unless ok do throw why
private def scope : OracleScope :=
  .mk (fun _ => .error "callback") (fun _ => .error "callback") (fun _ => .error "callback")
    (fun _ => .error "callback") (fun _ => .error "callback") (fun _ _ => .error "callback") (fun _ => .error "callback")
private def capability (mode : IxcMode) (recursors : Bool) (retry : Option AuxOracle) : AuxOracle :=
  .mk mode true (fun _ _ => .error "callback") (fun _ _ _ => .error "callback") (fun _ => .error "callback")
    recursors false (fun _ _ _ => scope) (fun _ => .error "callback") (fun _ => some "original status") retry (fun _ => .error "callback")

-- Independent expected policy table: every historical mode and both flags.
private def policies : Array (IxcMode × Bool × Option (Error × String)) := #[
  (.failClosed, true, none),
  (.failClosed, false, some (.recursorsDisabled, "AuxGen (configuration): recursors must be enabled (rec=off is retired)")),
  (.shadow, true, some (.unsupportedMode .shadow, "AuxGen (configuration): retired mode 'shadow' is unsupported")),
  (.shadow, false, some (.unsupportedMode .shadow, "AuxGen (configuration): retired mode 'shadow' is unsupported")),
  (.fallback, true, some (.unsupportedMode .fallback, "AuxGen (configuration): retired mode 'fallback' is unsupported")),
  (.fallback, false, some (.unsupportedMode .fallback, "AuxGen (configuration): retired mode 'fallback' is unsupported")),
  (.fallbackEager, true, some (.unsupportedMode .fallbackEager, "AuxGen (configuration): retired mode 'fallbackEager' is unsupported")),
  (.fallbackEager, false, some (.unsupportedMode .fallbackEager, "AuxGen (configuration): retired mode 'fallbackEager' is unsupported"))]

private def exactError (actual : Error) (expected : Error × String) : Except String Unit := do
  need (actual == expected.1 && actual.render == expected.2 && toString actual == expected.2) "configuration error tag/text differs"
  match actual.toCompileError with
  | .unsupportedExpr text => need (text == expected.2) "ordinary compiler error text differs"
  | _ => throw "configuration error became another compiler category"

private def matrix : Except String Nat := do
  need (policies.size == 8) "policy table incomplete"
  let anchor := capability .failClosed true none
  let mut count := 0
  for (mode, recursors, expected) in policies do
    for measureOnly in #[false, true] do
      match validateRequest { mode, recursors, measureOnly }, expected with
      | .ok intent, none => need (intent == (if measureOnly then .measure else .compile)) "valid intent was remapped"
      | .error actual, some wanted => exactError actual wanted
      | _, _ => throw "driver option matrix changed acceptance"
      count := count + 1
    for retry in #[none, some anchor] do
      let wanted := expected.orElse fun _ => if retry.isSome then
        some (.nestedRetry, "AuxGen (configuration): nested retry is unsupported") else none
      match validateCapability (capability mode recursors retry), wanted with
      | .ok (), none => pure ()
      | .error actual, some wanted => exactError actual wanted
      | _, _ => throw "capability matrix changed acceptance"
      count := count + 1
  need (count == 32) "option/capability matrix was not exhausted"
  return count

/-- Test the intended ordinary-error adapter locally; no production call site
is wired. Catching it preserves existing bookkeeping and creates no refusal. -/
private def ordinaryState : Except String Unit := do
  let initial : CompileM.BlockState := { univsFinal := true, auxReport := { retried := some "preserved" } }
  let act : CompileM.CompileM Bool := do
    try
      match validateRequest { mode := .shadow, recursors := false, measureOnly := true } with
      | .error e => throw e.toCompileError
      | .ok _ => pure false
    catch e =>
      let s ← CompileM.getBlockState
      match e with
      | .unsupportedExpr message => pure (message == "AuxGen (configuration): retired mode 'shadow' is unsupported" &&
          s.univsFinal && s.auxReport.refusal.isNone && s.auxReport.retried == some "preserved")
      | _ => pure false
  let (ok, after) ← (CompileM.CompileM.run default
    { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] } initial act).mapError toString
  need (ok && after.auxReport.refusal.isNone && after.auxReport.retried == some "preserved") "configuration handling mutated state or made a query packet"

def suite : List TestSeq := [
  .individualIO "unwired checked configuration: exact options, measure intent and ordinary errors" none (do
    let n ← IO.ofExcept matrix
    IO.ofExcept ordinaryState
    IO.println "unwired configuration: 16 option +16 capability cases; ordinary errors preserve refusal/retry bookkeeping"
    return (true, n + 1, 0, none)) .done]

end Tests.Ix.AuxGen.ConfigurationTests
