import LSpec
import Ix.AuxGen.Configuration
import Ix.Cli.DriverOptions

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

/-- Catching an ordinary error preserves bookkeeping and creates no refusal. -/
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

/-- Exercise actual boundaries with empty inputs and refusing callbacks: neither
an early empty return, measurement nor a retry region may bypass validation. -/
private def wired : IO Nat := do
  let require (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
  let rejected {α : Type} (r : Except String α) (want : String) : IO Unit := match r with
    | .error e => require (e == want) s!"configuration route: expected {want}, got {e}"
    | .ok _ => throw (IO.userError s!"configuration route accepted: {want}")
  let input ← IO.ofExcept ((Compile.CompileInput.fromAnnotations []).mapError toString)
  let mut count := 0
  for (mode, recursors, expected) in policies do
    for measureOnly in #[false, true] do
      let opts : CompileM.AuxIxcOptions := { mode, recursors, measureOnly }
      let config := { auxIxc := some opts : CompileM.DriverOptions }
      if let some (_, message) := expected then
        rejected (CompileM.compileEnvFoldWithSource { consts := {} }
          { lowLinks := {}, blocks := {}, blockRefs := {} } (aux := opts)) message
        rejected (← CompileM.compileDecoratedConsts [] (numWorkers := 1) (opts := config)) message
        rejected (← CompileM.compileLeanInput input (numWorkers := 1) (opts := config)) message
        rejected (← CompileM.compileLeanConsts [] (numWorkers := 1) (opts := config)) message
        count := count + 4
      else if measureOnly then
        rejected (CompileM.compileEnvFoldWithSource { consts := {} }
          { lowLinks := {}, blocks := {}, blockRefs := {} } (aux := opts))
          "AuxGen (configuration): measureOnly requires the IO measurement pipeline"
        count := count + 1
    let cli := toString mode ++ (if recursors then "" else ",rec=off")
    match Ix.Cli.auxIxcOptionsOf cli, expected with
    | .error e, some (_, message) => require (e == message) "CLI configuration error differs"
    | .ok opts, none => require (opts.mode == mode && opts.recursors && !opts.measureOnly && opts.trace) "CLI changed valid options"
    | _, _ => throw (IO.userError "CLI mode matrix differs")
    count := count + 1
  for (value, expected) in #[
      ("measure,rec=off", "AuxGen (configuration): recursors must be enabled (rec=off is retired)"),
      ("unknown", "IX_AUXGEN_IXC: unknown mode 'unknown' (shadow, fallback, failClosed, fallbackEager, measure)"),
      ("failClosed,asks=unknown", "IX_AUXGEN_IXC: unknown option 'asks=unknown' (asks=below, asks=inductive, asks=recursors, rec=off)")] do
    rejected (Ix.Cli.auxIxcOptionsOf value) expected
    count := count + 1
  for asks in ["below", "inductive", "recursors"] do
    let opts ← IO.ofExcept (Ix.Cli.auxIxcOptionsOf s!"measure,asks={asks}")
    require (opts.measureOnly && opts.mode == .failClosed && opts.recursors && opts.trace) "measurement lost checked policy"
    count := count + 1
  let anchor := capability .failClosed true none
  let initial : CompileM.BlockState := { univsFinal := true, auxReport := { retried := some "preserved" } }
  let maps : AddrMaps := { nameToAddr := fun _ => none }
  let mut badCapabilities := 0
  for (mode, recursors, expected) in policies do
    for retry in #[none, some anchor] do
      let wanted := expected.map (·.2) |>.orElse fun _ =>
        if retry.isSome then some "AuxGen (configuration): nested retry is unsupported" else none
      let some message := wanted | continue
      badCapabilities := badCapabilities + 1
      let oracle := capability mode recursors retry
      let kernel := AuxKernel.ixc maps oracle
      let actions : Array (CompileM.CompileM Unit) :=
        (#[.below, .brecOn, .recursor].map fun route =>
          discard <| (AuxScope.new kernel #[] #[] route).run AuxKernelCtx.new) ++ #[
          discard <| (kernel.elimDecision #[] 0 0).run AuxKernelCtx.new,
          discard <| (kernel.withFamily #[]).run AuxKernelCtx.new,
          discard <| (kernel.admitGenerated #[]).run AuxKernelCtx.new,
          discard <| (kernel.withFlatBlockVerdict #[] #[] #[]).run AuxKernelCtx.new,
          discard <| (kernel.checkCanonicalBlock #[] #[] #[]).run AuxKernelCtx.new,
          discard <| (generateAuxPatches #[] #[] maps kernel).run AuxKernelCtx.new,
          discard <| (compileMutualAuxTail #[] [] default maps kernel).run AuxKernelCtx.new,
          discard <| CompileM.runAuxTail Name.mkAnon #[] [] default maps kernel]
      require (actions.size == 11) "missing capability boundary"
      for action in actions do
        let caught : CompileM.CompileM Bool := do
          try action; pure false catch e => do
            let state ← CompileM.getBlockState
            pure (e == .unsupportedExpr message && state.univsFinal &&
              state.auxReport.refusal.isNone && state.auxReport.retried == some "preserved")
        let (ok, after) ← IO.ofExcept ((CompileM.CompileM.run
          { (default : CompileM.CompileEnv) with
            auxGenerationRetry := some (fun _ => .error "retry callback escaped validation") }
          { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] } initial caught).mapError toString)
        require (ok && after.auxReport.refusal.isNone) "configuration invoked callback or changed refusal/state"
        count := count + 1
      rejected (AuxKernel.ixcElimDecision oracle #[] 0 0) message
      count := count + 1
  require (badCapabilities == 15 && count == 251) s!"boundary coverage differs: {badCapabilities}/{count}"
  return count

def suite : List TestSeq := [
  .individualIO "checked configuration: exact options, live boundaries and ordinary errors" none (do
    let n ← IO.ofExcept matrix
    IO.ofExcept ordinaryState
    let routes ← wired
    IO.println s!"configuration: 16 option +16 capability cases; {routes} actual boundaries; ordinary errors preserve refusal/retry bookkeeping"
    return (true, n + 1 + routes, 0, none)) .done]

end Tests.Ix.AuxGen.ConfigurationTests
