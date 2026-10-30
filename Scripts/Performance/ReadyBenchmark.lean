import Ix.Compile.ReadyCompile
import Ix.CompileCertified
import Ix.Meta
import Ix.EnvScope

open Ix.CompileM

private def phase (label : String) (action : IO α) : IO α := do
  let start ← IO.monoMsNow
  let result ← action
  IO.println s!"phase {label} ms={(← IO.monoMsNow) - start}"
  (← IO.getStdout).flush
  return result

def main (args : List String) : IO UInt32 := do
  let [mode, path, scope, output, workersText, lookaheadText] := args
    | throw (IO.userError "expected reference|ready, source, local|full, output, workers, lookahead")
  unless mode == "reference" || mode == "ready" do throw (IO.userError "unknown execution mode")
  unless scope == "local" || scope == "full" do throw (IO.userError "unknown source scope")
  let some workers := workersText.toNat? | throw (IO.userError "invalid worker count")
  let some lookahead := lookaheadText.toNat? | throw (IO.userError "invalid lookahead")
  let start ← IO.monoMsNow
  let frontend ← phase "load" (getFileEnvCore path)
  let constants ← phase "select" do
    if scope == "local" then pure (Ix.EnvScope.localConstList frontend)
    else Ix.EnvScope.defaultConstList frontend path
  let (prepared, annotated) ← phase "source-contracts" do
    IO.ofExcept (← IO.lazyPure fun _ => prepareCertified frontend.env constants)
  let canonical ← phase "canon" (IO.lazyPure fun _ => canonInput prepared.toArray workers)
  let inputs := canonical.consts.size
  let (report, metrics) ← phase "compileReport" do
    if mode == "reference" then
      let report ← IO.lazyPure fun _ => Ix.Cert.compileReport canonical
      return (report, (none : Option Ix.Compile.ReadyQueue.Metrics))
    else
      let (report, metrics) ← Ix.Compile.ReadyCompile.reportIO { workers, lookahead } canonical
      return (report.val, some metrics)
  let (artifact, failures) ← IO.ofExcept report
  if let some name := failureOutside canonical failures then
    throw (IO.userError s!"failure outside original input: {name.pretty}")
  unless failures.isEmpty do
    let rows := failures.toMap.toArray.map fun (name, message) => (name.pretty, message)
    throw (IO.userError s!"compiler failures: {repr rows}")
  if annotated then
    discard <| IO.ofExcept (Ix.Resource.validate artifact (Ix.Resource.standardProfile artifact))
  let final ← phase "finalize" do
    Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.certifiedBackend workers)
      frontend.env Ix.RoleBinding.Compile.nativeCertSource (.plain constants) artifact
      Ix.Resource.typingLimits
  IO.ofExcept (validateFinalized annotated final)
  let bytes ← phase "serialize" do IO.ofExcept (← IO.lazyPure fun _ => Ixon.serEnv final)
  let retained ← IO.lazyPure fun _ => (prepared.length, frontend.env.header.mainModule)
  unless retained.1 ≥ inputs do throw (IO.userError "input retention/accounting changed")
  phase "write" (Ix.RoleBinding.Compile.writeAtomic output bytes)
  IO.println s!"artifact mode={mode} inputs={inputs} failures={failures.toMap.size} bytes={bytes.size} total-ms={(← IO.monoMsNow) - start}"
  if let some metrics := metrics then
    IO.println s!"ready-metrics {repr metrics}"
    unless metrics.started == metrics.completed + metrics.drained do
      throw (IO.userError "ready executor returned with unconsumed block tasks")
  return 0
