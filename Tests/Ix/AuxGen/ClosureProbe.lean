import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.AuxGen.LiteralSupport
import Tests.Ix.AuxGen.ProbeReport

/-! # The Source service on selected closures (`lake exe IxTests --ignored auxgen-closure-probe`)

AuxGen M3's coverage probe. Source mode covers whole libraries; on a
selected closure (`ix compile-lean --consts`) the drivers' Source service
can lack what Source mode needs. This runner compiles the selected
closure of each root (`PROBE_ROOTS`, comma-separated; by default
`compile-closure-whole`'s MCasesPat root) of Init+Std, as `ix compile-lean`
does, with the aux tails in explicit `failClosed` mode and their counts traced
(`[auxgen-ixc] …` on stderr), without and with the literal support the closure
lacks (`Ix.AuxGen.literalSupportFor`, generation side only), and prints the
run-ahead's report each time. Complete typed outcomes are emitted; compiler,
service or capture-completeness failures return nonzero. Source nonacceptance
is recorded separately and never relabeled as a harness failure. -/

namespace Tests.Ix.AuxGen.ClosureProbe

def defaultRoots : List Lean.Name := [`Lean.Parser.Tactic.MCasesPat.parse.go._unsafe_rec]

def run : IO UInt32 := do
  let env ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
  let roots ← match ← IO.getEnv "PROBE_ROOTS" with
    | some s => pure ((s.splitOn ",").filter (!·.isEmpty) |>.map String.toName)
    | none => pure defaultRoots
  let mut failures := 0
  for root in roots do
    let closure := Ix.EnvScope.collectSelectedDeps env [root]
    IO.println s!"[closure-probe] {root}: {closure.length} constants"
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
    let support := Ix.AuxGen.literalSupportFor env closure
    for (label, given) in [("without the literal support", []), ("with the literal support", support)] do
      let opts : Ix.CompileM.DriverOptions :=
        { auxIxc := some { mode := .failClosed, recursors := true, asks := .recursors, trace := true }, serviceSupport := given }
      match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) (opts := opts) with
      | .error e =>
        failures := failures + 1
        IO.println s!"[closure-probe] {root}, {label}: compile failed: {e}"
        ProbeReport.emit "closure-probe" [("root", Lean.toJson root.toString), ("branch", .str label),
          ("support", Lean.toJson given.length), ("outcome", .str "compile-error"), ("error", .str e)]
      | .ok out =>
        IO.println s!"[closure-probe] {root}, {label} ({given.length} constants): \
          {out.cenv.ungrounded.size} block failures; source service: {out.source.summary}"
        for (k, why) in out.source.notAccepted do
          IO.println s!"[closure-probe]   block not accepted: {k.pretty}: {why.take 300}"
        for (g, why) in out.source.refused do
          IO.println s!"[closure-probe]   group refused: {g}: {why.take 300}"
        let complete := ProbeReport.complete out.source
        let bad := out.cenv.ungrounded.size + (if out.source.error.isSome || !complete then 1 else 0)
        failures := failures + bad
        ProbeReport.emit "closure-probe" [("root", Lean.toJson root.toString), ("branch", .str label),
          ("support", Lean.toJson given.length), ("outcome", .str "compiled"), ("source", ProbeReport.source out.source),
          ("blockFailures", .arr (out.cenv.ungrounded.toArray.map fun (n, why) => .arr #[ProbeReport.name n, .str why])),
          ("harnessError", if complete then .null else .str "capture-completeness: Source report truncated/inconsistent")]
  return if failures == 0 then 0 else 1

end Tests.Ix.AuxGen.ClosureProbe
