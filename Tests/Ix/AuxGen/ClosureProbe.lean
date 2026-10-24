import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.AuxGen.LiteralSupport

/-! # The Source service on selected closures (`lake exe IxTests --ignored auxgen-closure-probe`)

AuxGen M3's coverage probe. Source mode covers whole libraries; on a
selected closure (`ix compile-lean --consts`) the drivers' Source service
can lack what Source mode needs, and IxC then refuses `.below`'s and
`.brecOn`'s questions where `Ix.Tc` answers them (`compile-closure-whole`'s
`MCasesPat` closure under `failClosed`). This runner compiles the selected
closure of each root (`PROBE_ROOTS`, comma-separated; by default
`compile-closure-whole`'s failing root) of Init+Std, as `ix compile-lean`
does, with the aux tails in `shadow` mode and their counts traced
(`[auxgen-ixc] …` on stderr), without and with the literal support the closure
lacks (`Ix.AuxGen.literalSupportFor`, generation side only), and prints the
run-ahead's report each time. It asserts nothing: it is a measurement. -/

namespace Tests.Ix.AuxGen.ClosureProbe

def defaultRoots : List Lean.Name := [`Lean.Parser.Tactic.MCasesPat.parse.go._unsafe_rec]

def run : IO UInt32 := do
  let env ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
  let roots ← match ← IO.getEnv "PROBE_ROOTS" with
    | some s => pure ((s.splitOn ",").filter (!·.isEmpty) |>.map String.toName)
    | none => pure defaultRoots
  for root in roots do
    let closure := Ix.EnvScope.collectSelectedDeps env [root]
    IO.println s!"[closure-probe] {root}: {closure.length} constants"
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
    let support := Ix.AuxGen.literalSupportFor env closure
    for (label, given) in [("without the literal support", []), ("with the literal support", support)] do
      let opts : Ix.CompileM.DriverOptions :=
        { auxIxc := some { mode := .shadow, trace := true }, serviceSupport := given }
      match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) (opts := opts) with
      | .error e => IO.println s!"[closure-probe] {root}, {label}: compile failed: {e}"
      | .ok out =>
        IO.println s!"[closure-probe] {root}, {label} ({given.length} constants): \
          {out.cenv.ungrounded.size} block failures; source service: {out.source.summary}"
        for (k, why) in out.source.notAccepted do
          IO.println s!"[closure-probe]   block not accepted: {k.pretty}: {why.take 300}"
        for (g, why) in out.source.refused do
          IO.println s!"[closure-probe]   group refused: {g}: {why.take 300}"
  return 0

end Tests.Ix.AuxGen.ClosureProbe
