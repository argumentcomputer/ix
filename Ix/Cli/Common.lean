module
public import Ix.CompileM
public import Ix.Merkle

/-!
  Helpers shared by the compile commands (`ix compile`, `ix compile-lean`,
  `ix compile-export`, `ix validate-lean`) and by the certified compile's
  failure listing (`Ix.CompileM.recordedFailures`).
-/

public section

namespace Ix.Cli

/-- The process's resident set size, from `/proc/self/status` (`?` where it
    cannot be read). -/
def residentSetSize : IO String := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let rss := (status.splitOn "\n").findSome? fun l =>
      if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
    return (rss.getD "?").trimAscii.toString
  catch _ => return "?"

/-- Failures listed root causes first: a constant that failed only because a
    dependency is missing is a cascade, listed after the ones that name the
    cause (a refusal's message must be visible in the bounded listing). -/
def rootCausesFirst {α : Type} (xs : List (α × String)) : List (α × String) :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  xs.filter (!cascade ·.2) ++ xs.filter (cascade ·.2)

/-- The canonical Merkle root of `env`'s stored constants, formatted as a hex string. -/
def rootOf (env : Ixon.Env) : String :=
  toString ((Ix.Merkle.merkleRootCanonical (env.consts.toArray.map (·.1))).getD Ix.Merkle.zeroAddress)

/-- Initial `CompileEnvStatus` for `original` and `failures` prior to finalization and serialization. -/
def statusOf (original : Ixon.Env) (failures : Std.HashMap Ix.Name String) :
    Ix.CompileM.CompileEnvStatus :=
  let ungrounded := (failures.toArray.map fun (n, r) => (n.pretty, r)).qsort (fun a b => a.1 < b.1)
  { root := rootOf original, ungrounded, nonCanonical := #[], bytes := 0, named := 0, uniqueAnon := 0 }

end Ix.Cli

end
