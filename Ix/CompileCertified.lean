module
public import Ix.Cert.Compile
public import Ix.Compile.ReadyCompile
public import Ix.Resource.Validate
public import Ix.RoleBinding.Compile
public section

/-!
# The certified compile of Lean source

`ix compile` and `ix compile-lean` compile with `Ix.Cert.compileReport`, the
function `Ix.Cert.CompileCorrect` is about, on the canonical environment of
their input:

1. **Source contracts.** The selected constants are prepared as the streamed
   pipeline prepares them (`prepareCertified`). A list with no contract
   registration and no contract metadata in either reserved namespace (a scan
   on tasks, `Ix.Compile.checkOrdinaryConstants`, which also checks that each
   constant is listed once, under its own name) is used as it is. Any other
   list is resolved and decorated (`Ix.Compile.compileInputFromEnv`, then
   `Ix.Compile.CompileInput.prepare`), then checked
   (`Ix.CompileM.checkPreparedSource`: no binder contract left unresolved,
   every semantic contract inspects).
2. **Canonicalization** (`canonInput`): `Ix.CanonM.canonChunk` on consecutive
   slices, on tasks. A chunk's value is `(nameS, constS)` of each of its
   constants (`Ix.Cert.Canon.canonChunkCorrect`), and the slices are joined in
   order, so the environment does not depend on the worker count.
3. **The compile**: `Ix.Cert.compileReport`, with its checks, at the default
   sharing limits, which it fixes. Execution runs through the
   `Ix.Compile.ReadyCompile.reportIO` subtype bridge
   (`{ result : ReportResult // result = Ix.Cert.compileReport env }` /
   `{ env : Ixon.Env // env = ... }`), which discharges the
   `ixe = (Ix.Compile.compileEnv rawEnv).1` / `compileReport` equality
   hypothesis of `Ix.Cert.checkReport_sound` and `Ix.Cert.CompileCorrect`
   directly from the parallel ready-queue execution without re-running
   sequential `compileEnv`.
4. **Accounting**: every failure it reports is an input constant's. With
   `compileReport`'s coverage check, every input constant is then published or
   reported as failed, and never both (the streamed pipeline's source
   accounting, `Ix.Compile.SourceGraph.Accounting`).
5. **Resources**: an input with semantic contracts compiles completely, and its
   artifact validates (`Ix.Resource.validate`), as the streamed pipeline's
   resource post-step requires (`Ix.CompileM.resourcePostStep`).

The artifact's role support and certificates are compiled the same way
(`certifiedBackend`), by `Ix.RoleBinding.Compile.finalize`.
-/

namespace Ix.CompileM

/-- The selected constants, prepared: unchanged when none has a contract
registration or contract metadata, otherwise resolved, decorated and checked.
The flag says whether the prepared list carries semantic contracts. -/
def prepareCertified (source : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) :
    Except String (List (Lean.Name × Lean.ConstantInfo) × Bool) := do
  let registry := Ix.Compile.sourceContractExtension.getState source
  let hints := Ix.Compile.sourceMeasureExtension.getState source
  if ← Ix.Compile.checkOrdinaryConstants constants
      (fun name => registry.contains name || hints.contains name) then
    return (constants, false)
  let input ← (Ix.Compile.compileInputFromEnv source constants).mapError toString
  let prepared ← input.prepare
  return (prepared, ← checkPreparedSource prepared)

/-- Prevent the compiler from dropping `x` before the enclosing `IO` action
runs, so its reference count is decremented inside `dropAsync`'s task. -/
@[noinline] private def keepAlive (α : Type) (x : α) : IO α :=
  pure x

/-- Drop a large arena or environment (`CompileState`, `Ixon.Env`,
`Ix.Environment`, `Lean.Environment`) on a background dedicated task so that
recursive Arena/RC teardown does not block the critical compilation path. -/
private def dropAsync (α : Type) (x : α) : IO (Task (Except IO.Error Unit)) :=
  IO.asTask (prio := .dedicated) do
    let _ ← keepAlive α x
    pure ()

/-- **The certified compiler's input**: the canonical environment of a prepared
list, canonicalized on `workers` tasks over consecutive slices, joined in order. -/
def canonInput (consts : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    Ix.Environment :=
  let tasks := (Ix.Compile.SourceGraph.Stream.partition consts workers).map fun part =>
    Task.spawn fun _ => Ix.CanonM.canonChunk part
  { consts := tasks.foldl (init := Std.HashMap.emptyWithCapacity consts.size) fun m t =>
      t.get.foldl (fun m (n, c) => m.insert n c) m }

/-- A failure that `failures` reports for a name that is not an input constant. -/
def failureOutside (env : Ix.Environment) (failures : Ix.Cert.Failures) : Option Ix.Name :=
  (failures.toMap.toList.find? fun (n, _) => !env.consts.contains n).map (·.1)

/-- The first published role name whose address is not the default role table's
address of that role (`Ix.Cert.PublishedRolesBound`), if any. -/
def unboundPublishedRole (ixe : Ixon.Env)
    (existing? : Option (Std.HashMap Ix.Kernel.Name Address) := none) :
    Option (Ix.Name × Ix.Kernel.Role × Address) :=
  let bound : Std.HashMap Ix.Kernel.Role Address :=
    Ix.Cert.roleTableBound.foldl (fun m (r, a) => if m.contains r then m else m.insert r a) {}
  let hasMismatch := match existing? with
    | some existing =>
      Ix.Kernel.Role.all.any fun r =>
        match existing[r.leanName]? with
        | some addr => bound[r]? != some addr
        | none => false
    | none => true
  if !hasMismatch then none
  else
    (Ix.Compile.Parallel.map 32 (fun (n, named) =>
      match Ix.Kernel.Role.ofLeanName? (Ix.LeanIngress.ingressName n) with
      | some r =>
        if bound[r]? == some named.addr then none else some (n, r, named.addr)
      | none => none) ixe.named.toArray).findSome? id

/-- The certified compile's result. -/
structure CertifiedOut where
  /-- The prepared input. -/
  prepared : List (Lean.Name × Lean.ConstantInfo)
  /-- The input carries semantic contracts. -/
  annotated : Bool
  /-- The number of input constants. -/
  inputs : Nat
  /-- `Ix.Cert.compileReport`'s artifact. -/
  env : Ixon.Env
  /-- `Ix.Cert.compileReport`'s failures. -/
  failures : Ix.Cert.Failures
  /-- Pre-validated source-address map from `Ix.RoleBinding.sourceAddresses env`. -/
  existing? : Option (Std.HashMap Ix.Kernel.Name Address) := none

/-- **The certified compile of a prepared list**: its canonical environment
(`canonInput`), then `Ix.Cert.compileReport`, then the accounting and, for an
input with semantic contracts, the resource checks. `log` receives each
phase's time. -/
def compileCertifiedPrepared (prepared : List (Lean.Name × Lean.ConstantInfo))
    (annotated : Bool) (workers : Nat := 32) (log : String → IO Unit := fun _ => pure ()) :
    IO (Except String CertifiedOut) := do
  let t0 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => canonInput prepared.toArray workers
  let inputs := env.consts.size
  unless inputs == prepared.length do
    return .error s!"source accounting: {prepared.length} prepared constants collapsed to {inputs} input entries"
  let t1 ← IO.monoMsNow
  log s!"canon ({inputs} constants): {t1 - t0}ms"
  let (report, _) ← Ix.Compile.ReadyCompile.reportIO { workers, lookahead := 8192 } env
  let t2 ← IO.monoMsNow
  log s!"compileReport: {t2 - t1}ms"
  let (ixe, failures) ← match report.val with
    | .ok out => pure out
    | .error e => return .error e
  if let some n := failureOutside env failures then
    return .error s!"source accounting: failure name '{n.pretty}' is outside the original input"
  let _ ← dropAsync _ env
  let existing ← match Ix.RoleBinding.sourceAddresses ixe with
    | .ok m => pure m
    | .error e => return .error e
  if let some (n, r, addr) := unboundPublishedRole ixe (some existing) then
    return .error s!"role check failed: the published role {n.pretty} ({repr r}) is at {addr}, \
      not its bound address in the default role table"
  if annotated then
    unless failures.isEmpty do
      return .error "resource compilation requires the complete requested closure"
    if let .error e := Ix.Resource.validate ixe (Ix.Resource.standardProfile ixe) then
      return .error e
  return .ok { prepared, annotated, inputs, env := ixe, failures, existing? := some existing }

/-- **The certified compile** of the constants `constants` of `source`:
`prepareCertified`, then `compileCertifiedPrepared`. -/
def compileCertified (source : Lean.Environment) (constants : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat := 32) (log : String → IO Unit := fun _ => pure ()) :
    IO (Except String CertifiedOut) := do
  let t0 ← IO.monoMsNow
  let (prepared, annotated) ← match prepareCertified source constants with
    | .ok p => pure p
    | .error e => return .error e
  log s!"source contracts ({if annotated then "semantic contracts" else "none"}): \
{(← IO.monoMsNow) - t0}ms"
  compileCertifiedPrepared prepared annotated workers log

/-- An input with semantic contracts is emitted only if its finalized artifact
validates too, as the streamed pipeline checks it after `finalize`. -/
def validateFinalized (annotated : Bool) (artifact : Ixon.Env) : Except String Unit := do
  if annotated then
    let _ ← Ix.Resource.validate artifact (Ix.Resource.standardProfile artifact)

/-- Up to three recorded failures, root causes first: a failure that only names a
missing constant is a dependent's, listed after the ones that name a cause. -/
def recordedFailures (failures : Std.HashMap Ix.Name String) : String :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  let all := failures.toList
  let ordered := all.filter (!cascade ·.2) ++ all.filter (cascade ·.2)
  "; ".intercalate (ordered.take 3 |>.map fun (n, e) => s!"{n.pretty}: {(e.replace "\n" " ").take 200}")

/-- Compile `constList` with the certified Lean compiler and return its `CompilePhases`. -/
def compilePhasesOf (leanEnv : Lean.Environment)
    (constList : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat := 8) : IO CompilePhases := do
  let certOut ← IO.ofExcept (← compileCertified leanEnv constList workers)
  unless certOut.failures.isEmpty do
    let fMap := certOut.failures.toMap
    throw (IO.userError s!"compilePhasesOf: {fMap.size} constant(s) failed to compile: {recordedFailures fMap}")
  let rawEnv := canonInput certOut.prepared.toArray workers
  let condensed := Ix.Cert.blocksOf rawEnv
  return { rawEnv, condensed, compileEnv := certOut.env }

end Ix.CompileM

namespace Ix.Cert.Compile

abbrev compileCertified := Ix.CompileM.compileCertified

end Ix.Cert.Compile

namespace Ix.RoleBinding.Compile

/-- The certified compiler as `finalize`'s backend: the role support and the
certificates are compiled with `Ix.Cert.compileReport`, and must compile
completely. -/
def certifiedBackend (workers : Nat) : Backend := fun _ input => do
  let prepared ← IO.ofExcept input.prepare
  let annotated ← IO.ofExcept (Ix.CompileM.checkPreparedSource prepared)
  let out ← IO.ofExcept (← Ix.CompileM.compileCertifiedPrepared prepared annotated workers)
  unless out.failures.isEmpty do
    throw (IO.userError "artifact support: incomplete certified compilation")
  return out.env

end Ix.RoleBinding.Compile

namespace Ix.RoleBinding

abbrev certifiedBackend := Ix.RoleBinding.Compile.certifiedBackend

end Ix.RoleBinding

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
