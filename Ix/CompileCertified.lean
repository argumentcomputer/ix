module
public import Ix.Cert.Compile
public import Ix.Compile.ReadyCompile
public import Ix.Resource.Validate
public import Ix.RoleBinding.Compile
public import Ix.Cli.Common
public import Ix.Compile.BinderData
public import Ix.Compile.KernelAnnotate
public section

/-!
# The certified compile of Lean source

`ix compile`, `ix compile-lean`, `ix compile-export` and `ix validate-lean`
compile with `Ix.Cert.compileReport`, the function `Ix.Cert.CompileCorrect` is
about, on the canonical environment of their input (`compileAndFinalize`):

1. **Source contracts.** The selected constants are prepared
   (`prepareCertified`). A list with no contract
   registration and no contract metadata in either reserved namespace (a scan
   on tasks, `Ix.Compile.checkOrdinaryConstants`, which also checks that each
   constant is listed once, under its own name) is used as it is. Any other
   list is resolved and decorated (`Ix.Compile.compileInputFromEnv`, then
   `Ix.Compile.CompileInput.prepare`), then checked
   (`Ix.CompileM.checkPreparedSource`: no binder contract left unresolved,
   every semantic contract inspects).
2. **Canonicalization** (`canonInput`): `Ix.CanonM.canonChunk` on consecutive
   slices (`Ix.CanonM.chunks`), on tasks. A chunk's value is `(nameS, constS)`
   of each of its constants (`Ix.Cert.Canon.canonChunkCorrect`), and the
   slices are joined in order, so the environment does not depend on the
   worker count.
3. **The compile**: `Ix.Cert.compileReport`, with its checks, at the default
   sharing limits, which it fixes. Execution runs through the
   `Ix.Compile.ReadyCompile.reportIO` subtype bridge
   (`{ result : ReportResult // result = Ix.Cert.compileReport env }` /
   `{ env : Ixon.Env // env = ... }`), which discharges the
   `ixe = (Ix.Compile.compileEnv rawEnv).1` / `compileReport` equality
   hypothesis of `Ix.Cert.checkReport_sound` and `Ix.Cert.CompileCorrect`
   directly from the parallel ready-queue execution without re-running
   sequential `compileEnv`.
4. **Accounting**: every failure it reports is an input constant's
   (`failureOutside`). With `compileReport`'s coverage check, every input
   constant is then published or reported as failed, and never both.
5. **Resources**: an input with semantic contracts compiles completely, and its
   artifact validates (`Ix.Resource.validate`), before `finalize` and after it
   (`validateFinalized`).

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
  let size := max 1 ((consts.size + workers - 1) / workers)
  let tasks := (Ix.CanonM.chunks consts size).map fun part =>
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
  /-- The binder-data annotator the compile ran with (`none` without binder data), for the
  definitions compiled later over the same input (`compilePhasesOf`). -/
  annotator? : Option Ix.BinderAnnotator := none
  /-- The safe records the annotator gave an undecided binder (their member names). -/
  undecided : Array String := #[]

/-- Whether the default role table binds the records the compiler writes. It binds the
records of the compile without binder data; regenerating it from records with their
binder data makes it current again. Until then the default-role check is not made. -/
def defaultRoleTableCurrent : Bool := false

/-- **The certified compile of a prepared list**: its canonical environment
(`canonInput`), then `Ix.Cert.compileReport`, then the accounting and, for an
input with semantic contracts, the resource checks. `log` receives each
phase's time.

With `defaultRoles`, every published role name must sit at the default role
table's address of its role (`unboundPublishedRole`): the input is ix's own
toolchain's, whose role constants the default table binds. An export of
another toolchain is compiled without it. Its role constants reach that
toolchain's `Init`, so they sit at other addresses (4.35.0's `Decidable` has
one constructor, so its `Int.decLt` does). `finalize` binds them in a table
generated from the export, and `checkFinalized` checks every published role
name against that table (`Ix.Cert.PublishedRolesBound` at the artifact's own
binding).

With `binderData`, IxC installs the canonical environment in Source mode
(`Ix.Compile.KernelAnnotate.installInput`) and the canonical environment carries
the annotator over it (`Ix.Compile.KernelAnnotate.annotator`): the compile writes
every record's binder data from it (`Ix.CompileM.withBinderSection`), and the
certified result is the compile of that environment. Without it, every record
with a binder carries the undecided section. The default role table binds records carrying
their binder data, so its check is made only with `binderData`, and only while that table is
current (`defaultRoleTableCurrent`). -/
def compileCertifiedPrepared (prepared : List (Lean.Name × Lean.ConstantInfo))
    (annotated : Bool) (workers : Nat := 32) (log : String → IO Unit := fun _ => pure ())
    (defaultRoles : Bool := true) (binderData : Bool := false) (keepAnnotator : Bool := false) :
    IO (Except String CertifiedOut) := do
  let t0 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => canonInput prepared.toArray workers
  let inputs := env.consts.size
  unless inputs == prepared.length do
    return .error s!"source accounting: {prepared.length} prepared constants collapsed to {inputs} input entries"
  let t1 ← IO.monoMsNow
  log s!"canon ({inputs} constants): {t1 - t0}ms"
  let mut env := env
  if binderData then
    match ← Ix.Compile.KernelAnnotate.installInput env workers with
    | .error e =>
      log s!"binder data: IxC's environment is not installed ({e}): every record with a binder \
        carries the undecided section"
    | .ok installed =>
      log s!"binder data: installed {installed.installed} declarations, {installed.failures.size} \
        refused ({installed.lenient} of them entered without their checks), {installed.ahead} pushed ahead in {installed.waves} waves; phases (ms) {installed.times}; {(← IO.monoMsNow) - t1}ms, rss \
        {← Ix.Cli.residentSetSize}"
      for (name, why) in installed.failures.extract 0 20 do
        log s!"binder data: the kernel refused {name}: {(why.replace "\n" " ").take 200}"
      env := { env with binderAnnotator? := some (Ix.Compile.KernelAnnotate.annotator installed) }
  let t1 ← IO.monoMsNow
  let (report, _) ← Ix.Compile.ReadyCompile.reportIO { workers, lookahead := 8192 } env
  let t2 ← IO.monoMsNow
  log s!"compileReport: {t2 - t1}ms"
  let (ixe, failures) ← match report.val with
    | .ok out => pure out
    | .error e => return .error e
  if let some n := failureOutside env failures then
    return .error s!"source accounting: failure name '{n.pretty}' is outside the original input"
  let annotator? := if keepAnnotator then env.binderAnnotator? else none
  let _ ← dropAsync _ env
  let existing ← match Ix.RoleBinding.sourceAddresses ixe with
    | .ok m => pure m
    | .error e => return .error e
  if defaultRoles && binderData && defaultRoleTableCurrent then
    if let some (n, r, addr) := unboundPublishedRole ixe (some existing) then
      return .error s!"role check failed: the published role {n.pretty} ({repr r}) is at {addr}, \
        not its bound address in the default role table"
  if annotated then
    unless failures.isEmpty do
      return .error "resource compilation requires the complete requested closure"
    if let .error e := Ix.Resource.validate ixe (Ix.Resource.standardProfile ixe) then
      return .error e
  let undecided := if binderData then
      (Ix.Compile.KernelAnnotate.undecidedSafe ixe workers).map toString
    else #[]
  return .ok { prepared, annotated, inputs, env := ixe, failures, existing? := some existing,
               annotator?,
               undecided }

/-- **The certified compile** of the constants `constants` of `source`:
`prepareCertified`, then `compileCertifiedPrepared` (with `defaultRoles`), with
the binder data from IxC's pass over the input (`Ix.Compile.KernelAnnotate`), unless
`binderData` is off: then every record with a binder carries the undecided
section. -/
def compileCertified (source : Lean.Environment) (constants : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat := 32) (log : String → IO Unit := fun _ => pure ())
    (defaultRoles : Bool := true) (binderData : Bool := true) (keepAnnotator : Bool := false) :
    IO (Except String CertifiedOut) := do
  let t0 ← IO.monoMsNow
  let (prepared, annotated) ← match prepareCertified source constants with
    | .ok p => pure p
    | .error e => return .error e
  log s!"source contracts ({if annotated then "semantic contracts" else "none"}): \
{(← IO.monoMsNow) - t0}ms"
  compileCertifiedPrepared prepared annotated workers log defaultRoles binderData keepAnnotator

/-- An input with semantic contracts is emitted only if its finalized artifact
validates too: `compileCertifiedPrepared` validates the compiled artifact, this
the finalized one. -/
def validateFinalized (annotated : Bool) (artifact : Ixon.Env) : Except String Unit := do
  if annotated then
    let _ ← Ix.Resource.validate artifact (Ix.Resource.standardProfile artifact)

/-- Up to three recorded failures, root causes first (`Ix.Cli.rootCausesFirst`). -/
def recordedFailures (failures : Std.HashMap Ix.Name String) : String :=
  "; ".intercalate ((Ix.Cli.rootCausesFirst failures.toList).take 3 |>.map fun (n, e) =>
    s!"{n.pretty}: {(e.replace "\n" " ").take 200}")

/-- Compile `constList` with the certified Lean compiler and return its `CompilePhases`. -/
def compilePhasesOf (leanEnv : Lean.Environment)
    (constList : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat := 8) : IO CompilePhases := do
  let certOut ← IO.ofExcept (← compileCertified leanEnv constList workers (keepAnnotator := true))
  unless certOut.failures.isEmpty do
    let fMap := certOut.failures.toMap
    throw (IO.userError s!"compilePhasesOf: {fMap.size} constant(s) failed to compile: {recordedFailures fMap}")
  -- the compile's annotator, so that a definition compiled over the input later
  -- (`Ix.Commit.compileDef`) gets its binder data
  let rawEnv := { canonInput certOut.prepared.toArray workers with binderAnnotator? := certOut.annotator? }
  let condensed := Ix.Cert.blocksOf rawEnv
  return { rawEnv, condensed, compileEnv := certOut.env }

end Ix.CompileM

namespace Ix.RoleBinding.Compile

/-- The certified compiler as `finalize`'s backend: the role support and the
certificates are compiled with `Ix.Cert.compileReport`, and must compile
completely. `defaultRoles` as in `Ix.CompileM.compileCertifiedPrepared`; the binder
data come from IxC's pass over the backend's prepared input, unless `binderData` is off. -/
def certifiedBackend (workers : Nat) (defaultRoles : Bool := true) (binderData : Bool := true) :
    Backend := fun _source input => do
  let prepared ← IO.ofExcept input.prepare
  let annotated ← IO.ofExcept (Ix.CompileM.checkPreparedSource prepared)
  let out ← IO.ofExcept
    (← Ix.CompileM.compileCertifiedPrepared prepared annotated workers (defaultRoles := defaultRoles)
      (binderData := binderData))
  unless out.failures.isEmpty do
    throw (IO.userError "artifact support: incomplete certified compilation")
  return out.env

end Ix.RoleBinding.Compile

namespace Ix.CompileM

/-- How `ix compile` gives records their binder data: while building each record,
from IxC's pass over the input (`inline`, the default:
`Ix.CompileM.withBinderSection` with `Ix.Compile.KernelAnnotate.annotator`); with every
binder undecided (`off`, for measurement); or as `off`, then by IxC's pass over
the finalized artifact, which is then re-addressed (`post`, for comparison:
`Ix.Compile.BinderData.apply`). -/
inductive BinderDataMode where
  | off | inline | post
  deriving BEq, Repr, Inhabited

def BinderDataMode.parse? : String → Option BinderDataMode
  | "off" => some .off
  | "inline" => some .inline
  | "post" => some .post
  | _ => none

/-- What `compileAndFinalize` made of a certified compile. -/
inductive Finalization where
  /-- Not finalized: a constant failed to compile, and a partial artifact was
  not allowed. -/
  | refused
  /-- `finalize`, `validateFinalized` or `Ixon.serEnv` failed. -/
  | failed (error : String)
  /-- The finalized artifact, after `strip`, and its serialization. -/
  | done (artifact : Ixon.Env) (bytes : ByteArray)

/-- **The certified compile, finalized**, as the compile commands run it:
`compileCertified`; then, unless a constant failed and `allowPartial` is false,
the role support, certificates and binding (`Ix.RoleBinding.Compile.finalize`
with `certifiedBackend`, the certificate theorems from `certSource`),
`validateFinalized`, `strip` and `Ixon.serEnv`. The outer error is the
compile's refusal. `log` receives each phase's time and the resident set size.
`defaultRoles` is off for another toolchain's export, as in
`compileCertifiedPrepared`; the finalized artifact's published role names are
then checked against its own binding (`checkFinalized`).

With `prefetch`, every role's certificate compile starts first, beside the
source compile (`Ix.RoleBinding.Compile.prefetchCertificates`): a compile of a
whole toolchain's library publishes every role, so `finalize` needs exactly
those certificates. The prefetch is always joined before returning, also on a
refusal or a failure, or when `finalize` needed other certificates: a task
still running when `main` returns would wait for subtasks that the runtime's
shutdown no longer runs.

Binder data (`binderData`): `inline` writes every record's section while the
record is built, and `finalize`'s generated theorem records get theirs from
IxC's pass over the records before they are addressed. `post` finalizes
without data, then gives every record its section
(`Ix.Compile.BinderData.apply`, the artifact re-addressed) before
`validateFinalized`; `onBinders` receives the report and the artifact. A binder
whose datum the annotator cannot decide carries the undecided node, and each
safe record with one is reported; with `strictBinderData` it fails the compile
instead.

With `defaultRoles`, `inline` and a current default table, a finalized artifact
whose table binds every role (a compile of the whole toolchain library) must be
bound at the default table's address: the default table is the one such a
compile generates. -/
def compileAndFinalize (source : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (allowPartial : Bool)
    (log : String → IO Unit := fun _ => pure ())
    (certSource : IO Lean.Environment := Ix.RoleBinding.Compile.nativeCertSource)
    (strip : Ixon.Env → Ixon.Env := id) (defaultRoles : Bool := true)
    (prefetch : Bool := false) (binderData : BinderDataMode := .inline)
    (strictBinderData : Bool := false)
    (onBinders : Ix.Compile.BinderData.Report → Ixon.Env → IO Unit := fun _ _ => pure ()) :
    IO (Except String (CertifiedOut × Finalization)) := do
  let inline := binderData == .inline
  let backend := Ix.RoleBinding.Compile.certifiedBackend workers defaultRoles inline
  let certificates? ← if prefetch then
      some <$> Ix.RoleBinding.Compile.prefetchCertificates backend certSource
    else pure none
  let run : IO (Except String (CertifiedOut × Finalization)) := do
    let out ← match ← compileCertified source constants workers log defaultRoles inline with
      | .ok out => pure out
      | .error e => return .error e
    log s!"rss after the compile: {← Ix.Cli.residentSetSize}"
    if !allowPartial && !out.failures.isEmpty then return .ok (out, .refused)
    try
      let t0 ← IO.monoMsNow
      let artifact ← Ix.RoleBinding.Compile.finalize backend source certSource
        (.plain constants) out.env Ix.Resource.typingLimits (existing? := out.existing?)
        (prefetched? := certificates?) (binderData := inline)
      let tb ← IO.monoMsNow
      log s!"finalize: {tb - t0}ms, rss {← Ix.Cli.residentSetSize}"
      let artifact ← match binderData with
        | .post =>
          let (artifact, binders) ← IO.ofExcept (Ix.Compile.BinderData.apply artifact)
          log s!"binder data: {(← IO.monoMsNow) - tb}ms, rss {← Ix.Cli.residentSetSize}; \
            {binders.summary}"
          onBinders binders artifact
          if strictBinderData && !binders.undecided.isEmpty then
            throw (IO.userError s!"binder data: {binders.undecided.size} undecided binder(s) \
              (--strict-binder-data)")
          pure artifact
        | .inline =>
          -- the records `finalize` added (support, certificates, evidence) too
          let added : Array (Address × Ixon.LazyConstant) := artifact.consts.fold (init := #[])
            fun acc a lc => if out.env.consts.contains a then acc else acc.push (a, lc)
          let addedUndecided := added.filterMap fun (a, lc) => match lc.get? with
            | some c =>
              if !Ix.Compile.KernelAnnotate.unsafeOrPartial c &&
                  c.binders.any (·.nodes.any (· == .undecided)) then some (toString a) else none
            | none => none
          let undecided := out.undecided ++ addedUndecided
          if defaultRoles && defaultRoleTableCurrent then
            if let some b := artifact.roleBinding then
              if let some t := Ix.Kernel.RoleTable.ofBytes b.bytes then
                if t.bound.size == Ix.Kernel.Role.all.length then
                  let d ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
                  unless b.address == d do
                    throw (IO.userError s!"role check failed: the compile binds every role in the \
                      table at {b.address}, not at the default table's address {d}")
          log s!"binder data: {undecided.size} safe record(s) with an undecided binder"
          for names in undecided.extract 0 20 do
            log s!"binder data: undecided binder in safe {names}"
          if strictBinderData && !undecided.isEmpty then
            throw (IO.userError s!"binder data: {undecided.size} safe record(s) with an undecided \
              binder (--strict-binder-data)")
          pure artifact
        | .off => pure artifact
      IO.ofExcept (validateFinalized out.annotated artifact)
      let t1 ← IO.monoMsNow
      let artifact := strip artifact
      let bytes ← IO.ofExcept (Ixon.serEnv artifact)
      log s!"serialize ({bytes.size} bytes): {(← IO.monoMsNow) - t1}ms"
      return .ok (out, .done artifact bytes)
    catch e => return .ok (out, .failed e.toString)
  try run
  finally
    if let some (_, task) := certificates? then
      let _ ← IO.wait task

end Ix.CompileM

end
