module
public import Ix.Cert.Compile
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
   sharing limits, which it fixes.
4. **Accounting**: every failure it reports is an input constant's. With
   `compileReport`'s coverage check, every input constant is then published or
   reported as failed, and never both (the streamed pipeline's source
   accounting, `Ix.Compile.SourceGraph.Accounting`).
5. **Resources**: an input with semantic contracts compiles completely, and its
   artifact validates (`Ix.Resource.validate`), as the streamed pipeline's
   resource post-step requires (`Ix.CompileM.resourcePostStep`).

The artifact's role support and certificates are compiled the same way
(`certifiedBackend`), by `Ix.RoleBinding.Compile.finalize`.

The streamed pipeline (`Ix.CompileM.compileLeanInputValidated`) stays available
as an uncertified option of both commands: only its fold is proved to be
`compileReport`'s (`Ix.Cert.Hybrid`), and its streamed front end is tested
against it.
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

/-- **The certified compiler's input**: the canonical environment of a prepared
list, canonicalized on `workers` tasks over consecutive slices, joined in order. -/
def canonInput (consts : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    Ix.Environment :=
  let tasks := (Ix.Compile.SourceGraph.Stream.partition consts workers).map fun part =>
    Task.spawn fun _ => Ix.CanonM.canonChunk part
  { consts := tasks.foldl (init := {}) fun m t => t.get.foldl (fun m (n, c) => m.insert n c) m }

/-- A failure that `failures` reports for a name that is not an input constant. -/
def failureOutside (env : Ix.Environment) (failures : Ix.Cert.Failures) : Option Ix.Name :=
  (failures.toMap.toList.find? fun (n, _) => !env.consts.contains n).map (·.1)

/-- The first published role name whose address is not the default role table's
address of that role (`Ix.Cert.PublishedRolesBound`), if any. -/
def unboundPublishedRole (ixe : Ixon.Env) : Option (Ix.Name × Ix.Kernel.Role × Address) :=
  let bound : Std.HashMap Ix.Kernel.Role Address :=
    Ix.Cert.roleTableBound.foldl (fun m (r, a) => if m.contains r then m else m.insert r a) {}
  ixe.named.toList.findSome? fun (n, named) =>
    match Ix.Kernel.Role.ofLeanName? (Ix.LeanIngress.ingressName n) with
    | some r =>
      if bound[r]? == some named.addr then none else some (n, r, named.addr)
    | none => none

/-- The certified compile's result. -/
structure CertifiedOut where
  /-- The prepared input, which `--rust-check` compiles too. -/
  prepared : List (Lean.Name × Lean.ConstantInfo)
  /-- The input carries semantic contracts. -/
  annotated : Bool
  /-- The number of input constants. -/
  inputs : Nat
  /-- `Ix.Cert.compileReport`'s artifact. -/
  env : Ixon.Env
  /-- `Ix.Cert.compileReport`'s failures. -/
  failures : Ix.Cert.Failures

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
  let report ← IO.lazyPure fun _ => Ix.Cert.compileReport env
  let t2 ← IO.monoMsNow
  log s!"compileReport: {t2 - t1}ms"
  let (ixe, failures) ← match report with
    | .ok out => pure out
    | .error e => return .error e
  if let some n := failureOutside env failures then
    return .error s!"source accounting: failure name '{n.pretty}' is outside the original input"
  if let .error e := Ix.RoleBinding.sourceAddresses ixe then
    return .error e
  if let some (n, r, addr) := unboundPublishedRole ixe then
    return .error s!"role check failed: the published role {n.pretty} ({repr r}) is at {addr}, \
      not its bound address in the default role table"
  if annotated then
    unless failures.isEmpty do
      return .error "resource compilation requires the complete requested closure"
    if let .error e := Ix.Resource.validate ixe (Ix.Resource.standardProfile ixe) then
      return .error e
  return .ok { prepared, annotated, inputs, env := ixe, failures }

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

end Ix.CompileM

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

end
