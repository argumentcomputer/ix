import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Fixtures.AuxiliaryIdentity

namespace Tests.Ix.Compile.AuxPublication

open _root_.Ix (Name)

private def need (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def decoded (env : Ixon.Env) : Except String Ixon.LazyEnvParts := do
  Ixon.deEnvVerifiedLazy (← Ixon.serEnv env)

/-- Synthetic block selectors must cover every member and reject malformed
member metadata. Ordinary duplicate selectors retain their coverage obligation. -/
def selectorControls (env : Ixon.Env) : IO Unit := do
  let some (container, entry) := env.named.toArray.find? fun (name, entry) =>
      _root_.Ix.Compile.Pass.hasReserved name && (entry.constMeta.info matches .muts ..)
    | throw (IO.userError "private helper block fixture missing")
  let .muts classes layout := entry.constMeta.info
    | throw (IO.userError "private helper block has wrong metadata kind")
  let parts ← IO.ofExcept (decoded env)
  let members ← IO.ofExcept (Pass3.expandKernelTargets parts #[container.pretty])
  need (!members.isEmpty) "private block selector lost all members"
  for cls in classes do
    for hash in cls do
      let some member := env.names.get? hash | throw (IO.userError "fixture member missing")
      need (members.contains member.pretty) "private block selector dropped a member"
  let repeated ← IO.ofExcept (Pass3.expandKernelTargets parts #["Nat", "Nat"])
  need (repeated == #["Nat", "Nat"]) "ordinary duplicate selector was silently dropped"
  let altered := fun classes =>
    let changed := { entry with constMeta := { entry.constMeta with info := .muts classes layout } }
    { env with named := env.named.insert container changed }
  for (label, badClasses) in #[
      ("empty class", classes.set! 0 #[]),
      ("wrong count", classes.push #[]),
      ("foreign member", classes.set! 0 #[(Name.fromLeanName `Nat).getHash])] do
    let bad ← IO.ofExcept (decoded (altered badClasses))
    need ((Pass3.expandKernelTargets bad #[container.pretty]).toOption.isNone)
      s!"block selector accepted {label}"

/-- End-to-end source-binding controls: compile the same captured closure in
Lean (one/four workers) and Rust, require exact bytes and source recovery, and
check every fixture/generated declaration in all three kernels. -/
def run (env : Lean.Environment) : IO UInt32 := do
  let root := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if root.isPrefixOf name then some name else none
  need (!seeds.isEmpty) "auxiliary publication fixture missing"
  let unit : Pass3.CUnit := {
    name := "AuxiliaryIdentity", env, seeds := seeds.toArray
    closure := Pass3.closureOf env seeds }
  let seq ← Twins.leanCompile env unit.closure (workers := 1)
  let par ← Twins.leanCompile env unit.closure (workers := 4)
  need (seq.cenv.ungrounded.isEmpty && par.cenv.ungrounded.isEmpty)
    s!"auxiliary source compilation failed: {seq.cenv.ungrounded.toArray.map (fun (n, e) => (n.pretty, e))}"
  for name in seeds do
    need ((seq.env.getNamed? (Name.fromLeanName name)).isSome) s!"source name not emitted: {name}"
  need (seq.bytes == par.bytes) "auxiliary publication depends on worker count"
  let (problems, summary) ← Pass3.decompileCheck unit seq
  need problems.isEmpty s!"auxiliary source recovery failed: {problems}"
  let dir : System.FilePath :=
    (← IO.getEnv "AUX_PUBLICATION_KEEP").getD "plans/tasks/lean-to-ixon-correctness/aux-publication-gate"
  IO.FS.createDirAll dir
  let leanPath := dir / "lean.ixe"
  let rustPath := dir / "rust.ixe"
  IO.FS.writeBinFile leanPath seq.bytes
  let input ← IO.ofExcept ((_root_.Ix.Compile.compileInputFromEnv env unit.closure).mapError toString)
  let constants ← IO.ofExcept input.prepare
  let status ← _root_.Ix.CompileM.rsCompileEnvBytesFFI constants rustPath.toString false
  need status.ungrounded.isEmpty s!"Rust rejected {status.ungrounded.size} source declarations"
  need ((← IO.FS.readBinFile rustPath) == seq.bytes) "auxiliary publication differs between Lean and Rust"
  let sourceNames : Std.HashSet Name := unit.seeds.foldl (fun s n => s.insert (Name.fromLeanName n)) {}
  let requested := seq.env.named.toArray.filterMap fun (name, _) =>
    if sourceNames.contains name || _root_.Ix.Compile.Pass.hasReserved name then some name.pretty else none
  let checks := dir / "kernels"
  IO.FS.createDirAll checks
  let result ← Pass3.kernelRun checks leanPath requested
  need result.failed.isEmpty s!"auxiliary publication kernel failures: {result.failed}"
  need (result.checked.all (fun (_, count) => count == result.targets.size))
    s!"auxiliary publication kernel coverage differs: {result.checked} / {result.targets.size}"
  selectorControls seq.env
  IO.println s!"[aux-publication] {summary}; {seq.bytes.size} bytes identical (Lean 1/4 workers, Rust); \
{result.targets.size} declarations accepted by all three kernels; selector controls passed"
  return 0

end Tests.Ix.Compile.AuxPublication
