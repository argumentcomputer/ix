module

public import Ix.RoleBinding.Compile
public import Ix.RoleBinding.ArtifactTiered
public import Ix.Cli.CompileCmd
public import LSpec

namespace Tests.Ix.RoleCompile

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checkArtifact (artifact : Ixon.Env) (roots : Array Address) : IO Unit := do
  IO.ofExcept (Ix.Resource.typeCheck artifact)
  let input ← IO.ofExcept ((Ix.RoleBinding.Artifact.prepareRecords artifact Ix.Resource.typingLimits).mapError toString)
  let (logical, count) ← if input.hasTier then do
      -- Selected source closures retain their original _unsafe_rec companions.
      -- Keep the logical-only refusal and check every record through the tier.
      require (!(Ix.RoleBinding.Artifact.check artifact Ix.Resource.typingLimits).isOk)
        "logical-only entry accepted a partial record"
      let receipt ← IO.ofExcept ((Ix.RoleBinding.Artifact.checkTiered artifact Ix.Resource.typingLimits).mapError toString)
      require (!receipt.tier.isEmpty) "tiered input lost its typed declarations"
      pure (receipt.logical, receipt.prepared.records.length)
    else do
      let receipt ← IO.ofExcept ((Ix.RoleBinding.Artifact.check artifact Ix.Resource.typingLimits).mapError toString)
      pure (receipt.target, receipt.prepared.records.length)
  require (count == artifact.consts.size && !logical.consts.isEmpty)
    "actual artifact checking did not cover every emitted record"
  let p := input.prepared
  let store := input.constants.foldl (fun out (a, c) => out.insert a c)
    ({} : Benchmarks.Kernel.CheckIxeStep.RecordStore)
  let setup := Benchmarks.Kernel.CheckIxeStep.setup store (artifact.blobs[·]?) p.table p.pre p.hints.lookup
  for address in roots do
    let key ← IO.ofExcept ((setup.cx.keyAt address).mapError reprStr)
    require (logical.find? key).isSome "a requested safe root was not installed in the logical environment"

private def check : IO Bool := IO.FS.withTempDir fun dir => do
  let executable ← IO.FS.realPath ".lake/build/bin/ix"
  for fixture in ["RoleCompileProof", "RoleCompileStructural"] do
    let path := dir / s!"{fixture}.ixe"
    let source := s!"Tests/Fixtures/{fixture}.lean"
    let result ← IO.Process.output {
      cmd := executable.toString
      args := #["compile-lean", source, "--local", "--workers", "4", "--rust-check", "--out", path.toString]
      env := #[("LD_LIBRARY_PATH", none)]
    }
    require (result.exitCode == 0) s!"actual artifact compilation failed:\n{result.stdout}\n{result.stderr}"
    require (result.stdout.contains "ALIGNED:") "the actual Rust/Lean artifact comparison did not run"
    let bytes ← IO.FS.readBinFile path
    let artifact ← IO.ofExcept (Ixon.deEnv bytes)
    require (bytes[0]? == some 0xE6 && artifact.roleBinding.isSome) "production output has no v6 binding"
    require ((← Ix.Cli.publishedEnvelopeVersion true path) == some 6) "published envelope report lost v6"
    let names := if fixture == "RoleCompileProof" then #[`artifactQuotient] else #[`artifactIncrement, `artifactLabel]
    let roots ← names.mapM fun name => do
      let some named := artifact.named[Ix.Name.fromLeanName name]?
        | throw (IO.userError s!"original requested name disappeared: {name}")
      pure named.addr
    checkArtifact artifact roots
    let anonymous ← IO.ofExcept (Ixon.deEnvAnon bytes)
    checkArtifact anonymous roots
    let some raw := artifact.roleBinding | throw (IO.userError "missing emitted binding")
    let table ← IO.ofExcept ((Ix.Kernel.Admission.admitBinding Address.admissionHash
      ⟨raw.address, raw.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e))
    if fixture == "RoleCompileProof" then
      let entries := ((table.evidence.find? (·.1 == .natDiv)).map (·.2)).getD #[]
      require (entries.size == 3 && entries.all (fun | .proof _ => true | _ => false))
        "Nat.div output did not carry its three actual proof records"
      require (artifact.named.contains (Ix.Name.fromLeanName `Nat.div.go._unsafe_rec))
        "the original partial companion was removed to make logical-only checking pass"
      for anon in [false, true] do
        let rustPath := dir / (if anon then "rust-anon.ixe" else "rust-named.ixe")
        let args := #["compile", source, "--local", "--no-build", "--out", rustPath.toString]
        let result ← IO.Process.output {
          cmd := executable.toString
          args := if anon then args.push "--anon" else args
        }
        require (result.exitCode == 0) s!"Rust production artifact failed:\n{result.stdout}\n{result.stderr}"
        let rustBytes ← IO.FS.readBinFile rustPath
        let rustArtifact ← IO.ofExcept (Ixon.deEnv rustBytes)
        checkArtifact rustArtifact roots
        if anon then
          -- The wire grammar always carries the anonymous name at index zero.
          let onlyAnonymous := rustArtifact.names.size == 1 && rustArtifact.names.toList.all
            (fun (_, name) => match name with | .anonymous _ => true | _ => false)
          require (rustArtifact.named.isEmpty && onlyAnonymous && rustArtifact.comms.isEmpty &&
            rustArtifact.originals.isEmpty && rustArtifact.originalHintOverrides.isEmpty)
            "strict anonymous publication retained named metadata or original data"
        else
          require (rustBytes == bytes)
            s!"Rust named publication differs from Lean: {rustBytes.size} versus {bytes.size} bytes"
    IO.println s!"artifact compilation: {fixture}, {artifact.consts.size} records, {bytes.size} bytes, logical roots checked, all records covered and bytes aligned"
  let empty ← Lean.mkEmptyEnvironment
  require (!(Ix.RoleBinding.Compile.supportInput empty {}).isOk)
    "missing actual prelude source was silently replaced"
  let refused ← try
    let _ ← Ix.RoleBinding.Compile.finalize (fun _ _ => pure {}) empty
      (Ix.Compile.CompileInput.plain []) {} Ix.Resource.typingLimits
    pure false
  catch _ => pure true
  require refused "missing source unexpectedly finalized"
  return true

public def suite : List LSpec.TestSeq := [
  .individualIO "production artifact bindings: source certificates, both compilers and certified checking" none (do
    let ok ← check
    return (ok, 0, 0, none)) .done
]

end Tests.Ix.RoleCompile
