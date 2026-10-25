module

public import Ix.RoleBinding.Compile
public import Ix.RoleBinding.Artifact
public import Ix.Cli.CompileCmd
public import LSpec

namespace Tests.Ix.RoleCompile

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

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
    let receipt ← IO.ofExcept ((Ix.RoleBinding.Artifact.check artifact Ix.Resource.typingLimits).mapError toString)
    require (receipt.prepared.records.length == artifact.consts.size && !receipt.target.consts.isEmpty)
      "actual artifact checking did not cover every emitted record"
    let anonymous ← IO.ofExcept (Ixon.deEnvAnon bytes)
    require (Ix.RoleBinding.Artifact.check anonymous Ix.Resource.typingLimits).isOk
      "anonymous loading lost certified support"
    let some raw := artifact.roleBinding | throw (IO.userError "missing emitted binding")
    let table ← IO.ofExcept ((Ix.Kernel.Admission.admitBinding Address.admissionHash
      ⟨raw.address, raw.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e))
    if fixture == "RoleCompileProof" then
      let entries := ((table.evidence.find? (·.1 == .natDiv)).map (·.2)).getD #[]
      require (entries.size == 3 && entries.all (fun | .proof _ => true | _ => false))
        "Nat.div output did not carry its three actual proof records"
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
        require (Ix.RoleBinding.Artifact.check rustArtifact Ix.Resource.typingLimits).isOk
          "Rust production output failed actual artifact checking"
        require (if anon then rustArtifact.named.isEmpty && rustArtifact.names.isEmpty
          else rustBytes == bytes) "Rust publication lost strict anonymity or complete byte parity"
    IO.println s!"artifact compilation: {fixture}, {artifact.consts.size} records, {bytes.size} bytes, certified and aligned"
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
