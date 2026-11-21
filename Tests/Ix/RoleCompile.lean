module

public import Ix.RoleBinding.Compile
public import Ix.RoleBinding.ArtifactTiered
public import Ix.Cli.CompileCmd
public import LSpec

/-!
  Artifact role-binding compilation tests.
-/

namespace Tests.Ix.RoleCompile

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checkArtifact (artifact : Ixon.Env) (roots : Array Address) : IO Unit := do
  IO.ofExcept (Ix.Typing.typeCheck artifact)
  let input ← IO.ofExcept ((Ix.RoleBinding.Artifact.prepareRecords artifact Ix.Typing.typingLimits).mapError toString)
  let (logical, count) ← if input.hasTier then do
      -- Selected source closures retain their original _unsafe_rec companions.
      -- Keep the logical-only refusal and check every record through the tier.
      require (!(Ix.RoleBinding.Artifact.check artifact Ix.Typing.typingLimits).isOk)
        "logical-only entry accepted a partial record"
      let receipt ← IO.ofExcept ((Ix.RoleBinding.Artifact.checkTiered artifact Ix.Typing.typingLimits).mapError toString)
      require (!receipt.tier.isEmpty) "tiered input lost its typed declarations"
      pure (receipt.logical, receipt.prepared.records.length)
    else do
      let receipt ← IO.ofExcept ((Ix.RoleBinding.Artifact.check artifact Ix.Typing.typingLimits).mapError toString)
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
      args := #["compile-lean", source, "--local", "--workers", "4", "--out", path.toString]
      env := #[("LD_LIBRARY_PATH", none)]
    }
    require (result.exitCode == 0) s!"actual artifact compilation failed:\n{result.stdout}\n{result.stderr}"
    let bytes ← IO.FS.readBinFile path
    let artifact ← IO.ofExcept (Ixon.deEnv bytes)
    require (bytes[0]? == some 0xE5 && artifact.roleBinding.isSome) "production output has no v5 binding"
    require ((← Ix.Cli.publishedEnvelopeVersion true path) == some 5) "published envelope report lost v5"
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
        let outPath := dir / (if anon then "cert-anon.ixe" else "cert-named.ixe")
        let args := #["compile", source, "--local", "--no-build", "--out", outPath.toString]
        let result ← IO.Process.output {
          cmd := executable.toString
          args := if anon then args.push "--anon" else args
        }
        require (result.exitCode == 0) s!"production artifact failed:\n{result.stdout}\n{result.stderr}"
        let outBytes ← IO.FS.readBinFile outPath
        let outArtifact ← IO.ofExcept (Ixon.deEnv outBytes)
        checkArtifact outArtifact roots
        if anon then
          -- The wire grammar always carries the anonymous name at index zero.
          let onlyAnonymous := outArtifact.names.size == 1 && outArtifact.names.toList.all
            (fun (_, name) => match name with | .anonymous _ => true | _ => false)
          require (outArtifact.named.isEmpty && onlyAnonymous && outArtifact.comms.isEmpty)
            "strict anonymous publication retained named metadata"
        else
          require (outBytes == bytes)
            s!"named publication differs from compile-lean: {outBytes.size} versus {bytes.size} bytes"
    IO.println s!"artifact compilation: {fixture}, {artifact.consts.size} records, {bytes.size} bytes, logical roots checked, all records covered and bytes aligned"
  let empty ← Lean.mkEmptyEnvironment
  require (!(Ix.RoleBinding.Compile.supportInput empty {}).isOk)
    "missing actual prelude source was silently replaced"
  let refused ← try
    let _ ← Ix.RoleBinding.Compile.finalize (fun _ _ => pure {}) empty (pure empty)
      (Ix.Compile.CompileInput.plain []) {} Ix.Typing.typingLimits
    pure false
  catch _ => pure true
  require refused "missing source unexpectedly finalized"
  -- Support may not change a reducibility hint the original stores, and the finalized
  -- artifact keeps the original's hints.
  let a := Address.blake3 (ByteArray.mk #[1])
  let hinted (h : Lean.ReducibilityHints) : Ixon.Env := { anonHints := ({} : Std.HashMap _ _).insert a h }
  let original := hinted (.regular 1)
  require (!(Ix.RoleBinding.Compile.mergeSupport Ix.Typing.typingLimits original (hinted .opaque)).isOk)
    "a support hint that changes the original's hint was merged"
  match Ix.RoleBinding.Compile.mergeSupport Ix.Typing.typingLimits original (hinted (.regular 5)) with
  | .ok merged =>
    require (merged.anonHints[a]? == some (.regular 1)) "the original's hint was not kept"
  | .error e => throw (IO.userError s!"a support hint that keeps the original's was refused: {e}")
  require (Ix.RoleBinding.Compile.checkFinalized original original).isOk
    "an unchanged artifact failed the finalized-artifact check"
  require (!(Ix.RoleBinding.Compile.checkFinalized original (hinted .opaque)).isOk)
    "a changed hint passed the finalized-artifact check"
  return true

public def suite : List LSpec.TestSeq := [
  .individualIO "production artifact bindings: source certificates, both compilers and certified checking" none (do
    let ok ← check
    return (ok, 0, 0, none)) .done
]

end Tests.Ix.RoleCompile
