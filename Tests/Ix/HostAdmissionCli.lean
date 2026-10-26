import Tests.Ix.RoleGeneration
import Ix.HostAdmission
import LSpec

namespace Tests.Ix.HostAdmissionCli

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checks : IO Nat := do
  let (artifact, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some falseAddress := generated.table.addressOf? .false | throw (IO.userError "fixture has no False")
  let unsafeAxiom : Ixon.Constant := {
    info := .axio ⟨true, 0, .ref 0 #[]⟩, sharing := #[], refs := #[falseAddress], univs := #[] }
  let unsafeAddress := Address.admissionHash (Ixon.serConstant unsafeAxiom)
  let tierArtifact := { artifact with consts := artifact.consts.insert unsafeAddress (Ixon.LazyConstant.ofConstant unsafeAxiom) }
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  try
    let logical := dir / "logical.ixe"
    let tier := dir / "tier.ixe"
    let unbound := dir / "unbound.ixe"
    let thin := dir / "thin.ixe"
    let statement := dir / "statement.ixhc"
    let tampered := dir / "tampered.ixhc"
    let unused := dir / "must-not-exist.ixhc"
    for (path, env) in [(logical, artifact), (tier, tierArtifact),
        (unbound, { artifact with roleBinding := none }),
        (thin, { artifact with assumptions := ({} : Std.HashSet Address).insert falseAddress })] do
      IO.FS.writeBinFile path (← IO.ofExcept (Ixon.serEnv env))
    let vars := #[("IX_KERNEL_CHECK_PROGRESS_MS", some "0"), ("IX_KERNEL_CHECK_SLOW_MS", some "0")]
    let calls ← IO.mkRef 0
    let call := fun (args : Array String) (code : UInt32) (text : String) => do
      calls.modify (· + 1)
      let output ← IO.Process.output { cmd := ix.toString, args, env := vars }
      ensure (output.exitCode == code && (output.stdout ++ output.stderr).contains text)
        s!"host CLI: expected {code}/{text}, got {output.exitCode}\n{output.stdout}\n{output.stderr}"
      return output
    for (path, flags, accepted) in [(logical, #[], "logical admission replayed"),
        (tier, #["--anon"], "tier constants typed only")] do
      let output ← call (#["check-lean", path.toString, "--host-out", statement.toString] ++ flags)
        0 "host admission statement:"
      let raw ← IO.FS.readBinFile statement
      let address := Address.admissionHash raw
      ensure (output.stdout.contains (toString address)) "reported host address differs from persisted bytes"
      let parsed ← IO.ofExcept (_root_.Ix.HostAdmission.Statement.decode raw)
      ensure (match parsed.kind with | .logical => path == logical | .tiered .. => path == tier)
        "whole CLI statement kind disagrees with actual input"
      let verify := #["verify-host", toString address, path.toString, "--statement-file", statement.toString]
      let _ ← call verify 0 accepted
      let _ ← call (verify.set! 1 (toString (Address.admissionHash "wrong address".toUTF8)))
        3 "stored bytes do not match their address"
      -- Readdress the changed expected statement so replay/equality, rather
      -- than the storage hash guard, must reject it against the same artifact.
      let changed := { parsed with bindingHash := Address.admissionHash "different binding".toUTF8 }
      let changedRaw ← IO.ofExcept changed.bytes
      IO.FS.writeBinFile tampered changedRaw
      let _ ← call #["verify-host", toString (Address.admissionHash changedRaw), path.toString,
        "--statement-file", tampered.toString] 3 "commitments differ from actual admitted artifact"
      for invalid in [unbound, thin] do
        discard <| call (verify.set! 2 invalid.toString) 3 ""
      IO.FS.writeBinFile tampered (raw.set! 4 2)
      discard <| call #["verify-host", toString (Address.admissionHash (raw.set! 4 2)), path.toString,
        "--statement-file", tampered.toString] 3 "unsupported version"
    for flags in [#["--consts", "Nat.div"], #["--max", "1"]] do
      let _ ← call (#["check-lean", logical.toString, "--host-out", unused.toString] ++ flags)
        2 "requires a complete bound artifact check"
      ensure (!(← unused.pathExists)) "ineligible selection persisted a host statement"
    let _ ← call #["check-lean", thin.toString, "--host-out", unused.toString]
      3 "thin artifact assumptions"
    ensure (!(← unused.pathExists)) "thin refusal persisted a closed host statement"
    let _ ← call #["verify-host", "bad-address", logical.toString] 2 "64 hexadecimal characters"
    let _ ← call #["verify-host", toString falseAddress, logical.toString,
      "--statement-file", (dir / "missing").toString] 1 ""
    let count ← calls.get
    IO.println s!"host admission CLI: {count} process controls passed"
    return count
  finally
    IO.FS.removeDirAll dir

def suite : List LSpec.TestSeq := [
  .individualIO "host statement persistence, addressed replay and actual CLI refusals" none (do
    let count ← checks
    return (true, count, 0, none)) .done]

end Tests.Ix.HostAdmissionCli
