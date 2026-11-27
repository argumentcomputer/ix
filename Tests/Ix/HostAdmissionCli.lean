import Tests.Ix.RoleGeneration
import Ix.HostAdmission
import Ix.Cli.CheckLeanCmd
import LSpec

namespace Tests.Ix.HostAdmissionCli

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- `artifact` with its `String.ofList` role moved to an alias of the bound
constant (a definition of the same type whose value is `String.ofList`), and the
published name `String.ofList` with it, as an artifact's author can (for example,
binding `String.ofList` to a definition returning the empty string allows a
statement false in Lean to be accepted under that binding). The alias computes
what Lean's does, so the kernel admits the artifact; the command line must still
refuse the moved literal support unless `--allow-custom-literal-support`. Returns
the artifact, the default record's address and the alias's. -/
private def movedLiteralSupport (artifact : Ixon.Env) (table : _root_.Ix.Kernel.RoleTable) :
    Except String (Ixon.Env × Address × Address) := do
  let some real := table.addressOf? .stringOfList | throw "fixture binds no String.ofList"
  let some lazy := artifact.consts[real]? | throw "fixture has no String.ofList record"
  let original ← lazy.get
  let .defn definition := original.info | throw "the String.ofList record is not a definition"
  let aliasRecord : Ixon.Constant := { original with
    refs := original.refs.push real
    info := .defn { definition with value := .ref original.refs.size.toUInt64 #[] } }
  let aliasAddress := Address.admissionHash (Ixon.serConstant aliasRecord)
  let bound := table.bound.toList.map fun (r, a) =>
    if r == _root_.Ix.Kernel.Role.stringOfList then (r, aliasAddress) else (r, a)
  let moved := _root_.Ix.Kernel.RoleTable.ofEntries table.version bound table.evidence.toList
  moved.check
  let bytes := moved.toBytes
  let named := artifact.named.toList.map fun (n, entry) =>
    if entry.addr == real then (n, { entry with addr := aliasAddress }) else (n, entry)
  return ({ artifact with
    consts := artifact.consts.insert aliasAddress (Ixon.LazyConstant.ofConstant aliasRecord)
    named := Std.HashMap.ofList named
    roleBinding := some ⟨Address.admissionHash bytes, bytes⟩ }, real, aliasAddress)

/-- `artifact` with its `True` role moved to a fresh alias (an alias of `True`
so the kernel would otherwise accept the binding by type), testing that even
`--allow-custom-literal-support` refuses moved trust-anchor roles. -/
private def movedTrueRole (artifact : Ixon.Env) (table : _root_.Ix.Kernel.RoleTable) :
    Except String (Ixon.Env × Address × Address) := do
  let some real := table.addressOf? .true | throw "fixture binds no True"
  let aliasRecord : Ixon.Constant := {
    info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .ref 0 #[] }
    sharing := #[], refs := #[real], univs := #[.zero], binders := #[] }
  let aliasAddress := Address.admissionHash (Ixon.serConstant aliasRecord)
  let bound := table.bound.toList.map fun (r, a) =>
    if r == _root_.Ix.Kernel.Role.true then (r, aliasAddress) else (r, a)
  let moved := _root_.Ix.Kernel.RoleTable.ofEntries table.version bound table.evidence.toList
  moved.check
  let bytes := moved.toBytes
  let named := artifact.named.toList.map fun (n, entry) =>
    if entry.addr == real then (n, { entry with addr := aliasAddress }) else (n, entry)
  return ({ artifact with
    consts := artifact.consts.insert aliasAddress (Ixon.LazyConstant.ofConstant aliasRecord)
    named := Std.HashMap.ofList named
    roleBinding := some ⟨Address.admissionHash bytes, bytes⟩ }, real, aliasAddress)

/-- The command line's binding gate and the kernel's strict admission agree:
on the default role table neither refuses; on
the default table with one literal-support pinned role (`Role.literalSupportPinned`)
moved, both refuse without `--allow-custom-literal-support` (`RolePins.committed`)
and both allow under `--allow-custom-literal-support` (`RolePins.trustAnchors`);
on the default table with `True` or `True.intro` (`Role.trustAnchorsPinned`)
moved, BOTH refuse both without and WITH `--allow-custom-literal-support`.
Returns the number of tables checked. -/
private def gateAgreesWithKernel : IO Nat := do
  let pins := _root_.Ix.Cli.CheckLeanCmd.rolePins
  ensure (pins false == .committed && pins true == .trustAnchors)
    "--allow-custom-literal-support does not select RolePins.trustAnchors"
  let default ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTable
  let defaultAddress ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTableAddress
  let c ← IO.ofExcept (_root_.Ix.Cli.CheckLeanCmd.compareBinding (some defaultAddress) default)
  let gateDefault ← _root_.Ix.Cli.CheckLeanCmd.bindingGate c "[gate-agreement]" false
  ensure (gateDefault.isOk && (_root_.Ix.Kernel.Admission.admitPinnedRoles (pins false) default).isOk)
    "the default role table is refused"
  let mut count := 1
  for role in _root_.Ix.Kernel.Role.literalSupportPinned do
    let label := _root_.Ix.Cli.CheckLeanCmd.roleLabel role
    let fresh := Address.admissionHash s!"moved literal-support {label}".toUTF8
    ensure (default.addressOf? role).isSome s!"the default role table does not bind {label}"
    let moved := _root_.Ix.Kernel.RoleTable.ofEntries default.version
      (default.bound.toList.map fun (r, a) => if r == role then (r, fresh) else (r, a))
      default.evidence.toList
    IO.ofExcept moved.check
    let c ← IO.ofExcept
      (_root_.Ix.Cli.CheckLeanCmd.compareBinding (some (Address.admissionHash moved.toBytes)) moved)
    let gateRefusal ← _root_.Ix.Cli.CheckLeanCmd.bindingGate c "[gate-agreement]" false
    match gateRefusal, _root_.Ix.Kernel.Admission.admitPinnedRoles (pins false) moved with
    | .error e, .error _ =>
      ensure (e.message.contains s!"{label} bound to {fresh}" &&
          e.message.contains "--allow-custom-literal-support")
        s!"the refusal of a moved {label} does not name it and the flag: {e.message}"
    | .ok _, _ => throw (IO.userError s!"the command line admits a moved {label}")
    | _, .ok _ => throw (IO.userError s!"the kernel's committed pins admit a moved {label}")
    let gateAllowed ← _root_.Ix.Cli.CheckLeanCmd.bindingGate c "[gate-agreement]" true
    ensure (gateAllowed.isOk && (_root_.Ix.Kernel.Admission.admitPinnedRoles (pins true) moved).isOk)
      s!"--allow-custom-literal-support does not release a moved {label} in both"
    count := count + 1
  for role in _root_.Ix.Kernel.Role.trustAnchorsPinned do
    let label := _root_.Ix.Cli.CheckLeanCmd.roleLabel role
    let fresh := Address.admissionHash s!"moved trust-anchor {label}".toUTF8
    ensure (default.addressOf? role).isSome s!"the default role table does not bind {label}"
    let moved := _root_.Ix.Kernel.RoleTable.ofEntries default.version
      (default.bound.toList.map fun (r, a) => if r == role then (r, fresh) else (r, a))
      default.evidence.toList
    IO.ofExcept moved.check
    let c ← IO.ofExcept
      (_root_.Ix.Cli.CheckLeanCmd.compareBinding (some (Address.admissionHash moved.toBytes)) moved)
    for allow in [false, true] do
      let gateRefusal ← _root_.Ix.Cli.CheckLeanCmd.bindingGate c "[gate-agreement]" allow
      match gateRefusal, _root_.Ix.Kernel.Admission.admitPinnedRoles (pins allow) moved with
      | .error e, .error _ =>
        ensure (e.message.contains s!"{label} bound to {fresh}")
          s!"the refusal of a moved {label} (allow={allow}) does not name it: {e.message}"
      | .ok _, _ => throw (IO.userError s!"the command line admits a moved {label} (allow={allow})")
      | _, .ok _ => throw (IO.userError s!"the kernel admits a moved {label} (allow={allow})")
    count := count + 1
  return count

private def checks : IO Nat := do
  let agreeing ← gateAgreesWithKernel
  IO.println s!"binding gate and kernel pins agree on {agreeing} role tables"
  let (artifact, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let (movedArtifact, realOfList, aliasOfList) ← IO.ofExcept (movedLiteralSupport artifact generated.table)
  let (movedTrueArtifact, realTrue, aliasTrue) ← IO.ofExcept (movedTrueRole artifact generated.table)
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
    let moved := dir / "moved-literal-support.ixe"
    let movedTrue := dir / "moved-true.ixe"
    for (path, env) in [(logical, artifact), (tier, tierArtifact), (moved, movedArtifact),
        (movedTrue, movedTrueArtifact),
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
    -- The binding is printed and compared with the default role table; literal
    -- support moved off the default table's records is refused by both commands unless
    -- --allow-custom-literal-support, which prints a warning.
    let honest ← call #["check-lean", logical.toString] 0
      "literal support: every bound literal-support role is at the default table's record"
    ensure (honest.stdout.contains "[check-lean] role binding: ") "check-lean did not print the binding"
    let movedLine := s!"String.ofList bound to {aliasOfList}, not the default table's {realOfList}"
    for flags in [#[], #["--anon"]] do
      let out ← call (#["check-lean", moved.toString, "--host-out", unused.toString] ++ flags) 3
        "--allow-custom-literal-support"
      ensure (out.stdout.contains movedLine && !out.stdout.contains "accepted all")
        s!"moved literal support: refusal did not name the role, or the run went on\n{out.stdout}"
      ensure (!(← unused.pathExists)) "a refused binding persisted a host statement"
    let allowed ← call #["check-lean", moved.toString, "--allow-custom-literal-support",
      "--host-out", statement.toString] 0 "WARNING (--allow-custom-literal-support)"
    ensure (allowed.stdout.contains movedLine && allowed.stdout.contains "accepted all")
      s!"--allow-custom-literal-support did not report the role or the admission\n{allowed.stdout}"
    -- the flag runs under RolePins.trustAnchors: releases only the literal-support roles
    -- while keeping True and True.intro pinned to the default role table
    let released := "RolePins.trustAnchors"
    let truePinned := "True and True.intro remain pinned"
    ensure (allowed.stdout.contains released && allowed.stdout.contains truePinned)
      s!"--allow-custom-literal-support did not describe RolePins.trustAnchors\n{allowed.stdout}"
    -- Moved True is STILL refused (exit 3) even under --allow-custom-literal-support
    let movedTrueLine := s!"True bound to {aliasTrue}, not the default table's {realTrue}"
    for flags in [#[], #["--allow-custom-literal-support"]] do
      let refusedTrue ← call (#["check-lean", movedTrue.toString, "--host-out", unused.toString] ++ flags) 3
        "True and True.intro remain pinned"
      ensure (refusedTrue.stdout.contains movedTrueLine && !refusedTrue.stdout.contains "accepted all")
        s!"moved True was not refused with flags {flags}\n{refusedTrue.stdout}"
      ensure (!(← unused.pathExists)) "a refused moved-True binding persisted a host statement"
    let movedAddress := Address.admissionHash (← IO.FS.readBinFile statement)
    let replay := #["verify-host", toString movedAddress, moved.toString, "--statement-file", statement.toString]
    let refusedReplay ← call replay 3 "--allow-custom-literal-support"
    ensure (refusedReplay.stdout.contains movedLine && !refusedReplay.stdout.contains "replayed")
      s!"verify-host accepted moved literal support by default\n{refusedReplay.stdout}"
    let allowedReplay ← call (replay.push "--allow-custom-literal-support") 0
      "WARNING (--allow-custom-literal-support)"
    ensure (allowedReplay.stdout.contains released && allowedReplay.stdout.contains truePinned &&
        allowedReplay.stdout.contains "replayed")
      s!"verify-host under the flag did not describe RolePins.trustAnchors\n{allowedReplay.stdout}"
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
