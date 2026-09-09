import Ix.Cli.CheckCmd

/-!
Prepare, but do not execute, a focused ixVM regression partition from an
ix-refine/0 report's failed singleton blocks. The full partition is preserved;
the normal native check path still validates the whole environment's coverage.
This is a diagnostic selection, not a certificate that skipped blocks pass.
-/
open Lean System

namespace Benchmarks.IxVM.FocusFailures

structure Target where
  sourceShard : Nat
  block : Address
  label : String
  reason : String
  deriving Inhabited

def failedTargets (report : Json) : Except String (Array Target) := do
  unless (← report.getObjValAs? String "schema") == "ix-refine/0" do
    throw "expected an ix-refine/0 report"
  let leaves ← report.getObjValAs? (Array Json) "leaves"
  let mut targets := #[]
  let mut seen : Std.HashSet Address := {}
  let mut leafIds : Std.HashSet Nat := {}
  for leaf in leaves do
    let id ← leaf.getObjValAs? Nat "id"
    if leafIds.contains id then throw s!"duplicate report leaf {id}"
    leafIds := leafIds.insert id
    if (← leaf.getObjValAs? String "status") != "failed" then continue
    let before := targets.size
    for part in ← leaf.getObjValAs? (Array Json) "parts" do
      if (← part.getObjValAs? String "status") != "failed" then continue
      let blocks ← part.getObjValAs? (Array String) "blocks"
      unless blocks.size == 1 do
        throw s!"leaf {id}: expected a failed singleton block, got {blocks.size}"
      let some block := Address.fromString blocks[0]! | throw "invalid block address"
      if seen.contains block then throw s!"duplicate failed block {block}"
      seen := seen.insert block
      let label ← part.getObjValAs? String "label"
      let reason ← part.getObjValAs? String "reason"
      targets := targets.push { sourceShard := id, block := block, label := label, reason := reason }
    if targets.size == before then throw s!"failed leaf {id} has no failed singleton parts"
  if targets.isEmpty then throw "report contains no failed singleton blocks"
  return targets

/-- Remainder first, then failed singletons in report order. No measured peak
is carried to a different partition or executor revision. -/
def refinements (shards : Array (Array Address)) (targets : Array Target) :
    Except String (Array Ix.Cli.CheckCmd.LeafRefinement) := do
  let mut grouped : Std.HashMap Nat (Array Address) := {}
  for target in targets do
    let some blocks := shards[target.sourceShard]? | throw "source shard is out of range"
    unless blocks.contains target.block do
      throw s!"failed block {target.block} does not belong to source shard {target.sourceShard}"
    let previous := grouped[target.sourceShard]?.getD #[]
    if previous.contains target.block then throw "duplicate selection"
    grouped := grouped.insert target.sourceShard (previous.push target.block)
  let mut result := #[]
  for id in (grouped.toArray.map (·.1)).qsort (· < ·) do
    let selected := grouped[id]!.toList
    let remainder := shards[id]!.filter (!selected.contains ·)
    let singletons := selected.toArray.map fun block => (#[block], 0)
    let parts := (if remainder.isEmpty then #[] else #[(remainder, 0)]) ++ singletons
    -- An already-singleton source leaf needs no refinement.
    if parts.size > 1 then result := result.push { shard := id, parts }
  return result

def selectedIds (shards : Array (Array Address)) (targets : Array Target) :
    Except String (Array Nat) := do
  let mut ids := #[]
  for target in targets do
    let owners := (shards.mapIdx fun id blocks => (id, blocks)).filter
      fun (_, blocks) => blocks.contains target.block
    unless owners.size == 1 && owners[0]!.2 == #[target.block] do
      throw s!"refined manifest does not uniquely isolate {target.block}"
    ids := ids.push owners[0]!.1
  return ids

def prepare (ixe source reportPath out : FilePath) : IO (Array Nat) := do
  let sidecar := FilePath.mk (out.toString ++ ".focus.json")
  if (← out.pathExists) || (← sidecar.pathExists) then
    throw <| IO.userError "output or focus sidecar already exists; choose a fresh path"
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile reportPath))
  let targets ← IO.ofExcept (failedTargets report)
  let bytes ← IO.FS.readBinFile source
  let provenance ← IO.ofExcept (report.getObjVal? "source")
  let expected ← IO.ofExcept (provenance.getObjValAs? String "blake3")
  unless toString (Address.blake3 bytes) == expected do
    throw <| IO.userError "source manifest digest does not match the failure report"
  let environment ← IO.ofExcept (report.getObjVal? "env")
  let expectedEnv ← IO.ofExcept (environment.getObjValAs? String "path")
  unless (← IO.FS.realPath ixe) == (← IO.FS.realPath expectedEnv) do
    throw <| IO.userError "environment path does not match the failure report"
  let expectedBytes ← IO.ofExcept (environment.getObjValAs? Nat "bytes")
  unless (← ixe.metadata).byteSize.toNat == expectedBytes do
    throw <| IO.userError "environment size does not match the failure report"
  let view ← IO.ofExcept (Ix.Cli.CheckCmd.parseIxesManifest bytes)
  let cuts ← IO.ofExcept (refinements view.shards targets)
  IO.println s!"[ixvm-focus] isolating {targets.size} failed blocks; retaining all {view.shards.size} source leaves"
  -- Zero-copy mmap and native static-profile/refinement logic. No Lean env
  -- decoding, checking of passed constants, or fabricated partial manifest.
  let handle ← IO.ofExcept (Aiur.EnvHandle.fromIxe ixe.toString)
  let _ ← Aiur.shardManifestRefine handle source.toString
    (Ix.Cli.CheckCmd.refinementsBlob cuts) ByteArray.empty out.toString
  let focusedBytes ← IO.FS.readBinFile out
  let focused ← IO.ofExcept (Ix.Cli.CheckCmd.parseIxesManifest focusedBytes)
  let ids ← IO.ofExcept (selectedIds focused.shards targets)
  let selections := (targets.zip ids).map fun (target, id) => Json.mkObj [
    ("id", toJson id), ("source_shard", toJson target.sourceShard),
    ("block", toJson (toString target.block)), ("previous_label", toJson target.label),
    ("previous_reason", toJson target.reason)]
  let selection := String.intercalate "," (ids.toList.map toString)
  IO.FS.writeFile sidecar <| (Json.mkObj [
    ("schema", toJson "ixvm-focus/0"), ("report", toJson reportPath.toString),
    ("source_blake3", toJson expected), ("env", environment),
    ("manifest", toJson out.toString),
    ("manifest_blake3", toJson (toString (Address.blake3 focusedBytes))),
    ("selection", toJson selection), ("targets", toJson selections),
    ("scope", toJson "Diagnostic execution targets only; no previously passed claim is certified or reused.")
  ]).pretty ++ "\n"
  IO.println s!"[ixvm-focus] prepared {focused.shards.size} leaves; execute only --shards {selection}"
  IO.println s!"[ixvm-focus] target provenance → {sidecar}"
  return ids

private def expect (p : Bool) (message : String) : IO Unit :=
  unless p do throw <| IO.userError message

private def fixtureManifest (blocks : Array Address) : ByteArray := Id.run do
  let mut bytes : ByteArray := ⟨#[0x49, 0x58, 0x45, 0x53, 0, 0, 0, 0] ++ Array.replicate 16 0⟩
  bytes := bytes ++ (1 : UInt32).toLEBytes ++ (0 : UInt32).toLEBytes
    ++ ⟨Array.replicate 25 0⟩ ++ blocks.size.toUInt32.toLEBytes
  for block in blocks do bytes := bytes ++ block.hash
  return bytes ++ (0 : UInt32).toLEBytes ++ ⟨#[0, 0]⟩

private def roundtripTest : IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    let ixe := dir / "env.ixe"
    let source := dir / "source.ixes"
    let reportPath := dir / "report.json"
    let out := dir / "focused.ixes"
    let mut env : Ixon.Env := {}
    let mut addresses := #[]
    for n in [:3] do
      let c : Ixon.Constant := ⟨.axio ⟨false, n.toUInt64, .sort 0⟩, #[], #[], #[.succ .zero]⟩
      let addr := Address.blake3 (Ixon.serConstant c)
      addresses := addresses.push addr
      env := env.storeConst addr c
    let envBytes ← IO.ofExcept (Ixon.serEnv env)
    let sourceBytes := fixtureManifest addresses
    IO.FS.writeBinFile ixe envBytes
    IO.FS.writeBinFile source sourceBytes
    let parts := (addresses.extract 1 3).map fun block => Json.mkObj [
      ("status", toJson "failed"), ("blocks", toJson #[toString block]),
      ("label", toJson "0.test"), ("reason", toJson "test memory limit")]
    let report := Json.mkObj [("schema", toJson "ix-refine/0"),
      ("env", Json.mkObj [("path", toJson ixe.toString), ("bytes", toJson envBytes.size)]),
      ("source", Json.mkObj [("blake3", toJson (toString (Address.blake3 sourceBytes)))]),
      ("leaves", toJson #[Json.mkObj [("id", toJson (0 : Nat)),
        ("status", toJson "failed"), ("parts", toJson parts)]])]
    IO.FS.writeFile reportPath report.compress
    let ids ← prepare ixe source reportPath out
    expect (ids == #[1, 2]) "native refinement returned wrong target ids"
    let focused ← IO.ofExcept (Ix.Cli.CheckCmd.parseIxesManifest (← IO.FS.readBinFile out))
    expect (focused.shards == addresses.map (#[·])) "refinement changed the full partition"
    expect (focused.aggregationTree.leaves.toList.mergeSort == [0, 1, 2])
      "refined aggregation tree lost or repeated a leaf"
    let vm ← IO.ofExcept IxVM.ixVM
    let compiled ← IO.ofExcept vm.compile
    let result ← IO.ofExcept (← compiled.bytecode.checkPartition
      (compiled.getFuncIdx `verify_claim |>.get!) ixe.toString out.toString
      1 false Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
      (dir / "execution.json").toString "test" "focus roundtrip" "none" (some ids))
    expect (result.constants == 2 && result.shards == 2 && result.failures == 0)
      "focused execution ran the wrong targets or failed"
    let audit ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "execution.json")))
    let leaves ← IO.ofExcept (audit.getObjValAs? (Array Json) "leaves")
    expect ((← IO.ofExcept (leaves[0]!.getObjValAs? String "status")) == "unchanged")
      "unselected constant was reported checked"
    let refused ← try let _ ← prepare ixe source reportPath out; pure false catch _ => pure true
    expect refused "existing output was overwritten"
  finally
    IO.FS.removeDirAll dir

def selfTest : IO Unit := do
  let a := Address.blake3 "a".toUTF8
  let b := Address.blake3 "b".toUTF8
  let c := Address.blake3 "c".toUTF8
  let target : Target := { sourceShard := 1, block := b, label := "1.0", reason := "limit" }
  let part := Json.mkObj [("status", toJson "failed"), ("blocks", toJson #[toString b]),
    ("label", toJson "1.0"), ("reason", toJson "limit")]
  let report := fun parts => Json.mkObj [("schema", toJson "ix-refine/0"),
    ("leaves", toJson #[Json.mkObj [("id", toJson (1 : Nat)),
      ("status", toJson "failed"), ("parts", toJson parts)]])]
  expect ((← IO.ofExcept (failedTargets (report #[part]))).size == 1) "report selection"
  expect (!(failedTargets (report #[part, part])).isOk) "duplicate failure accepted"
  expect (!(failedTargets (report (#[] : Array Json))).isOk) "empty failure accepted"
  let cuts ← IO.ofExcept (refinements #[#[a], #[b, c]] #[target])
  let some cut := cuts[0]? | throw <| IO.userError "missing refinement"
  expect (cuts.size == 1 && cut.shard == 1 &&
    cut.parts == #[(#[c], 0), (#[b], 0)]) "failed block not isolated"
  expect ((← IO.ofExcept (selectedIds #[#[a], #[c], #[b]] #[target])) == #[2])
    "selection confused original and refined ids"
  expect (!(selectedIds #[#[a], #[b, c]] #[target]).isOk) "non-singleton accepted"
  expect (!(selectedIds #[#[b], #[b]] #[target]).isOk) "duplicate ownership accepted"
  expect (!(refinements #[#[a], #[c]] #[target]).isOk) "wrong owner accepted"
  expect (!(refinements #[#[a]] #[target]).isOk) "out-of-range owner accepted"
  expect ((← IO.ofExcept (refinements #[#[a], #[b]] #[target])).isEmpty)
    "already singleton needlessly refined"
  roundtripTest
  IO.println "[ixvm-focus] selection and native refinement/execution tests passed"

end Benchmarks.IxVM.FocusFailures

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--self-test"] => Benchmarks.IxVM.FocusFailures.selfTest; return 0
    | [ixe, source, report, out] =>
      let _ ← Benchmarks.IxVM.FocusFailures.prepare ixe source report out
      return 0
    | _ =>
      IO.eprintln "usage: bench-ixvm-focus ENV.ixe SOURCE.ixes REPORT.json FOCUSED.ixes\n       bench-ixvm-focus --self-test"
      return 1
  catch e => IO.eprintln s!"[ixvm-focus] {e}"; return 1
