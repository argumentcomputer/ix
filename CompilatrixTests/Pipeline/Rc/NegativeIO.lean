import CompilatrixTests.Recheck.Rc.ReplayIO
import Compilatrix.X86.ELFRead
import CompilatrixTests.Pipeline.Rc.Support

/-! Actual-source failure and independent emitted-object corruption controls.
The production certificate executable runs in separate processes; no copy of
its acceptance predicate is used as the negative oracle. -/
set_option autoImplicit false
namespace CompilatrixTests.Pipeline.Rc.NegativeIO
open Compilatrix Lean System
open CompilatrixTests.Recheck.Rc

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

def process (logs : FilePath) (label : String) (reader : FilePath)
    (phase : String) (bundle : FilePath) (expectedExit : UInt32)
    (expectedError : Option String := none) : IO Unit := do
  let results := logs / label
  IO.FS.createDirAll results
  let args := #["--kill-after=5", "120", reader.toString, "replay", phase,
    bundle.toString, results.toString]
  let started ← IO.monoMsNow
  let output ← IO.Process.output { cmd := "timeout", args }
  let elapsed := (← IO.monoMsNow) - started
  IO.FS.writeFile (logs / (label ++ ".stdout")) output.stdout
  IO.FS.writeFile (logs / (label ++ ".stderr")) output.stderr
  IO.FS.writeFile (logs / (label ++ ".json")) ((Json.mkObj [
    ("command", toJson ("timeout" : String)), ("args", toJson args),
    ("expected_exit", toJson expectedExit.toNat), ("exit", toJson output.exitCode.toNat),
    ("elapsed_ms", toJson elapsed)]).pretty ++ "\n")
  check (label ++ ": wrong exit boundary (timeout/signal is not rejection)")
    (output.exitCode == expectedExit)
  if let some message := expectedError then
    check (label ++ ": wrong rejection diagnostic") ((output.stderr.splitOn message).length > 1)
    check (label ++ ": reader advanced beyond first-root admission") output.stdout.isEmpty

def hashBundle (bundle : FilePath) : IO Unit := do
  let hashes ← IO.Process.output { cmd := "sha256sum", args := ReplayIO.files bundle }
  check "bundle hashing failed" (hashes.exitCode == 0)
  IO.FS.writeFile (bundle / "bundle.sha256") hashes.stdout

def copyBundle (original copy : FilePath) : IO Unit := do
  check "refusing to overwrite negative bundle" (!(← copy.pathExists))
  IO.FS.createDirAll copy
  for root in Fixtures.roots do
    for suffix in [".rc.json", ".producer.o"] do
      IO.FS.writeBinFile (copy / (root ++ suffix)) (← IO.FS.readBinFile (original / (root ++ suffix)))
  hashBundle copy

/-- Mutate an actual instruction byte while retaining a structurally readable
ELF. The source and certificate are unchanged. The mutated object is never
linked or executed: the production reader must refuse it first. -/
def corruptText (bundle : FilePath) : IO Unit := do
  let path := bundle / "reverseList.producer.o"
  let original ← IO.FS.readBinFile path
  let some view := X86.ELFRead.parse original | throw (IO.userError "positive ELF parse failed")
  let some text := view.sections.find? (fun elfSection => elfSection.name == ".text".toUTF8) |
    throw (IO.userError "positive ELF has no text section")
  check "positive text section is empty" (text.header.size > 0)
  let position := text.header.offset
  check "text byte outside object" (position < original.size)
  let changed := original.set! position (original[position]! ^^^ 1)
  let some after := X86.ELFRead.parse changed | throw (IO.userError "text mutation damaged ELF structure")
  check "text mutation had no effect" (after.text != view.text && changed.size == original.size)
  IO.FS.writeBinFile path changed

def corruption (logs : FilePath) (reader : FilePath) : IO FilePath := do
  let bundle := logs / "positive-bundle"
  check "refusing to overwrite positive bundle" (!(← bundle.pathExists))
  IO.FS.createDirAll bundle
  process logs "positive-write" reader "write" bundle 0
  process logs "positive-read" reader "read" bundle 0
  let stale := logs / "object-stale-hash"
  copyBundle bundle stale
  corruptText stale
  process logs "reject-object-stale-hash" reader "read" stale 1
    (some "RC source/certificate/object bundle changed")
  let rehashed := logs / "object-rehashed"
  copyBundle bundle rehashed
  corruptText rehashed
  hashBundle rehashed
  check "certificate changed during object-only corruption"
    ((← IO.FS.readBinFile (bundle / "reverseList.rc.json")) ==
      (← IO.FS.readBinFile (rehashed / "reverseList.rc.json")))
  process logs "reject-object-rehashed" reader "read" rehashed 1
    (some "reverseList: fresh validated ELF differs byte-for-byte from producer ELF")
  let guarded ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (bundle / "bundle.sha256").toString] }
  check "positive source/certificate/object bundle changed" (guarded.exitCode == 0)
  pure bundle

def tinyRegions (bundle logs : FilePath) : IO Unit := do
  let mut report : Array Json := #[]
  for root in Fixtures.roots do
    let input ← Fixtures.source root
    let cert ← IO.ofExcept (Recheck.RcReplay.Cert.ofText
      (← IO.FS.readFile (bundle / (root ++ ".rc.json"))))
    let artifact ← IO.ofExcept ((Recheck.RcReplay.run (ReplayIO.config root) input.program cert).mapError (·.message))
    check "tiny-region replay ELF differs from persisted producer artifact"
      (artifact.backend.object == (← IO.FS.readBinFile (bundle / (root ++ ".producer.o"))))
    let some entry := artifact.roots.head? | throw (IO.userError "no actual root")
    let some (sig, ty) := entry.ty | throw (IO.userError "no complete root signature")
    let executable ← CompilatrixTests.Rt.Native.link { work := logs }
      ("tiny-" ++ root) artifact.backend.object entry.symbol
    -- 4096 is an admitted region, with too little object area for 256 cells.
    -- The successful neighbor uses exactly the same code and arguments.
    for (label, bytes, n, wantStatus, wantInit) in
        [("small-success", 4096, 8, 0, false),
         ("root-exhaustion", 4096, 256, 1, false),
         ("large-success", 32768, 256, 0, false),
         ("initializer-refusal", 4088, 8, 1, true)] do
      let rows ← CompilatrixTests.Pipeline.Rc.runNative logs (root ++ "-" ++ label) executable
        { region := bytes, stack := 1048576, ty := some (sig, ty), dump := true } [[n, 7]]
      let [row] := rows | throw (IO.userError "native driver result arity changed")
      check (root ++ "/" ++ label ++ ": wrong status/init/ABI boundary")
        (row.status == UInt64.ofNat wantStatus && row.init == wantInit && row.ok)
      let want := ReplayIO.expected root n 7
      if wantStatus == 0 then
        check (root ++ "/" ++ label ++ ": complete independent tree differs")
          (row.obs == some (Rt.renderObs want) && row.readback bytes sig ty == some want)
      else
        check (root ++ "/" ++ label ++ ": failure returned a successful observation") row.obs.isNone
      report := report.push (Json.mkObj [
        ("root", toJson root), ("case", toJson label), ("region_bytes", toJson bytes),
        ("n", toJson n), ("seed", toJson (7 : Nat)), ("status", toJson row.status.toNat),
        ("initializer_failed", toJson row.init), ("abi_ok", toJson row.ok),
        ("complete_observation", toJson row.obs)])
    let hashes ← IO.Process.output {
      cmd := "sha256sum", args := #[executable.toString, (logs / ("tiny-" ++ root ++ ".o")).toString] }
    check "native negative artifact hashing failed" (hashes.exitCode == 0)
    IO.FS.writeFile (logs / (root ++ ".artifacts.sha256")) hashes.stdout
  IO.FS.writeFile (logs / "tiny-regions.json") ((toJson report).pretty ++ "\n")

def run (logs : FilePath)
    (reader : FilePath := ".lake/build/bin/tests-rc-certificate") : IO Unit := do
  Fixtures.verify
  IO.FS.createDirAll logs
  let bundle ← corruption logs reader
  tinyRegions bundle logs
  Fixtures.verify
  IO.FS.writeFile (logs / "complete.txt")
    "PASS: fresh positive source/certificate/ELF neighbor; object-only text corruption refused at stale-hash and rehashed-byte-identity boundaries; three actual-source root heap exhaustions distinct from initializer refusal; six complete-tree successful neighbors.\n"

end CompilatrixTests.Pipeline.Rc.NegativeIO
