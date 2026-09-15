import Compilatrix.Tools.Check
import Compilatrix.Aiur.Wire.ComponentCheck

/-! Bounded file ingress and fresh-process agreement with frozen, handwritten
wire fixtures. Passing the component checker does not establish AIR or
execution correctness; the wire-corpus fixture tests representation only. -/

namespace Compilatrix.Tools.AiurWireCheck

open Lean System Check
open Compilatrix.Aiur.Wire
open Compilatrix.Ixon

def readBounded (path : FilePath) : IO ByteArray := do
  need ((← path.metadata).type == .file) s!"bytecode input is not a regular file: {path}"
  let handle ← IO.FS.Handle.mk path .read
  let limit := ({} : Limits).maxBytes
  let bytes ← handle.read (limit + 1).toUSize
  need (bytes.size ≤ limit) "Aiur bytecode input byte limit"
  need ((← handle.read 1).isEmpty) "Aiur bytecode input exceeds bounded read"
  return bytes

def parseRoot (value : String) : IO Address := do
  need (isHex 64 value) "expected root must be 64 lowercase hexadecimal digits"
  present (Address.ofBytes? (← checked (unhex value))) "invalid content root width"

def replay (input : FilePath) (expected : String) (output : Option FilePath) : IO Json := do
  let bytes ← readBounded input
  let root ← parseRoot expected
  let accepted ← checked (ingest {} {} bytes root)
  if let some output := output then IO.FS.writeBinFile output (preimage accepted.value)
  return Json.mkObj [
    ("format", toJson "aiur-bytecode/1"), ("revision", toJson revision),
    ("root", toJson root.toHex), ("bytes", toJson bytes.size),
    ("functions", toJson accepted.value.functions.size),
    ("memory_buckets", toJson accepted.value.memorySizes.size),
    ("circuits", toJson accepted.value.circuits.size),
    ("call_components", toJson accepted.value.callComponents.size),
    ("component_mode", toJson (if accepted.value.callComponents.isEmpty then "ranked-fallback" else "checked-static"))]

private def compareReport (actual expected : Json) : IO Unit := do
  for key in ["root", "bytes", "functions", "memory_buckets", "circuits", "call_components", "component_mode"] do
    need ((← field actual key) == (← field expected key)) s!"Aiur fixture report differs: {key}"

private def rejectedProcess (executable : String) (input : FilePath) (root : Address)
    (message : String) : IO Unit := do
  let result ← IO.Process.output {
    cmd := executable
    args := #["--bytecode", input.toString, "--expect-root", root.toHex] }
  need (result.exitCode != 0 && result.stderr.contains message)
    s!"Aiur corruption was accepted or rejected for the wrong reason: {message}\n{result.stdout}{result.stderr}"

def verifyFixtures (root : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let directory := root / "fixtures/aiur-bytecode"
  let index ← readJson (directory / "expected.json")
  need ((← strField index "format") == "aiur-bytecode/1" &&
    (← strField index "revision") == revision) "Aiur fixture format/revision differs"
  let rows ← arrField index "fixtures"
  let names ← rows.mapM (strField · "name")
  need (names == #["empty", "unit-counter", "ranked-mutual", "wire-corpus"])
    "Aiur fixture inventory differs"
  let executable ← IO.appPath
  let some bin := executable.parent | throw (IO.userError "missing executable directory")
  let generated := temporary / "generated"
  let _ ← Check.run (bin / "tests-aiur").toString #["--emit-wire", generated.toString]
  for row in rows do
    let name ← strField row "name"
    let expected ← readBounded (directory / (name ++ ".bin"))
    let actual ← readBounded (generated / (name ++ ".bin"))
    need (actual == expected) s!"Aiur fresh-process bytes differ: {name}"
    let output := temporary / (name ++ ".replayed.bin")
    let report ← Check.run executable.toString #["--bytecode", (generated / (name ++ ".bin")).toString,
      "--expect-root", ← strField row "root", "--output", output.toString]
    compareReport (← checked (Json.parse report)) row
    need ((← readBounded output) == expected) s!"Aiur re-encoded bytes differ: {name}"
  let counter ← readBounded (directory / "unit-counter.bin")
  let mutated := temporary / "mutated.bin"
  for (value, message) in [
      (counter.push 0, "trailing bytes"),
      (counter.extract 0 (counter.size - 1), "EOF"),
      (counter.set! 0 0, "framing"),
      (counter.set! 20 0, "framing"),
      (counter.set! (counter.size - 1) 2, "boolean")] do
    IO.FS.writeBinFile mutated value
    rejectedProcess executable.toString mutated (Address.blake3 value) message
  IO.FS.writeBinFile mutated counter
  rejectedProcess executable.toString mutated (Address.replicate 0) "root mismatch"
  let ranked ← readBounded (directory / "ranked-mutual.bin")
  let forged := (ranked.set! (ranked.size - 1) 0).set! (ranked.size - 3) 0
  IO.FS.writeBinFile mutated forged
  rejectedProcess executable.toString mutated (Address.blake3 forged) "invalid static call components"
  IO.println "aiur-wire-check-ok: 4 frozen fixtures, fresh-process encoding/replay, 7 corruption rejections"

end Compilatrix.Tools.AiurWireCheck
