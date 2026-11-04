import Ix.FormalCompiler
import AiurTests.U8
import Aiur.Library.Blake3.Goldilocks
import Aiur.SourceBundle

/-!
Differential checks and measurements of the direct compiler handoff.

`formal-image-tests fixture` compiles a small Goldilocks program (the byte
library client) twice: through the independent JSON encoders
(`Execution.Export.toJson`, `functionJsonOf`, `chipJson`, `groupJson`) and
through the runtime image handed to the prover. The prover must hold the
same bytecode, plans, circuits and groups as the JSON reference, and its
binary round trip must agree as well.

`formal-image-tests <ixvm|verifier|aggregation> [reference.json]` compiles
a certified program with the linked compiler, compares it with a JSON
artifact the standalone exporter wrote for the same source when one is
given, persists and reloads it, and reports each phase's wall time and the
peak resident set.
-/

open Lean Aiur Ix

private def now : IO Nat := IO.monoNanosNow

private def ms (start stop : Nat) : String := s!"{(stop - start) / 1000000} ms"

/-- Peak resident set (`VmHWM`) in MiB. -/
private def peak : IO String := do
  let status ← IO.FS.readFile "/proc/self/status"
  let line := (status.splitOn "\n").find? (·.startsWith "VmHWM:") |>.getD "VmHWM: ?"
  return (line.drop 6).trimAscii.toString

private def report (label : String) (start stop : Nat) : IO Unit := do
  IO.println s!"{label}: {ms start stop}, peak RSS {← peak}"

private def check (label : String) (difference : String) : IO Unit := do
  unless difference.isEmpty do throw (IO.userError s!"{label}: {difference}")
  IO.println s!"{label}: JSON reference, direct image and binary round trip agree"

/-- The JSON artifact as the exporters wrote it before the image existed. -/
private def referenceJson {source : Modules.Program F} [Field F] [DecidableEq F]
    (prepared : Modules.Prepared source) (exported : Execution.Export F) (modulus : Nat)
    (encode : F → Nat) : Except String Json := do
  let program ← exported.toJson modulus encode
  let specialized ← Generic.specialize prepared.environment.source prepared.entries
  let inlined ← Inlining.prepare specialized.program specialized.inlineNames prepared.entries
  let artifact ← Optimized.compile inlined.program prepared.entries {}
  let physical ← Optimized.Physical.prepare artifact
  let functions ← ((inlined.program.functions.zip artifact.layouts).zip
      exported.bytecode.functions).mapM fun ((f, layout), code) =>
    Trace.functionJson encode inlined.program artifact.config f layout
      (physical.representative f.name) code (artifact.entries.contains f.name)
  let chips ← physical.system.chips.mapM (Trace.chipJson encode)
  let trace := Json.mkObj [("version", toJson (2 : Nat)), ("modulus", toJson modulus),
    ("functions", toJson functions), ("chips", toJson chips), ("groups", Json.arr #[])]
  return Json.mkObj [("program", program), ("trace", trace)]

def fixture : IO Unit := do
  let F := Library.U32.Goldilocks.F
  let modulus := Library.U32.Goldilocks.modulus
  let source := Library.Blake3.Goldilocks.program.append (AiurU8Tests.client.toField F)
  let prepared ← IO.ofExcept (Modules.prepare source AiurU8Tests.entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let reference ← IO.ofExcept (referenceJson prepared exported modulus ZMod.val)
  let image ← Trace.modulesImage prepared exported modulus ZMod.val
  let registry ← FormalProver.Registry.new
  let program ← FormalCompiler.registryOfImage registry (ByteArray.mk (Array.replicate 32 7)) image
  IO.FS.withTempDir fun dir => do
    let path := dir / "reference.json"
    IO.FS.writeFile path reference.compress
    check "fixture" (← program.compare path.toString)
    let fromJson ← registry.loadJson path.toString
    unless (← fromJson.identity) == (← program.identity) do
      throw (IO.userError "fixture: the JSON and image programs have different identities")
    let binary := dir / "fixture.aiur"
    program.save binary.toString "fixture" "test" (ByteArray.mk (Array.replicate 32 0))
    let reloaded ← (← FormalProver.Registry.new).loadBinary binary.toString
    unless (← reloaded.identity) == (← program.identity) do
      throw (IO.userError "fixture: the reloaded binary has another identity")
    let key ← (← registry.system program {}).key
    let keyJson ← (← (← FormalProver.Registry.new).system fromJson {}).key
    unless key == keyJson do throw (IO.userError "fixture: verifying keys differ")
    IO.println "fixture: identities and verifying keys agree"

def certified (target : FormalProver.Target) (name sourcePath : String)
    (reference : Option String) : IO Unit := do
  let text ← Aiur.SourceBundle.read sourcePath
  let t0 ← now
  let env ← FormalCompiler.frontend "."
  let t1 ← now
  report s!"{name}: frontend import" t0 t1
  let image ← FormalCompiler.image env target text
  let t2 ← now
  report s!"{name}: cold compilation to the typed image" t1 t2
  let registry ← FormalProver.Registry.new
  let program ← FormalCompiler.registryOfImage registry (ByteArray.mk (Array.replicate 32 1)) image
  let t3 ← now
  report s!"{name}: FFI transfer, program check and trace plan" t2 t3
  IO.FS.withTempDir fun dir => do
    let binary := dir / s!"{name}.aiur"
    program.save binary.toString name FormalCompiler.identity (ByteArray.mk (Array.replicate 32 0))
    let t4 ← now
    report s!"{name}: binary persistence ({(← binary.metadata).byteSize} bytes)" t3 t4
    let other ← FormalProver.Registry.new
    let reloaded ← other.loadBinary binary.toString
    let t5 ← now
    report s!"{name}: binary load, program check and trace plan" t4 t5
    unless (← reloaded.identity) == (← program.identity) do
      throw (IO.userError s!"{name}: the reloaded binary has another identity")
    let s0 ← now
    let system ← registry.system program {}
    let s1 ← now
    report s!"{name}: system preparation (verifying key)" s0 s1
    let recursive := target != .ixvm
    let _ ← system.identity recursive
    let r0 ← now
    for _ in [0:100] do
      let _ ← registry.system program {}
      let _ ← system.identity recursive
    let r1 ← now
    IO.println s!"{name}: 100 repeated system lookups and key queries: {ms r0 r1}"
    let (programs, plans, systems, provers) ← FormalProver.counters
    IO.println s!"{name}: constructed {programs} programs, {plans} plans, {systems} systems, \
      {provers} provers"
    if let some path := reference then
      let c0 ← now
      check name (← program.compare path)
      report s!"{name}: comparison with {path}" c0 (← now)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fixture"] => fixture
  | target :: rest =>
    let reference := rest.head?
    match target with
    | "ixvm" => certified .ixvm "ixvm" "IxVM/IxVM/Program.sources" reference
    | "verifier" => certified .verifier "verifier" "MultiStark/MultiStark/Program.sources" reference
    | "aggregation" =>
      certified .aggregation "aggregation" "MultiStark/MultiStark/Aggregate.sources" reference
    | _ => throw (IO.userError s!"unknown target {target}")
  | [] => throw (IO.userError "usage: formal-image-tests fixture | <ixvm|verifier|aggregation> [reference.json]")
  return 0
