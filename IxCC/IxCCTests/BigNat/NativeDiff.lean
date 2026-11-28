import IxCCTests.BigNat.NativeDiffCore
import IxCCTests.BigNat.WireTest

/-! # Pure-Lean 100k+ Native Arbitrary-Precision Differential Harness (`IxCCTests.BigNat.NativeDiff`)

Executable driver supporting both `NativeDiff` differential modes (`--self-test`, `--batch`,
`--exe-dir`, `--exe`, `--emit-vectors`) and Phase 4 Xeon wiring modes (`--wire`, `--boundary`,
`--diff [N]`, `--k5`, `--k5-test-only`, `--native-batch`, `--all`) via `IxCCTests.BigNat.WireTest`. -/

namespace IxCCTests.BigNat.NativeDiff

open IxCC.BigNat

/-- Mode 1: In-process self-test comparing `IxCC.BigNat` + `WF` against Lean 4 GMP. -/
def runSelfTest (cfg : Config) (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  for c in cases do
    let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
    let (got, wfOk) := c.op.evalBigNat cfg.boolAsNat c.a c.b
    if got == expected && wfOk then
      st := { st with checked := st.checked + 1 }
    else
      st ← reportMismatch st c expected got wfOk
      if cfg.failFast then return st
  let decSamples := boundaryVals ++ #[allOnesLimbs 32, allOnesLimbs 64, allOnesLimbs 128, allOnesLimbs 1000]
  for n in decSamples do
    let bn := ofNat n
    let dec := toDecimal bn
    let rt := ofDecimal dec
    let ok := dec == toString n && rt == some bn
    if ok then
      st := { st with checked := st.checked + 1 }
    else
      st ← reportMismatch st { tag := "decimal-rt", op := .add, a := n, b := 0 }
        (toString n) dec (rt == some bn)
      if cfg.failFast then return st
  pure st

/-- Mode 2: Stream chunks of `<op> <a> [b]\n` to a single compiled `ixcc` batch executable. -/
def runBatch (cfg : Config) (exe : String) (extraArgs : Array String)
    (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  let chunkSz := max 1 cfg.batchChunkSize
  let numChunks := (cases.size + chunkSz - 1) / chunkSz
  for ci in [:numChunks] do
    let start := ci * chunkSz
    let stop := min cases.size (start + chunkSz)
    let slice := cases.extract start stop
    let mut inputBuf := ""
    for c in slice do
      inputBuf := inputBuf ++ c.toRequestLine ++ "\n"
    let child ← IO.Process.spawn {
      cmd := exe
      args := extraArgs
      stdin := .piped
      stdout := .piped
      stderr := .piped
    }
    let (stdin, child) ← child.takeStdin
    let writeTask ← IO.asTask (prio := .dedicated) do
      stdin.putStr inputBuf
      stdin.flush
    let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let stdout ← child.stdout.readToEnd
    let _ ← IO.ofExcept writeTask.get
    let stderr ← IO.ofExcept errTask.get
    let exitCode ← child.wait
    if exitCode != 0 then
      throw (IO.userError s!"batch executable '{exe}' exited with code {exitCode}: {stderr}")
    let lines := (stdout.splitOn "\n").toArray.filter (fun l => !l.trimAscii.isEmpty)
    if lines.size != slice.size then
      throw (IO.userError s!"batch chunk {ci}: expected {slice.size} output lines, got {lines.size}")
    for j in [:slice.size] do
      let c := slice[j]!
      let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
      let got := lines[j]!.trimAscii.toString
      if got == expected then
        st := { st with checked := st.checked + 1 }
      else
        st ← reportMismatch st c expected got true
        if cfg.failFast then return st
  pure st

/-- Resolve the binary path for `op` under `--exe-dir` / `--exe`. -/
def resolveOpExe (exeDir : Option String) (overrides : Array (DiffOp × String)) (op : DiffOp) :
    Option String :=
  match overrides.find? (fun p => p.1 == op) with
  | some (_, path) => some path
  | none => exeDir.map fun dir => s!"{dir}/{op.name}"

/-- Mode 3: Invoke per-operation standalone compiled `ixcc --exe` binaries (`<exe> <a> [b]`). -/
def runExePerOp (cfg : Config) (exeDir : Option String) (overrides : Array (DiffOp × String))
    (cases : Array DiffCase) (addBackHits : Nat) : IO RunStats := do
  let mut st : RunStats := { addBackHits }
  let limit := min cases.size cfg.exeLimit
  for i in [:limit] do
    let c := cases[i]!
    match resolveOpExe exeDir overrides c.op with
    | none => pure ()
    | some exe =>
      let args := if c.op.isUnary then #[toString c.a] else #[toString c.a, toString c.b]
      let out ← IO.Process.output { cmd := exe, args }
      if out.exitCode != 0 then
        throw (IO.userError s!"exe '{exe}' exited {out.exitCode} on {c.tag}: {out.stderr}")
      let got := out.stdout.trimAscii.toString
      let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
      if got == expected then
        st := { st with checked := st.checked + 1 }
      else
        st ← reportMismatch st c expected got true
        if cfg.failFast then return st
  pure st

/-- Mode 4: Emit `<op> <a> <b> <expected>` lines to `outPath` for external/CI differential suites. -/
def runEmitVectors (cfg : Config) (outPath : String) (cases : Array DiffCase)
    (addBackHits : Nat) : IO RunStats := do
  let h ← IO.FS.Handle.mk outPath .write
  let mut count := 0
  for c in cases do
    let expected := c.op.evalGMP cfg.boolAsNat c.a c.b
    h.putStrLn s!"{c.op.name} {c.a} {c.b} {expected}"
    count := count + 1
  h.flush
  pure { checked := count, failures := 0, wfFailures := 0, addBackHits }

def runWithConfig (cfg : Config) : IO Unit := do
  let (cases, addBackHits) := buildAllCases cfg
  if cfg.filterOp.isNone && addBackHits < 10 then
    throw (IO.userError s!"Expected ≥ 10 Knuth Algorithm D add-back triggers, got {addBackHits}")
  let st ← match cfg.mode with
    | .selfTest => runSelfTest cfg cases addBackHits
    | .batch exe extra => runBatch cfg exe extra cases addBackHits
    | .exePerOp dir ovs => runExePerOp cfg dir ovs cases addBackHits
    | .emitVectors path => runEmitVectors cfg path cases addBackHits
  if st.failures != 0 then
    throw (IO.userError
      s!"NativeDiff FAILED: {st.failures} mismatches ({st.wfFailures} WF failures) out of {st.checked} checks")
  IO.println
    s!"NativeDiff PASS: {st.checked} checks, 0 failures ({st.addBackHits} Knuth D add-back triggers, 0..1000 limbs, Karatsuba thresholds 31..1000)"

private def isWireMode : List String → Bool
  | ["--wire"] | ["--boundary"] | ["--diff"] | ["--diff", _]
  | ["--k5"] | ["--k5-test-only"] | ["--native-batch"] | ["--all"] => true
  | _ => false

def main (args : List String) : IO Unit := do
  if isWireMode args then
    IxCCTests.BigNat.WireTest.runCli args
  else
    match parseArgs args with
    | .error msg =>
      IO.eprintln s!"NativeDiff usage error: {msg}"
      IO.eprintln "Usage: native-diff [--self-test | --batch <exe> [--arg <x>] | --exe-dir <dir> | --exe <op>=<path> | --emit-vectors <file>]"
      IO.eprintln "                   [--wire | --boundary | --diff [N] | --k5 | --k5-test-only | --native-batch | --all]"
      IO.eprintln "                   [--count <N>] [--seed <UInt64>] [--op <name>] [--bool-as-nat] [--exe-limit <N>] [--fail-fast]"
      IO.Process.exit 2
    | .ok cfg => runWithConfig cfg

end IxCCTests.BigNat.NativeDiff

def main (args : List String) : IO Unit := IxCCTests.BigNat.NativeDiff.main args
