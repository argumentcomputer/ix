/-
  Per-library fidelity gates (ixc-catalog plan Phase 1 / Q1).

  "Can ix faithfully compile/decompile library X" is a per-library
  question, answered by the existing 8-phase `ix validate` pipeline
  (compile, aux-gen congruence, alpha-canonicity, decompile both ways,
  per-constant roundtrip, nested detection) over the library's
  `Benchmarks/Compile` driver — no cross-library packaging, no
  namespace work. These suites drive the real CLI in a subprocess and
  gate on the `--report` JSON, which keeps heavyweight closures
  (Mathlib!) out of the test binary's compile-time deps
  (`ValidateCmd.lean`'s constraint) and exercises exactly what a user
  runs.

  Ignored suites (`lake test -- --ignored fidelity-<lib>`): need
  `lake build ix` first; FLT/Mathlib legs are heavy and manual, with
  network + `lake exe cache get` on the first workspace build.
  `fidelity-initstd` is the cheap merge-queue leg.
-/
module

public import LSpec

public section

open LSpec

namespace Tests.Ix.CompileFidelity

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- Drive `ix validate <source> --report` in a subprocess and gate on
    the report: every phase row present, zero failures, `passed`. The
    report is read even when the process exits nonzero — the Rust core
    writes it on abort paths too, so the gate can name the phase that
    died instead of just the exit code. -/
private def fidelityLeg (source : String) :
    IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  let dir ← IO.FS.createTempDir
  try
    let reportPath := dir / "validate-report.json"
    let exe ← IO.FS.realPath ixExe
    let r ← IO.Process.output {
      cmd := exe.toString
      args := #["validate", source, "--report", reportPath.toString] }
    let content ← try IO.FS.readFile reportPath catch _ => pure ""
    if content.isEmpty then
      return (false, 0, 0, some s!"no report written (exit {r.exitCode}): \
{r.stderr.take 300} … {(r.stdout.takeEnd 300).toString}")
    let checks : Except String (Nat × Nat) := do
      let json ← Lean.Json.parse content
      let passed ← (← json.getObjVal? "passed").getBool?
      let totalFailures ← (← json.getObjVal? "totalFailures").getNat?
      let phases ← (← json.getObjVal? "phases").getArr?
      if phases.isEmpty then
        throw "report carries no phase rows"
      unless passed && totalFailures == 0 do
        let failing := phases.filterMap fun ph =>
          match ph.getObjVal? "name", ph.getObjVal? "fail" with
          | .ok (.str name), .ok fails =>
            match fails.getNat? with
            | .ok n => if n > 0 then some s!"{name} ({n})" else none
            | .error _ => none
          | _, _ => none
        throw s!"{totalFailures} validation failure(s): \
{String.intercalate ", " failing.toList}"
      let constants ← (← json.getObjVal? "constants").getNat?
      return (constants, phases.size)
    match checks with
    | .ok (constants, phaseCount) =>
      if r.exitCode != 0 then
        return (false, constants, phaseCount,
          some s!"report passed but ix validate exited {r.exitCode}")
      return (true, constants, phaseCount, none)
    | .error m => return (false, 0, 0, some m)
  finally
    IO.FS.removeDirAll dir

private def leg (lib source : String) : List TestSeq := [
  .individualIO
    s!"fidelity: {lib} validates clean (8-phase, subprocess, --report gate)"
    none (fidelityLeg source) .done ]

def initStdSuite : List TestSeq :=
  leg "InitStd" "Benchmarks/Compile/CompileInitStd.lean"

def fltSuite : List TestSeq :=
  leg "FLT" "Benchmarks/Compile/CompileFLT.lean"

def mathlibSuite : List TestSeq :=
  leg "Mathlib" "Benchmarks/Compile/CompileMathlib.lean"

end Tests.Ix.CompileFidelity
