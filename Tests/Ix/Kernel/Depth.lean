/-! # Reduction steps and record counts take no native stack (`lake test -- kernel-depth`)

The kernel's reduction loops (`whnfCoreLoopI`, `whnfLoopI`, `defeqLoopI`)
used to keep two to three native frames per step, and the recursions over
the number of records (the index build `mkFEnvGo`, the certified entry's
whole-unit check `unitsGo`, the host's record loop `checkLoopWith`) one or two
per record. Their executed forms are loops now (`docs/kernel.md`, "Native
stack"). Each case below runs in a process of its own (`kernel-depth-case`,
`Tests/Ix/Kernel/DepthCase.lean`) on a **2 MiB stack** (`LEAN_STACK_SIZE_KB=2048`, which the runtime applies to the
main thread, to dedicated threads and to the task pool's workers), through
the entry points that reach it; before the change each aborted with
"Stack overflow detected" at the size given:

* `delta` (records `D0 : Type := Prop`, `Dj : Type := D(j-1)`,
  `X : D_n := ∀ p : Prop, p`: one conversion unfolds `n` one-line
  definitions) at 90,000, accepted by the certified entry
  (`Ixon.Authenticated.checkBytes`, what `ix verify-host` runs) and by the
  tiered entry (`checkBytesTiered`, what IxCC's front end runs) (aborted at
  13,000 on 2 MiB, 52,000 on 8 MiB); at 150,000, past the conversion loop's
  fuel (100,000 steps), declined with the fuel named, not aborted;
* `iota` (`X : Prop := Nat.rec (fun _ => Prop) P (fun n ih => ih) n`, a
  literal, and `T : X := fun p h => h`: one head normalisation runs `n` ι
  and `n` β steps) at 100,000, accepted by the certified entry (aborted:
  `whnfCoreLoopI` took the same stack per step);
* `wide` (`n` one-line records, no unfolding) at 200,000, accepted by the
  certified entry (aborted at 28,000 on 2 MiB, 112,000 on 8 MiB: `unitsGo`);
* `step` (`n` one-line declarations and a failing last one) at 200,000,
  through the record-by-record check `ix check-lean` and `kernel-check-ixe`
  run (`Run.runRecords`, serially and on the pool): every declaration
  accepted but the last, which is rejected (aborted: the failure rebuilds
  the index of every installed constant with `mkFEnvGo`, and the host's
  record loop kept two frames per record);
* a **control**: a plain non-tail recursion a million deep aborts on the
  same stack, so a stack setting that stopped taking effect fails the test.

The cases are deliberately past the old limits by a wide margin and short:
about a second each. -/

namespace Tests.Ix.Kernel.Depth

/-- The stack every case runs on, in KiB. -/
def stackKb : Nat := 2048

/-- The case runner (`Tests/Ix/Kernel/DepthCaseMain.lean`), which `IxTests` builds. -/
def caseExe : System.FilePath := ".lake" / "build" / "bin" / "kernel-depth-case"

/-- `(name, n, what the verdict line must start with)`; an empty expectation
means the child must abort. -/
def cases : List (String × Nat × String) :=
  [("control", 1000000, ""),
   ("delta", 90000, "accepted"),
   ("delta-tiered", 90000, "accepted"),
   ("delta", 150000, "declined"),
   ("iota", 100000, "accepted"),
   ("wide", 200000, "accepted"),
   ("step", 200000, "200000 accepted, last reject, 200001 rows"),
   ("step-pool", 200000, "200000 accepted, last reject, 200001 rows")]

def run : IO UInt32 := do
  IO.println s!"kernel-depth: reduction steps and record counts on a {stackKb} KiB stack"
  let exe ← IO.FS.realPath caseExe
  let mut failed := 0
  for (name, n, want) in cases do
    -- no core file for the control's abort
    let out ← IO.Process.output {
      cmd := "sh", args := #["-c", "ulimit -c 0; exec \"$0\" \"$@\"", exe.toString, name, toString n],
      env := #[("LEAN_STACK_SIZE_KB", some (toString stackKb))] }
    let line := (out.stdout.splitOn "\n").find? (·.startsWith s!"{name} {n}: ") |>.getD ""
    let verdict := toString (line.drop (s!"{name} {n}: ").length)
    let ok :=
      if want.isEmpty then out.exitCode != 0 && out.stderr.contains "Stack overflow"
      else out.exitCode == 0 && verdict.startsWith want &&
        (name != "delta" || n < 100000 || verdict.contains "fuel exhausted: defeq loop")
    let shown := if want.isEmpty then
        s!"aborted (exit {out.exitCode}){if out.stderr.contains "Stack overflow" then ", stack overflow" else ""}"
      else if line.isEmpty then s!"no verdict (exit {out.exitCode}): {(toString (out.stderr.takeEnd 300)).replace "\n" " "}"
      else verdict
    IO.println s!"  {name} {n}: {shown}{if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  (← IO.getStdout).flush
  if failed == 0 then
    IO.println "kernel-depth: every case passed"
    return 0
  IO.eprintln s!"kernel-depth: {failed} cases failed"
  return 1

end Tests.Ix.Kernel.Depth
