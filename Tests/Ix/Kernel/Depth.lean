import IxCK.Kernel.Admission.Bytes

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
* `bounds`: the two bounds the depth stages skip by (`storedDepthBound`, `expandedDepthBound`)
  hold on the shapes that nest most per byte, written out and shared;
* `wide-w0`, `wide-w1`, `wide-w4`: 20,000 of the same records with phase B on at most 0 (the
  calling thread), 1 and 4 tasks (`Limits.workers`): accepted, as without the bound;
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
   ("bounds", 0, "bounds hold"),
   ("wide-w0", 20000, "accepted"),
   ("wide-w1", 20000, "accepted"),
   ("wide-w4", 20000, "accepted"),
   ("step", 200000, "200000 accepted, last reject, 200001 rows"),
   ("step-pool", 200000, "200000 accepted, last reject, 200001 rows")]

/-- KD's chain (`nestedChain`), whose 32-bit hashes cycled, on a 64 MiB stack (a
level takes about 780 bytes; the chain nests once per level): `(name, n, what the
verdict must start with, its bound in ms)`. With the 32-bit hash `nested0` took
83 s at 32,000 levels and `nested3` 57 s at 16,000; with the 64-bit hash 35 and
49 ms at 32,000 on the loaded build box, so the bound is 20 times that. The
`hash` cases check that neither chain's hashes repeat in 1,000,000 levels (at
32 bits they repeated after 8,323 and 3,961). -/
def chainCases : List (String × Nat × String × Nat) :=
  [("nested0", 32000, "returned the λ", 1000),
   ("nested3", 32000, "returned the λ", 1000),
   ("hash0", 1000000, "no repeat", 0),
   ("hash3", 1000000, "no repeat", 0)]

/-- The chain cases' stack, in KiB. -/
def chainStackKb : Nat := 65536

/-- The milliseconds a verdict line reports (`… in N ms`), if any. -/
def reportedMs (verdict : String) : Option Nat :=
  ((verdict.splitOn " in ").getLast?.bind fun t => (t.splitOn " ms").head?.bind String.toNat?)

/-- The default limits (only `maxDepth` and the stack it gives are read). -/
def defaultLimits : Ix.Kernel.Admission.Limits :=
  { maxRecords := 0, maxBlobs := 0, maxTotalBytes := 0, maxRecordBytes := 0, maxRecordUnivNodes := 0 }

/-- **The depth limit** (`Limits.maxDepth`; `docs/kernel.md`, "Native stack"):
each shape of `kernel-depth-case`'s `shape` (λ and ∀ telescopes, an argument
nest, a spine, a `let` nest, a `succ` and a `max` universe), written out and
with one sharing entry per level, at the limit and one past it, under
`maxDepth` 64 on the small stack and under the default (16,384) on the stack
`Limits.stackFor` gives it. At the limit each shape is accepted; one past it the
entry declines with `.limit .depth`, before decoding (written out) or after it
(shared). The measured depth comes from an oracle of the test's own
(`exprDepth`). -/
def limitCases : List (String × Nat × Nat) :=
  let big := defaultLimits.stackFor / 1024
  ["lam", "pi", "appArg", "spine", "let", "usucc", "umax"].flatMap fun s =>
    ["flat", "shared"].flatMap fun e =>
      [(s!"limit64-{s}-{e}", 64, stackKb), (s!"limit64-{s}-{e}", 65, stackKb),
       (s!"limit-{s}-{e}", defaultLimits.maxDepth, big),
       (s!"limit-{s}-{e}", defaultLimits.maxDepth + 1, big)]

/-- **The depth stages themselves** (`Admission.Depth`): `(name, n, what the verdict must start
with, its bound in ms, the stack in KiB)`. `differential`: `n` generated records (half of them with
sharing tables that refer forward, to themselves or past their end), each scanned by the kernel's
scan and by its first form (`Tests.Ix.Kernel.DepthRef`) at ten limits and with bytes mutated, and
measured by the expanded check and by the general post-order: no difference. `walk-spine`,
`post-spine`, `post-cycle`: the expanded check alone on a spine of `n` arguments under the limit
`n + 1`, by the walk; the same spine behind a forward reference, by the post-order; a cyclic table
holding it. At 16,384 and at 65,536 levels each takes at most 4 ms (measured; before KI's change the
post-order copied its value array at every node: 143 and 203 ms at 16,384, 2,467 and 2,410 ms at
65,536, `kernel-depth-case old-walk-spine`, `old-post-spine`); the bounds are far above the linear
times and below the quadratic ones at 65,536. The walk recurses once per level (about 80 bytes of
native stack each), so it runs on the stack `Limits.stackFor` gives the limit. `differential` at
3,000 records takes about 2 s: 30,000 scans and expanded checks (about 500 records by the
post-order) and 216,000 scans of mutated bytes; the corpus-scale run (Init+Std and the committed
closures, 1.7 million scans) is a probe, not a test. -/
def stageCases : List (String × Nat × String × Nat × Nat) :=
  let kb (d : Nat) := ({ defaultLimits with maxDepth := d }).stackFor / 1024
  [("differential", 3000, "no differences", 0, stackKb),
   ("walk-spine", 16384, "within (in order)", 500, kb 16385),
   ("walk-spine", 65536, "within (in order)", 1000, kb 65537),
   ("post-spine", 16384, "within (post-order)", 500, kb 16385),
   ("post-spine", 65536, "within (post-order)", 1000, kb 65537),
   ("post-cycle", 65536, "past (post-order)", 1000, kb 65538)]

/-- One `limitCases` case: its line and whether it passed. -/
def limitCaseOk (name : String) (d : Nat) (verdict : String) (exitCode : UInt32) : Bool :=
  let maxDepth := if name.startsWith "limit64" then 64 else defaultLimits.maxDepth
  exitCode == 0 && verdict.startsWith s!"depth {d}, " &&
    if d ≤ maxDepth then
      !verdict.contains "Resource.depth" && verdict.contains "accepted"
    else verdict.contains "declined" && verdict.contains "Resource.depth"

def run : IO UInt32 := do
  IO.println s!"kernel-depth: reduction steps and record counts on a {stackKb} KiB stack"
  let exe ← IO.FS.realPath caseExe
  let mut failed := 0
  let all := cases.map (fun (c, n, w) => (c, n, w, stackKb, 0)) ++
    chainCases.map (fun (c, n, w, b) => (c, n, w, chainStackKb, b)) ++
    stageCases.map (fun (c, n, w, b, kb) => (c, n, w, kb, b))
  for (name, n, want, kb, bound) in all do
    -- no core file for the control's abort
    let out ← IO.Process.output {
      cmd := "sh", args := #["-c", "ulimit -c 0; exec \"$0\" \"$@\"", exe.toString, name, toString n],
      env := #[("LEAN_STACK_SIZE_KB", some (toString kb))] }
    let line := (out.stdout.splitOn "\n").find? (·.startsWith s!"{name} {n}: ") |>.getD ""
    let verdict := toString (line.drop (s!"{name} {n}: ").length)
    let ok :=
      if want.isEmpty then out.exitCode != 0 && out.stderr.contains "Stack overflow"
      else out.exitCode == 0 && verdict.startsWith want &&
        (name != "delta" || n < 100000 || verdict.contains "fuel exhausted: defeq loop") &&
        (bound == 0 || (reportedMs verdict).any (· ≤ bound))
    let shown := if want.isEmpty then
        s!"aborted (exit {out.exitCode}){if out.stderr.contains "Stack overflow" then ", stack overflow" else ""}"
      else if line.isEmpty then s!"no verdict (exit {out.exitCode}): {(toString (out.stderr.takeEnd 300)).replace "\n" " "}"
      else verdict
    IO.println s!"  {name} {n}: {shown}{if bound == 0 then "" else s!" (bound {bound} ms)"}{if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  for (name, d, kb) in limitCases do
    let out ← IO.Process.output {
      cmd := "sh", args := #["-c", "ulimit -c 0; exec \"$0\" \"$@\"", exe.toString, name, toString d],
      env := #[("LEAN_STACK_SIZE_KB", some (toString kb))] }
    let line := (out.stdout.splitOn "\n").find? (·.startsWith s!"{name} {d}: ") |>.getD ""
    let verdict := toString (line.drop (s!"{name} {d}: ").length)
    let ok := limitCaseOk name d verdict out.exitCode
    let shown := if line.isEmpty then
        s!"no verdict (exit {out.exitCode}): {(toString (out.stderr.takeEnd 300)).replace "\n" " "}"
      else verdict
    IO.println s!"  {name} {d} ({kb} KiB): {shown}{if ok then "" else "  FAILED"}"
    unless ok do failed := failed + 1
  (← IO.getStdout).flush
  if failed == 0 then
    IO.println "kernel-depth: every case passed"
    return 0
  IO.eprintln s!"kernel-depth: {failed} cases failed"
  return 1

end Tests.Ix.Kernel.Depth
