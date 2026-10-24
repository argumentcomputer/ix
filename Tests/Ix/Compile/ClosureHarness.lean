/-
  The closure suites' shared harness (`compiler-selected-closure`,
  `compiler-selected-closure-e2e`, `checker-support-regression`,
  `compile-closure-whole`, `pack-units`): one copy of what each of them
  needs (R11-08).

  - `compileClosure`: the ordinary Lean compile of a closure, as
    `ix compile-lean` runs it (`compileInputFromEnv`, then
    `compileLeanInput`). It is the unvalidated entry, which is fine for
    fixtures without source contracts (CQ2.22(d)).
  - `rustClosure`/`rustCheck`: the Rust compile (`ix compile`'s FFI,
    `rsCompileEnvBytesFFI`) of the same prepared constants, and the check
    that it gives the Lean compile's artifact byte for byte.
  - `decompileCheck`: decompile fidelity of an output against its source
    closure, as `ix validate-lean --full-oracle` phase 5 checks it.
  - `certify`/`verdictOf`: the certified checker (`kernel-check-ixe`) on an
    artifact, and the verdict of the record that owns a name.
  - `ixN`, `toLeanName`, `nameSet`, `sameNames`, `ownConstants`,
    `namedDiff`, `readIxe`.

  Every file goes to a directory the caller made with `IO.FS.createTempDir`,
  never under `out/` (R11-24).

  Ported from a9cf3607: `Tests/Ix/Compile/Pass3.lean` (`compileUnit`, `ixN`,
  `toLeanName`, `decompileCheck`, the certified leg of `kernelRun`), the
  `certify` of `Tests/Ix/Compile/CheckerSupport.lean`, the `rustLeg` of
  `Tests/Ix/Compile/ClosureWhole.lean`, and `readIxe`/`ixToLeanName` of
  `Ix/Cli/PackCmd.lean` (TT-13 keeps them out of the CLI). Pass 3 does not
  exist on this line, so a closure is compiled by the ordinary compiler.
  The `check-rs` and `check-lean` legs of `kernelRun` are dropped: the
  suites keep the certified leg only (plan §4.1).

  Depends on `Tests.Ix.Compile.AuxCert.recordOf` (CQ2.19 commit 4,
  `cq219-80071705-auxcert.patch`).
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Ix.DecompileDriver
import Ix.AuxGen.LiteralSupport
import Ix.Ixon
import Tests.Ix.Compile.AuxCert
import Tests.Ix.Compile.KernelReport

open Lean

namespace Tests.Ix.Compile.ClosureHarness

/-! ## Names and closures -/

def ixN (n : Name) : _root_.Ix.Name := _root_.Ix.Name.fromLeanName n

def toLeanName : _root_.Ix.Name → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (toLeanName p) s
  | .num p n _ => .num (toLeanName p) n

def nameSet (cs : List (Name × ConstantInfo)) : Std.HashSet Name :=
  cs.foldl (fun acc c => acc.insert c.1) {}

/-- The two closures hold the same names. -/
def sameNames (xs ys : List (Name × ConstantInfo)) : Bool :=
  let ys' := nameSet ys
  xs.length == ys.length && xs.all (ys'.contains ·.1)

/-- The constants the file itself elaborates (no imported module owns them),
in the environment's order: the seeds of `Ix.EnvScope.localConstList`. -/
def ownConstants (env : Environment) : List Name :=
  env.constants.toList.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isNone then some n else none

/-! ## Compiles -/

/-- The sharing limits the Rust compiler reads (`IX_SHARING_LIMITS`, read by
Rust at every compile and decompile entry point and by no Lean driver), so
that the Lean legs run under the same limits as the Rust leg. -/
def compilerLimits : IO Ix.Sharing.Exact.Limits := do
  IO.ofExcept (← Ix.CompileM.compilerSharingLimitsFromEnv)

/-- The ordinary Lean compile of `closure`, as `ix compile-lean` runs it
(`compileInputFromEnv`, then `compileLeanInput`). Per-block failures are
in `out.cenv.ungrounded`; the caller decides what to do with them. -/
def compileClosure (env : Environment) (closure : List (Name × ConstantInfo))
    (workers : Nat := 32) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  -- AuxGen M3: the literal support the closure lacks, for the drivers' Source
  -- service only, as `ix compile-lean` gives it (generation side).
  let opts : Ix.CompileM.DriverOptions :=
    { sharingLimits := (← compilerLimits)
      serviceSupport := Ix.AuxGen.literalSupportFor env closure }
  match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) (opts := opts) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"Lean compile failed: {e}")

/-- The Rust compile (`ix compile`'s FFI) of the same prepared constants as
`compileClosure`, written to `path`. Partial output is allowed, so the status
lists every refused constant. Returns the written bytes and the status. -/
def rustClosure (env : Environment) (closure : List (Name × ConstantInfo))
    (path : System.FilePath) : IO (ByteArray × Ix.CompileM.CompileEnvStatus) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  let constants ← IO.ofExcept input.prepare
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
  return (← IO.FS.readBinFile path, status)

/-- The Rust leg: the Rust compile of `closure` (written to `path`) must be
the Lean compile `lean`, byte for byte, with no refusal. `none` when it is;
otherwise the difference, counted by Named entry. -/
def rustCheck (label : String) (env : Environment) (closure : List (Name × ConstantInfo))
    (lean : Ix.CompileM.LeanPipelineOut) (path : System.FilePath) : IO (Option String) := do
  let (bytes, status) ← rustClosure env closure path
  if bytes == lean.bytes && status.ungrounded.isEmpty then return none
  let rust ← IO.ofExcept (Ixon.rsDeEnv bytes)
  let mut differ := 0
  let mut leanOnly := 0
  for (n, a) in lean.env.named do
    match rust.named.get? n with
    | some b => if a != b then differ := differ + 1
    | none => leanOnly := leanOnly + 1
  let rustOnly := (rust.named.toList.filter fun (n, _) => !lean.env.named.contains n).length
  let first := (status.ungrounded[0]?).map (fun (n, m) => s!", first {n}: {m.take 200}") |>.getD ""
  return some s!"{label}: the Rust compile differs: Rust {bytes.size} B, Lean {lean.bytes.size} B; \
    Named entries different {differ}, Lean-only {leanOnly}, Rust-only {rustOnly}; \
    Rust failures {status.ungrounded.size}{first}"

/-- How two `Named` entries of one name differ: `none` when they are equal,
else the class: `address` (the constant itself differs), or `metadata` with
the fields that differ (`constMeta`, `original`, `hints`). -/
def namedDiff (a b : Ixon.Named) : Option String :=
  if a == b then none
  else if a.addr != b.addr then some "address"
  else
    let fields := [("constMeta", a.constMeta != b.constMeta),
      ("original", a.original != b.original), ("hints", a.hints != b.hints)]
    some s!"metadata ({", ".intercalate (fields.filterMap fun (f, d) => if d then some f else none)})"

/-! ## Decompile -/

/-- Decompile fidelity: the output, decompiled by the full Lean decompiler
(`decompileEnvFullParallel`, as `ix validate-lean --full-oracle` phase 5 and
the `decompile-diff` suite run it), equals the canonicalized source constants
of `closure` (`ConstantInfo` BEq), in both directions. A constant whose block
failed to compile (`out.cenv.ungrounded`) is not expected. Returns the
problems and a summary line. -/
def decompileCheck (env : Environment) (closure : List (Name × ConstantInfo))
    (out : Ix.CompileM.LeanPipelineOut) : IO (Array String × String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  let prepared ← IO.ofExcept input.prepare
  let src : Std.HashMap _root_.Ix.Name _root_.Ix.ConstantInfo :=
    (_root_.Ix.CanonM.canonChunk prepared.toArray).foldl (fun m (n, ci) => m.insert n ci) {}
  let (decompiled, errors, _) ← _root_.Ix.DecompileM.decompileEnvFullParallel out.env (some src)
    (sharingLimits := (← compilerLimits))
  let mut problems : Array String := #[]
  let mut matched := 0
  for (n, ci) in decompiled do
    match src.get? n with
    | none => problems := problems.push s!"decompiled, not in source: {n.pretty}"
    | some orig =>
      if ci == orig then matched := matched + 1
      else problems := problems.push s!"decompile mismatch: {n.pretty}"
  for (n, e) in errors do
    problems := problems.push s!"decompile error {n.pretty}: {e.take 200}"
  let errNames : Std.HashSet _root_.Ix.Name := errors.foldl (fun s (n, _) => s.insert n) {}
  for (n, _) in src do
    if !decompiled.contains n && !errNames.contains n && !out.cenv.ungrounded.contains n then
      problems := problems.push s!"not decompiled: {n.pretty}"
  return (problems, s!"{matched}/{src.size} decompiled equal")

/-! ## The certified checker -/

private def certExe : System.FilePath := ".lake" / "build" / "bin" / "kernel-check-ixe"

/-- The certified checker (`kernel-check-ixe`, a `needs` of `IxTests`) on
`bytes`: the artifact is written to `<dir>/<label>.ixe`, the rows to
`<dir>/<label>.jsonl` and the checker's output to `<dir>/<label>.log`, where
`dir` is the caller's temporary directory. Every record is checked:
`CHECK_IXE_ROOTS` is unset, since string roots cannot spell a private
name's numeric component. `LD_LIBRARY_PATH` is unset, as for every spawned
binary. Acceptance is a row verdict (`KernelReport.parse`), not exit 0. -/
def certify (dir : System.FilePath) (label : String) (bytes : ByteArray) (jobs : Nat := 4) :
    IO KernelReport.Report := do
  let path := dir / s!"{label}.ixe"
  let rows := dir / s!"{label}.jsonl"
  IO.FS.writeBinFile path bytes
  let exe ← IO.FS.realPath certExe
  let out ← IO.Process.output
    { cmd := exe.toString, args := #[path.toString, rows.toString, "--jobs", toString jobs],
      env := #[("CHECK_IXE_ROOTS", none), ("LD_LIBRARY_PATH", none)] }
  IO.FS.writeFile (dir / s!"{label}.log") (out.stdout ++ out.stderr)
  unless ← rows.pathExists do
    throw (IO.userError s!"kernel-check-ixe wrote no rows for {label} (exit {out.exitCode})")
  IO.ofExcept (KernelReport.parse (← IO.FS.readFile rows) out.exitCode)

/-- The verdict of the record that owns `name` in the compiled `env`: a
projection's block, else the constant (`AuxCert.recordOf`). The report must
cover that record (`KernelReport.checkCoverage`). -/
def verdictOf (report : KernelReport.Report) (env : Ixon.Env) (name : Name) :
    Except String KernelReport.Verdict := do
  let some nd := env.named[ixN name]? | throw s!"the output has no {name}"
  let address := toString (AuxCert.recordOf env nd.addr)
  KernelReport.checkCoverage report #[(toString name, address)]
  let some verdict := report[address]? | throw s!"no verdict for {name}@{address}"
  return verdict

/-! ## Files -/

/-- Read an `.ixe` (Rust reader, `Ixon.rsDeEnv`). -/
def readIxe (path : System.FilePath) : IO Ixon.Env := do
  match Ixon.rsDeEnv (← IO.FS.readBinFile path) with
  | .ok e => pure e
  | .error e => throw (IO.userError s!"cannot read {path}: {e}")

end Tests.Ix.Compile.ClosureHarness
