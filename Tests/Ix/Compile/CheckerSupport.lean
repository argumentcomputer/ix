import Ix.EnvScope
import Ix.CompileDriver
import IxC.Kernel.CoreDefs
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.KernelReport

open Lean

namespace Tests.Ix.Compile.CheckerSupport

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def names (cs : List (Name × ConstantInfo)) : Std.HashSet Name :=
  cs.foldl (fun acc c => acc.insert c.1) {}

private def sameNames (xs ys : List (Name × ConstantInfo)) : Bool :=
  xs.length == ys.length && xs.all ((names ys).contains ·.1)

/-- The untrusted support policy tracks the entire existing checker table;
the test alone imports kernel definitions, never a compiler module. -/
def tableCheck : IO Unit := do
  let ops := [``Nat.pred, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
    ``Nat.beq, ``Nat.ble, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.land,
    ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight]
  let kernelOps := Ix.Kernel.natOpNames ++ Ix.Kernel.natDivModNames
  require ((ops.map toString) == kernelOps.map toString) "checker operation coverage drift"
  for n in ops do
    require ((checkerSupportNames n).map Ix.Kernel.Name.ofLeanName ==
      Ix.Kernel.natOpDeps (Ix.Kernel.Name.ofLeanName n)) s!"checker support drift at {n}"
  require ((checkerSupportNames ``Nat.log2).isEmpty) "unaccelerated operation gained support"
  require ((checkerSupportOf {} ``Nat.land).isEmpty) "support synthesized missing source records"
  IO.println "[checker-support] all 15 operation policies agree with the unchanged kernel"

private def compile (env : Environment) (closed : List (Name × ConstantInfo))
    (mode : Bool) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closed).mapError toString)
  let output ← IO.ofExcept ((← Ix.CompileM.compileLeanInput input
    (numWorkers := 4) (pass3? := some mode)).mapError toString)
  require output.cenv.ungrounded.isEmpty "checker-support regression has ungrounded declarations"
  return output

private def certify (dir : System.FilePath) (label : String) (bytes : ByteArray)
    : IO KernelReport.Report := do
  let path := dir / s!"{label}.ixe"
  let report := dir / s!"{label}.jsonl"
  IO.FS.writeBinFile path bytes
  let out ← IO.Process.output
    { cmd := ".lake/build/bin/kernel-check-ixe",
      args := #[path.toString, report.toString, "--jobs", "4"],
      -- Check every record of this small selected artifact. String root names
      -- cannot represent a private Lean Name's numeric component faithfully.
      env := #[("CHECK_IXE_ROOTS", none), ("LD_LIBRARY_PATH", none)] }
  IO.FS.writeFile (dir / s!"{label}.log") (out.stdout ++ out.stderr)
  IO.ofExcept (KernelReport.parse (← IO.FS.readFile report) out.exitCode)

private def verdict (report : KernelReport.Report) (env : Ixon.Env)
    (name : Name) : IO KernelReport.Verdict := do
  let some nd := env.named[Pass3.ixN name]? | throw <| IO.userError s!"missing output name {name}"
  let address := toString (AuxCert.recordOf env nd.addr)
  IO.ofExcept (KernelReport.checkCoverage report #[(toString name, address)])
  let some result := report[address]? | throw <| IO.userError s!"missing verdict {name}"
  return result

/-- Exact failing corpus case, both rewrite modes. Raw closure remains a negative
control; selected closure must certify and retain every whole-output Named record
(including metadata, original and hints), constant body and blob. -/
def run : IO UInt32 := do
  tableCheck
  let env ← getFileEnv "Tests/Ix/Compile/CheckerSupport/Single.lean"
  let seeds := (env.constants.toList.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isNone then some n else none)
  require (!seeds.isEmpty) "empty Single fixture"
  let raw := Ix.EnvScope.collectDeps env seeds (withRecursors := true) (withCompilerSupport := true)
  let selected := Ix.EnvScope.collectSelectedDeps env seeds
  require (!(names raw).contains ``Nat.mul) "raw negative control unexpectedly contains Nat.mul"
  require ((names raw).contains ``Nat.land && (names selected).contains ``Nat.mul)
    "selected closure failed to add required Nat pin ground"
  require (sameNames selected (Lean.collectDependenciesMany
    (seeds ++ Ix.EnvScope.introducedSupport env).toArray env.constants
    (withCompilerSupport := true) (withCheckerSupport := true) (withUnits := true))) "collectors disagree"
  require (sameNames selected (Ix.EnvScope.collectSelectedDeps env (selected.map (·.1))))
    "checker support closure is not a fixed point"
  require (sameNames selected (Ix.EnvScope.collectSelectedDeps env seeds.reverse))
    "checker support depends on seed order"
  let dir : System.FilePath := "out/checker-support"
  IO.FS.createDirAll dir
  let added := selected.filter (fun c => !(names raw).contains c.1)
  IO.FS.writeFile (dir / "added-source-names.txt") (String.intercalate "\n" (added.map (toString ∘ Prod.fst)))
  let required := [`AX.S_T_0_0_dir.isBase, `AX.S_T_0_0_dir.isBase.match_1,
    `AX.S_T_0_0_dir.isBase._sparseCasesOn_1, ``Nat.land, ``Nat.mul]
  for mode in [false, true] do
    let label := if mode then "on" else "off"
    let whole ← compile env env.constants.toList mode
    let closed ← compile env selected mode
    let negative ← compile env raw mode
    for (name, nd) in closed.env.named do
      require (whole.env.named[name]? == some nd) s!"{label}: whole Named differs for {name.pretty}"
    for (address, body) in closed.env.consts do
      require ((whole.env.consts[address]?).map Ixon.LazyConstant.rawBytes == some body.rawBytes)
        s!"{label}: whole record differs at {address}"
    for (address, blob) in closed.env.blobs do
      require (whole.env.blobs[address]? == some blob) s!"{label}: whole blob differs at {address}"
    for (name, nd) in negative.env.named do
      require (closed.env.named[name]? == some nd) s!"{label}: support changed raw Named {name.pretty}"
    let positiveReport ← certify dir s!"selected-{label}" closed.bytes
    for name in required do
      let row ← verdict positiveReport closed.env name
      require (row.outcome == "accept") s!"{label}: {name}: {row.outcome}: {row.reason}"
    for name in seeds do
      let row ← verdict positiveReport closed.env name
      require (row.outcome == "accept" || (row.outcome == "decline" && AuxCert.documentedDecline row.reason))
        s!"{label}: fixture {name}: {row.outcome}: {row.reason}"
    let rawReport ← certify dir s!"raw-{label}" negative.bytes
    let decline ← verdict rawReport negative.env ``Nat.land
    require (decline.outcome == "decline" && decline.reason == "unsupported Nat.div/mod environment (Nat.land)")
      s!"{label}: raw control lost its exact Nat.land decline"
    for name in required.take 3 do
      let blocked ← verdict rawReport negative.env name
      require (blocked.outcome == "blocked") s!"{label}: raw helper {name} is not blocked"
    let unit : Pass3.CUnit := { name := "checker-support", env, seeds := seeds.toArray, closure := selected }
    let (errors, summary) ← Pass3.decompileCheck unit closed
    require errors.isEmpty s!"{label}: {errors}"
    IO.println s!"[checker-support] {label}: {seeds.length} fixture names; {added.length} source supports; full Named/record/blob identity; {summary}; certified accepts and raw declines verified"
  return 0

end Tests.Ix.Compile.CheckerSupport
