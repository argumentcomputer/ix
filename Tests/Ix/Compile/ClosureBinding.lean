import Ix.Meta
import Ix.EnvScope
import Ix.CompileCertified
import Tests.Ix.Compile.ClosureHarness

/-!
  closure-binding-diagnosis (manual): the role binding a selected closure's
  artifact is read under, and the certified checker's verdicts on it.

  `compiler-selected-closure-e2e` and `checker-support-regression` compile a
  closure through the closure harness (`ClosureHarness.compileClosure`: the
  Lean entry, without binder data and without role finalization) and check
  the artifact with `kernel-check-ixe`. An artifact with no role binding is
  read under the default role table and the committed prelude
  (`Ix.KernelCheck.Binding.context`). This runner compiles the same closures
  three ways and prints, for each:

  - whether the artifact carries its own role binding;
  - every published role name whose address is not the default role
    table's address of that role (`Ix.CompileM.unboundPublishedRole`
    reports only the first);
  - the checker's outcome counts, and every rejected or declined record
    with its reason.

  The three compiles: `lean`, the harness's; `certified`, the certified
  compile with binder data (`Ix.CompileM.compileCertified`), not finalized;
  `finalized`, the certified compile with its role support, certificates
  and binding (`Ix.CompileM.compileAndFinalize`), as `ix compile --consts`
  writes it.

  Closures: the selected closure of `PassO2.SA._sizeOf_1`
  (`Tests/Ix/Compile/Fixtures/MutualSizeOf.lean`), and the selected and raw
  closures of the constants of `Tests/Ix/Compile/CheckerSupport/Single.lean`.
  The artifacts, rows and checker logs stay in a temporary directory, printed
  first. Exit 0 whatever the verdicts; 1 only when a step cannot run.

  Run with: `lake test -- --ignored closure-binding-diagnosis` (after
  `lake build kernel-check-ixe`).
-/

open Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.ClosureBinding

/-- Every published name of `ixe` that names a role: the name, the role, its
address in `ixe`, and the default role table's address of the role (`none`:
the table does not bind it). -/
def publishedRoles (ixe : Ixon.Env) :
    Array (Ix.Name × Ix.Kernel.Role × Address × Option Address) :=
  let bound : Std.HashMap Ix.Kernel.Role Address :=
    Ix.Cert.roleTableBound.foldl (fun m (r, a) => if m.contains r then m else m.insert r a) {}
  ixe.named.toArray.filterMap fun (n, named) =>
    match Ix.Kernel.Role.ofLeanName? (Ix.LeanIngress.ingressName n) with
    | some r => some (n, r, named.addr, bound[r]?)
    | none => none

private def line (label msg : String) : IO Unit :=
  IO.println s!"[closure-binding] {label}: {msg}"

/-- The binding, the published roles against the default table, and the
checker's verdicts on the artifact `ixe` with bytes `bytes`. -/
def describe (dir : System.FilePath) (label : String) (ixe : Ixon.Env) (bytes : ByteArray)
    (roots : List Name := []) : IO Unit := do
  let binding := match ixe.roleBinding with
    | some b => s!"present at {b.address}"
    | none => "absent"
  line label s!"{ixe.consts.size} records, {bytes.size} bytes, role binding {binding}"
  let roles := publishedRoles ixe
  let differ := roles.filter fun (_, _, a, b) => b != some a
  line label s!"{roles.size} published role names, {differ.size} not at the default table's \
    address of their role"
  for (n, r, a, b) in differ.qsort (fun x y => x.1.pretty < y.1.pretty) do
    line label s!"  {n.pretty} ({repr r}) at {a}; default table: \
      {(b.map toString).getD "unbound"}"
  let report ← certify dir label bytes
  let counts := report.fold (init := ({} : Std.HashMap String Nat))
    fun m _ v => m.insert v.outcome (m.getD v.outcome 0 + 1)
  let countList := (counts.toArray.qsort fun x y => x.1 < y.1).toList.map fun (o, k) => s!"{o} {k}"
  line label s!"rows {report.size}: {", ".intercalate countList}"
  let failing := report.toArray.filter fun (_, v) => v.outcome == "reject" || v.outcome == "decline"
  for (a, v) in failing.qsort (fun x y => x.2.reason < y.2.reason) do
    line label s!"  {v.outcome} {a.take 8} {v.names}: {v.reason}"
  for root in roots do
    match verdictOf report ixe root with
    | .ok v => line label s!"root {root}: {v.outcome} {v.reason}"
    | .error e => line label s!"root {root}: {e}"

/-- The three compiles of `closure` (see the module docstring), each described. -/
def compileThreeWays (dir : System.FilePath) (tag : String) (env : Environment)
    (closure : List (Name × ConstantInfo)) (roots : List Name) : IO Bool := do
  IO.println s!"[closure-binding] {tag}: closure of {closure.length} constants"
  let mut ok := true
  -- the closure harness's compile
  let lean ← compileClosure env closure
  line s!"{tag}-lean" s!"{lean.cenv.ungrounded.size} refusals"
  describe dir s!"{tag}-lean" lean.env lean.bytes roots
  -- the certified compile with binder data, not finalized
  match ← Ix.CompileM.compileCertified env closure with
  | .error e =>
    line s!"{tag}-certified" s!"compile refused: {e.take 600}"
    ok := false
  | .ok out =>
    line s!"{tag}-certified" s!"{out.failures.toMap.size} failures"
    let bytes ← IO.ofExcept (Ixon.serEnv out.env)
    describe dir s!"{tag}-certified" out.env bytes roots
  -- the certified compile, finalized as `ix compile --consts` writes it
  match ← Ix.CompileM.compileAndFinalize env closure 32 (allowPartial := false) with
  | .error e =>
    line s!"{tag}-finalized" s!"compile refused: {e.take 600}"
    ok := false
  | .ok (_, .refused) =>
    line s!"{tag}-finalized" "not finalized: a constant failed to compile"
    ok := false
  | .ok (_, .failed e) =>
    line s!"{tag}-finalized" s!"finalization failed: {e.take 600}"
    ok := false
  | .ok (_, .done artifact bytes) =>
    describe dir s!"{tag}-finalized" artifact bytes roots
  return ok

def run : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  IO.println s!"[closure-binding] files in {dir}"
  let mut ok := true
  -- the e2e fixture, its first seed set
  let sizeOfEnv ← getFileEnv "Tests/Ix/Compile/Fixtures/MutualSizeOf.lean"
  let seeds := [`PassO2.SA._sizeOf_1]
  ok := (← compileThreeWays dir "sizeOf-selected" sizeOfEnv
    (Ix.EnvScope.collectSelectedDeps sizeOfEnv seeds) seeds) && ok
  -- the checker-support fixture, selected and raw
  let singleEnv ← getFileEnv "Tests/Ix/Compile/CheckerSupport/Single.lean"
  let own := ownConstants singleEnv
  let roots := [`AX.S_T_0_0_dir.isBase, ``Nat.land, ``Nat.mul]
  ok := (← compileThreeWays dir "single-selected" singleEnv
    (Ix.EnvScope.collectSelectedDeps singleEnv own) roots) && ok
  ok := (← compileThreeWays dir "single-raw" singleEnv
    (Ix.EnvScope.collectDeps singleEnv own { recursors := true }) roots) && ok
  IO.println s!"[closure-binding] done"
  return if ok then 0 else 1

end Tests.Ix.Compile.ClosureBinding
