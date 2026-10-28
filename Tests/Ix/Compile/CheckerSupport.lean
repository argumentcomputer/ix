/-
  checker-support-regression: a selected closure carries the checker's
  certificate ground (`Ix.EnvScope.checkerSupportOf`, from `IxC.Kernel.Roles`
  `Role.deps`; CQX.3), on the exact failing corpus case `S_T_0_0_dir`
  (`Tests/Ix/Compile/CheckerSupport/Single.lean`).

  The checker installs a well-founded `Nat` operation only when every
  operation of its recurrences is stored (`divModEnvGuardF`,
  `IxC/Kernel/DeclCheck.lean`). The evidence of those recurrences must also
  lie in the reference closure (`evidenceLocal`, `IxC/Kernel/Roles.lean`).
  The fixture's `isBase` helpers reach `Nat.land`. `Nat.land`'s value does
  not mention `Nat.mul`, but its certificate needs it.

  - **Raw closure** (`collectDeps … { recursors := true }`), the negative
    control. It holds `Nat.land` and lacks `Nat.mul`. The certified checker
    declines `Nat.land` with `rawLandDecline`, and blocks the three
    `isBase` helpers.
  - **Selected closure** (`collectSelectedDeps`).
    - It holds `Nat.mul`, is a fixed point, and does not depend on the
      seed order.
    - Its compile's Named entries, records and blobs are the whole
      compile's. The raw compile's Named entries are unchanged by the
      support.
    - The certified checker accepts `Nat.land`, `Nat.mul` and the helpers.
      Every fixture constant is accepted or declined in a documented class.
    - The output decompiles to the source.

  Ported from 650500c2 and a9cf3607 `Tests/Ix/Compile/CheckerSupport.lean`:
  - Its `lean_exe checker-support-regression` is now an `IxTests` ignored
    runner (R11-23).
  - `tableCheck` is dropped. It checked a hand copy of `natOpDeps`; the
    drift check of the derivation from `Role.deps` lives in the primary
    suite (plan §2.6).
  - The mode loop is gone (R11-16).
  - The "collectors agree" check is gone: there is one collector (R01-17).
    It is replaced by the seed-order check.
  - The raw control no longer has compiler support.
  - Pass 3 is replaced by the closure harness.
  - Files go to a temporary directory, not `out/checker-support` (R11-24).
  - The decline text is re-recorded against this tree's checker
    (`rawLandDecline`).

  Run with: `lake test -- --ignored checker-support-regression` (after
  `lake build kernel-check-ixe`).
-/
import Ix.Meta
import Ix.EnvScope
import Tests.Ix.Compile.ClosureHarness

open Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.CheckerSupport

def fixture : System.FilePath := "Tests/Ix/Compile/CheckerSupport/Single.lean"

/-- The certified checker's reason for declining `Nat.land` in the raw
closure (`IxC/Kernel/DeclCheck.lean:882`), as `kernel-check-ixe` renders it
since IxC step 6: the key as its Lean name and the first eight hexadecimal
digits of its record address (`Ix.Kernel.Reader.spellWith`). Recorded from a
run of this tree, character for character; re-record it when the raw
closure's `Nat.land` record moves. -/
def rawLandDecline : String := "unsupported Nat.div/mod environment (Nat.land@de8c100c)"

/-- The constants the certificate ground concerns: the fixture's three
`isBase` helpers (blocked in the raw closure), then `Nat.land` and `Nat.mul`. -/
def required : List Name := [`AX.S_T_0_0_dir.isBase, `AX.S_T_0_0_dir.isBase.match_1,
  `AX.S_T_0_0_dir.isBase._sparseCasesOn_1, ``Nat.land, ``Nat.mul]

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"[checker-support] {message}"

/-- `compileClosure`, with no refusal. -/
private def compileClean (label : String) (env : Environment)
    (closure : List (Name × ConstantInfo)) : IO Ix.CompileM.LeanPipelineOut := do
  let out ← compileClosure env closure (workers := 4)
  require out.cenv.ungrounded.isEmpty
    s!"{label}: {out.cenv.ungrounded.size} refusals, first \
      {out.cenv.ungrounded.toList.head?.map (·.1.pretty)}"
  return out

private def verdict (report : KernelReport.Report) (env : Ixon.Env) (name : Name) :
    IO KernelReport.Verdict :=
  IO.ofExcept (verdictOf report env name |>.mapError (s!"[checker-support] " ++ ·))

def run : IO UInt32 := do
  let env ← getFileEnv fixture
  let seeds := ownConstants env
  require (!seeds.isEmpty) "empty Single fixture"
  let raw := Ix.EnvScope.collectDeps env seeds { recursors := true }
  let selected := Ix.EnvScope.collectSelectedDeps env seeds
  let rawNames := nameSet raw
  let selectedNames := nameSet selected
  require (rawNames.contains ``Nat.land) "the raw closure lacks Nat.land (fixture)"
  require (!rawNames.contains ``Nat.mul) "raw negative control unexpectedly contains Nat.mul"
  require (selectedNames.contains ``Nat.mul) "the selected closure lacks Nat.mul"
  require (sameNames selected (Ix.EnvScope.collectSelectedDeps env (selected.map (·.1))))
    "the selected closure is not a fixed point"
  require (sameNames selected (Ix.EnvScope.collectSelectedDeps env seeds.reverse))
    "the selected closure depends on the seed order"
  let dir ← IO.FS.createTempDir
  IO.println s!"[checker-support] files in {dir}"
  let added := selected.filter (fun c => !rawNames.contains c.1)
  IO.FS.writeFile (dir / "added-source-names.txt")
    (String.intercalate "\n" (added.map (toString ∘ Prod.fst)))
  let whole ← compileClean "whole" env env.constants.toList
  let closed ← compileClean "selected" env selected
  let negative ← compileClean "raw" env raw
  -- the selected output against the whole compile
  for (name, nd) in closed.env.named do
    match whole.env.named[name]? with
    | none => require false s!"the whole output lacks {name.pretty}"
    | some w =>
      if let some cls := namedDiff nd w then
        require false s!"whole Named differs for {name.pretty}: {cls}"
  for (address, body) in closed.env.consts do
    require ((whole.env.consts[address]?).map Ixon.LazyConstant.rawBytes == some body.rawBytes)
      s!"whole record differs at {address}"
  for (address, blob) in closed.env.blobs do
    require (whole.env.blobs[address]? == some blob) s!"whole blob differs at {address}"
  for (name, nd) in negative.env.named do
    require (closed.env.named[name]? == some nd) s!"support changed raw Named {name.pretty}"
  -- the selected closure certifies
  let positive ← certify dir "selected" closed.bytes
  for name in required do
    let row ← verdict positive closed.env name
    require (row.outcome == "accept") s!"selected: {name}: {row.outcome}: {row.reason}"
  for name in seeds do
    let row ← verdict positive closed.env name
    require (row.outcome == "accept" ||
        (row.outcome == "decline" && Tests.Ix.Compile.ClosureHarness.documentedDecline row.reason))
      s!"selected: fixture {name}: {row.outcome}: {row.reason}"
  -- the raw closure: the exact decline, and the helpers blocked
  let rawReport ← certify dir "raw" negative.bytes
  let decline ← verdict rawReport negative.env ``Nat.land
  require (decline.outcome == "decline" && decline.reason == rawLandDecline)
    s!"raw control lost its exact Nat.land decline: {decline.outcome}: {decline.reason}"
  for name in required.take 3 do
    let blocked ← verdict rawReport negative.env name
    require (blocked.outcome == "blocked") s!"raw helper {name} is not blocked: {blocked.outcome}"
  let (errors, summary) ← decompileCheck env selected closed
  require errors.isEmpty s!"decompile: {errors}"
  IO.println s!"[checker-support] {seeds.length} fixture names; {added.length} source supports; \
    full Named/record/blob identity; {summary}; certified accepts and raw declines verified"
  IO.FS.removeDirAll dir
  return 0

end Tests.Ix.Compile.CheckerSupport
