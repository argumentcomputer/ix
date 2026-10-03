/-
  aux-cert: the A0 safety fixtures, through both compilers, both kernels and
  the certified checker.

  Every fixture is a standalone Lean file under `Tests/Ix/Compile/AuxCert/`
  (never imported into the test binary: some must be refused, and a refused
  constant would fail every whole-environment suite). The fixtures are the
  auxgen audit reproducers (`plans/review/auxgen-audit/{whitebox,blackbox}/
  repro`, 28 + 10 files, verbatim), their passing neighbours
  (`Neighbours.lean`), and the A0 fixtures: `SurgCollapseEq` (the equal-arms
  neighbour of `SurgCollapse`), `F4FlatAlphaUsers` (an eta-wrapped collapsed
  recursor) and `NestMutGroup` (nesting through an external mutual family).

  Per fixture, as the CLI runs it (`IxTests` depends on the `ix` target):

  1. `ix compile <file> --no-build` and `ix compile-lean <file> --rust-check`.
     A fixture expected to compile must exit 0 in both and print `ALIGNED`,
     and the Rust output must be sha256-identical to the Lean output (which
     `--rust-check` showed byte-identical to a second Rust compile): two
     compiles, byte-equal. A refusal must exit 1 in both, write nothing, and
     print the exact message. A recorded expected failure (a totality defect
     outside A0, by audit id) must fail with its recorded message.
  2. On a compiled output: `ix check-rs --ns`, `ix check-lean` (meta mode, on
     the fixture's constants) and `kernel-check-ixe` (the certified checker).
     Every failing constant must be listed as a known failure with its defect
     id, the certified checker may decline only in documented classes and
     must reject nothing unlisted, and every listed failure must still fail
     (an unexpected pass is reported, so the record stays exact).
  3. Required and forbidden names in the output (`NestMutGroup`: exactly the
     two nested auxiliaries Lean has).

  The `rfl` theorems in the fixtures are the value pins: the only checks
  that see a meaning change (WB-B4's `fg_ab`), since `--rust-check` and
  `validate` compare the compilers with each other, not with Lean.

  Run with: `lake test -- --ignored aux-cert` (after `lake build ix
  kernel-check-ixe`). `AUX_CERT_JOBS` sets the fixture parallelism (default
  4); `AUX_CERT_ONLY` restricts to a comma-separated list of fixture stems.
-/
import Lean.Data.Json
import LSpec

open LSpec

namespace Tests.Ix.Compile.AuxCert

/-- What both compilers must do with a fixture. -/
inductive Expect where
  /-- Both compile it (exit 0), `ALIGNED`, byte-equal outputs. -/
  | compiles
  /-- Both refuse it: exit 1, nothing written, `msg` in the output. -/
  | refuses (msg : String)
  /-- A recorded expected failure outside A0's items (a totality defect, a
      kernel or elaborator limitation): `defect` is the audit id; `ix compile`
      exits nonzero printing `msg`, and the Lean mirror exits nonzero too
      (`leanToo = false`: the Lean mirror is not run). -/
  | xfail (defect msg : String) (leanToo : Bool := true)
  deriving Inhabited

/-- One fixture and its record. -/
structure Fixture where
  /-- File stem under `Tests/Ix/Compile/AuxCert/`. -/
  stem : String
  /-- Name prefixes the fixture owns (a namespace, or its top-level names). -/
  ns : List String
  expect : Expect := .compiles
  /-- Constants known to fail a check: `(leg, name, defect)` with leg
      `rs` (`check-rs`), `lean` (`check-lean`) or `cert` (certified checker,
      reject or undocumented decline); name `*` stands for every constant of
      the fixture on that leg and `P.*` for every name under `P`. -/
  knownFails : List (String × String × String) := []
  /-- Names that must be in the compiled output. -/
  requireNames : List String := []
  /-- Names that must not be in the compiled output. -/
  forbidNames : List String := []
  deriving Inhabited

/-- Substring test (independent of the `String` pattern API). -/
def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The certified checker's documented decline classes
    (`docs/kernel.md`, the audits): unsafe and partial declarations, and the
    modeller's reflexive/nested limitations. -/
def documentedDecline (reason : String) : Bool :=
  ["unsafe", "partial", "reflexive", "nested inductive"].any (hasSub reason ·)

/-- Known failures of `names` on one leg. -/
def kf (leg defect : String) (names : List String) : List (String × String × String) :=
  names.map fun n => (leg, n, defect)

-- The fixture record (filled from the A0 survey on 2026-10-03, Lean
-- 4.34.1; expected behaviours from `plans/replan/D-evidence-digest.md` §2,
-- `audit-whitebox-5.md` and `audit-blackbox-final.md`).
def fixtures : List Fixture := [
  -- A0 item 1 (WB-B4): the collapse refusal, its equal-arms neighbour, and
  -- the eta-wrapped partial applications of collapsed recursors.
  { stem := "SurgCollapse", ns := ["SurgCollapse"]
    expect := .refuses "collapse call site drops distinct arguments" },
  { stem := "SurgCollapseEq", ns := ["SurgCollapseEq"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  { stem := "F4FlatAlphaUsers", ns := ["F4FlatAlphaUsers"]
    expect := .refuses "collapse call site is a partial application" },
  { stem := "F4_NestedAlphaUsers", ns := ["A", "B", "r", "t", "sizeL", "sizeLA"]
    expect := .refuses "collapse call site is a partial application" },
  -- A0 item 2 (WB-B1, A5/C3, C1): the user's names stay the user's.
  { stem := "FieldBelow", ns := ["FieldBelow"] },
  { stem := "FieldBelowRace", ns := ["FieldBelowRace"] },
  { stem := "L1_UserBelowName", ns := ["T", "use_below"] },
  { stem := "SurgName", ns := ["SurgName"] },
  -- A0 item 3 (WB-B8): no forced large elimination.
  { stem := "SortUDecl", ns := ["SortUD"] },
  -- A0 item 3 (WB-E1/A4): an evaporation target that is not a one-motive
  -- recursor is refused, naming the block.
  { stem := "F3_SplitRoseRace", ns := ["A", "B", "Rose"]
    expect := .refuses "is not a one-motive recursor" },
  { stem := "NestRoseSplit", ns := ["NestRoseSplit"]
    expect := .refuses "is not a one-motive recursor" },
  { stem := "NestMutExt", ns := ["NestMutExt"]
    expect := .refuses "is not a one-motive recursor" },
  { stem := "NestMutExtA", ns := ["NestMutExtA"]
    expect := .refuses "is not a one-motive recursor" },
  -- A0 extra item (WB-A1, a1c item 7): external mutual groups.
  { stem := "NestMutGroup", ns := ["NestMutGroup"]
    requireNames := ["NestMutGroup.T.rec_1", "NestMutGroup.T.rec_2"]
    forbidNames := ["NestMutGroup.T.rec_3", "NestMutGroup.T.rec_4"] },
  { stem := "NestMutExtT", ns := ["NestMutExtT"] },
  { stem := "NestFo", ns := ["NestFo"] },
  -- Passing neighbours with value pins.
  { stem := "Neighbours"
    ns := ["F1Pair", "F1Ring", "F1Triple", "F4Flat", "F5PSigma", "F5Prod",
      "F6AFirst", "F8NoSplit", "L2Data", "L2TwoCtors", "RecBelow"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)"
      ["F1Pair.*", "F1Ring.*", "F1Triple.*", "F4Flat.*"] },
  -- Reproducers that compile cleanly (the audits' refuted leads).
  { stem := "BetaField", ns := ["BetaField"] },
  { stem := "DotCtor", ns := ["DotCtor"] },
  { stem := "EvapClosure", ns := ["EvapClosure"] },
  { stem := "F2_SplitNestedClosure", ns := ["A", "B"] },
  -- WB §6: the certified checker declines the reflexive nested `R`
  -- (its documented modeller limitation); its dependents are blocked.
  { stem := "NestShapes", ns := ["NestShapes"]
    knownFails := kf "cert" "WB §6 (certified: reflexive nested decline)" ["NestShapes.R.*"] },
  -- Compiled, with constants a checker rejects: totality defects outside
  -- A0, recorded by id.
  { stem := "Coind", ns := ["Coind"]
    knownFails :=
      kf "rs" "WB-B2" ["Coind.CA._functor.existential_equiv", "Coind.CA.casesOn",
        "Coind.CB._functor.existential_equiv", "Coind.CB.casesOn"] ++
      kf "lean" "WB-B2" ["Coind.CA._functor.existential_equiv", "Coind.CA.casesOn",
        "Coind.CB._functor.existential_equiv", "Coind.CB.casesOn"] ++
      kf "cert" "WB-B2" ["Coind.CA._functor.existential_equiv",
        "Coind.CB._functor.existential_equiv", "Coind.CA.functor_unfold",
        "Coind.CB.functor_unfold", "Coind.CA.mk", "Coind.CB.mk", "Coind.CA.casesOn",
        "Coind.CB.casesOn"] },
  { stem := "PropSplit", ns := ["PropSplit"]
    knownFails := ["rs", "lean", "cert"].flatMap fun leg =>
      kf leg "WB-B2" ["PropSplit.p1", "PropSplit.p2", "PropSplit.q1", "PropSplit.q2"] },
  { stem := "PropCollapse", ns := ["PropCollapse"]
    knownFails := kf "rs" "WB-B2" ["PropCollapse.p_cases"] ++
      kf "cert" "WB-B2" ["PropCollapse.p_cases"] ++
      kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress), WB-B2" ["*"] },
  { stem := "L2_PropSplit", ns := ["A", "B", "ua"]
    knownFails := ["rs", "lean", "cert"].flatMap fun leg => kf leg "BB-L2 (= WB-B2)" ["ua"] },
  { stem := "RecAlias", ns := ["RecAlias"]
    knownFails := kf "rs" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] ++
      kf "lean" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] ++
      kf "cert" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2",
        "RecAlias.PA.triv"] },
  { stem := "SurgAlias", ns := ["SurgAlias"]
    knownFails :=
      kf "rs" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.A.a.sizeOf_spec", "SurgAlias.f",
        "SurgAlias.f1"] ++
      kf "lean" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.A.a.sizeOf_spec", "SurgAlias.f",
        "SurgAlias.f1"] ++
      kf "cert" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.f", "SurgAlias.f1",
        "SurgAlias.A._sizeOf_inst", "SurgAlias.A.a.sizeOf_spec", "SurgAlias.A.nil.sizeOf_spec"] },
  { stem := "SurgSplit", ns := ["SurgSplit"]
    knownFails := kf "rs" "WB-B3" ["SurgSplit.A.len._f", "SurgSplit.len2"] ++
      kf "lean" "WB-B3" ["SurgSplit.A.len._f", "SurgSplit.len2"] ++
      kf "cert" "WB-B3" ["SurgSplit.A.len._f", "SurgSplit.A.len", "SurgSplit.len2",
        "SurgSplit.A.len._sunfold"] },
  { stem := "UnsafeI", ns := ["UnsafeI"]
    knownFails := kf "rs" "WB-B9" ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] ++
      kf "lean" "WB-B9" ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] },
  { stem := "F1_Collapse2p1", ns := ["A", "B", "C"]
    knownFails := kf "rs" "BB-F1 (metadata of collapsed aliases)" ["*"] ++
      kf "lean" "BB-F1, BB-F7" ["*"] },
  { stem := "F5_SigmaNestedNested", ns := ["T"]
    knownFails := ["rs", "lean"].flatMap fun leg =>
      kf leg "BB-F5 (kernel completeness)" ["T.rec", "T.rec_1", "T.rec_2"] },
  { stem := "F7_AlphaVLean", ns := ["A", "B"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  -- Expected compile failures outside A0 (totality defects).
  { stem := "AliasIdx", ns := ["AliasIdx"]
    expect := .xfail "WB-A3" "function expected, got Sort u" },
  { stem := "KernelSpec", ns := ["KernelSpec"]
    expect := .xfail "WB-A7" "is_large_eliminator failed" },
  { stem := "SurgIdx", ns := ["SurgIdx", "SurgIdx2"]
    expect := .xfail "WB-A2" "found no residual Pi binders" },
  { stem := "F6_OrderIdxBrecOn", ns := ["A", "B"]
    expect := .xfail "BB-F6 (= WB-A2)" "found no residual Pi binders" },
  { stem := "F8_PropSplitNested", ns := ["A", "B", "PBox"]
    expect := .xfail "BB-F8" "source recursor has no elimination level" },
  -- Reproducers Lean itself rejects (audit notes; kept so the record is
  -- complete): nothing reaches either compiler.
  { stem := "PropEvap", ns := ["PropEvap"]
    expect := .xfail "WB §9 (Lean rejects the file)" "Application type mismatch" },
  { stem := "SortU", ns := ["SortU"]
    expect := .xfail "WB-B8 note (Lean rejects the file)" "Invalid universe polymorphic resulting type" },
  { stem := "SortURec", ns := ["SortURec"]
    expect := .xfail "WB-B8 note (Lean rejects the file)" "Invalid universe polymorphic resulting type" },
  { stem := "SortUOpt", ns := ["SortUOpt"]
    expect := .xfail "WB-B8 note (Lean rejects the file)" "Unknown constant `SortUOpt.SU.ctorIdx`" }
]


/-! ## Running one fixture -/

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
private def certExe : System.FilePath := ".lake" / "build" / "bin" / "kernel-check-ixe"

/-- Nested `lake` builds (compile-lean builds the fixture module) must not see
    the toolchain's `LD_LIBRARY_PATH` (see `Tests.Cli.spawnEnv`). -/
private def spawnEnv : Array (String × Option String) := #[("LD_LIBRARY_PATH", none)]

private def run (cmd : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let exe ← IO.FS.realPath cmd
  IO.Process.output { cmd := exe.toString, args, env := spawnEnv }

private def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  return (out.stdout.splitOn " ").headD ""

private def owns (f : Fixture) (name : String) : Bool :=
  f.ns.any fun p => name == p || name.startsWith (p ++ ".")

/-- A recorded name pattern: an exact name, `*` (every constant of the
    fixture), or `P.*` (every name under `P`). -/
private def isPattern (n : String) : Bool := n == "*" || n.endsWith ".*"

private def matchesPat (n name : String) : Bool :=
  n == name || n == "*" || (n.endsWith ".*" && name.startsWith (n.dropEnd 1).toString)

private def known (f : Fixture) (leg name : String) : Option String :=
  f.knownFails.findSome? fun (l, n, d) =>
    if l == leg && matchesPat n name then some d else none

/-- `✗ name: message` lines of a checker's output. -/
private def failLines (out : String) : List (String × String) :=
  out.splitOn "\n" |>.filterMap fun line =>
    let l := line.trimAsciiStart.toString
    if l.startsWith "✗ " then
      let body := (l.drop 2).toString
      match body.splitOn ": " with
      | name :: rest => some (name, ": ".intercalate rest)
      | [] => none
    else none

/-- Rows of a `kernel-check-ixe` jsonl file: names, outcome, reason. -/
private def certRows (path : System.FilePath) :
    IO (Array (List String × String × String)) := do
  let content ← IO.FS.readFile path
  let mut rows := #[]
  for line in content.splitOn "\n" do
    if line.isEmpty then continue
    let .ok j := Lean.Json.parse line | continue
    let names := match j.getObjValAs? (Array String) "names" with
      | .ok ns => ns.toList
      | .error _ => []
    let outcome := (j.getObjValAs? String "outcome").toOption.getD ""
    let reason := (j.getObjValAs? String "reason").toOption.getD ""
    rows := rows.push (names, outcome, reason)
  return rows

/-- Runs one fixture; returns its problems (empty: as recorded) and a
    one-line summary. -/
def runFixture (f : Fixture) : IO (Array String × String) := do
  let src := s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean"
  let dir ← IO.FS.createTempDir
  let mut problems : Array String := #[]
  try
    let rsOut := dir / "rs.ixe"
    let leanOut := dir / "lean.ixe"
    let rs ← run ixExe #["compile", src, "--no-build", "--out", rsOut.toString]
    let rsText := rs.stdout ++ rs.stderr
    let runLean := match f.expect with
      | .xfail _ _ false => false
      | _ => true
    let ln : IO.Process.Output ← if runLean then
        run ixExe #["compile-lean", src, "--rust-check", "--out", leanOut.toString]
      else pure { exitCode := (0 : UInt32), stdout := "", stderr := "" }
    let lnText := ln.stdout ++ ln.stderr
    let rsCode : UInt32 := rs.exitCode
    let lnCode : UInt32 := ln.exitCode
    match f.expect with
    | .refuses msg =>
      if rsCode != 1 || !hasSub rsText msg then
        problems := problems.push s!"ix compile: expected exit 1 with '{msg}', got exit {rs.exitCode}"
      if lnCode != 1 || !hasSub lnText msg then
        problems := problems.push s!"ix compile-lean: expected exit 1 with '{msg}', got exit {ln.exitCode}"
      if ← rsOut.pathExists then
        problems := problems.push "ix compile wrote an output for a refused fixture"
      return (problems, s!"refused ({msg})")
    | .xfail defect msg leanToo =>
      if rsCode == 0 || !hasSub rsText msg then
        problems := problems.push s!"expected failure {defect}: ix compile exit {rs.exitCode}, '{msg}' {if hasSub rsText msg then "present" else "absent"}"
      -- The Lean mirror must fail too; its bounded listing need not show
      -- the Rust message (a different constant of the block may be listed).
      if leanToo && lnCode == 0 then
        problems := problems.push s!"expected failure {defect}: ix compile-lean exit 0"
      return (problems, s!"expected failure {defect}")
    | .compiles => pure ()
    if rsCode != 0 then
      problems := problems.push s!"ix compile exit {rs.exitCode}: {(rsText.takeEnd 400).toString}"
      return (problems, "compile failed")
    if lnCode != 0 || !hasSub ln.stdout "ALIGNED" then
      problems := problems.push s!"ix compile-lean --rust-check: exit {ln.exitCode}, no ALIGNED: {(lnText.takeEnd 400).toString}"
    else if (← sha256 rsOut) != (← sha256 leanOut) then
      problems := problems.push "two compiles differ: ix compile vs ix compile-lean --rust-check outputs"
    -- The certified checker; its rows also list the output's names.
    let certPath := dir / "cert.jsonl"
    let cert ← run certExe #[rsOut.toString, certPath.toString, "--jobs", "8"]
    let rows ← if ← certPath.pathExists then certRows certPath else pure #[]
    if rows.isEmpty then
      problems := problems.push s!"kernel-check-ixe wrote no rows (exit {cert.exitCode})"
    let allNames : List String := rows.toList.flatMap (·.1) |>.eraseDups
    let mine := allNames.filter (owns f)
    for n in f.requireNames do
      unless allNames.contains n do problems := problems.push s!"output lacks {n}"
    for n in f.forbidNames do
      if allNames.contains n then problems := problems.push s!"output has {n}"
    -- Observed failures per leg.
    let mut failed : Array (String × String × String) := #[]
    for (names, outcome, reason) in rows do
      let ours := names.filter (owns f)
      if ours.isEmpty || outcome == "accept" then continue
      if outcome == "decline" && documentedDecline reason then continue
      for n in ours do failed := failed.push ("cert", n, s!"{outcome}: {reason}")
    let rsCheck ← run ixExe #["check-rs", rsOut.toString, "--ns", ",".intercalate f.ns]
    for (n, m) in failLines (rsCheck.stdout ++ rsCheck.stderr) do
      failed := failed.push ("rs", n, m)
    let namesFile := dir / "names.txt"
    IO.FS.writeFile namesFile ("\n".intercalate mine ++ "\n")
    let failOut := dir / "lean.fail"
    let leanCheck ← run ixExe #["check-lean", rsOut.toString, "--consts-file",
      namesFile.toString, "--fail-out", failOut.toString, "--workers", "8"]
    let leanFails ← if ← failOut.pathExists then
        pure ((← IO.FS.readFile failOut).splitOn "\n" |>.filter fun l =>
          !l.isEmpty && !l.startsWith "#")
      else pure []
    for n in leanFails do failed := failed.push ("lean", n.trimAscii.toString, "")
    if leanFails.isEmpty && leanCheck.exitCode != 0 then
      failed := failed.push ("lean", "*", s!"check-lean exit {leanCheck.exitCode}")
    for (leg, n, m) in failed do
      if (known f leg n).isNone then
        problems := problems.push s!"{leg}: {n} fails, not recorded: {m.take 200}"
    for (leg, n, d) in f.knownFails do
      unless isPattern n || failed.any (fun (l, m, _) => l == leg && m == n) do
        problems := problems.push s!"{leg}: {n} recorded as failing ({d}) but passes"
    let nKnown := failed.size
    return (problems, s!"compiled, ALIGNED, {mine.length} names, {nKnown} recorded failure(s)")
  finally
    IO.FS.removeDirAll dir

/-- Runs `xs` with at most `jobs` tasks at a time, keeping the order. -/
private def mapPool (jobs : Nat) (xs : List Fixture)
    (k : Fixture → IO (Array String × String)) : IO (List (Array String × String)) := do
  let mut out := #[]
  let rec chunks (n : Nat) (ys : List Fixture) (fuel : Nat) : List (List Fixture) :=
    match fuel with
    | 0 => [ys]
    | fuel + 1 => if ys.isEmpty then [] else ys.take n :: chunks n (ys.drop n) fuel
  for chunk in chunks (max jobs 1) xs xs.length do
    let tasks ← chunk.mapM fun x => IO.asTask (k x)
    for t in tasks do
      match ← IO.wait t with
      | .ok r => out := out.push r
      | .error e => out := out.push (#[s!"exception: {e}"], "exception")
  return out.toList

def suite : List TestSeq := [
  .individualIO "aux-cert: A0 fixtures through both compilers and three checkers"
    none (do
    for exe in [ixExe, certExe] do
      unless ← exe.pathExists do
        return (false, 0, 0, some s!"{exe} missing — run `lake build ix kernel-check-ixe`")
    let jobs := ((← IO.getEnv "AUX_CERT_JOBS").bind String.toNat?).getD 4
    let only := ((← IO.getEnv "AUX_CERT_ONLY").map (·.splitOn ",")).getD []
    let fs := if only.isEmpty then fixtures else fixtures.filter (only.contains ·.stem)
    let results ← mapPool jobs fs runFixture
    let mut failedN := 0
    for (f, (problems, summary)) in fs.zip results do
      if problems.isEmpty then
        IO.println s!"[aux-cert] {f.stem}: ok — {summary}"
      else
        failedN := failedN + 1
        IO.println s!"[aux-cert] FAIL {f.stem} — {summary}"
        for p in problems do IO.println s!"[aux-cert]   {p}"
    let n := fs.length
    return (failedN == 0, n - failedN, n,
      if failedN == 0 then none else some s!"{failedN} fixture(s) differ from the record"))
    .done
]

end Tests.Ix.Compile.AuxCert
