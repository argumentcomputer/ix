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

  1. `ix compile <file> --no-build --local` and `ix compile-lean <file>
     --rust-check --local`, run concurrently. `--local` compiles the
     fixture's own constants with their dependency closure instead of the
     whole import environment (Init, 117k constants, or Lean for
     `SortUDecl`): a block's compiled form depends only on its closure, so
     the fixture's constants come out as in a whole-file compile, without
     recompiling Init twice per fixture (the whole-file suite took about 33
     minutes at 4-way). `AUX_CERT_WHOLE=1` runs the whole-file compiles
     instead and adds the bridge between the two scopes: a third compile,
     `ix compile --local`, whose every named entry (address, metadata,
     original, hints) must equal the whole-file entry, and which must hold
     every fixture-owned name of the whole-file output.
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
     (an unexpected pass is reported, so the record stays exact); a large
     uniform class is recorded by its exact count (`knownCounts`). Every leg
     must check every fixture constant (check-lean: all but the selectors it
     reports as matching nothing).
  3. Required and forbidden names in the output (`NestMutGroup`: exactly the
     two nested auxiliaries Lean has).

  The output's names are read from its own named section (all of them):
  the required and forbidden names, the constants handed to `check-lean`, and
  the attribution of a certified-checker failure to every fixture name of the
  failing record (a projection belongs to its block). The checker's rows list
  at most three names per record, chosen in hash-map order, so a suite reading
  names off the rows saw a subset that depended on the rest of the
  environment.

  The `rfl` theorems in the fixtures are the value pins: the only checks
  that see a meaning change (WB-B4's `fg_ab`), since `--rust-check` and
  `validate` compare the compilers with each other, not with Lean.

  Run with: `lake test -- --ignored aux-cert` (after `lake build ix
  kernel-check-ixe`). `AUX_CERT_JOBS` sets the fixture parallelism (default
  4); `AUX_CERT_ONLY` restricts to a comma-separated list of fixture stems;
  `AUX_CERT_WHOLE=1` selects the whole-file scope (above). The verdict lines
  are the same in both scopes; `[aux-cert] time` lines report each
  fixture's wall time.
-/
import Lean.Data.Json
import Tests.Ix.Compile.KernelReport
import LSpec
import Ix.Ixon

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
      reject or undocumented decline), by exact name. -/
  knownFails : List (String × String × String) := []
  /-- A large uniform class of failures on one leg, beyond `knownFails`:
      `(leg, defect, count)`; exactly `count` other constants fail on that
      leg, and for a meta-mode-only defect (BB-F7, BB-F1) the certified
      checker accepts each of them. -/
  knownCounts : List (String × String × Nat) := []
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
  -- the eta-wrapped partial applications of collapsed recursors. Until M6R
  -- slice 6 the legacy surgery refused `SurgCollapse` ("collapse call site
  -- drops distinct arguments") and the eta-wrapped two ("collapse call site is
  -- a partial application"); Pass 3 uses source-telescope images and
  -- the faithful rewrite instead of that argument adaptation.
  -- Rechecked against e020a72e in Pass 3: identical artifact and all kernel
  -- verdicts. BB-F7: 71 unknown constants, B.g app mismatch, three unmatched aliases.
  { stem := "SurgCollapse", ns := ["SurgCollapse"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 75)] },
  { stem := "SurgCollapseEq", ns := ["SurgCollapseEq"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 77)] },
  -- Same base comparison: 56 unknown constants and three unmatched aliases.
  { stem := "F4FlatAlphaUsers", ns := ["F4FlatAlphaUsers"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 59)] },
  -- Same base comparison: 76 unknown constants and four unmatched aliases.
  { stem := "F4_NestedAlphaUsers", ns := ["A", "B", "r", "t", "sizeL", "sizeLA"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 80)] },
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
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress; F1Pair, F1Ring, \
      F1Triple, F4Flat)", 357)] },
  -- Reproducers that compile cleanly (the audits' refuted leads).
  { stem := "BetaField", ns := ["BetaField"] },
  { stem := "DotCtor", ns := ["DotCtor"] },
  { stem := "EvapClosure", ns := ["EvapClosure"] },
  { stem := "F2_SplitNestedClosure", ns := ["A", "B"] },
  -- Metadata on the index spine and in constructor field domains (`a98663c0`),
  -- with elaborated neighbours (`MdataSpine.Plain*`).
  { stem := "MdataSpine", ns := ["MdataSpine"] },
  -- WB §6: the certified checker declines the reflexive nested `R`
  -- (its documented modeller limitation); its dependents are blocked.
  { stem := "NestShapes", ns := ["NestShapes"]
    knownFails := kf "cert" "WB §6 (certified: reflexive nested decline)" ["NestShapes.R"]
    knownCounts := [("cert", "WB §6 (blocked by NestShapes.R)", 29)] },
  -- Compiled, with constants a checker rejects: totality defects outside
  -- A0, recorded by id. The legacy surgery's defects (WB-B2 on `Coind`,
  -- `PropSplit`, `L2_PropSplit` and `PropCollapse.p_cases` for `rs` and
  -- `cert`; WB-B3 on `SurgSplit`; WB-B5's `SurgAlias.f`, `f1`) went with it
  -- at M6R slice 6: Pass 3's output passes every checker there.
  { stem := "Coind", ns := ["Coind"] },
  { stem := "PropSplit", ns := ["PropSplit"] },
  { stem := "PropCollapse", ns := ["PropCollapse"]
    knownFails := kf "lean" "WB-B2" ["PropCollapse.p_cases"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 32)] },
  { stem := "L2_PropSplit", ns := ["A", "B", "ua"] },
  { stem := "RecAlias", ns := ["RecAlias"]
    knownFails := kf "rs" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] ++
      kf "lean" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] ++
      kf "cert" "WB-B6" ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2",
        "RecAlias.PA.triv"] },
  { stem := "SurgAlias", ns := ["SurgAlias"]
    knownFails :=
      kf "rs" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.A.a.sizeOf_spec"] ++
      kf "lean" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.A.a.sizeOf_spec"] ++
      kf "cert" "WB-B5" ["SurgAlias.A._sizeOf_1", "SurgAlias.A._sizeOf_inst",
        "SurgAlias.A.a.sizeOf_spec", "SurgAlias.A.nil.sizeOf_spec"] },
  { stem := "SurgSplit", ns := ["SurgSplit"] },
  { stem := "UnsafeI", ns := ["UnsafeI"]
    knownFails := kf "rs" "WB-B9" ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] ++
      kf "lean" "WB-B9" ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] },
  { stem := "F1_Collapse2p1", ns := ["A", "B", "C"]
    knownCounts := [("rs", "BB-F1 (metadata of collapsed aliases)", 71),
      ("lean", "BB-F1, BB-F7", 93)] },
  -- CORPUS-IPB (M1-j, owner 2026-10-06): a Prop block whose collapse merges
  -- members with alpha-equivalent Lean `.below` inductives is refused in both
  -- compilers (the corpus shapes `M3_P_alpha2p1`, `M4_P_mixed`): by Pass 3's
  -- images ("image: hypothesis motive N not in its slot's class", "image: no
  -- eliminator for Lean motive N"; until M6R slice 6 the legacy surgery's
  -- `REFUSED-IPB-COLLAPSE`). Valid
  -- neighbours: `IPBCollapseNone` (the same block without the pair),
  -- `F1_Collapse2p1` (the `Type` version, above) and `PropCollapse` (a full
  -- Prop collapse whose `.below` members stay distinct).
  { stem := "IPBCollapse2p1", ns := ["IPBCollapse2p1"]
    expect := .refuses "image: " },
  { stem := "IPBMixed", ns := ["IPBMixed"]
    expect := .refuses "image: " },
  { stem := "IPBCollapseNone", ns := ["IPBCollapseNone"] },
  { stem := "F5_SigmaNestedNested", ns := ["T"]
    knownFails := ["rs", "lean"].flatMap fun leg =>
      kf leg "BB-F5 (kernel completeness)" ["T.rec", "T.rec_1", "T.rec_2"] },
  { stem := "F7_AlphaVLean", ns := ["A", "B"]
    knownCounts := [("lean", "BB-F7 (collapsed block in Ix.Tc meta ingress)", 59)] },
  -- Expected compile failures outside A0 (totality defects).
  { stem := "AliasIdx", ns := ["AliasIdx"]
    expect := .xfail "WB-A3" "function expected, got Sort u" },
  { stem := "KernelSpec", ns := ["KernelSpec"]
    expect := .xfail "WB-A7" "is_large_eliminator failed" },
  -- The legacy surgery's totality defects (WB-A2 "found no residual Pi
  -- binders" on `SurgIdx`, `F6_OrderIdxBrecOn`; BB-F8 "source recursor has no
  -- elimination level" on `F8_PropSplitNested`) went with it at M6R slice 6:
  -- Pass 3 compiles the three.
  { stem := "SurgIdx", ns := ["SurgIdx", "SurgIdx2"] },
  { stem := "F6_OrderIdxBrecOn", ns := ["A", "B"] },
  { stem := "F8_PropSplitNested", ns := ["A", "B", "PBox"] },
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
    the toolchain's `LD_LIBRARY_PATH` (see `Tests.Cli.spawnEnv`); `IX_PASS3` is
    unset, so both compilers run Pass 3, their only mode since M6R slice 6 (the
    record above was measured with the legacy surgery, `IX_PASS3=off`, until
    then, and re-measured under Pass 3 at slice 6). -/
private def spawnEnv : Array (String × Option String) :=
  #[("LD_LIBRARY_PATH", none), ("IX_PASS3", none)]

private def run (cmd : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let exe ← IO.FS.realPath cmd
  IO.Process.output { cmd := exe.toString, args, env := spawnEnv }

private def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  return (out.stdout.splitOn " ").headD ""

private def owns (f : Fixture) (name : String) : Bool :=
  f.ns.any fun p => name == p || name.startsWith (p ++ ".")

private def known (f : Fixture) (leg name : String) : Option String :=
  f.knownFails.findSome? fun (l, n, d) =>
    if l == leg && n == name then some d else none

/-- The record the certified checker reports the constant at `addr` under:
    the block of a projection, else the constant itself (mirrors
    `Benchmarks.Kernel.CheckIxeStep.owner`). -/
def recordOf (env : Ixon.Env) (addr : Address) : Address :=
  match (env.consts.get? addr).bind (·.get?) with
  | some c => match c.info with
    | .dPrj p => p.block
    | .iPrj p => p.block
    | .rPrj p => p.block
    | .cPrj p => p.block
    | _ => addr
  | none => addr

/-- The bridge between the two scopes (`AUX_CERT_WHOLE=1`): `ix compile
    --local` must succeed, every named entry of its output (address,
    metadata, original, hints) must be the whole-file output's entry for that
    name, and the local output must hold every fixture-owned name `mine` of
    the whole-file output. -/
def scopeBridge (src : String) (wholeEnv : Ixon.Env) (localOut : System.FilePath)
    (mine : List String) : IO (Array String) := do
  let r ← run ixExe #["compile", src, "--no-build", "--local", "--out", localOut.toString]
  if r.exitCode != 0 then
    return #[s!"bridge: ix compile --local exit {r.exitCode}: \
{((r.stdout ++ r.stderr).takeEnd 300).toString}"]
  let load (p : System.FilePath) : IO Ixon.Env := do
    IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile p))
  let localEnv ← load localOut
  let mut problems : Array String := #[]
  let mut differing : Nat := 0
  for (n, named) in localEnv.named do
    if wholeEnv.named.get? n != some named then
      differing := differing + 1
      if differing ≤ 5 then
        problems := problems.push s!"bridge: {n} differs between the local and whole-file outputs"
  if differing > 5 then
    problems := problems.push s!"bridge: … {differing} differing entries in all"
  let localNames : Std.HashSet String :=
    localEnv.named.fold (fun s n _ => s.insert (toString n)) {}
  for n in mine do
    unless localNames.contains n do
      problems := problems.push s!"bridge: {n} is in the whole-file output, not the local one"
  return problems

/-- Runs one fixture; returns its problems (empty: as recorded) and a
    one-line summary. -/
def runFixture (whole : Bool) (f : Fixture) : IO (Array String × String) := do
  let src := s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean"
  let dir ← IO.FS.createTempDir
  let mut problems : Array String := #[]
  try
    let rsOut := dir / "rs.ixe"
    let leanOut := dir / "lean.ixe"
    -- The two compiles are independent processes: run them concurrently.
    let scope : Array String := if whole then #[] else #["--local"]
    let rsTask ← IO.asTask (prio := .dedicated) (run ixExe
      (#["compile", src, "--no-build", "--out", rsOut.toString] ++ scope))
    let runLean := match f.expect with
      | .xfail _ _ false => false
      | _ => true
    let ln : IO.Process.Output ← if runLean then
        run ixExe (#["compile-lean", src, "--rust-check", "--out", leanOut.toString] ++ scope)
      else pure { exitCode := (0 : UInt32), stdout := "", stderr := "" }
    let rs ← IO.ofExcept (← IO.wait rsTask)
    let rsText := rs.stdout ++ rs.stderr
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
      if ← leanOut.pathExists then
        problems := problems.push "ix compile-lean wrote an output for a refused fixture"
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
    -- `check-rs` needs only the output: run it alongside the certified checker.
    let rsCheckTask ← IO.asTask (prio := .dedicated)
      (run ixExe #["check-rs", rsOut.toString, "--ns", ",".intercalate f.ns,
        "--fail-out", (dir / "rs.fail").toString])
    -- The output's names come from its own named section, complete: the
    -- certified checker's rows list at most three names per record, chosen
    -- in hash-map order, which depends on the rest of the environment.
    let outEnv ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile rsOut))
    let allNames : List String :=
      (outEnv.named.toArray.map (toString ·.1)).qsort (· < ·) |>.toList
    let mine := allNames.filter (owns f)
    -- A name belongs to the record the checker reports it under: its
    -- constant, or the block of a projection (`CheckIxeStep.owner`).
    let mut byRecord : Std.HashMap String (Array String) := {}
    for (n, named) in outEnv.named do
      let s := toString n
      if owns f s then
        let key := toString (recordOf outEnv named.addr)
        byRecord := byRecord.insert key ((byRecord.getD key #[]).push s)
    -- The certified checker.
    let certPath := dir / "cert.jsonl"
    let cert ← run certExe #[rsOut.toString, certPath.toString, "--jobs", "8"]
    let rsCheck ← IO.ofExcept (← IO.wait rsCheckTask)
    IO.FS.writeFile (dir / "cert.stdout") cert.stdout
    IO.FS.writeFile (dir / "cert.stderr") cert.stderr
    unless ← certPath.pathExists do
      throw (IO.userError s!"kernel-check-ixe wrote no report (exit {cert.exitCode})")
    let report ← IO.ofExcept (KernelReport.parse (← IO.FS.readFile certPath) cert.exitCode)
    let expected := byRecord.toArray.flatMap fun (address, ns) => ns.map (·, address)
    IO.ofExcept (KernelReport.checkCoverage report expected)
    if whole then
      problems := problems ++ (← scopeBridge src outEnv (dir / "local.ixe") mine)
    for n in f.requireNames do
      unless allNames.contains n do problems := problems.push s!"output lacks {n}"
    for n in f.forbidNames do
      if allNames.contains n then problems := problems.push s!"output has {n}"
    -- Observed failures per leg.
    let mut failed : Array (String × String × String) := #[]
    for (address, verdict) in report do
      if verdict.outcome == "accept" then continue
      if verdict.outcome == "decline" && documentedDecline verdict.reason then continue
      for n in byRecord.getD address #[] do
        failed := failed.push ("cert", n, s!"{verdict.outcome}: {verdict.reason}")
    -- every check-rs failure from its fail-out file (stdout shows the first 30)
    let rsRows ← if ← (dir / "rs.fail").pathExists then
        pure (KernelReport.failOutRows (← IO.FS.readFile (dir / "rs.fail")))
      else pure #[]
    for (n, m) in rsRows do
      failed := failed.push ("rs", n, m)
    if rsCheck.exitCode != 0 && rsRows.isEmpty then
      failed := failed.push ("rs", "*", s!"check-rs exit {rsCheck.exitCode}")
    let namesFile := dir / "names.txt"
    IO.FS.writeFile namesFile ("\n".intercalate mine ++ "\n")
    let failOut := dir / "lean.fail"
    -- Match the Pass 3 kernel gate: start each requested item with fresh
    -- worker state. A warm cache can resolve a collapsed alias through an
    -- earlier item's type, masking BB-F7 failures in scheduling order.
    let leanCheck ← run ixExe #["check-lean", rsOut.toString, "--consts-file",
      namesFile.toString, "--fail-out", failOut.toString, "--workers", "8",
      "--clear-every", "1"]
    IO.FS.writeFile (dir / "lean.stdout") leanCheck.stdout
    IO.FS.writeFile (dir / "lean.stderr") leanCheck.stderr
    if leanCheck.exitCode == 0 || leanCheck.exitCode == 3 then
      discard <| IO.ofExcept (KernelReport.checkedLeanTargets leanCheck.stdout)
    let leanFails ← if ← failOut.pathExists then
        pure (KernelReport.leanFailureLabels (← IO.FS.readFile failOut) false)
      else pure #[]
    for n in KernelReport.leanUnmatched (leanCheck.stdout ++ leanCheck.stderr) do
      failed := failed.push ("lean", n, "requested selector matched no checkable work item")
    let leanMsgs ← if ← failOut.pathExists then
        pure (KernelReport.failOutRows (← IO.FS.readFile failOut))
      else pure #[]
    for n in leanFails do
      let n := n.trimAscii.toString
      failed := failed.push ("lean", n, ((leanMsgs.find? (·.1 == n)).map (·.2)).getD "")
    if leanFails.isEmpty && leanCheck.exitCode != 0 then
      failed := failed.push ("lean", "*", s!"check-lean exit {leanCheck.exitCode}")
    -- `AUX_CERT_FAILURES=<file>`: every failure, one row `stem leg name message`
    if let some file := ← IO.getEnv "AUX_CERT_FAILURES" then
      let leanN := (KernelReport.checkedLeanTargets leanCheck.stdout).toOption.getD 0
      let rsN := (KernelReport.rsChecked (rsCheck.stdout ++ rsCheck.stderr)).getD 0
      -- one write per fixture: the fixtures run concurrently
      let mut out := s!"#checked\t{f.stem}\t{mine.length}\t{expected.size}\t{rsN}\t{leanN}\n"
      for (leg, n, m) in failed do
        out := out ++ s!"{f.stem}\t{leg}\t{n}\t{(m.replace "\n" " | ").replace "\t" " "}\n"
      let h ← IO.FS.Handle.mk file .append
      h.putStr out
      h.flush
    -- every failure is recorded: by name, or within a leg's recorded count
    -- (a meta-mode-only class only where the certified checker accepts)
    let certFail := failed.filterMap fun (l, n, _) => if l == "cert" then some n else none
    for leg in ["cert", "rs", "lean"] do
      let rest := failed.filter fun (l, n, _) => l == leg && (known f leg n).isNone
      match f.knownCounts.find? (·.1 == leg) with
      | some (_, d, count) =>
        if rest.size != count then
          problems := problems.push s!"{leg}: {rest.size} failure(s) beyond the named ones, \
            recorded {count} ({d})"
        if (hasSub d "BB-F7" || hasSub d "BB-F1") then
          for (_, n, _) in rest do
            if certFail.contains n then
              problems := problems.push s!"{leg}: {n} counted as {d}, but the certified checker rejects it"
      | none =>
        for (_, n, m) in rest do
          problems := problems.push s!"{leg}: {n} fails, not recorded: {m.take 200}"
    for (leg, n, d) in f.knownFails do
      unless failed.any (fun (l, m, _) => l == leg && m == n) do
        problems := problems.push s!"{leg}: {n} recorded as failing ({d}) but passes"
    -- every leg checks every fixture constant (check-lean: but the selectors it
    -- reports as matching nothing; nothing where its ingress stops, a `*` failure)
    let unmatched := (failed.filter fun (l, _, m) =>
      l == "lean" && m == "requested selector matched no checkable work item").size
    let leanStops := failed.any fun (l, n, _) => l == "lean" && n == "*"
    let leanN := (KernelReport.checkedLeanTargets leanCheck.stdout).toOption.getD 0
    let rsN := (KernelReport.rsChecked (rsCheck.stdout ++ rsCheck.stderr)).getD 0
    for (leg, k, want) in [("cert", expected.size, mine.length), ("rs", rsN, mine.length),
        ("lean", leanN, if leanStops then 0 else mine.length - unmatched)] do
      if k != want then
        problems := problems.push s!"{leg} checked {k} constant(s), expected {want}"
    let nKnown := failed.size
    return (problems, s!"compiled, ALIGNED, {mine.length} names, {nKnown} recorded failure(s)")
  finally
    IO.FS.removeDirAll dir

/-- Runs `xs` on `jobs` workers that each take the next unstarted item (no
    straggler waits between batches), keeping the order of the results. -/
private def mapPool (jobs : Nat) (xs : List Fixture)
    (k : Fixture → IO (Array String × String)) : IO (List (Array String × String)) := do
  let items := xs.toArray
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate items.size (#["not run"], "not run"))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < items.size then
        let r ← try k items[i] catch e => pure (#[s!"exception: {e}"], "exception")
        results.modify (·.set! i r)
      else break
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask (prio := .dedicated) worker
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e
  return (← results.get).toList

def suite : List TestSeq := [
  .individualIO "aux-cert: A0 fixtures through both compilers and three checkers"
    none (do
    for exe in [ixExe, certExe] do
      unless ← exe.pathExists do
        return (false, 0, 0, some s!"{exe} missing — run `lake build ix kernel-check-ixe`")
    let jobs := ((← IO.getEnv "AUX_CERT_JOBS").bind String.toNat?).getD 4
    let only := ((← IO.getEnv "AUX_CERT_ONLY").map (·.splitOn ",")).getD []
    let whole := ((← IO.getEnv "AUX_CERT_WHOLE").map (· != "0")).getD false
    let fs := if only.isEmpty then fixtures else fixtures.filter (only.contains ·.stem)
    IO.println s!"[aux-cert] {fs.length} fixtures, {jobs} jobs, \
{if whole then "whole-file scope with the local bridge" else "local scope"}"
    let t0 ← IO.monoMsNow
    let results ← mapPool jobs fs fun f => do
      let t ← IO.monoMsNow
      let r ← runFixture whole f
      IO.println s!"[aux-cert] time {f.stem}: {(← IO.monoMsNow) - t} ms"
      return r
    let mut failedN := 0
    for (f, (problems, summary)) in fs.zip results do
      if problems.isEmpty then
        IO.println s!"[aux-cert] {f.stem}: ok — {summary}"
      else
        failedN := failedN + 1
        IO.println s!"[aux-cert] FAIL {f.stem} — {summary}"
        for p in problems do IO.println s!"[aux-cert]   {p}"
    IO.println s!"[aux-cert] wall time: {(← IO.monoMsNow) - t0} ms"
    let n := fs.length
    return (failedN == 0, n - failedN, n,
      if failedN == 0 then none else some s!"{failedN} fixture(s) differ from the record"))
    .done
]

end Tests.Ix.Compile.AuxCert
