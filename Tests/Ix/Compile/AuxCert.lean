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
     (an unexpected pass is reported, so the record stays exact).
  3. Required and forbidden names in the output (`NestMutGroup`: exactly the
     two nested auxiliaries Lean has).
  4. For the canonical-layout fixtures (`NestedLevels`, `CanonSiblingNest`,
     which live in `Tests/Ix/Compile/Fixtures/`): every record holding a
     fixture name is accepted by the certified checker (no decline at all,
     documented or not); names that must share one compiled address (the
     two presentations of a block, its collapsed members, the canonical
     recursors and auxiliary under their `_ix` display names when the block
     changed); recursor blocks of an exact size (one class and one
     canonical auxiliary); and the Lean names that must hold Pass 3 images
     (a definition with `Named.original`).
  5. AuxGen M5c's shadow leg, on a compiled fixture: `ix compile-lean` again
     under `IX_AUXGEN_IXC=shadow` (each safe block's aux tail asks both
     kernels and uses `Ix.Tc`'s answers), after the production compile and
     alongside the checks. Its output must equal production's byte for byte
     (production is `failClosed`, IxC's answers alone), and its traced counts
     must show no IxC answer, decision or recursor `whnf` different from
     `Ix.Tc`'s and no refusal on a block Source mode accepts: the stop rule
     (`shadowCheck`; a block it does not accept retries on `fallback`).

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
  /-- File stem under `Tests/Ix/Compile/AuxCert/` (the fixture's label
      when `src` names its file). -/
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
  /-- The source file, when it is not `Tests/Ix/Compile/AuxCert/<stem>.lean`. -/
  src : Option String := none
  /-- Every record holding a fixture name must be accepted by the certified
      checker: a decline fails even in a documented class. -/
  certAccepts : Bool := false
  /-- Groups of names that must have one compiled address each. -/
  sameAddress : List (List String) := []
  /-- `(name, n)`: the name is a projection into a block of exactly `n`
      members. -/
  blockSizes : List (String × Nat) := []
  /-- Names that must hold Pass 3 images: a definition carrying
      `Named.original` (Lean's own form of the auxiliary), the Lean name of an
      auxiliary of a changed block whose Ix form is under its `_ix` display
      name. -/
  images : List String := []
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

/-- A name of `Tests.Ix.Compile.Fixtures.NestedLevels`: `family`'s
    presentation `p`, then `m`. -/
def nestedLevelsName (family p m : String) : String :=
  s!"Tests.Ix.Compile.Fixtures.NestedLevels.{family}.{p}.{m}"

/-- `NestedLevels`, per family: the two presentations' members (one class:
    `Left` and `Right` collapse), their constructors and their canonical
    recursors share one address each, and the canonical auxiliary is one.
    The block is changed (its class collapses two members), so Pass 3
    stores its Ix recursors under their `_ix` display names
    (`Ix.Compile.Pass.ixAuxName`): each member's `x._ix.rec`, and the one
    canonical auxiliary at its canonical position under the component's
    first class representative (`Mixed`: `A.Right._ix.rec_1`,
    `B.Left._ix.rec_1`; `Neighbour`: `A.Right._ix.rec_1`, `B.Right._ix.rec_1`;
    every source `rec_N` of both presentations is displayed there; Lean
    numbers `Mixed`'s three occurrences and `Neighbour`'s two). The Lean
    names hold the images (`nestedLevelsImages`), which follow the
    presentation's member order, so they are compared by the twins record
    (`NonCanonicalDefault`, `IMAGE`), not here. -/
def nestedLevelsSame : List (List String) :=
  [("Mixed", "Left"), ("Neighbour", "Right")].flatMap fun (family, repB) =>
    let both := fun (suffix : String) =>
      ["A", "B"].flatMap fun p =>
        ["Left", "Right"].map fun m => nestedLevelsName family p (m ++ suffix)
    [both "", both ".mk", both "._ix.rec",
     [nestedLevelsName family "A" "Right._ix.rec_1", nestedLevelsName family "B" s!"{repB}._ix.rec_1"]]

/-- `NestedLevels`' canonical recursor blocks: one class and one canonical
    auxiliary. -/
def nestedLevelsBlocks : List (String × Nat) :=
  ["Mixed", "Neighbour"].flatMap fun family =>
    ["A", "B"].map fun p => (nestedLevelsName family p "Left._ix.rec", 2)

/-- `NestedLevels`' Lean recursors, every one an image: both members' `rec`,
    and the source `rec_N` (hanging off the first member Lean lists: `Left`
    in `A`, `Right` in `B`). -/
def nestedLevelsImages : List String :=
  [("Mixed", 3), ("Neighbour", 2)].flatMap fun (family, nAux) =>
    (["A", "B"].flatMap fun p => ["Left", "Right"].map fun m => nestedLevelsName family p (m ++ ".rec")) ++
    (List.range nAux).flatMap fun j =>
      [nestedLevelsName family "A" s!"Left.rec_{j + 1}",
       nestedLevelsName family "B" s!"Right.rec_{j + 1}"]

-- The fixture record (filled from the A0 survey on 2026-10-03, Lean
-- 4.34.1; expected behaviours from `plans/replan/D-evidence-digest.md` §2,
-- `audit-whitebox-5.md` and `audit-blackbox-final.md`).
def fixtures : List Fixture := [
  -- A0 item 1 (WB-B4): the collapse refusal, its equal-arms neighbour, and
  -- the eta-wrapped partial applications of collapsed recursors. Until Pass 3
  -- the call-site surgery refused `SurgCollapse` ("collapse call site drops
  -- distinct arguments") and the eta-wrapped two ("collapse call site is a
  -- partial application"); Pass 3 rewrites the callers through images
  -- instead, so all four compile (the donor's record after its flip).
  { stem := "SurgCollapse", ns := ["SurgCollapse"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  { stem := "SurgCollapseEq", ns := ["SurgCollapseEq"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  { stem := "F4FlatAlphaUsers", ns := ["F4FlatAlphaUsers"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  { stem := "F4_NestedAlphaUsers", ns := ["A", "B", "r", "t", "sizeL", "sizeLA"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  -- A0 item 2 (WB-B1, A5/C3, C1): the user's names stay the user's.
  { stem := "FieldBelow", ns := ["FieldBelow"] },
  { stem := "FieldBelowRace", ns := ["FieldBelowRace"] },
  { stem := "L1_UserBelowName", ns := ["T", "use_below"] },
  { stem := "SurgName", ns := ["SurgName"] },
  -- A0 item 3 (WB-B8): no forced large elimination.
  { stem := "SortUDecl", ns := ["SortUD"] },
  -- A nested Prop inductive whose `IndPredBelow` family has `P.below_1.rec`:
  -- its original form compiles the same in both compilers.
  { stem := "BelowNRec", ns := ["BelowNRec"] },
  -- CQ3.1 (D-09): a nested `Sort u` singleton whose expanded block has two
  -- members eliminates into Prop only, as in Lean (lane P `6327e496`).
  -- `Box T` is nested under the definition `K`; the kernels find it there
  -- (D-14) and accept the two-motive recursors. The certified checker's
  -- modeller takes the field as an ordinary one since CQX.8 (no member left
  -- once its carriers are rewritten), then declines the block: a non-`Prop`
  -- nested block with a small eliminator (its `_impl.unpack` eliminates into
  -- `Sort u`). The block's dependents are blocked on it.
  { stem := "NestedSortU", ns := ["NestedSortU"]
    knownFails :=
      kf "cert" "IxC modeller: a non-Prop nested block with a small eliminator (decline)"
        ["NestedSortU.T", "NestedSortU.T.mk", "NestedSortU.T.rec", "NestedSortU.T.rec_1",
          "NestedSortU.t_rec"] },
  -- CQX.8: `T`'s field `K True (Box T)` mentions the block only before
  -- whnf. The Rust kernel tests positivity after whnf, as Lean does, and
  -- accepts `T` and its recursors (D-14 finds `Box T` under `K`); `Ix.Tc`
  -- still rejects the block (not fixed: deleted in CQX.2). The certified
  -- checker's modeller passes the field since CQX.8 and declines the block
  -- as `NestedSortU`'s (a non-`Prop` nested block with a small eliminator).
  { stem := "NestedSortUK", ns := ["NestedSortUK"]
    knownFails :=
      kf "lean" "CQX.8 (Ix.Tc tests positivity before whnf; not fixed, CQX.2)"
        ["NestedSortUK.T", "NestedSortUK.T.*"] ++
      kf "cert" "IxC modeller: a non-Prop nested block with a small eliminator (decline)"
        ["NestedSortUK.T", "NestedSortUK.T.mk", "NestedSortUK.T.rec", "NestedSortUK.T.rec_1",
          "NestedSortUK.t_rec"] },
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
  -- Metadata on the index spine and in constructor field domains (spine walks),
  -- with elaborated neighbours (`MdataSpine.Plain*`).
  { stem := "MdataSpine", ns := ["MdataSpine"] },
  -- WB §6: the certified checker declines the reflexive nested `R`
  -- (its documented modeller limitation); its dependents are blocked.
  { stem := "NestShapes", ns := ["NestShapes"]
    knownFails := kf "cert" "WB §6 (certified: reflexive nested decline)"
      ["NestShapes.R", "NestShapes.R.*"] },
  -- Compiled, with constants a checker rejects: totality defects outside
  -- A0, recorded by id.
  -- The call-site surgery's defects (WB-B2 on `Coind`, `PropSplit`,
  -- `L2_PropSplit` and `PropCollapse.p_cases`; WB-B3 on `SurgSplit`; WB-B5 on
  -- `SurgAlias`) went with it: Pass 3's output passes every checker there.
  -- WB-B5 was the split-minor adapter's syntactic test for a recursive field,
  -- which missed `Id' B` and so mis-adapted `A.rec`'s calls in `SurgAlias.f`,
  -- `f1` and the `sizeOf` family (`A._sizeOf_1`, `_sizeOf_inst`,
  -- `a.sizeOf_spec`, `nil.sizeOf_spec`); Pass 3 develops `A.rec`'s image
  -- instead, with no syntactic test, and every leg accepts them (the box's
  -- run of the flip, 2026-10-20; the donor kept the `sizeOf` rows).
  { stem := "Coind", ns := ["Coind"] },
  { stem := "PropSplit", ns := ["PropSplit"] },
  { stem := "PropCollapse", ns := ["PropCollapse"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress), WB-B2" ["*"] },
  { stem := "L2_PropSplit", ns := ["A", "B", "ua"] },
  -- WB-B6: a recursive field behind a reducible alias (`Id' (PA n)`, and
  -- `Branches Higher`, an alias of a function telescope). The Prop `.below`
  -- family is built from the recursor's minor premises, so every leg accepts.
  { stem := "RecAlias", ns := ["RecAlias"] },
  { stem := "SurgAlias", ns := ["SurgAlias"] },
  { stem := "SurgSplit", ns := ["SurgSplit"] },
  -- WB-A3: the nested auxiliary's index sits behind a reducible alias;
  -- both recursor generators peel it through `whnf`.
  { stem := "AliasIdx", ns := ["AliasIdx"] },
  -- CQ3.3 (SP5): the canonical layout's fixtures (in `Fixtures/`).
  -- `NestedLevels`: in each family `Left` and `Right` collapse into one
  -- class, and its occurrences are one canonical auxiliary up to compiled
  -- addresses and `canonUniv` levels (`Mixed`'s `List.{max 0 0}` and
  -- `List.{0}`), so the certified checker reads one container group: it
  -- declined `Mixed` before CQ3.3 (SP5 §3.1). `CanonSiblingNest`:
  -- occurrences of the members of an external mutual group.
  { stem := "NestedLevels", ns := ["Tests.Ix.Compile.Fixtures.NestedLevels"]
    src := some "Tests/Ix/Compile/Fixtures/NestedLevels.lean"
    certAccepts := true, sameAddress := nestedLevelsSame, blockSizes := nestedLevelsBlocks
    images := nestedLevelsImages },
  { stem := "CanonSiblingNest", ns := ["CanonSiblingNest"]
    src := some "Tests/Ix/Compile/Fixtures/CanonSiblingNest.lean"
    certAccepts := true },
  -- WB-B9 and BB-F5 were the kernels' head-only nested discovery (D-14):
  -- `UNestNeg`'s and `T`'s occurrences sit under a binder or a
  -- non-inductive head, and both kernels now find them.
  { stem := "UnsafeI", ns := ["UnsafeI"] },
  { stem := "F1_Collapse2p1", ns := ["A", "B", "C"]
    knownFails := kf "rs" "BB-F1 (metadata of collapsed aliases)" ["*"] ++
      kf "lean" "BB-F1, BB-F7" ["*"] },
  { stem := "F5_SigmaNestedNested", ns := ["T"] },
  { stem := "F7_AlphaVLean", ns := ["A", "B"]
    knownFails := kf "lean" "BB-F7 (collapsed block in Ix.Tc meta ingress)" ["*"] },
  -- WB-A7, fixed by CQ3.1: `P`'s elimination is decided by the kernels'
  -- rule before the field probe, which failed on the auxiliary `And P P`
  -- the bridge's kernel does not hold. `T` (`Id (List T)`) is nested under
  -- a definition; the kernels find it there (D-14) and accept the
  -- two-motive recursors, while the certified checker's modeller declines
  -- the block (one inductive hypothesis for no syntactically recursive
  -- field, SP5 §3.5), blocking its dependents.
  { stem := "KernelSpec", ns := ["KernelSpec"]
    knownFails :=
      kf "cert" "IxC modeller: nested under a definition (SP5 §3.5; decline)"
        ["KernelSpec.T", "KernelSpec.T.*"] },
  -- Until Pass 3 these failed in the call-site surgery: WB-A2 (`SurgIdx`,
  -- BB-F6 `F6_OrderIdxBrecOn`: the eta adapter "found no residual Pi
  -- binders") and BB-F8 (`F8_PropSplitNested`: `B.below` read `A.below_1`
  -- from the other SCC). Pass 3 rewrites the callers through images; all
  -- three compile (the donor's record after its flip).
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
    the toolchain's `LD_LIBRARY_PATH` (see `Tests.Cli.spawnEnv`). -/
private def spawnEnv : Array (String × Option String) := #[("LD_LIBRARY_PATH", none)]

private def run (cmd : System.FilePath) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let exe ← IO.FS.realPath cmd
  IO.Process.output { cmd := exe.toString, args, env := spawnEnv ++ env }

private def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  return (out.stdout.splitOn " ").headD ""

/-- The counts of a traced compile's `[auxgen-ixc]` lines (`IX_AUXGEN_IXC`;
    `Ix.AuxGen.IxcStats.line`, one line per safe block's tail, keyed by the
    block), summed by name over the tails whose block `skip` does not hold,
    and how many tails were summed; a pair `a/b` (`flat`, `below`) as
    `<name>Installed`/`<name>Admitted` and `<name>Refused`. -/
def tailCounts (out : String) (skip : String → Bool := fun _ => false) :
    Std.HashMap String Nat × Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  let mut tails := 0
  for line in out.splitOn "\n" do
    unless line.startsWith "[auxgen-ixc] " do continue
    let some head := (line.splitOn ": ")[0]? | continue
    let some body := (line.splitOn ": ")[1]? | continue
    unless body.startsWith "queries " do continue
    if skip (head.drop "[auxgen-ixc] ".length).toString then continue
    tails := tails + 1
    let words := (body.splitOn " ").filter (· != "") |>.toArray
    for i in [0:words.size / 2] do
      let some k := words[2 * i]? | continue
      let some v := words[2 * i + 1]? | continue
      match v.splitOn "/" with
      | [a, b] =>
        let first := if k == "flat" then "flatInstalled" else s!"{k}Admitted"
        m := m.insert first (m.getD first 0 + a.toNat!)
        m := m.insert s!"{k}Refused" (m.getD s!"{k}Refused" 0 + b.toNat!)
      | _ => m := m.insert k (m.getD k 0 + v.toNat!)
  return (m, tails)

/-- The traced counts the stop rule holds at 0 on a shadow compile (AuxGen
    M5c; `auxgen-below-ixc`'s assertions): an IxC answer, decision, recursor
    `whnf` or elimination decision different from `Ix.Tc`'s, a skipped field
    `Ix.Tc` finds recursive, a Lean-layout block whose canonical recursors are
    not Lean's, and every refusal. -/
def shadowStopCounts : List String :=
  ["differ", "decisionsDiffer", "recDiffer", "recSkipDiffer", "elimDiffer", "leanRecDiffer",
   "refused", "scopesRefused", "flatRefused", "belowRefused", "recRefused", "elimRefused"]

/-- **AuxGen M5c's shadow leg** on a compiled fixture: `ix compile-lean` again
    with every safe block's tail asking both kernels and using `Ix.Tc`'s
    answers (`IX_AUXGEN_IXC=shadow`). Its output must be production's byte for
    byte (production is `failClosed`: IxC's answers alone), and its traced
    counts must hold the stop rule (`shadowStopCounts` at 0: every IxC answer
    equal to `Ix.Tc`'s, nothing refused) on every block Source mode accepts. A
    block it does not accept re-runs on `fallback` in production (M5c's retry,
    its rows exempt unless identical), so its tail is left out; the compile
    lists those blocks (`source service, block not accepted: <block>: <why>`,
    at most 8: a ninth's refusals would count, failing closed). The problems,
    and a summary. -/
def shadowCheck (sh : IO.Process.Output) (shadowOut leanOut : System.FilePath) :
    IO (Array String × String) := do
  let text := sh.stdout ++ sh.stderr
  if sh.exitCode != 0 then
    return (#[s!"shadow compile (IX_AUXGEN_IXC=shadow): exit {sh.exitCode}: \
      {(text.takeEnd 400).toString}"], "shadow failed")
  let mut problems : Array String := #[]
  if (← sha256 shadowOut) != (← sha256 leanOut) then
    problems := problems.push "shadow compile's output differs from production's"
  let lines := text.splitOn "\n"
  let marker := "source service, block not accepted: "
  let notAccepted : List String := lines.filterMap fun l =>
    let l := l.trimAscii.toString
    if l.startsWith marker then ((l.drop marker.length).toString.splitOn ": ").head? else none
  let (c, tails) := tailCounts text (notAccepted.contains ·)
  for k in shadowStopCounts do
    let v := c.getD k 0
    if v != 0 then problems := problems.push s!"shadow: {k} {v} (stop rule)"
  if !problems.isEmpty then
    for l in (lines.filter (·.startsWith "[auxgen-ixc]   ")).take 4 do
      problems := problems.push s!"shadow sample: {(l.drop 15).toString.take 300}"
  return (problems, s!"shadow over {tails} tails ({notAccepted.length} of blocks Source does \
    not accept left out): recursor whnf {c.getD "recWhnf" 0} (stuck after β \
    {c.getD "recBeta" 0}), elimination {c.getD "elim" 0}, levels {c.getD "queries" 0}")

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

/-- Rows of a `kernel-check-ixe` jsonl file: address, names (at most three,
    for reporting), outcome, reason. -/
private def certRows (path : System.FilePath) :
    IO (Array (String × List String × String × String)) := do
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
    let address := (j.getObjValAs? String "address").toOption.getD ""
    rows := rows.push (address, names, outcome, reason)
  return rows

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

/-- The output's layout against the fixture's record: names that share one
    address (`sameAddress`), projections into blocks of an exact size
    (`blockSizes`), and Lean names that hold Pass 3 images (`images`: a
    definition with `Named.original`). Pure, so the same check runs on any
    compiler's output. -/
def layoutProblems (f : Fixture) (outEnv : Ixon.Env) : Array String := Id.run do
  let mut problems : Array String := #[]
  let namedOf : Std.HashMap String Ixon.Named :=
    outEnv.named.fold (fun m n named => m.insert (toString n) named) {}
  let addrOf (n : String) : Option Address := (namedOf.get? n).map (·.addr)
  for group in f.sameAddress do
    for n in group do
      unless namedOf.contains n do problems := problems.push s!"output lacks {n}"
    match group.filterMap addrOf with
    | a :: rest =>
      unless rest.all (· == a) do problems := problems.push s!"addresses differ within {group}"
    | [] => pure ()
  for (n, size) in f.blockSizes do
    match addrOf n with
    | none => problems := problems.push s!"output lacks {n}"
    | some a =>
      let block := recordOf outEnv a
      let members : Option Nat := if block == a then none else
        match (outEnv.consts.get? block).bind (·.get?) with
        | some c => match c.info with
          | .muts ms => some ms.size
          | _ => none
        | none => none
      unless members == some size do
        problems := problems.push
          s!"{n}: block of {(members.map toString).getD "no"} members, expected {size}"
  -- Pass 3 images: a definition with `Named.original` under the Lean name
  for n in f.images do
    match namedOf.get? n with
    | none => problems := problems.push s!"output lacks {n}"
    | some named =>
      let isDefn := match (outEnv.consts.get? named.addr).bind (·.get?) with
        | some c => (c.info matches .defn _)
        | none => false
      unless isDefn && named.original.isSome do
        problems := problems.push
          s!"{n}: not an image (a definition with Named.original; it holds \
{if isDefn then "a definition without Named.original" else "no definition"})"
  return problems

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
  let src := f.src.getD s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean"
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
    -- AuxGen M5c's shadow leg (`shadowCheck`), alongside the checks below: the
    -- fixture's module is built by now, so its nested `lake build` races nothing.
    let shadowOut := dir / "shadow.ixe"
    let shadowTask ← if lnCode == 0 then
        some <$> IO.asTask (prio := .dedicated) (run ixExe
          (#["compile-lean", src, "--out", shadowOut.toString] ++ scope)
          #[("IX_AUXGEN_IXC", some "shadow")])
      else pure none
    -- `check-rs` needs only the output: run it alongside the certified checker.
    let rsCheckTask ← IO.asTask (prio := .dedicated)
      (run ixExe #["check-rs", rsOut.toString, "--ns", ",".intercalate f.ns])
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
    let rows ← if ← certPath.pathExists then certRows certPath else pure #[]
    if rows.isEmpty then
      problems := problems.push s!"kernel-check-ixe wrote no rows (exit {cert.exitCode})"
    if whole then
      problems := problems ++ (← scopeBridge src outEnv (dir / "local.ixe") mine)
    for n in f.requireNames do
      unless allNames.contains n do problems := problems.push s!"output lacks {n}"
    for n in f.forbidNames do
      if allNames.contains n then problems := problems.push s!"output has {n}"
    -- Every record of the fixture accepted, shared addresses, block sizes,
    -- images.
    if f.certAccepts then
      let accepted : Std.HashSet String := rows.foldl (init := {}) fun s (address, _, outcome, _) =>
        if outcome == "accept" then s.insert address else s
      for (record, names) in byRecord.toList do
        unless accepted.contains record do
          problems := problems.push
            s!"cert: record {record.take 12} ({names.toList.take 3}) is not accepted"
    problems := problems ++ layoutProblems f outEnv
    -- Observed failures per leg.
    let mut failed : Array (String × String × String) := #[]
    for (address, names, outcome, reason) in rows do
      if outcome == "accept" then continue
      if outcome == "decline" && documentedDecline reason && !f.certAccepts then continue
      let ours := ((byRecord.getD address #[]).toList ++ names.filter (owns f)).eraseDups
      for n in ours do failed := failed.push ("cert", n, s!"{outcome}: {reason}")
    let rsCheck ← IO.ofExcept (← IO.wait rsCheckTask)
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
    let mut shadowSummary := ""
    if let some t := shadowTask then
      let (shProblems, summary) ← shadowCheck (← IO.ofExcept (← IO.wait t)) shadowOut leanOut
      problems := problems ++ shProblems
      shadowSummary := s!"; {summary}"
    return (problems, s!"compiled, ALIGNED, {mine.length} names, {nKnown} recorded \
      failure(s){shadowSummary}")
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
