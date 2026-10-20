/-
  The records of `pass3` (`Tests.Ix.Compile.Pass3`), by unit: the kernel
  failures of its two legs (`table`), the root block failures
  (`compileFailures`), the refusals of Pass 3's own images
  (`imageRefusals`), the documented decompile defects (`decompileKnown`),
  and the documented defect of a constant (`defectOf`, for `emit`). The
  machinery that checks them is the harness's
  (`Tests.Ix.Compile.Harness.Kernels.check`, `Harness.Check.failureProblems`,
  `decompileProblems`).

  Legs: `cert` (the certified checker) and `rs` (`ix check-rs`, meta mode).
  The donor's record (a9cf3607, KF triage 2026-10-05, 89 rows) had a third,
  `lean` (`ix check-lean`, `Ix.Tc`'s meta mode; 62 rows, mostly BB-F7 on
  collapsed aliases, and the one `mayBeEmpty` row); that leg returns after
  M7's `check-lean` move (Q-CHECKLEAN), with its rows re-recorded on IxC
  Meta. The donor's `switch` column went with the call-site surgery (every
  row was `on`); its rows for units this tree does not have (the
  definitional and proof-justified passes' fixtures `Pass/O*`, batch 5; the
  CORPUS-IPB units `IPBCollapse2p1`, `IPBMixed`) are not carried.

  **Status: measured off the box, to be confirmed on it** (Q2 commit 4's
  plan, `q2-tests-plan.md` §6). The rows are `PASS3_EXPECT_EMIT`'s from a
  research fork's run of this suite on the Q2 tree (2026-10-20: one suite
  run, an anonymous recheck and two meta rechecks of the kept outputs), each
  reviewed against the donor's row for the same unit and this tree's
  aux-cert record (the same fixtures, legs and binaries). Against the
  donor: `F1_Collapse2p1`'s `AppTypeMismatch` 62 → 59 and `C4Evap`'s 156 →
  154 (stable over the three meta runs); `SurgAlias`'s four WB-B5 rows not
  carried (no leg rejects a `SurgAlias` constant here); `NestedSortU`/
  `NestedSortUK` are this tree's. The box's first run writes the failures
  (`PASS3_FAILURES`), rechecks them (`pass3-tools`, `PASS3_RECHECK`) and
  emits the rows again (`PASS3_EXPECT_EMIT`); a difference is reviewed and
  recorded with its reason. A recorded row is never loosened to pass.

  Causes:
  - `BB-F1`: the Rust kernel's meta mode on the aliases of a collapsed block
    (`AppTypeMismatch`, `ctor return type: head is not the inductive`); the
    certified checker and anonymous mode accept them (`metaOnly`).
  - `REFUSED-SIBLING (A0 …)`: the compile refused a block on purpose (A0's
    "not a one-motive recursor", kept by the lane's decision for Q2); the
    constants that reach the refused member through metadata cannot be
    resolved by the meta kernel (its named entry is absent). Anonymous mode
    accepts them.
  - `WB §6`, `KF-UNIVM`: the documented defects of the aux-cert
    record and the KF triage on the same fixtures; `IxC modeller: …`: the
    certified checker's documented modeller declines of this tree's
    aux-cert record (CQ3.1, CQX.8, SP5 §3.5).
  - `CERT-AXIOM`: the certified checker declines axioms outside its
    standard set (`Tests.Ix.Compile.LevelSpellings` declares its own).
-/
import Tests.Ix.Compile.Harness.Check
import Tests.Ix.Compile.Harness.Kernels

namespace Tests.Ix.Compile.Pass3Kernels

open Tests.Ix.Compile.Harness

/-- The kernel-failure record (see the module docstring for its status). -/
def table : List Expect := [
  -- the four evaporation fixtures and image-gen's C4: A0 refuses the block
  { unit := "F3_SplitRoseRace", leg := "rs",
    cause := "REFUSED-SIBLING (A0 refuses the block of A: not a one-motive recursor)",
    msg := "Named entry for 'A", count := 10 },
  { unit := "NestRoseSplit", leg := "rs",
    cause := "REFUSED-SIBLING (A0 refuses the block of NestRoseSplit.A: not a one-motive recursor)",
    msg := "Named entry for 'NestRoseSplit.A", count := 10 },
  { unit := "NestMutExt", leg := "rs",
    cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExt.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExt.A", count := 20 },
  { unit := "NestMutExtA", leg := "rs",
    cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExtA.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExtA.A", count := 10 },
  { unit := "C4Evap", leg := "rs",
    cause := "REFUSED-SIBLING (A0 refuses the block of C4b.Src.A: not a one-motive recursor)",
    msg := "Named entry for 'C4b.Src.A", count := 154 },
  -- the certified checker's documented modeller declines, and their dependents
  { unit := "NestShapes", leg := "cert", cause := "WB §6",
    msg := "blocked: ", count := 25 },
  { unit := "NestShapes", leg := "cert", cause := "WB §6",
    msg := "decline: reader: in-process model",
    names := ["NestShapes.R", "NestShapes.R.leaf", "NestShapes.R.mk", "NestShapes.R.rec",
      "NestShapes.R.rec_1"] },
  { unit := "KernelSpec", leg := "cert",
    cause := "IxC modeller: nested under a definition (SP5 §3.5; decline)",
    msg := "blocked: ", count := 20 },
  { unit := "KernelSpec", leg := "cert",
    cause := "IxC modeller: nested under a definition (SP5 §3.5; decline)",
    msg := "decline: reader: in-process model",
    names := ["KernelSpec.T", "KernelSpec.T.leaf", "KernelSpec.T.mk", "KernelSpec.T.rec",
      "KernelSpec.T.rec_1"] },
  { unit := "NestedSortU", leg := "cert",
    cause := "IxC modeller: a non-Prop nested block with a small eliminator (decline)",
    msg := "decline: ",
    names := ["NestedSortU.T", "NestedSortU.T.mk", "NestedSortU.T.rec", "NestedSortU.T.rec_1"] },
  { unit := "NestedSortU", leg := "cert",
    cause := "IxC modeller: a non-Prop nested block with a small eliminator (decline)",
    msg := "blocked: ", names := ["NestedSortU.t_rec"] },
  { unit := "NestedSortUK", leg := "cert",
    cause := "IxC modeller: a non-Prop nested block with a small eliminator (decline)",
    msg := "decline: ",
    names := ["NestedSortUK.T", "NestedSortUK.T.mk", "NestedSortUK.T.rec", "NestedSortUK.T.rec_1"] },
  { unit := "NestedSortUK", leg := "cert",
    cause := "IxC modeller: a non-Prop nested block with a small eliminator (decline)",
    msg := "blocked: ", names := ["NestedSortUK.t_rec"] },
  -- BB-F1: the Rust kernel's meta mode on collapsed aliases
  { unit := "F1_Collapse2p1", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", count := 59 },
  { unit := "F1_Collapse2p1", leg := "rs", cause := "BB-F1",
    msg := "ctor return type: head is not the inductive", count := 9 },
  { unit := "C8Collapse3", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "twins", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  -- the aux corpus
  { unit := "corpus", leg := "cert", cause := "CERT-AXIOM",
    msg := "decline: non-standard axiom", count := 20 },
  { unit := "corpus", leg := "rs", cause := "KF-UNIVM",
    msg := "populate_recursor_rules_from_block: canonical-order mismatch",
    names := ["IxVMInd.UnivM.rec", "IxVMInd.UnivM.rec_1", "IxVMInd.UnivM.rec_2"] }
]

/-- The root block failures of a unit (measured as `table`): A0's
evaporation refusal (Pass 2; aux-cert `.refuses "is not a one-motive
recursor"`), every failing member of the refused block and the
constructors' block entry. Every other block failure must be a consequence
of one (REFUSED-SIBLING) or a recorded image refusal. (The donor's `AliasIdx`
row, WB-A3, is not carried: `AliasIdx` compiles on this tree.) -/
def compileFailures : List CompileFailure := [
  { unit := "F3_SplitRoseRace", cause := "A0 (not a one-motive recursor)",
    msg := "is not a one-motive recursor", names := ["A", "A.mk"] },
  { unit := "NestRoseSplit", cause := "A0 (not a one-motive recursor)",
    msg := "is not a one-motive recursor", names := ["NestRoseSplit.A2", "NestRoseSplit.A2.mk"] },
  { unit := "NestMutExt", cause := "A0 (not a one-motive recursor)",
    msg := "is not a one-motive recursor",
    names := ["NestMutExt.A", "NestMutExt.A.mk", "NestMutExt.A2", "NestMutExt.A2.mk"] },
  { unit := "NestMutExtA", cause := "A0 (not a one-motive recursor)",
    msg := "is not a one-motive recursor", names := ["NestMutExtA.A", "NestMutExtA.A.mk"] },
  { unit := "C4Evap", cause := "A0 (not a one-motive recursor)",
    msg := "is not a one-motive recursor", names := ["C4b.Src.A2", "C4b.Src.A2.mk"] }
]

/-- Refusals of Pass 3's own images. None on this tree's units (the donor's
two rows were the CORPUS-IPB units, which this tree does not have). -/
def imageRefusals : List ImageRefusal := []

/-- Documented source-recovery defects. None (the donor's inventory was
empty too). -/
def decompileKnown : List DecompileKnown := []

/-- Units the Rust decompiler (`rs_decompile_roundtrip`) must roundtrip too,
with no error (its aux_gen roundtrip errors included): `SurgAlias`, whose
recursive field hides behind `Id'` and names an alpha-twin of `Nat` (the
decompile's `find_rec_target` Phase 3; `SourceIngressReducedDefs`'s `C`/`D`,
in the test environment, are the same shape). -/
def rustDecompileUnits : List String := ["SurgAlias"]

/-- The documented defect a constant's failure belongs to, by its name (the
fixture families keep the fixtures' namespaces), for `emit`. -/
def defectOf (unit name : String) : String := Id.run do
  for (p, d) in [("SurgAlias", "WB-B5"), ("IxVMInd.UnivM", "KF-UNIVM"), ("NestShapes", "WB §6"),
      ("KernelSpec", "IxC modeller: nested under a definition (SP5 §3.5; decline)"),
      ("NestedSortU", "IxC modeller: a non-Prop nested block with a small eliminator (decline)")] do
    if hasSub name p then return d
  match unit with
  | "NestShapes" => "WB §6"
  | _ => "UNCLASSIFIED"

/-- The environment variables that select a `pass3-tools` mode; `pass3`
refuses to run while one is set. -/
def toolModes : List String :=
  ["PASS3_CLOSURE", "PASS3_VIEW", "PASS3_FIND", "PASS3_RECHECK", "PASS3_EXPECT_EMIT"]

end Tests.Ix.Compile.Pass3Kernels
