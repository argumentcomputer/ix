/-
  The records of `pass3` (`Tests.Ix.Compile.Pass3`), by unit: the kernel
  failures of its cert/Rust legs (`table`), exact measured IxC outcomes
  (`leanRecords`), the root block failures
  (`compileFailures`), the refusals of Pass 3's own images
  (`imageRefusals`), the documented decompile defects (`decompileKnown`),
  and the documented defect of a constant (`defectOf`, for `emit`). The
  machinery that checks them is the harness's
  (`Tests.Ix.Compile.Harness.Kernels.check`, `Harness.Check.failureProblems`,
  `decompileProblems`).

  Legs: `cert` (the certified checker), `rs` (`ix check-rs`, meta mode), and
  `lean` (IxC, exact selected labels with accept/typed kept distinct).
  The donor's record (a9cf3607, KF triage 2026-10-05, 89 rows) had a third,
  `lean` (`ix check-lean`, `Ix.Tc`'s meta mode; 62 rows, mostly BB-F7 on
  collapsed aliases, and the one `mayBeEmpty` row). M7 records only measured
  IxC boundaries, with exact labels/reasons and artifact-derived addresses;
  none of those 62 old rows is copied. The donor's `switch` column went with the call-site surgery (every
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

/-- The four measured artifact-reader reason forms. Unsafe inductive pieces
still decline in Admission.isTierInfo/readInductive; Source generation's typing
tier is separate. This is a record of outcomes, not a typing claim. -/
inductive LeanReason where
  | smallEliminator (typeName : String)
  | minorMismatch (typeName ctorName : String)
  | unsafeInductive
  | blocked (rootName : String)

private def namedAddress (env : Ixon.Env) (name : String) (owner : Bool := false) : Except String Address := do
  let [(_, nd)] := env.named.toList.filter (fun (n, _) => n.pretty == name)
    | throw s!"IxC record: missing or ambiguous name {name}"
  let some _ := env.getConst? nd.addr | throw s!"IxC record: missing or malformed payload for {name}"
  let address := if owner then Tests.Ix.Compile.AuxCert.recordOf env nd.addr else nd.addr
  let some _ := env.getConst? address | throw s!"IxC record: missing or malformed owner of {name}"
  return address

def LeanReason.expected (env : Ixon.Env) : LeanReason → Except String (String × String)
  | .unsafeInductive => pure ("decline", "decline: reader: unsafe inductive declaration")
  | .blocked root => do
    return ("blocked", s!"blocked: {← namedAddress env root true}")
  | .smallEliminator typeName => do
    let address ← namedAddress env typeName
    return ("decline", s!"decline: reader: in-process model of #{(toString address).take 12}: small eliminator on a non-Prop block")
  | .minorMismatch typeName ctorName => do
    let typ ← namedAddress env typeName
    let ctor ← namedAddress env ctorName
    return ("decline", s!"decline: reader: in-process model of #{(toString typ).take 12}: minor 1 (#{(toString ctor).take 12}): 1 inductive hypotheses for 0 recursive fields")

structure LeanRecord where
  unit : String
  reason : LeanReason
  names : List String

/-- M7's nine-unit measurement: 17 exact groups, 134 refused labels across
five units. Every other measured label accepts or types; unmeasured refusals
remain errors. No namespace wildcard or inferred unsafe-failure rule. -/
def leanRecords : List LeanRecord := [
  { unit := "NestedSortU", reason := .smallEliminator "NestedSortU.T", names := [
    "NestedSortU.T",
    "NestedSortU.T.mk",
    "NestedSortU.T.rec",
    "NestedSortU.T.rec_1"
  ] },
  { unit := "NestedSortU", reason := .blocked "NestedSortU.T.rec", names := [
    "NestedSortU.t_rec"
  ] },
  { unit := "NestedSortUK", reason := .smallEliminator "NestedSortUK.T", names := [
    "NestedSortUK.T",
    "NestedSortUK.T.mk",
    "NestedSortUK.T.rec",
    "NestedSortUK.T.rec_1"
  ] },
  { unit := "NestedSortUK", reason := .blocked "NestedSortUK.T", names := [
    "NestedSortUK.t_rec"
  ] },
  { unit := "NestShapes", reason := .blocked "NestShapes.R.rec", names := [
    "NestShapes.R._sizeOf_1",
    "NestShapes.R._sizeOf_2",
    "NestShapes.R.below",
    "NestShapes.R.below_1",
    "NestShapes.R.brecOn",
    "NestShapes.R.brecOn.eq",
    "NestShapes.R.brecOn.go",
    "NestShapes.R.brecOn_1",
    "NestShapes.R.brecOn_1.eq",
    "NestShapes.R.brecOn_1.go",
    "NestShapes.R.casesOn",
    "NestShapes.R.recOn"
  ] },
  { unit := "NestShapes", reason := .minorMismatch "NestShapes.R" "NestShapes.R.mk", names := [
    "NestShapes.R",
    "NestShapes.R.leaf",
    "NestShapes.R.mk",
    "NestShapes.R.rec",
    "NestShapes.R.rec_1"
  ] },
  { unit := "NestShapes", reason := .blocked "NestShapes.R", names := [
    "NestShapes.R._sizeOf_inst",
    "NestShapes.R.ctorElim",
    "NestShapes.R.ctorElimType",
    "NestShapes.R.ctorIdx",
    "NestShapes.R.leaf.elim",
    "NestShapes.R.leaf.sizeOf_spec",
    "NestShapes.R.mk.elim",
    "NestShapes.R.mk.inj",
    "NestShapes.R.mk.injEq",
    "NestShapes.R.mk.noConfusion",
    "NestShapes.R.mk.sizeOf_spec",
    "NestShapes.R.noConfusion",
    "NestShapes.R.noConfusionType"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNestNeg.rec", names := [
    "UnsafeI.UNestNeg.below",
    "UnsafeI.UNestNeg.below_1",
    "UnsafeI.UNestNeg.brecOn",
    "UnsafeI.UNestNeg.brecOn.eq",
    "UnsafeI.UNestNeg.brecOn.go",
    "UnsafeI.UNestNeg.brecOn_1",
    "UnsafeI.UNestNeg.brecOn_1.eq",
    "UnsafeI.UNestNeg.brecOn_1.go",
    "UnsafeI.UNestNeg.casesOn",
    "UnsafeI.UNestNeg.noConfusion",
    "UnsafeI.UNestNeg.noConfusionType",
    "UnsafeI.UNestNeg.recOn"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UN", names := [
    "UnsafeI.UN.below",
    "UnsafeI.UN.below_1",
    "UnsafeI.UN.brecOn",
    "UnsafeI.UN.brecOn.eq",
    "UnsafeI.UN.brecOn.go",
    "UnsafeI.UN.brecOn_1",
    "UnsafeI.UN.brecOn_1.eq",
    "UnsafeI.UN.brecOn_1.go",
    "UnsafeI.UN.casesOn",
    "UnsafeI.UN.ctorIdx",
    "UnsafeI.UN.mk.noConfusion",
    "UnsafeI.UN.noConfusion",
    "UnsafeI.UN.noConfusionType",
    "UnsafeI.UN.recOn"
  ] },
  { unit := "UnsafeI", reason := .unsafeInductive, names := [
    "UnsafeI.U",
    "UnsafeI.U.leaf",
    "UnsafeI.U.mk",
    "UnsafeI.U.rec",
    "UnsafeI.UN",
    "UnsafeI.UN.mk",
    "UnsafeI.UN.rec",
    "UnsafeI.UN.rec_1",
    "UnsafeI.UNeg",
    "UnsafeI.UNeg.mk",
    "UnsafeI.UNeg.rec",
    "UnsafeI.UNestNeg",
    "UnsafeI.UNestNeg.mk",
    "UnsafeI.UNestNeg.rec",
    "UnsafeI.UNestNeg.rec_1"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNeg", names := [
    "UnsafeI.UNeg.below",
    "UnsafeI.UNeg.brecOn",
    "UnsafeI.UNeg.brecOn.eq",
    "UnsafeI.UNeg.brecOn.go",
    "UnsafeI.UNeg.casesOn",
    "UnsafeI.UNeg.ctorIdx",
    "UnsafeI.UNeg.mk.noConfusion",
    "UnsafeI.UNeg.noConfusion",
    "UnsafeI.UNeg.noConfusionType",
    "UnsafeI.UNeg.recOn"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.U", names := [
    "UnsafeI.U.ctorElim",
    "UnsafeI.U.ctorElimType",
    "UnsafeI.U.ctorIdx",
    "UnsafeI.U.depth",
    "UnsafeI.U.depth.match_1",
    "UnsafeI.U.leaf.elim",
    "UnsafeI.U.mk.elim",
    "UnsafeI.U.mk.noConfusion",
    "UnsafeI.U.noConfusion",
    "UnsafeI.U.noConfusionType"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNestNeg", names := [
    "UnsafeI.UNestNeg.ctorIdx",
    "UnsafeI.UNestNeg.mk.noConfusion"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.U.rec", names := [
    "UnsafeI.U.below",
    "UnsafeI.U.brecOn",
    "UnsafeI.U.brecOn.eq",
    "UnsafeI.U.brecOn.go",
    "UnsafeI.U.casesOn",
    "UnsafeI.U.recOn"
  ] },
  { unit := "KernelSpec", reason := .blocked "KernelSpec.T.rec", names := [
    "KernelSpec.T.below",
    "KernelSpec.T.below_1",
    "KernelSpec.T.brecOn",
    "KernelSpec.T.brecOn.eq",
    "KernelSpec.T.brecOn.go",
    "KernelSpec.T.brecOn_1",
    "KernelSpec.T.brecOn_1.eq",
    "KernelSpec.T.brecOn_1.go",
    "KernelSpec.T.casesOn",
    "KernelSpec.T.ctorElim",
    "KernelSpec.T.ctorIdx",
    "KernelSpec.T.mk.noConfusion",
    "KernelSpec.T.noConfusion",
    "KernelSpec.T.noConfusionType",
    "KernelSpec.T.recOn"
  ] },
  { unit := "KernelSpec", reason := .minorMismatch "KernelSpec.T" "KernelSpec.T.mk", names := [
    "KernelSpec.T",
    "KernelSpec.T.leaf",
    "KernelSpec.T.mk",
    "KernelSpec.T.rec",
    "KernelSpec.T.rec_1"
  ] },
  { unit := "KernelSpec", reason := .blocked "KernelSpec.T", names := [
    "KernelSpec.T.ctorElimType",
    "KernelSpec.T.leaf.elim",
    "KernelSpec.T.mk.elim",
    "KernelSpec.T.mk.inj",
    "KernelSpec.T.mk.injEq"
  ] },
]

def leanExpectations (unit : String) (env : Ixon.Env) : Except String (Array LeanReport.Row) := do
  let mut expected := #[]
  for record in leanRecords.filter (·.unit == unit) do
    unless !record.names.isEmpty do throw s!"{unit}: empty IxC refusal record"
    let (outcome, reason) ← record.reason.expected env
    expected := expected ++ record.names.toArray.map fun label => { label, outcome, reason }
  return expected

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
