/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Import provenance for `Ix.Kernel`, the vendored con-leche tree among it

Every imported file has a row: its source path and SHA-256 at its origin's
revision, its destination path and SHA-256, and its transformation. Rows
are grouped into `PortSet`s, each with one origin (repository, revision,
and how `--source` reads it) and one licence, so rows from different
sources coexist. The file inventory, hashes, headers, licences and source
hashes are enforced by `Tests/Ix/Kernel/Provenance.lean`
(`lake exe kernel-provenance`).

**The old branch.** Recorded on 2026-09-17 from the `jcb/ix-kernel-consistency`
branch of the Ix repository at `oldBranch.revision` (the old workspace's
working copy was identical to the pin). Step L6 of the con-leche port
(plans/ix-kernel-con-leche-port-v4.md, 2026-10-01) retired the intrinsic
kernel these rows were ported for: 96 of the 97 Lean rows went with it,
including the 20 `SetTheory`/`SetModel` rows that formed their own set
(ported from con-leche `86cd20a6`; the checker now uses con-leche's own
copies, vendored under `Ix/Kernel/` below). The one remaining row is `Ix/Kernel/Ref.lean`
(`ConstRef`, the Ixon reader's reference type); the licence files remain
with it, and the notice was rewritten to record the retirement. For the
retired rows, The transformations are the namespace
rename `Ix.Theory` to `Ix.Kernel`, the provenance header, for three files
the import trim that makes the kernel depend on Lean core only, and for twelve
files the `letE` constructor with its cases, for three model files the
`ConstantFact.recursor` constructor, and for the ordinary-inductive route
the K2 adaptation (no input store, the recursor at member 1 of its block,
inference in place of witness validation, published rule facts) and likewise
for the structure and natural-number routes and the `Signature` rule checker,
for the equality, `Iff`, and `Nonempty` bases and the quotient and standard-axiom
routes (no input store, per-primitive facts and readings, the model-only
split of the equality basis, inference in place of witness validation),
and the natural-number family reference on literals. P01 changes bounded
validators to structured search outcomes without changing their semantic
claims. P02 adds exact reference-transfer and admission fidelity evidence,
and K3 makes recursor references explicit and shares Nat/structure facts
between family-only and supplied-recursor stages,
as the header of
every ported file stated. License files are verbatim copies; the notice was
updated to this repository's paths on 2026-09-30 and for the retirement on
2026-10-01. The branch's own provenance chain is retained in
`Ix/Kernel/NOTICE`.

**Con-leche** (plans/ix-kernel-con-leche-port-v4.md, 2026-09-30; vendored
under `Ix.Kernel` on 2026-10-01). Con-leche's checker is vendored in place
under `Ix/Kernel/**` from con-leche at `conLeche.revision`. Until 2026-10-01
it kept its upstream paths and namespace (`ConLeche/**`, `ConLeche`) and
its verbatim files were byte-identical; since then every file goes through
one mechanical rewrite, `scripts/vendor-conleche.py`: `ConLeche/Kernel/X`
and `ConLeche/X` become `Ix/Kernel/X`, the namespace and module prefix
`ConLeche` becomes `Ix.Kernel`, and one comment line in front names the
source file. A `rewritten` row is exactly that: its target is the script's
output on its source at the row's revision, and `kernel-provenance
--source-git` re-derives it through the script and compares hashes, so
"verbatim up to the rewrite" stays checkable and an upstream sync is
`vendor-conleche.py sync`, then a diff. An adapted Lean file (eight rows)
starts with the con-leche form of the port header, its source path
upstream's, and its summary ends with the rewrite:

```
/-
Ported from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526.
Source: ConLeche/Kernel/CheckerBase.lean
Transformations: …
-/
module
```

`conLecheRows` is generated: `scripts/provenance-rows.py` turns a TSV
(`source_path`, `source_sha256`, `dest_path`, `dest_sha256`,
`transformation`; `vendor-conleche.py rows` prints the rewritten ones) into
rows and splices them between the markers below. Con-leche's `LICENSE`
travels with the tree as `Ix/Kernel/LICENSE-CON-LECHE` (verbatim), and
`Ix/Kernel/NOTICE` states the vendoring. The adapted files that carry
Argument's modifications copyright declare `Apache-2.0 AND (MIT OR
Apache-2.0)` and form their own set, as the old branch's set-theory rows
did; every other con-leche row is Apache-2.0.

Seven files are at a later con-leche revision, `conLecheKeepProj.revision`
(`3ca9e2fe`, upstream task #323, KEEPPROJ: a projection that does not fire
is returned as itself by `whnfCore`, so `a.i =?= b.i` compares arguments
first). They were pulled verbatim at int-5 (`plans/review/int-5/README.md`),
are rewritten like the others, and form their own Apache-2.0 set
(`conLecheKeepProjTargets`). Both
checkouts, `plans/refs/con-leche` and `plans/refs/con-leche-upstream`, hold
both revisions, so one `--source-git` run checks every con-leche row. -/

namespace Tests.Ix.Kernel.ImportManifest

/-- How the optional `--source` checks read a file at a revision. -/
inductive Vcs where
  /-- `jj -R <workspace> file show -r <revision> root:"<path>"` (`--source`). -/
  | jj
  /-- `git -C <checkout> show <revision>:<path>` (`--source-git`). -/
  | git
  deriving Repr, BEq

/-- Where a set of rows comes from. -/
structure Origin where
  /-- Names the source in messages and in the port header. -/
  label : String
  repository : String
  revision : String
  vcs : Vcs
  deriving Repr, BEq

/-- The header an adapted Lean file from `origin` starts with. -/
def Origin.header (origin : Origin) (source : String) : String :=
  s!"/-\nPorted from {origin.label} at {origin.revision}.\nSource: {source}\n"

/-- The old Ix consistency branch (`Ix/Theory/**`). -/
def oldBranch : Origin where
  label := "Ix branch jcb/ix-kernel-consistency"
  repository := "https://github.com/argumentcomputer/ix.git"
  revision := "ad60e5f6dd23655da79cf9898d2b6b3fefbe8658"
  vcs := .jj

/-- Con-leche, the origin of the vendored tree (`Ix/Kernel/**`). The checkout
`plans/refs/con-leche` is clean at this revision. -/
def conLeche : Origin where
  label := "con-leche"
  repository := "https://github.com/leanprover/con-leche.git"
  revision := "ae0c0c4e4ce6a0081648aff03fe9c39d002c4526"
  vcs := .git

/-- Con-leche at upstream task #323 (KEEPPROJ), `conLeche.revision` plus two
commits: `1e567fcf` (the modeller's index-lifting fix, not pulled) and
`3ca9e2fe` (#323). The files #323 changes that this repository ports are
taken from here verbatim (int-5); every other con-leche row stays at
`conLeche.revision`. `plans/refs/con-leche` holds this revision too. -/
def conLecheKeepProj : Origin where
  label := "con-leche"
  repository := "https://github.com/leanprover/con-leche.git"
  revision := "3ca9e2fe749a51cba4c6e3527aeecba074c29316"
  vcs := .git

/-- How a ported file relates to its source. -/
inductive Transformation where
  /-- Byte-identical: no header, and the two recorded hashes are equal. -/
  | verbatim
  /-- The mechanical rewrite "path and namespace `ConLeche` → `Ix.Kernel`"
  (`vendorScript`) of the source, and nothing else: the target is the
  script's output on the source at the row's revision, it starts with
  `vendorHeader source`, and the target path is the script's destination of
  the source path. `kernel-provenance --source-git` re-derives the target
  through the script. -/
  | rewritten
  /-- Changed as summarized; an adapted Lean file starts with its origin's
  port header, and declares the set's licence if it declares one. -/
  | adapted (summary : String)
  deriving Repr, BEq

/-- The script that vendors con-leche (`Transformation.rewritten`). -/
def vendorScript : String := "scripts/vendor-conleche.py"

/-- The first line the vendoring rewrite gives a file from `source`
(`header` in `vendorScript`). -/
def vendorHeader (source : String) : String :=
  s!"-- con-leche's {source}, vendored by scripts/vendor-conleche.py " ++
    "(paths and namespace ConLeche → Ix.Kernel); see Ix/Kernel/NOTICE.\n"

/-- One imported file. -/
structure PortRow where
  /-- Path at the origin's revision. -/
  source : String
  /-- Path in this repository. -/
  target : String
  sourceSha256 : String
  targetSha256 : String
  transformation : Transformation
  deriving Repr

/-- Rows sharing one origin and one licence (an SPDX expression). -/
structure PortSet where
  origin : Origin
  license : String
  rows : Array PortRow
  deriving Repr

/-- An old-branch Lean row, recorded before rows carried their own
transformation; the summary is in the file's port header. -/
structure PortedFile where
  /-- Path in the source revision. -/
  source : String
  /-- Path in this repository. -/
  target : String
  sourceSha256 : String
  targetSha256 : String
  deriving Repr

def PortedFile.toRow (row : PortedFile) : PortRow :=
  ⟨row.source, row.target, row.sourceSha256, row.targetSha256, .adapted "as stated in the port header"⟩

/-- Modules authored in this repository, including the pure Ixon boundary.
Reorganized codec proofs retain their source path/revision in each header;
they are not imports from the older model branch inventoried below. The
intrinsic kernel's authored modules (its checker, ingress and egress over
its own syntax, its runtime, `Ix/Kernel/Model.lean`, `Consistency`) were
retired at L6; `Ix/Kernel/Ingress/Records.lean` keeps the record store the
certified entries use. The Ixon boundary of the vendored checker is
`Ix/Kernel/Ixon/*` (until 2026-10-01 `Ix/Kernel/ConLeche/*`).
`Ix/Kernel/LevelGeran.lean` and `Ix/Kernel/Verify/LevelGeran.lean` are Ix's,
inside the vendored con-leche tree because the adapted `Ix/Kernel/Level.lean`
and `Ix/Kernel/Verify/Level.lean` import them, and a vendored module imports
only the vendored tree, `Init`, `Std` and `Lean` (`scripts/layering.sh`,
clause 5): Géran's sublevels, the fallback that makes the level comparison
decide the case nanoda's misses (cl-level). -/
def authored : Array String := #[
  "Ix/Ixon/Types.lean", "Ix/Ixon/Types/Kinds.lean", "Ix/Ixon/Types/Modes.lean",
  "Ix/Ixon/Types/Contract.lean", "Ix/Ixon/Codec.lean", "Ix/Ixon/Wire.lean", "Ix/Ixon/Verify.lean",
  "Ix/Ixon/Audit.lean", "Ix/Ixon/Verify/Basic.lean", "Ix/Ixon/Verify/Expr.lean",
  "Ix/Ixon/Verify/ExprSpine.lean", "Ix/Ixon/Verify/Constant.lean",
  "Ix/Ixon/Verify/ConstantTables.lean", "Ix/Ixon/Verify/NonrecursiveConstant.lean",
  "Ix/Ixon/Verify/RecursorConstant.lean", "Ix/Ixon/Verify/MutualConstant.lean",
  "Ix/Ixon/Verify/Framing.lean", "Ix/Ixon/Bounded/Universe.lean",
  "Ix/Ixon/Verify/BoundedUniverse.lean", "Ix/Ixon/Bounded/Constant.lean",
  "Ix/Ixon/Verify/BoundedConstant.lean", "Ix/Ixon/Bounded/Size.lean",
  "Ix/Ixon/Verify/ReaderBounds.lean", "Ix/Ixon/Verify/ConstantBounds.lean",
  "Ix/Ixon/Verify/Work.lean", "Ix/Ixon/Verify/WorkTags.lean", "Ix/Ixon/Verify/WorkExpr.lean",
  "Ix/Ixon/Verify/WorkArray.lean", "Ix/Ixon/Verify/WorkUniverse.lean",
  "Ix/Ixon/Verify/WorkConstant.lean", "Ix/Ixon/Verify/WorkRecord.lean",
  "Ix/Ixon/Verify/WorkAdmission.lean", "Ix/Ixon/WireCheck.lean", "Ix/Ixon/Verify/WireCheck.lean",
  "Ix/Ixon/Canonical.lean", "Ix/Ixon/Verify/Canonical.lean", "Ix/Ixon/Admission.lean",
  "Ix/Ixon/Verify/Admission.lean", "Ix/Ixon/Admission/Audit.lean", "Ix/Ixon/Projection.lean",
  "Ix/Ixon/ProjectionProofs.lean", "Ix/Ixon/ProjectionAudit.lean", "Ix/Ixon/ReduceUniverse.lean",
  "Ix/Ixon/BlockOrder.lean", "Ix/Ixon/BlockOrderProofs.lean", "Ix/Ixon/BlockOrderAudit.lean",
  "Ix/Kernel/Egress/Projection.lean", "Ix/Kernel.lean", "Ix/Kernel/Audit/Axioms.lean",
  "Ix/Kernel/Audit/Imports.lean", "Ix/Kernel/Audit/Runtime.lean", "Ix/Kernel/Audit/Roots.lean",
  "Ix/Address/Core.lean", "Ix/Kernel/Search.lean", "Ix/Kernel/Ixon/Reader.lean",
  "Ix/Kernel/Ixon/Prelude.lean", "Ix/Kernel/Ixon/PinData.lean",
  "Ix/Kernel/Ixon/NatOpPinData.lean", "Ix/Ixon/KernelAdmission.lean",
  "Ix/Kernel/Ixon/ReaderSpec.lean", "Ix/Kernel/Ixon/Installed.lean",
  "Ix/Kernel/Ixon/Values.lean", "Ix/Ixon/KernelConsistency.lean",
  "Ix/Ixon/Admission/Bytes.lean", "Ix/Ixon/Consistency.lean", "Ix/Kernel/Ingress/Records.lean",
  "Ix/Kernel/LevelGeran.lean", "Ix/Kernel/Verify/LevelGeran.lean"
]

/-- Lean modules ported from the old branch (one since L6). -/
def ported : Array PortedFile := #[
  ⟨"Ix/Theory/Ref.lean", "Ix/Kernel/Ref.lean", "72b21fcb84bf5653761ff1bbc305447c391c6446a0d5ffcab7151e42013b5844", "caf46bf8c993b544c75973b1091af72006573433faa23a38b35e6ed9fd422255"⟩
]

/-- License and notice files from the old branch. -/
def licenses : Array PortRow := #[
  ⟨"Ix/Theory/LICENSE", "Ix/Kernel/LICENSE", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", .verbatim⟩,
  ⟨"Ix/Theory/LICENSE-APACHE", "Ix/Kernel/LICENSE-APACHE", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", .verbatim⟩,
  ⟨"Ix/Theory/LICENSE-MIT", "Ix/Kernel/LICENSE-MIT", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", .verbatim⟩,
  ⟨"Ix/Theory/NOTICE", "Ix/Kernel/NOTICE", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497", "2f067442e273aeba9c7c22c874600fa58fb251628341a794025c528d8286bcce", .adapted "paths updated to this repository (2026-09-30): the ported directories, the hash record, and the file references outside this repository; the model and set-theory paragraphs rewritten for their retirement at L6, and a section on the vendored con-leche tree added (2026-10-01)"⟩
]

/-- Files vendored from con-leche at `conLeche.revision`: the import closure
of `ConLeche.model_exists` (`Ix.Kernel.model_exists` here) plus the eight
frontend modules the Ixon reader imports (`ConLeche/Frontend/**` and
`ConLeche/Verify/Frontend/Prepare.lean`, L4a) and
`ConLeche/Verify/Cached/StreamThm.lean` (the no-False theorem at the stream,
L5); seven of them, upstream task #323's, at `conLecheKeepProj.revision`
since int-5. 445 rows are `rewritten` (until 2026-10-01: `verbatim`, at their
upstream paths), eight `adapted`: `Verify/Cached/AgreeFloor` and
`Verify/Cached/PushChain` with the one-line 4.34.0 fix, `MainTheorem` cut to
`model_exists`, `Kernel/CheckerBase` importing `NatOpPinSet` instead of
`NatOpPins` (L4b), `Kernel/Level` and `Verify/Level` falling back on Géran's
sublevels where nanoda's level comparison is incomplete (cl-level,
`plans/review/cl-level/rows.tsv`), `Frontend/InModel/Nested` forming its
container groups independently of the auxiliary motives' order (cl-m1),
and the axiom pin `Tests/Ix/Kernel/Axioms.lean`; each adapted summary ends
with the vendoring rewrite.

One transformation applies to the tree as a whole: upstream's
`ConLeche/Kernel/NatOpPins.lean` is not vendored. It splices upstream's JSON
pin dumps (`pins/*.json`, through `ConLeche/PinGen/Dump.lean`) at
elaboration time, and Ix's Nat-operation pins are generated from Ixon
records instead (`Ix/Kernel/Ixon/NatOpPinData.lean`). L4b deleted the
dumps and `Dump` and kept `NatOpPins` verbatim but unbuilt, which forced
per-file globs in both lakefiles; int-4 deleted it
(`plans/review/int-4/README.md`).

Generated from the L1-L3 TSV as re-recorded at integration
(`plans/review/int-2/rows.tsv`), L4a's rows (`plans/review/int-3/rows.tsv`),
L4b's changes (`plans/review/cl-l4b/rows-full.tsv`), L5's row
(`plans/review/cl-l5/rows.tsv`), int-4's deletion
(`plans/review/int-4/rows.tsv`), cl-m1's `Nested` row with the seven
rows of con-leche #323 at `conLecheKeepProj.revision`
(`plans/review/int-5/rows.tsv`), and the move under `Ix/Kernel`
(`plans/review/final/rows.tsv`, 2026-10-01). -/
def conLecheRows : Array PortRow := #[
-- BEGIN con-leche rows (generated by scripts/provenance-rows.py)
  ⟨"ConLeche/Kernel/Basis.lean", "Ix/Kernel/Basis.lean", "7b8ecf5df443fa2240726fe5d3b6decfb15c3c1c955c11fff7572bc7b196f294", "5dccbc7c9da55d3d384ce8c882c9e92b532a17f17f57a270fed3944de4d242ae", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Builder.lean", "Ix/Kernel/Basis/Builder.lean", "20d3d1318701c6d29f585c453c66db60bc24ae5a2b2560ef451c2746eecbbe89", "b5ad2c794a2df71084a9b69f2aac2af9a65dae92b971f9d53349d380c6bfdc59", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Empty.lean", "Ix/Kernel/Basis/Empty.lean", "c87c9152504486ad01537c96e0f9d05236b7288e0724b17707cc41edeaf14db2", "ebf51d4a441bdbf562bd3589b230ad3d8b90f37b0aaa6f477a17ba5836c711db", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Eq.lean", "Ix/Kernel/Basis/Eq.lean", "ee75b1e0b9d16a8305f293e29cb3c153d9da0408ed49dd55def91f3105860659", "5d160362766a6f1235f7dd3d9f852e02982ecc3cdbe9cedc82ad3dc422bcd24e", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/False.lean", "Ix/Kernel/Basis/False.lean", "802a9aa9804934878f7d214e21f8f6e1324ff9cbdfa2b6ebe589ad324e1c2fe5", "6ed8014756c407fb758e7cecbadd36a891ff04113658e2309e7cd2b481b03ffc", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Names.lean", "Ix/Kernel/Basis/Names.lean", "5788f567b8c6a0c240e985a026cc9a91c5afdd25681a1f4fb075e3c1706283cd", "34525c70f574cecb0c2df6a645707b4683ec225652c5ffe500cd5312d79ab171", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Nat.lean", "Ix/Kernel/Basis/Nat.lean", "b42c21a878217d2b45b0c654616c97724efe0ca7efbd74dcdf9d188ebf5e1ad0", "1415dd846b7f8359e0fba3ce064c978abf0f33d58f9a099cc7845fee684349d3", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/PUnit.lean", "Ix/Kernel/Basis/PUnit.lean", "79cba561d5abdb4bc30b66f529ea33be2803f3c3dfa732eb73b522481836e76f", "de3e0295bad4fdeb3d115d4f2ce74275d77b350d0b68a2b95d5562da63767cbb", .rewritten⟩,
  ⟨"ConLeche/Kernel/Basis/Quot.lean", "Ix/Kernel/Basis/Quot.lean", "4abb3ced9c0870e4ab0706d516b3866262e34c826b86c634dd250988a9ae4eeb", "3bcd762a3a426ec151af36ca9b15d456d88001eab63d34c300126727183a766b", .rewritten⟩,
  ⟨"ConLeche/Kernel/BasisA.lean", "Ix/Kernel/BasisA.lean", "3defab91fe906f628f21e1f377e70009093ee9b064fa1b3180b2994f77568e05", "c0b24272adc609d080ee20a2099529dc363bbe18b9e635c8b9d9c4dd28fe0aa6", .rewritten⟩,
  ⟨"ConLeche/Kernel/BasisGen.lean", "Ix/Kernel/BasisGen.lean", "b931115c804693476b0ce0f457ba1925cdd2d5c6aca623baf692c9e20b1f06ca", "c340f2c8456f8d0b41d34c7d553ce4aeacc9d4167d7d5ab2c46b249917bbdf36", .rewritten⟩,
  ⟨"ConLeche/Cached/CheckerC.lean", "Ix/Kernel/Cached/CheckerC.lean", "47e379e20bd3649297d2971203b58d98e4d4e001c9cf62607286a931eaefef55", "28e7f2d6d0c7e810a3f8e28977f745a16f22a8485aaa62851700e57cbf34c12d", .rewritten⟩,
  ⟨"ConLeche/Cached/CoreC.lean", "Ix/Kernel/Cached/CoreC.lean", "4a4a6ebf41fe6fa810d9820a8df523f7cb3cbb85f9bff79116ec6da26b71674e", "fafcf7bdc518b337b46d6c732f34613435273fb291bf81168b343fe735b98bae", .rewritten⟩,
  ⟨"ConLeche/Cached/ExprNodes.lean", "Ix/Kernel/Cached/ExprNodes.lean", "6dcdebb32c53eb169c2772ae65b0b3f19094a1b487f555061c7a784bbe03bb3e", "c5915111a5892f319bd9abf64da54b90a02bdb68b4759846a0780ff1b231cb07", .rewritten⟩,
  ⟨"ConLeche/Cached/ExprOpsC.lean", "Ix/Kernel/Cached/ExprOpsC.lean", "3077a19b38490a4d05d1bf8e1719009a06e15813fff54b760f1c9e5c1534d18d", "bcafe102dad237cd150b4a4f99bf8ff8e267a7ab71693390876a1cdb0b285269", .rewritten⟩,
  ⟨"ConLeche/Cached/Installed.lean", "Ix/Kernel/Cached/Installed.lean", "be979a23cfab59998c6cc26d2ee10f88ef33091d3cb205bf73f383403185d214", "42d991fdac9b848c91784add3b511d55a456079e69f25d7d0a2c5a43e4615015", .rewritten⟩,
  ⟨"ConLeche/Cached/ParsedC.lean", "Ix/Kernel/Cached/ParsedC.lean", "8a1b3fdb1381142e0c776d37c046ad2857244a23880883e830422c5a7499eddf", "612ea0715abb987e47084ca4fa326baeb0d2bd9fe9026790d1957c586b4b81d3", .rewritten⟩,
  ⟨"ConLeche/Cached/StateC.lean", "Ix/Kernel/Cached/StateC.lean", "94a2c0c31a2891112dee894b2310aa003ed7873d4c928bdc32f0fed0300ed88b", "8c7f586706b8abd99c02e5163a2ee26903659aca97cc4670d7a915f057ed0f57", .rewritten⟩,
  ⟨"ConLeche/Kernel/Canon.lean", "Ix/Kernel/Canon.lean", "54e7e6bb11ff89aad144f1ee8f67cabadea2a3d4650fce7cab906ec21a7f1c00", "f70b68c01dd72b7898c2d731456c36499aae23bca93a1a1f2985a00799a33dad", .rewritten⟩,
  ⟨"ConLeche/Kernel/Checker.lean", "Ix/Kernel/Checker.lean", "a8c2664b05e12be39acb295b92b0d47f7c9f93cd718fdd35cebcbed13c3d8171", "ed00991ee1853a869ecace1a27f93425fa461aa1489700430149f7f0835907df", .rewritten⟩,
  ⟨"ConLeche/Kernel/CheckerBase.lean", "Ix/Kernel/CheckerBase.lean", "36287a16d891918875877bc34460bbabe95be8d5047faa5662ddc3e63bed9959", "de9ac7e409bd67fd4ef8e018ebc00897446205d8ee17cc950adcd8ebd4de6deb", .adapted "adapted: `public import ConLeche.Kernel.NatOpPins` replaced by `public import ConLeche.Kernel.NatOpPinSet` (the Nat-op pins are generated from Ixon, Ix/Kernel/Ixon/NatOpPinData.lean; upstream NatOpPins is not ported, int-4); port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Kernel/CheckerSplit.lean", "Ix/Kernel/CheckerSplit.lean", "fa4a4c976de37b2b725a63e15f7eece2b1766cb16ff30d92668f0a8e8b7cd16f", "15826dde82ab32be3bd97ef8a48fde60c739f11ead91b3a5966a5f1c62b12248", .rewritten⟩,
  ⟨"ConLeche/Kernel/Core.lean", "Ix/Kernel/Core.lean", "1a9b147883c674a900146881313a7cb47df7a6b620ed9e3b4e5ba9a739c7a2b5", "21608aa3b14cc9bcdd3d538da7404b93462214b18ceee947eeebc5c9a3062c72", .rewritten⟩,
  ⟨"ConLeche/Kernel/CoreDefs.lean", "Ix/Kernel/CoreDefs.lean", "a543d9899b588131f6c5abdbea7c492861563f23644dda001d9b41a38186758d", "69a5664eaf3bfaeba2a3cf7ba94988b4333acf6681218eeb05ecc5f53020b247", .rewritten⟩,
  ⟨"ConLeche/Kernel/CoreIO.lean", "Ix/Kernel/CoreIO.lean", "9a735f4bc0ab465601cc32b0df3a73317a0bb1e021d8cb2b33ac6db52c1d4618", "be399321cd18ef966c297995996f1fff8c689f364090e67985fbd70d65cd1efb", .rewritten⟩,
  ⟨"ConLeche/Kernel/DeclCheck.lean", "Ix/Kernel/DeclCheck.lean", "c529106553fd316337d5cc83ae0432b08178f488c1d7e1dc1eb8c676b3881df0", "b80aae2548a410f03d6f0c71710b3f1646fe7cb68cd28abe2327b987bdae771a", .rewritten⟩,
  ⟨"ConLeche/Denotes.lean", "Ix/Kernel/Denotes.lean", "dcfb3577afd63cc7a4a42c1125b4739393f709a6f8a303cdb625dbc640190759", "cff91a49d2c499a712d6aae01b55f1cd0ce21c635148d33b07dd16c5198089a8", .rewritten⟩,
  ⟨"ConLeche/Kernel/Env.lean", "Ix/Kernel/Env.lean", "d9fab0471d394c71bd0bbec808619f95b0842cf8b0b080fa0d06f9954fefef7c", "7c1d4ad30c879dea0e2ceb739ba3b1b8e7fe9a451a763f6b33cf0b881b3d772f", .rewritten⟩,
  ⟨"ConLeche/Kernel/Exclusive.lean", "Ix/Kernel/Exclusive.lean", "0c3679bafbeac89f644aa812f5db35b8acaf84077f39ea7548eb918b0e234f81", "fdf2791bdfe5eb2b9d11c7846dc8802ca7e25e1830cf4b1b9313b7042117e857", .rewritten⟩,
  ⟨"ConLeche/Kernel/Expr.lean", "Ix/Kernel/Expr.lean", "49b5c5ab59de8027688faf385ab81284f4d968b344230060784abd69062d5eda", "a6e197184359338cc249ab16ce72196415080d287b9ada375418a94c983c453d", .rewritten⟩,
  ⟨"ConLeche/Kernel/ExprOps.lean", "Ix/Kernel/ExprOps.lean", "82fddb9060f6fa930799824eea235e8e6363fdacd561d4d2793c20c16750346c", "4bd4efd32743f5236d4d75ffbe221c59986eb29f69e8744b9af87be4d3de51f9", .rewritten⟩,
  ⟨"ConLeche/Kernel/FEnv.lean", "Ix/Kernel/FEnv.lean", "5954d4b19a66fed120aa4da957c72c1366c5c24d3ffa51422cc57e86608513f4", "bb286183aa935325cb5d9ae712ea8b6a9d52dcbcbc5d7f11ec70262497cea68e", .rewritten⟩,
  ⟨"ConLeche/Frontend/InModel.lean", "Ix/Kernel/Frontend/InModel.lean", "aa0f6cddb2f4478d038e8f2c19aae65fc0bc81eb7adbe9189ed20a4185c0b358", "a184062085a6ecda102423337d3482b178097b2468125c2daf50cc6a9eb96948", .rewritten⟩,
  ⟨"ConLeche/Frontend/InModel/Kit.lean", "Ix/Kernel/Frontend/InModel/Kit.lean", "5602c1926326cb46b0f55e14a496609a284804e2fe8de5060b9edb5ab603f6de", "e1ff2ebaf5ee495c692ebb87e8dfcd8902c389cb350fb30a3e016665e8754923", .rewritten⟩,
  ⟨"ConLeche/Frontend/InModel/Mutual.lean", "Ix/Kernel/Frontend/InModel/Mutual.lean", "8884e3c820d619c364ac6a3008b9e675374735720fb504da5e83beb102e4f466", "48b90012d963835046c2c4c7a91b04b6f71096a8ddf332d4829e3c7497a4bcbd", .rewritten⟩,
  ⟨"ConLeche/Frontend/InModel/Nested.lean", "Ix/Kernel/Frontend/InModel/Nested.lean", "75ac54033a53fe4076d687ddebf05c601767892db01189082ba8e3e3e0d86fd4", "ef0d5d7c39d0f5caac203d5bed693ac08b22aa0a54d83353352f99875aed426f", .adapted "adapted: genNested forms the container groups largest family first (not in motive order) and declines a group that shares a member with an earlier one, since Ix's compiler orders a nested block's auxiliary motives canonically (cl-m1); port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Frontend/NatOpGround.lean", "Ix/Kernel/Frontend/NatOpGround.lean", "4c9c4d081a0152d6dff1395485f29fdf26f90ed6f4cdcf5d0fd6064a326f2356", "2211fe04feb5b59d622bb1b5e918ca0df3364284c7e2be1df71eb31fa75c0d4e", .rewritten⟩,
  ⟨"ConLeche/Frontend/Prepare.lean", "Ix/Kernel/Frontend/Prepare.lean", "cb12fc5b5e5e0a7c1028cdd05869f46862faee514e2d89118eae622e7adec9ae", "1719db54343890845694b8d43b21c5d940d12aea62bdf5a557c5ad8f121b6116", .rewritten⟩,
  ⟨"ConLeche/Frontend/ProjRec.lean", "Ix/Kernel/Frontend/ProjRec.lean", "83edeabc2c033ee5410bf76700d0cdf9983d7ad63056e54be4708373eafd91c3", "4e4c38024962204b44400f49a3d4e15e764846207732902326d069b6c7e9439a", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/Modeled.lean", "Ix/Kernel/Inductives/Modeled.lean", "5afd66146f16634252ccafc80bf1a5e2eeed791fc794ec598d24745f9562d66d", "01d856ecf756062ef6af8238ca58ea7a806756b88aca4fdba50cb8b1ccde96d1", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeInstall.lean", "Ix/Kernel/Inductives/NativeInstall.lean", "67eb53764350f826d6ecdbe1c5feac8d53261ea8e8cb79b0503123451d858c69", "52ece5d0dec1862c990c49a0e66e22dc280f2e1d5e87f89497d936310cd5f57f", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeInstallF.lean", "Ix/Kernel/Inductives/NativeInstallF.lean", "82ec5ee5bc8cc18c05b081af72a12a6a2509326382afaecef7a2f7e41e922ecc", "23fb9dd7ae9e25bae5968e538ee52838f29428ac2f48fd58480160a94a2a5f15", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeParts.lean", "Ix/Kernel/Inductives/NativeParts.lean", "2989380cbecdad3cb9fc07e0ffa91f224e00051586d5ae01069243444bd15775", "95949bea2f2dfc037823abe6d896eaa08c578ca643567dd7adf0468638d371ae", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/StructInstall.lean", "Ix/Kernel/Inductives/StructInstall.lean", "83e7ecc40470d0c1bbac4173e6e8605bdd37708fba5670aa0e69e10b6a5958b0", "a235592ae9d6828a9e93e4cfc87f484d20fb09ca93f42646bc415ff1625a6f09", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/StructInstallF.lean", "Ix/Kernel/Inductives/StructInstallF.lean", "d5efb8f0e8585335e4ae9620addecdb8769c068f550a81085824a0ff3bee0146", "602c9dff9e0b73340a7ca3fedc634b08f30e48614cdef41abd5cb53beb5117e2", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/StructParts.lean", "Ix/Kernel/Inductives/StructParts.lean", "eeda8ddfce0c5af4706093057de5b28ffaee7abdd2a4afe85ecf013a52f5a000", "d713dc5a8c37a3b343eda89f55e35af9c27eeb3db73a60101d218612df1ade3a", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/SumInstall.lean", "Ix/Kernel/Inductives/SumInstall.lean", "6718f72cd716970e1df4ab4347cb8bd2d92f463282fcfb58eff22d053dc10690", "2b6bbb1e600e46b960685cbd6609e1912dd6b502b667077cb21584956778051a", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/SumInstallF.lean", "Ix/Kernel/Inductives/SumInstallF.lean", "ad68353c7da5eb350d615e5938a55279aa628e233866a9e056f7129a419c72bc", "65c61cc025fad8e52cc1726dafc4f3003aba1e257f13fcbab70a76e8cb5a8ec3", .rewritten⟩,
  ⟨"ConLeche/Kernel/Inductives/SumParts.lean", "Ix/Kernel/Inductives/SumParts.lean", "c3dd816a698db3dab5413bc6f6701f69c13c3c7da79424450268a5ff0007dc59", "4b2e5178093f458c9ed6ee2d50d8348565a840ffc357229ddbdbd6848a1265bd", .rewritten⟩,
  ⟨"ConLeche/Kernel/Level.lean", "Ix/Kernel/Level.lean", "2ae9b97c4d67c9a476c7b6edd49a5bb6738f2d5c60d38f13ab692861a03364bc", "66cdabe06630d0983bcdddca791ecf96351c505652d1b0578d0d9d73f0756544", .adapted "adapted: in `rest`, the `(param, max)` case answers with `Geran.leq` (Géran's sublevels, the Ix module now at `Ix/Kernel/LevelGeran.lean`) when both branches of the `max` fail, instead of `false`, so that nanoda's incomplete split is decided (cl-level); `public import ConLeche.Kernel.LevelGeran`; port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/MainTheorem.lean", "Ix/Kernel/MainTheorem.lean", "cf76ba7275a8be8846395654aa5b16275cc97329bdc45945d6a93e91f20fb229", "f5f479e7a59e3a33a74e57aabb8d3f5ef48b12bdf8eff86ac0330e88a68f93f1", .adapted "adapted: model_exists only; no_False_declaration and its frontend/StreamThm imports dropped; docstring cut; port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Model/Annot/Bit.lean", "Ix/Kernel/Model/Annot/Bit.lean", "4c0b92043d8dfd1fc8d5ae4a9b81663c61230259729ce714546d2d3ee6424d09", "3b6bb6f12d4aa12f7f34e6692a17af893e7254e821bca46ef741d24191166a1f", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitClosed.lean", "Ix/Kernel/Model/Annot/BitClosed.lean", "f5d970148a7c9cc9b485187a03a521493c703d4beb61855433832443ba4283b1", "ff8bf31cebd586ae19a6a4efe73e0f16a362c6b25b78dfa1e94b861a991d65bf", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitConsCross.lean", "Ix/Kernel/Model/Annot/BitConsCross.lean", "29f10124c90bdbe6e8622e18470a97ad4f9d1d79a67c5007d90b99736a082332", "72d19629b8d1d63267bb8c8e572939117f5ce5c76f72cbb8058055dadfcd9abc", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitExtend.lean", "Ix/Kernel/Model/Annot/BitExtend.lean", "3dca0c0a2b057abf1283e2ab27deacf900a05f21bb0af8280705023e69b3cad6", "aff32508ff00cfb7a30b8faa4667a951ed2cb0447fcb486d5b149ec51eeae211", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitExtendTower.lean", "Ix/Kernel/Model/Annot/BitExtendTower.lean", "2fbdcd5875996e2f0f47da134ef29882f9ac9ff8d769390c8a91f8cf267be5b4", "0ee4d84938e3f8d36d77c01ca6fe2442961be31e475f23d353755ddf84433d10", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitInst.lean", "Ix/Kernel/Model/Annot/BitInst.lean", "70d98baa07165550d03849e909bb33822fdb142f5cc91b8006435646caa49294", "7ebb4ad6450d764173484aae156d6a277f83fcad99af12fcef7e63c34dbeba86", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitInstall.lean", "Ix/Kernel/Model/Annot/BitInstall.lean", "8b4cdb526fa1a8824d9e274813ce42a6c84fcae4ee69408818b33dec4f9e9157", "8d9610fb08167360549b8c541a635e252abd90e1243242302b6006eea099f8c7", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitLemmas.lean", "Ix/Kernel/Model/Annot/BitLemmas.lean", "9387a7aab8758e94992f6869c9124ebf91fe5f7370763eac5b1e1d3cc161bc16", "c41ae3cdb70f4e7b5b474517ced957d720efedfe984d6412658a05681849d7ca", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitLevels.lean", "Ix/Kernel/Model/Annot/BitLevels.lean", "1c74b01c06cd81294b7188f256863ab32bc237b649997cd14c44ee3d61aae904", "de35421e182bc6c1cfd8bb4c5d59ea190c004a494f45deefbba3442ecc1d8ee5", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitRename.lean", "Ix/Kernel/Model/Annot/BitRename.lean", "fdcfd36b1689f4cd83782c6638f84c353272b051712e1dca0e916875f89e095b", "bee9a8a496e6d173fd3b9f584a0fae6ed0917572972d292323fa78820f5696b6", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/BitShift.lean", "Ix/Kernel/Model/Annot/BitShift.lean", "7707b1cc24a4e5de6ad73281378cf54f4d823b450c29db00237d95d2e27c8fcd", "2e5f658bc18d18cd0bf637d696c6c04de2fbf58118af2f561b435f9d29b6a074", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/EnvModel.lean", "Ix/Kernel/Model/Annot/EnvModel.lean", "d409cec291e9070c0bfb96415a9cd3e303f009e58f4f211ac05a0230c90e8beb", "f051adc708e4f73ca7f19ebead46d1c52cf240e11fe488f7e8e3757f2f0ab88b", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/EnvModelM.lean", "Ix/Kernel/Model/Annot/EnvModelM.lean", "435718225541385057f3fdcadc76d95aef4750c559e18485c0f62f5f399d54ae", "b44b74a1523dfed50acb2645866c4cf4120d7578cd1eb0fa3a28f5660e79ee82", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/Laws.lean", "Ix/Kernel/Model/Annot/Laws.lean", "826224bf057a7e32c98dc7adbda2657a34e9cfd2f17394190b4211c7b31a551c", "faa14cc6c8bb2f7814351b6b2cce934e2a54aced88c8e07eff020cc1dc05e2a6", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/Valid.lean", "Ix/Kernel/Model/Annot/Valid.lean", "dc16587e866652e3da8f62db46b285eef1caa7be0c325f56a8e64ff5946aa928", "fa6fd797935fdcc3a47b022e0090326c00ecc3f104cf8f5c207682df1eb4dd44", .rewritten⟩,
  ⟨"ConLeche/Model/Annot/ValidSpine.lean", "Ix/Kernel/Model/Annot/ValidSpine.lean", "df908974921fe4d7da34a8b342ada80a9b9042f8b9b511b1d429081eb2494d29", "cd63132fa1ffc56f8be1b84702474de88e0ff7f68c6f45a9fba71c2dc35088e0", .rewritten⟩,
  ⟨"ConLeche/Model/AxiomBits.lean", "Ix/Kernel/Model/AxiomBits.lean", "b1de6902126d181ccf9b73219ab9e99e72add0347e1035a317f01e0d8678114b", "3604de29caed21ccda81eda1b26394c9d319b71fa796113ae6a5b9bc1bf44583", .rewritten⟩,
  ⟨"ConLeche/Model/AxiomMem.lean", "Ix/Kernel/Model/AxiomMem.lean", "f91609e6b36b9b446980b2534d99fb198efd33a96c9c387b7023f42d5bb85bc0", "63760512c09db14eb7b45186f54aa133e51914f93a5b79168a7e3bc7ffb91390", .rewritten⟩,
  ⟨"ConLeche/Model/AxiomPin.lean", "Ix/Kernel/Model/AxiomPin.lean", "3dd59f86a1be7b807049c12209ad2750977a8e392470518825e1d51b77020942", "1069d1ffd4572df3486a548bc1ca7c8c4af0b0a8138c3dc60b3df67ebd7db186", .rewritten⟩,
  ⟨"ConLeche/Model/AxiomReduce.lean", "Ix/Kernel/Model/AxiomReduce.lean", "98d61ca524559ba5f9d392499b11831298f6467a32c40824df85cd83d78193ca", "8a39eae9050b2513cd23ac52635b32455915bf1ad58dff3ca1fb61f1685fc5be", .rewritten⟩,
  ⟨"ConLeche/Model/BasisBlocks.lean", "Ix/Kernel/Model/BasisBlocks.lean", "fb7b30e909ef2e8dfc3b81f7b9e28516013a63add7517bb0ab31c43e1b1ed57d", "1c85d592ec4ab5db2e7e73843bdf558a3558570668bf5a41fca46a65daa27705", .rewritten⟩,
  ⟨"ConLeche/Model/BasisCons.lean", "Ix/Kernel/Model/BasisCons.lean", "60a9b6a917aaef5cd3486eaee302c52bc5375984baaab10c35791aa56bf7b16e", "7979659734e025597bc875748e7bcbb3b861226a7366e42747e8c65e52258396", .rewritten⟩,
  ⟨"ConLeche/Model/BasisEmpty.lean", "Ix/Kernel/Model/BasisEmpty.lean", "ced691a8671145547b9ec8c2c123757239ecaca31ed3a0d3b72d23ee395d8001", "a6f55b6b499b25a5447ad0dbdb4250cd15ad83cbe3515a0a468fe2d20dc23b38", .rewritten⟩,
  ⟨"ConLeche/Model/BasisEq.lean", "Ix/Kernel/Model/BasisEq.lean", "db47c03cf2234453eed377aba9631f8d202c25e926a889b5bcadcd39134a1075", "4fcfacdfdccfa7e8fe3687ec545b5b72e0c258e9e760cd2b3d79bfab176d5d26", .rewritten⟩,
  ⟨"ConLeche/Model/BasisFalse.lean", "Ix/Kernel/Model/BasisFalse.lean", "48a082ef4029a4bb0866262a46b4118e7261a341569352223a32b10d4b19c0f0", "8d696079155aea8ce12f0f089c79a122bfc73d8a3c92b6a345b08cb384a385f4", .rewritten⟩,
  ⟨"ConLeche/Model/BasisQuot.lean", "Ix/Kernel/Model/BasisQuot.lean", "94ffec8c9768cc33703d0362e10c6e94bf0c6ff8ffb84738e8c5d501a16d98c3", "0e4048198ae8bd5a6820eb59782017032124db1fc13f449b7a583bc42eaaf8b6", .rewritten⟩,
  ⟨"ConLeche/Model/BasisStep.lean", "Ix/Kernel/Model/BasisStep.lean", "b808b1764443050f6641a2109f724c69b82c8d5d0d78e9a196c1c927cb95ca8f", "c90f4067addc27d09b39b5513600bea06e352546d21cdd5141dc3aea7339be68", .rewritten⟩,
  ⟨"ConLeche/Model/BasisTypeOk.lean", "Ix/Kernel/Model/BasisTypeOk.lean", "6ae64ee87cf0b210e5160a776ae9bf6b831e56821a677105fe29f5e966f8c308", "125f5beaa34593458e73ae67165987495945cca9bd4fd6d792aaded3aeeca0c1", .rewritten⟩,
  ⟨"ConLeche/Model/BitAgree.lean", "Ix/Kernel/Model/BitAgree.lean", "d63d3b401e2a9ca41ee2e6fe8b3300c4a9a239b1b66d8debbe6f86ad90892106", "89f4a734dd2c5a0c23a8dbac65c8969f9da1685dc59c4986e09da3f897d890ec", .rewritten⟩,
  ⟨"ConLeche/Model/Caps.lean", "Ix/Kernel/Model/Caps.lean", "71b71a8f61851dbb371b40eaf1d3ac195698b3909ee61a125563ac303a846564", "6385044d2005732f5f55cb88ce7d69c9158ae2ce695095eb1d5542703be648a3", .rewritten⟩,
  ⟨"ConLeche/Model/Capstone.lean", "Ix/Kernel/Model/Capstone.lean", "7060906ee65fa49ee4091c38a24c5730992ab794df7593cc5cc950f3440e0605", "d1db17e61141d04238a3f855017ed2361a26d1bc0ec7dc77b6e5d779226d102b", .rewritten⟩,
  ⟨"ConLeche/Model/Claims.lean", "Ix/Kernel/Model/Claims.lean", "39097d5fda06bbdf6685cad8203fb6e9c7d70026740040f441e774bf414fae9c", "4eef1dc00d8cf3bf7a9aafd1c203a23a273a1330e28b6bc9744d80fa92363ec7", .rewritten⟩,
  ⟨"ConLeche/Model/ClaimsIO.lean", "Ix/Kernel/Model/ClaimsIO.lean", "d6fe36ed831e4d98a6566f3d081764714ef86e87bbd2e3b0216b40eb38cba8eb", "ab05412f77fe3806e937757c545ec7624097f0b5b47c68b51e60acdc2f77e918", .rewritten⟩,
  ⟨"ConLeche/Model/CtxOkKit.lean", "Ix/Kernel/Model/CtxOkKit.lean", "01cd1bbf4d3171ecfd4c8419e36a1991b65976a4788604b8703a70d4be7d8a42", "8830f19001b0c61b3f0b7c150c62ee9eee5364538777beb9170fe894dfa7cfac", .rewritten⟩,
  ⟨"ConLeche/Model/Currency.lean", "Ix/Kernel/Model/Currency.lean", "af7f5feb54cbb293c0d6c1becb661c092986bc5f38245c463cf3a5e8e4d900b0", "c56fee1178b0a62b8ed147b759b028eff1b5b2e09c445c982288d2c8ca6f4484", .rewritten⟩,
  ⟨"ConLeche/Model/DeclInd.lean", "Ix/Kernel/Model/DeclInd.lean", "87aa0e2f6eefc06f582597d28c373ab0bdbc33c2d5647e1fe2b238dd004120c1", "c46a02d25dce1fd696ea381fdcfaac23b4702ee0afdcb5c73de18a78d538f232", .rewritten⟩,
  ⟨"ConLeche/Model/Denotes.lean", "Ix/Kernel/Model/Denotes.lean", "d126aae5c78f1bb27ffa546de537148e10f4b9ba6b3b06885f947b15af164b96", "f8eb5936706d10182f77b1ef27641648a4b604004df3b2a114e5a0fa826eb5da", .rewritten⟩,
  ⟨"ConLeche/Model/DivMod.lean", "Ix/Kernel/Model/DivMod.lean", "b7f8959f68019f52866c570e461f77e0b71971d4fb4edd93207a683ab82e1107", "4f1a5ecb7aace8c55e9f2b7ff635e5c714a6f5d43c7f40492473a176cb5c9ac5", .rewritten⟩,
  ⟨"ConLeche/Model/DivModCert.lean", "Ix/Kernel/Model/DivModCert.lean", "2ca2f860363d900ed8362db10bb15b7f384f5c52ecddef3aba4d6b4b23fe5d63", "706bb4738282fd6705c0598be4eed72419511cfb9669eaf8e0796f167b88d206", .rewritten⟩,
  ⟨"ConLeche/Model/EqTower.lean", "Ix/Kernel/Model/EqTower.lean", "31859926f07185ef99822a24ab72c36a86cf6794c2fe4ba617a22b1567f06045", "3972a735f5c290bc72ef8b9d620ba7227a12a6c93619db7d003870e840cab9b9", .rewritten⟩,
  ⟨"ConLeche/Model/ErasePwInv.lean", "Ix/Kernel/Model/ErasePwInv.lean", "eee1ffbfacfa1b99a5934c91732df6171076c617f18637bb4d2ba50740d2e9e0", "2692c273725cfd8e725682a5b569145e5b3c284e8e13fbd26a7b091f88540f09", .rewritten⟩,
  ⟨"ConLeche/Model/Fold.lean", "Ix/Kernel/Model/Fold.lean", "ce6a3384730396faea412b3fdeb0f2f99dbdade8774cdd6981a938abb696d484", "2a08aeb1acdf211866b0180f73f9b5d50dfa0ee81175327209324fc6a4b26514", .rewritten⟩,
  ⟨"ConLeche/Model/Harvest.lean", "Ix/Kernel/Model/Harvest.lean", "bf7a439527c6784e96aa758e5ba0572e0a3d3f2ef9fabe491dacd97aa85fa803", "4712e9f1d0c1d068eed60d3e819b317eea748eba54a62576992bee88beeaacda", .rewritten⟩,
  ⟨"ConLeche/Model/IOLicense.lean", "Ix/Kernel/Model/IOLicense.lean", "8b958cf40212d35f2254a8c2aae8861c681533653b0cb85bb01c2c349df22d7b", "e3bb68183f4fbf055d640a32a069acfe55c7909a3683461d64ea6a46e71d6c5a", .rewritten⟩,
  ⟨"ConLeche/Model/IndAnnotKit.lean", "Ix/Kernel/Model/IndAnnotKit.lean", "6ec2754a62fc4d88bc371957f67f1986d1f9e75b3d36475d155a6565a3f8581b", "a482fb5104405ccaccf9d80398e309f15d7beea2fedead24b35871bd63fcd061", .rewritten⟩,
  ⟨"ConLeche/Model/IndAnnotMem.lean", "Ix/Kernel/Model/IndAnnotMem.lean", "9e0464654bf3dd382b84b18b9ecca23f338da6fa746f66f91fc25e204585422a", "1295a0e9a6a69935a3832b84aec0c3f3185322821822be1ffe1e3c55ea3c9ee4", .rewritten⟩,
  ⟨"ConLeche/Model/IndBottomNested.lean", "Ix/Kernel/Model/IndBottomNested.lean", "4fa99d53305ed26f514ab8b17732876afb28bad887297604dff50c6b700f7aa8", "d9a73267aad2cf1f8beb76a4d879e19ee538d20dfdc32f07115b4c15efc939bf", .rewritten⟩,
  ⟨"ConLeche/Model/IndBottomPlain.lean", "Ix/Kernel/Model/IndBottomPlain.lean", "3b925a992f8f70c28fe6a98cabc5b1d7fb14aebb7b43a14dc162d97a89d3bde8", "9eebc657f11e1fbde467a9174c58a0696f702f1be82442d8a1065f4f8d95573d", .rewritten⟩,
  ⟨"ConLeche/Model/IndBottomProj.lean", "Ix/Kernel/Model/IndBottomProj.lean", "970ef24ac75acdd03789b27d1ef4014fdd370386ef9f46ce85d3e34d1a110551", "84da35e38a30143b760e2dc96037b10d37667ea24e0e608b52fbb4de5b1f031a", .rewritten⟩,
  ⟨"ConLeche/Model/IndCaps.lean", "Ix/Kernel/Model/IndCaps.lean", "49c0da1fcecf6f68cf5b578d7ab778452a24ea58db9962b0af127fb34b0c1f50", "712fd48fca34f069d14907c59d873bd60a4d47a43c915c2b92b7aff443248568", .rewritten⟩,
  ⟨"ConLeche/Model/IndCons.lean", "Ix/Kernel/Model/IndCons.lean", "86053208ac0344520fb4ad2ad1976ba6063fe6d541f72dbdc3510ff8a452899b", "96b81bf42d5be884e7e436c32a3ab4f0ab9eab60ea673c9c94f02ed7a270c153", .rewritten⟩,
  ⟨"ConLeche/Model/IndCross.lean", "Ix/Kernel/Model/IndCross.lean", "c278cdba4b18c55951ab1a5ec9ea875afcfabe98b820e6c8a5fb1c1cb5b5ce66", "6a518e03ce86fcd0ad86cd8a14ec9c7980b76610b80709f0ff2da776b9eb8a7e", .rewritten⟩,
  ⟨"ConLeche/Model/IndDomGrade.lean", "Ix/Kernel/Model/IndDomGrade.lean", "ae66fc8750929e8c1f406eac8b63f8ff63ccbe1792c1df96e32c6c67384a8820", "e3eff9969e1736405b2cc0f73149ea69edfd1092d5773c06ce126401fc3f2e18", .rewritten⟩,
  ⟨"ConLeche/Model/IndEtaLaw.lean", "Ix/Kernel/Model/IndEtaLaw.lean", "8218679b47c6e60e9404ae80b5cd180094cd75d9806f026d2a3a0d143e4e55c1", "5f54a283344e0b5741fdca1a5b177b45d654d08d2687d0651fba08d21218503f", .rewritten⟩,
  ⟨"ConLeche/Model/IndFieldGrade.lean", "Ix/Kernel/Model/IndFieldGrade.lean", "febf413c5aa40e55162288d470ffa30ee2363fb0d30d5b7788c598b9f3b6b9a1", "3910095b381c1e87c892e8bac0467b766e05d032ec7df2813125e20e99a65acf", .rewritten⟩,
  ⟨"ConLeche/Model/IndFire.lean", "Ix/Kernel/Model/IndFire.lean", "d72d4add39e09c9d3123d8a6b9269dcde4ebca5b6290b6f836de53a953e539a5", "94b14598b6d6137007b195eea8a206d80f263d8a79b00b2fa0fc158e966afd7b", .rewritten⟩,
  ⟨"ConLeche/Model/IndFrame.lean", "Ix/Kernel/Model/IndFrame.lean", "85a60fdb6d2f7a323c7cf6f4564b154f5d10765f6e4572c8742f1118e5b943cf", "2d5ee1c7432650b7c866551b545d6b9af2cdb74fa4d6574fae6b9927fd9a5c19", .rewritten⟩,
  ⟨"ConLeche/Model/IndGrade.lean", "Ix/Kernel/Model/IndGrade.lean", "7298ab6e3bdd8750312e63098341e02c8ec01382f77da68a5844662f2f7df65b", "79da2857f2aadbeefd0b19541fe260c7c69f116eeeefea80bc1bbf06ac6cb134", .rewritten⟩,
  ⟨"ConLeche/Model/IndLamTower.lean", "Ix/Kernel/Model/IndLamTower.lean", "19ce9d70c8f901f6bd80f6e408a123bed097ea4a6b84143efb1fa966a777e8ad", "8edf54302e2ca0e6d03e22d2825aa9e109087edfa63d1769103a46b0a1cc623d", .rewritten⟩,
  ⟨"ConLeche/Model/IndMember.lean", "Ix/Kernel/Model/IndMember.lean", "fc511632ccb6574d2a8ddea10a65a5bede3fcba647393b496b10d1f7b8900851", "598ea7dbb5b64bcaed5c71347bf757d5326e64fd42c42eb2f622713d32a56970", .rewritten⟩,
  ⟨"ConLeche/Model/IndMembers.lean", "Ix/Kernel/Model/IndMembers.lean", "d4218787e5230dbf5708a977c7cef5080ee27c72ae009669bbb15bbc3f760afb", "bd0af563d3d533c168969bb717f50bb9127b9fc028821dadc4c6e832dc9a93d4", .rewritten⟩,
  ⟨"ConLeche/Model/IndNestedParam.lean", "Ix/Kernel/Model/IndNestedParam.lean", "ad464417338f13a2ae936e80ecacaca5a2de091646a90ed62f55ffbeb35003b2", "eef40f3323cb8aecc2f06ea9b27663f0014c76ee80e80bcca7346da7133950b2", .rewritten⟩,
  ⟨"ConLeche/Model/IndOpenRev.lean", "Ix/Kernel/Model/IndOpenRev.lean", "d84c300b83436656b03410118845e3b185d5be232dcc24d8272bd70bf06fd2cf", "cb8832e4dff3644cc0c13a3f7a6b9e109daa394692ffebfebb4c24970a20b6c6", .rewritten⟩,
  ⟨"ConLeche/Model/IndOpenerGrade.lean", "Ix/Kernel/Model/IndOpenerGrade.lean", "43d54021f803b4dbaf610fbb5cdedb1c5045e951f7140d18c8928e84b7fcd546", "af405a29a3a31f3d2d29dd4a407cde8620466589d40dbaab723832e0bc2e4456", .rewritten⟩,
  ⟨"ConLeche/Model/IndParamGrade.lean", "Ix/Kernel/Model/IndParamGrade.lean", "09f8f37ccfb37f46892f34d50ed47522b917f0ab434b1f4dc1e01bb429e51185", "c885005693a77322521e54912c8bd0ca19312285959cdb0885037f86d9ce4398", .rewritten⟩,
  ⟨"ConLeche/Model/IndPinGrade.lean", "Ix/Kernel/Model/IndPinGrade.lean", "45ffe4f187db053ee0663157e1d6120d1bd9dc93f3736514b4e549d65510bab8", "f8e747d8b758697c446dead9735f4494399b75b699ff02d0d6f1aead295e985b", .rewritten⟩,
  ⟨"ConLeche/Model/IndPinRow.lean", "Ix/Kernel/Model/IndPinRow.lean", "66928c5a03347cfdf4f3a3cfb286d88d596eb2928b30eda6f2400fd64bad6a71", "2543c754c42269f5a39ffc03f4150eb740fbabbdcf439f8aef153fbfb1d0f6d2", .rewritten⟩,
  ⟨"ConLeche/Model/IndPlainParam.lean", "Ix/Kernel/Model/IndPlainParam.lean", "c4a1fbee14d4e1aa56b7b60e10f8488082095737826b185d68b5887198287ae6", "35d8fa86428f9e0ffc90f71d80f9a46ddc8e99a66d265a6a1284cf9180b18bfe", .rewritten⟩,
  ⟨"ConLeche/Model/IndPoint.lean", "Ix/Kernel/Model/IndPoint.lean", "8cedf437cdd6cfafadaae33e6b492242253e9036aad742d0ae863e74b568e25f", "e41b5f6d3557a0db153814db4bd3d5f05b73582e7a412925f50dca565cb3ef55", .rewritten⟩,
  ⟨"ConLeche/Model/IndPointKit.lean", "Ix/Kernel/Model/IndPointKit.lean", "63ed5eda242822a447ce0d87d829aeb815cb6d522cbb3b206d5f9b747e3051f1", "739a109d9f250e146493a40d98d242d6c28d2c7b0c315a900a241fa0f8bc0906", .rewritten⟩,
  ⟨"ConLeche/Model/IndPrefixGrade.lean", "Ix/Kernel/Model/IndPrefixGrade.lean", "8757f77a90bb5f7932946b2880b90bb3d1ae3d965481538c0754fe96f822c0b3", "0ac5739367d02604d0b4c118ffb8880a8d2a28d6d8fb8b5bc6e4bf8b16eaa8d7", .rewritten⟩,
  ⟨"ConLeche/Model/IndProjCaps.lean", "Ix/Kernel/Model/IndProjCaps.lean", "d29bc4a9ce00720901c81ccf435805370607eb7d9e6ab0a4b803ad12a16e6ffc", "6e0092f591abebf7246cb025a541357ea7422e219b5ad9307800684cc7ce5444", .rewritten⟩,
  ⟨"ConLeche/Model/IndProjEta.lean", "Ix/Kernel/Model/IndProjEta.lean", "3ff866c4170ccc91aa53f68af53c7a46710aa6affe7d265a0bd301b00c7182d5", "27102c3d3f454867b608fa487e3d1ea3d249f5d29d1b6399ce8e3c2f9f37d921", .rewritten⟩,
  ⟨"ConLeche/Model/IndProjKit.lean", "Ix/Kernel/Model/IndProjKit.lean", "e9d3f6f35984ca5956520420e50d83f4c6dace6be5f4f8ba4da0858c88eef8a8", "f2ef97d83ccd351cffbf41753bd047d798d6a49959e031871cc1acb3f1848bf2", .rewritten⟩,
  ⟨"ConLeche/Model/IndRecs.lean", "Ix/Kernel/Model/IndRecs.lean", "1d78bf7b1ceac74be57cd850a355200566b5ac3e73bc6eb407e588561bfce9a1", "6445d8b2060501c2132696d3824bab4fb29ee40537576bd974d24d510dd09695", .rewritten⟩,
  ⟨"ConLeche/Model/IndReduct.lean", "Ix/Kernel/Model/IndReduct.lean", "952bd5ae78676be2f68c4c62b57d08970f6fa189556691dfcc5e4071356901ff", "8b1273d6df86ed2e7d2fdb489611931ea8b43f40ae732919acaa734c21e29216", .rewritten⟩,
  ⟨"ConLeche/Model/IndRename.lean", "Ix/Kernel/Model/IndRename.lean", "9ec0fb808943d11beab0ce0a7bb58f58c716858570cd6ed394197ed0b91e832b", "dee6a97c69f44fcf2d6528de637b909d94aa10a9eb27de5691d0dd41779a8fb9", .rewritten⟩,
  ⟨"ConLeche/Model/IndRuns.lean", "Ix/Kernel/Model/IndRuns.lean", "f1969872b53e644949d5658e0e4d76c29ff4cb9ffdc9001192d317bb6884a102", "7affb080963f0896780ffa84ffd6ae886af07276e75bd338ff2ba102591c6480", .rewritten⟩,
  ⟨"ConLeche/Model/IndStageKit.lean", "Ix/Kernel/Model/IndStageKit.lean", "9eddf840c0ec2048f2a815e95b9abeae09a51981ff02ac7bcbbae87ae445c526", "3b7fde5a83284e587fef7373176470bb5e1ebec8646cb1636e01720abc0515df", .rewritten⟩,
  ⟨"ConLeche/Model/IndSubst.lean", "Ix/Kernel/Model/IndSubst.lean", "195e676febfe6257a7754fd9d3c2c1b009b5c393df0ae1f75b427ae49d292526", "447efa29beac622ce9da631fe71f9ff528c9e2b79fa5a9de634a5b5cb0a374f9", .rewritten⟩,
  ⟨"ConLeche/Model/IndTele.lean", "Ix/Kernel/Model/IndTele.lean", "0fbf988a6f997be32d1ccb26280f8c054ab423d29f79bae57bd6de8ff663fff3", "61559f9265e374122c9c2c689179862e864bd52eee3a17a19c6331af9e2f82df", .rewritten⟩,
  ⟨"ConLeche/Model/IndTowerRead.lean", "Ix/Kernel/Model/IndTowerRead.lean", "f097fa4821cc2aa2aa2a464dd49e5dcc071918a15599016e0e37991b0b76500f", "3d78ae30131e90410f476fa08cd78f184d0d76092b03a0d82c3a2b31b3033d96", .rewritten⟩,
  ⟨"ConLeche/Model/IndTransport.lean", "Ix/Kernel/Model/IndTransport.lean", "132e5c52682e4d1f197dc8aedef734f90da092451a76e9a7b40b0383d6881284", "04978f1f5c5bf7a7b669d1e03991eeee927b57424eedbd7573e1a966e97910d7", .rewritten⟩,
  ⟨"ConLeche/Model/IndUnitLaw.lean", "Ix/Kernel/Model/IndUnitLaw.lean", "2203354bdd9e7a6e0c2b1269fe6ddbf16246275f71c5b27d9a3ef31c95e860a9", "324e0c4b78a3c571d33df0d6fd82438db21cedf0bbdfd5d7db81554c6e6c1c2a", .rewritten⟩,
  ⟨"ConLeche/Model/IndZipField.lean", "Ix/Kernel/Model/IndZipField.lean", "4d798d25cf6a64866096bfd6b4888ae090727119c1019344a7f83773abdd7432", "ae524a993e14679d1292307cc6be8a79c8f2031c88f088fcbafb092f94772b45", .rewritten⟩,
  ⟨"ConLeche/Model/IndZipper.lean", "Ix/Kernel/Model/IndZipper.lean", "e16bdbec069ca8cf292656b0ea001f851525ebf9c17a6710918bc8cdb7a914c1", "73712138e0272e46ea0e60c7d00b3cd4c2b2c954f44239f75bb94cd6286ef57b", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/DeclNative.lean", "Ix/Kernel/Model/Inductives/DeclNative.lean", "3b4390f79bd232e493a865d44334c68052b9dbb1dfdb310fe2df86826a33e0e3", "b5ca2112200b0deddc52603080fc8cfcf2169333732dae2d75b66e2b54474217", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/DeclStruct.lean", "Ix/Kernel/Model/Inductives/DeclStruct.lean", "bd8ab51c1b68c966bd6893c2637bdd44615f2030d75b1864410e5f80055bf474", "9f486cbc2e3048e65acc3af22c7dc54a20c4b9b8f79f0ade93ee7489ee903c5e", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/DeclSum.lean", "Ix/Kernel/Model/Inductives/DeclSum.lean", "8a793598c80400bcccf4133c10f850617ecc1484156c29a07bf16cf124229b7f", "7f5c2c6992178b52ccdea4d7fc125fcf4840802ff7e3f005e872143c3974cce6", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixAssemblyKit.lean", "Ix/Kernel/Model/Inductives/FixAssemblyKit.lean", "d3b169316df667e9acfa3df735d01a5854aea20953632a7f28db96137647b25c", "f421def305812772137953ce960a9d055b47e3a2a51f3e1e8871dda7a1f33a1e", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixChainFacts.lean", "Ix/Kernel/Model/Inductives/FixChainFacts.lean", "34f59e26f1dfeb3b1ef21b2a056c09ff1454b261cefd4cc5ea21dbcb4f100f71", "3d4b2d184c1aa749fa1137021abaa7d9c64ff37ce36dc56cf132f6eb216bad72", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixChains.lean", "Ix/Kernel/Model/Inductives/FixChains.lean", "ffaebd758e1a231293bbd218bd97656c42b98cca81e9253604edafb126b087d2", "2ffb3bcf86cbed76344801cea8c7baf8fc415d6a141243beb0512d22afa73eac", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorCross.lean", "Ix/Kernel/Model/Inductives/FixCtorCross.lean", "bf92114562c5c52606402e184045e05a38cb89527dd7d008fcb4697bed81c610", "f087cc5913d5d6a821c9617403399d2981109b9080a9c132cae5e96100411bb9", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorReads.lean", "Ix/Kernel/Model/Inductives/FixCtorReads.lean", "18b1ffd0a0d13ab7fb6a74d9cb540673ff01ad8c8cb7dfff80d4c0ccf0516fcb", "a86df6129637c8409103b883fb22b6833ddb5477f032574ff3156777db6f530a", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorsLoop.lean", "Ix/Kernel/Model/Inductives/FixCtorsLoop.lean", "e0a0a96a8a9c6b9d14df1d7d011b300c50d0c3c0a197b283ae75331e3637c215", "9e2be31a5021b7b407c092d36d2e0f87d37351e94f19b5973b83227fa3b833eb", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixData.lean", "Ix/Kernel/Model/Inductives/FixData.lean", "8b147aae74f874efe509dcc11ed8f6d37750909f5e0dba00cff6c1bf94633372", "bf816e254a60a43d83b7605fee250bef7f305487b5960e1b5cfd3dfedaac6ae7", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixEntryLaw.lean", "Ix/Kernel/Model/Inductives/FixEntryLaw.lean", "3f35447bc8091381a940567fd55a7c106d1762e253f853e95fa7026ebd097ee0", "f7084f494f190e721155b4ae2fb88eb72afbef212d6bdc174f4a8fa65c0b0447", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixIntro.lean", "Ix/Kernel/Model/Inductives/FixIntro.lean", "1612df2a9ec2c599d602eb20a5116b1d29f053d1185b076b5625831cff8d114f", "280798d64c0274a48695ac1b9ab0761384546dc35ab83a0cea334b5b76684b8f", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixLeafOk.lean", "Ix/Kernel/Model/Inductives/FixLeafOk.lean", "f2f951fd8de8c2cf91786193c6dd4f8576af6ac77f64639164b06ca117a437ed", "7672d71de959b757a1718aef7636d5a7ea92f6e0e7e9d49a92b5b751138ed28f", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixNoBVar.lean", "Ix/Kernel/Model/Inductives/FixNoBVar.lean", "6a0496d825cfec85e025bf5c94dc3d0add50c3999c30f219084e216a90c1443d", "c515229d67bdcda5ea4ab4a78e1865f2839415c13f3e7df06689b30c06d99542", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRealChains.lean", "Ix/Kernel/Model/Inductives/FixRealChains.lean", "43f0022f5f877dcc9b1b009d39811f7069679686a52ea0e5775d1a732816fc9c", "12c50a7e10fec1eb55778bf9527c8ec79f32dd01f70a47f698742bd8b5c60a15", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecData.lean", "Ix/Kernel/Model/Inductives/FixRecData.lean", "6001059472406873238fa94371d15186e9692ce52aa899ced89bea69f4f5d4ef", "b12f0cb5f15614a2fef34e3337a2f3c7ca3aa1e248734dd2ca3e0778ac396bca", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecFrames.lean", "Ix/Kernel/Model/Inductives/FixRecFrames.lean", "5bbaf042b29b35aeae8308904c6f7cfd7ebb0c6efbb3e217280008d23254594e", "3f8e02364f67bbfa8411b954927fea6aa7a321c1f408a0e391c5d615963ea5f8", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecKFrame.lean", "Ix/Kernel/Model/Inductives/FixRecKFrame.lean", "edadfd90bb35caa546e814a49d2032e1d2a26d4402fd29cee3b1d5352a6a2275", "df09279523dd801d7c7d141ad802f880e652b1799edbc9362d9f1b1a730999a8", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecLaw.lean", "Ix/Kernel/Model/Inductives/FixRecLaw.lean", "ced9a9fc4b250bd09c7d144bb0e766215f815b9818b5a37279b80c2be4465571", "843b0ede2cd650667c80187cdf57a5f2d5a5317cad192253360a49f7cf4875aa", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecLeaf.lean", "Ix/Kernel/Model/Inductives/FixRecLeaf.lean", "0b884d43625d411e888e9dfe4fea37d6dbc942a4a6057f711466077f925aca1f", "3546d6502a5f7b4efb617e6055014c09d62e4d2a53cf1a93bbe99712fa263420", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecPre.lean", "Ix/Kernel/Model/Inductives/FixRecPre.lean", "e0a91d01d96f52aebe19a25fb7821990100587acd435b8b4a4b62dba23f67d7e", "e1cca37abacb754af76f5e52447b7d82bf801b9a551a546fec411efdff4c60f9", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecRead.lean", "Ix/Kernel/Model/Inductives/FixRecRead.lean", "2822b9a4c5f5225c9d992a01e9051b36e3472b8dd48182a7c8faaf2ccdf99224", "5deaaeaeb1e2b85cdd48d0ba5ef5a6c9a7cb719190290268893dbbeec90ea806", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRecReadDefs.lean", "Ix/Kernel/Model/Inductives/FixRecReadDefs.lean", "d3c6db22721eb2810444c54d2a55f667818206e12f004d6e02042a1a861b39c5", "777fb1ba38e71cd2313eeaf85761a32cf22a702167389c5eb99a617a71554b0a", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleData.lean", "Ix/Kernel/Model/Inductives/FixRuleData.lean", "fd5ff5a83662c75319ed00c43723f934d6dbeb4fb7c88a0353a9fb85e0fbcb54", "35b627e6da77819cc921f26c612a2c1eaaadadff5547b31a839c9127ff5b4f2f", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleKit.lean", "Ix/Kernel/Model/Inductives/FixRuleKit.lean", "f7a3b99e95223d00c217d22faf401e1bc0fa7c0395b5a29c8f40ffd59d2f41c4", "ed31d9af59f110640eaef57f4ff87d9de74240c4ba3a98c522f5f324ca7ce707", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleOk.lean", "Ix/Kernel/Model/Inductives/FixRuleOk.lean", "31db492fbfa40b7dd3148f9a0cc41a0c219c52ed8b2097e14e3eec6a9cec1827", "b1647b152fc980f40711f05f04880c2d48a01137290bff40abee1c06fa6a8942", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixShadow.lean", "Ix/Kernel/Model/Inductives/FixShadow.lean", "be57d006087d80cbd9ba82f86391b524e296ab22261c7bb73a4088b9825daba0", "fe8594db7ee417edf694f3a3cb07fa79a24a5e97f76c1c2fd55754c5785dd5e9", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixStageFormer.lean", "Ix/Kernel/Model/Inductives/FixStageFormer.lean", "ed1db09bff63f723ed5649e5e070a74a3ae08aa2b2640b85313f81b227d5c3c5", "67b363d1dc97002b465ab576f8eec0b4bc7eb6aed9f1b0aa900d1a139be736c4", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixStageRec.lean", "Ix/Kernel/Model/Inductives/FixStageRec.lean", "cafe9f19cae0dfabd82f7c067c1aa9c111976ed22e5d8adfa3398f7213ae6f72", "9e083c46d4852ce3c2ec7e3ce444db94801af54097f56f410f20d40836c6ac51", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixStageTable.lean", "Ix/Kernel/Model/Inductives/FixStageTable.lean", "326fd9e8efd8f0290f23605ed2c7317764c65ad73056ec9e9cb9aca03d8a4ad8", "5c8827f2b5847c4afdb4e10a1056f3193a08e7bc1e4779a840ca629449c8c52a", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixTeleBound.lean", "Ix/Kernel/Model/Inductives/FixTeleBound.lean", "8a79586948d129b36e7bacdf0b28473bb8ecd98cebac43d897f390ed25c743ab", "bb9f2417250adad426378fd10a0403200120ee54c0dcecb2494fc965a8f0f48c", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixWitness.lean", "Ix/Kernel/Model/Inductives/FixWitness.lean", "b93ddf0e2027ea7f4ab2cf60f2317451ee2b83a5087d038db70140010f7a0f91", "9080ecc2ca6bd9edf7e8156d2719abf758f47bd42cbfcd222a6cbc733df3c27c", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/FixZeroField.lean", "Ix/Kernel/Model/Inductives/FixZeroField.lean", "a5a167bc14fb4586cfdbaf122b718c29505680cbfdf3c76d22fe50f7f32d42dd", "693bf1bc0fe7cc870dc4d95eb4fa1b9db9a4d7916af768293194cfa6a1d2f5b1", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructBits.lean", "Ix/Kernel/Model/Inductives/StructBits.lean", "777b17489d082b5d52a32533f615b8f23b51fb796ba98651c42508d867810203", "6436d8b0427952476b57358b56888dc3902f7a638ffa6254ae570b470bab6bfc", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructBodyFrames.lean", "Ix/Kernel/Model/Inductives/StructBodyFrames.lean", "8d061e66a4b9a3455df5ece71fee04e15e4cd67ac4fd68b0f9ccbbbd38ef1849", "df32c6e24ce7d52ab5232214391b6230166c54820b844cf45c3ed38481af7177", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructCaps.lean", "Ix/Kernel/Model/Inductives/StructCaps.lean", "2389a893fb9b35cd6cf6f8a65ac48dae145248c10dac1835be6cb8dc9a510afb", "2718a7a5276cf0fc2e9f61fa32b6315760973b540fcb568c4d22e5198f56b96c", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructCtorData.lean", "Ix/Kernel/Model/Inductives/StructCtorData.lean", "1ed5465b8e9fa0bd71bbb74c8223ef716ef1c3037d47b5ac0dda279dfa979fdd", "473bb4848add6207927ead08f77f034e64df062855ba1d94d0b0d9c100cabbdf", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructCtorFrames.lean", "Ix/Kernel/Model/Inductives/StructCtorFrames.lean", "492795cb4b47a8c075a2de3852a4d803f29464c67765891638630b3630588f2e", "039d8292e88d182739431f21215474fba3aa44056944a7774f56f620ebef7305", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructData.lean", "Ix/Kernel/Model/Inductives/StructData.lean", "cb6d8c3cb3c9c5cc10767f4257d7d6c3ac18cb38ee3eaa11ad1517399439789a", "3ac3c1dc65027b11f80c4b88e06616b421b38d563277b448b6d11cc9349de4cd", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryFree.lean", "Ix/Kernel/Model/Inductives/StructEntryFree.lean", "07ddcec55697a5a127181cadbec2839b0fa2ee239baf21b8ba6528c44060cb1b", "0a155072df546d947d994f9d804977ad6169e5821bf493730acaa2197be1bfc0", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryKit.lean", "Ix/Kernel/Model/Inductives/StructEntryKit.lean", "c51fd31666a57050b752892ef983e8bffb17817e67a17b121771e7456e4ee09e", "6abbdffa66a92e3a669335f29a8d3ea1bc28827847ebb137f86b0af7944829bf", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryKit2.lean", "Ix/Kernel/Model/Inductives/StructEntryKit2.lean", "629ed74ecfe0497c92e8196c9347f4f5ba67e0b64b1a3bcecc1733767b1ecaff", "cd150bc9c02190be660968b9b2ee8b512fee7ee2d9f3c56c95475b090d4d2e5e", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructFrame.lean", "Ix/Kernel/Model/Inductives/StructFrame.lean", "22d1d0f9bfa63ac1f90939c50cc635724604543ff042aa0f2befb878b6725b2c", "728aff55b1cf2b1bf4075bf7daf3ccfccafdca139fc0b9cc552bbcc4e9f4e386", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructFrames.lean", "Ix/Kernel/Model/Inductives/StructFrames.lean", "49466ea295c66f08ac964821d0f5b89a21262cc31e0b5968a6f731749db12d4b", "00446dd9ed35c048e81276aee4f5525b00f3820e8b058704cd728129e2f94399", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructIntro.lean", "Ix/Kernel/Model/Inductives/StructIntro.lean", "fada441b211e13d401491e0f4a7a83b5190079f6289f47858fb6139764db2e8c", "2ca716ecb524ad91515c10de9807557d615159d840e5008f77a4628d7c6e0b06", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructLaws.lean", "Ix/Kernel/Model/Inductives/StructLaws.lean", "8b80cc1d871ee16731db80bf8bc6370212d2bb0395830b558632825a09f38402", "d170b05d403dc1ed2e76a11f6aabe32c45c6ac8becc1055e69eb0499ebf3293c", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRead.lean", "Ix/Kernel/Model/Inductives/StructRead.lean", "209a18b8c54bdcc477488ea526f2bcf0d694b013c7b48e7cbb57ab3b288e6f84", "fbd17faa175be2f3aff67499c7127db10dc863b2a1f8d18f3df08c2b861d2d20", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecFrames.lean", "Ix/Kernel/Model/Inductives/StructRecFrames.lean", "05dc7f919a8ba3c63100599c742a31c7e6a282dd5927792676c660a4a9db532c", "517992dccd9555170651017a4567cfeafb39034300f5737826a1ee5650223176", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecKit2.lean", "Ix/Kernel/Model/Inductives/StructRecKit2.lean", "eeb56cc1abd507b59f698a34e313b35ba6976605fa272ff669f3824cb1dc1c08", "02396c3ac71bb0ecec1ab6a92329a82b737c015fbd944dd03b102cf3055fe5f5", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecLam.lean", "Ix/Kernel/Model/Inductives/StructRecLam.lean", "32b8dedcd161fc66b19ade8414048b75630102fee6cc963082dc74557bd93604", "c5b6dba0171594cca0e67b38e013858f930e384cffd87153241bac884816b77a", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecLawKit.lean", "Ix/Kernel/Model/Inductives/StructRecLawKit.lean", "6def26a2ad245269cce6fe1aca61bc9168c9c66f7ced4ee44a14870cd4fdc1f3", "e32d71f91b50d8ea23c1d539db09819884b7c4fd93d611079689d879bb18130e", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecRead.lean", "Ix/Kernel/Model/Inductives/StructRecRead.lean", "00bf9838724ddc65d60f5337872d809ee80dde2c05b3e372579f671997ed78e6", "a9580cddb80a3eb748c48e37121955855d25b1fdfb558334e909cd84921117ef", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRecSpine.lean", "Ix/Kernel/Model/Inductives/StructRecSpine.lean", "cc6e2e44311fe42e842091609fc4fc4a8a8d54ee9ac3264b0cf07d4f234b310f", "52d0fbcc4e4fbe10e853abde54480c50216a67d24205918ed613265ed3f9db59", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructRows.lean", "Ix/Kernel/Model/Inductives/StructRows.lean", "bb058bb51a48ab5596b9aa3b969a01d38b367da995f9d45e727d5c43ceb0980f", "1d5beec52b10dcb7df0032cd692ebaba9edd7e8de53b77e9c83363b6f1682514", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructStageCtor.lean", "Ix/Kernel/Model/Inductives/StructStageCtor.lean", "76c9251bc00a83916a08b8bfddfae15b83e3b47d11ac920886d7d7537b924bfb", "f7d326f9ccb3cec9303d5742fe6cbf48381c4abf99627dc96dc24f98e18c6389", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructStageFormer.lean", "Ix/Kernel/Model/Inductives/StructStageFormer.lean", "940ef4d9445907ff76398c237de1c22143cb74d5bfc300c3fd1c94d92d20e82b", "d02ad2dd48dbcee620f68acebdf621669b6db7a8b9df53188bc49959259b2113", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructStageTable.lean", "Ix/Kernel/Model/Inductives/StructStageTable.lean", "59d2b899af15fc8684d8dee3040562f833cdde30a23ee00498621b0b1c07d4dd", "67417a1483d1f6f3828bc33ce10d6b755c5c8dbe5d2d88941a8616b64bb112a1", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/StructTele.lean", "Ix/Kernel/Model/Inductives/StructTele.lean", "2b01f4b2b1d9368fa02dbfe1e4a6d7d62b0bfe45ed427f1ff8c78b29a49f50ce", "9c6f1ff9fab63ee8bbfae18762b8390d1c075eb185bfc7fb2bb3b0134215eb2d", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumData.lean", "Ix/Kernel/Model/Inductives/SumData.lean", "5d1b775c885bd19151b5cc973378eff0868583a46eba70703f17e2f7a7f12a0c", "d57dd22c2f6b77037d2c850c697e21f0a49c21b75e1cfe46eb2c23927feca6b8", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumIntro.lean", "Ix/Kernel/Model/Inductives/SumIntro.lean", "170b78e7658026e74f6d38dceb19eca59c78ce32fbf17ae502ead47cd236987b", "e920f4c37e5bb2420ed79322e50d9d4f327aeefbd5992b8a8f9633afaa7382c7", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumRecData.lean", "Ix/Kernel/Model/Inductives/SumRecData.lean", "50a869c1a9b1eb290477e69d098c7624e19a1c4498b6091ed14dd7bc83c04b58", "18c785f91f5134492b45e6906f40a0494b2ccb3a837e29fb1a003d3d1a289ad9", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumRecFrames.lean", "Ix/Kernel/Model/Inductives/SumRecFrames.lean", "bee9bf582ac0175761701d63553c37147e4f915a272d00fc1678957558f8619d", "f81d261dd6f5d6fe003cafb5401ca58c46302086a2d5504186015b61bad5e127", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumRecRead.lean", "Ix/Kernel/Model/Inductives/SumRecRead.lean", "175413516667c9aeb3ad1711bcb98561dcb79357a1f4a1d374f832aad7211251", "e2543cbae0d7e5f644fbcc6b439e2ceb8e4e0d5551b6daf5654d195be3d34289", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumStageCtor.lean", "Ix/Kernel/Model/Inductives/SumStageCtor.lean", "2343c1bc9cdefa006c989b5ed31d9d9c8e19cd05fcc93cdb5caeca965efd2ddb", "2a432879a92e57d6471561bdc86658de990378a8db9fb3c8f034409bbf94f058", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumStageFormer.lean", "Ix/Kernel/Model/Inductives/SumStageFormer.lean", "b3d0be5cee16b560d0ae08746c8c118c93cb81ebb7c0a1674ad6966938993d6d", "175459865ae15855b2345b3b8a69a920a56cb31138849f9d615ce06ad4b64a09", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/SumStageRec.lean", "Ix/Kernel/Model/Inductives/SumStageRec.lean", "41415eb4e185461e89eeb551b0054aeee13c4d4a2379855071598a6800fe0a05", "6a81576b98086ad00441170ecac4a976dd2bbddcdb6d0d9e4dab6ff5e024b09d", .rewritten⟩,
  ⟨"ConLeche/Model/Inductives/TowerCons.lean", "Ix/Kernel/Model/Inductives/TowerCons.lean", "e241df5da452eab84338b3ebd2ec778f1d9fd992acf64b48411f220af35d4570", "f5bff9531529d5f917dbfce7260faffd1e4613282e788d3edffde1d0fd076ae2", .rewritten⟩,
  ⟨"ConLeche/Model/Install.lean", "Ix/Kernel/Model/Install.lean", "dfe1bc8e1f14a53069fa8352e29c597ca08368ff4632010e81b918dc263b1ac0", "1abca88d69bcdadffcec7ecb7d4c4702c67b2df65f5f1bfa60e4423f8f91789b", .rewritten⟩,
  ⟨"ConLeche/Model/IotaRuleNested.lean", "Ix/Kernel/Model/IotaRuleNested.lean", "87eb689d3f0157f3c86f9613b1e5c2c1f77a2ba20ba5494354e7bb8280a66b9b", "2296a22259488f07fa29d7fe862973c59402ddc44c96209a3a026fc91606c167", .rewritten⟩,
  ⟨"ConLeche/Model/IotaRulePlain.lean", "Ix/Kernel/Model/IotaRulePlain.lean", "a86243f77caaaa24156d44b05e020bdc7da20c37809718d2f1df48b4f8995efd", "9abb5d44c53f85161e7d65a01afddeae1fdbf87547caedadb1c5295fe42a0dbc", .rewritten⟩,
  ⟨"ConLeche/Model/Levels.lean", "Ix/Kernel/Model/Levels.lean", "9ee30b0e11a6b940f2edb9b120095b747255ac03f53ad22e115df4e4c86e6fa3", "6de76a804932052bc1b53d2cd1c2e9bcedb607de9f31967df155430a65c0fc72", .rewritten⟩,
  ⟨"ConLeche/Model/NatEqs.lean", "Ix/Kernel/Model/NatEqs.lean", "889cea85622b941b548e58d93b9add12fe502f6a0f6e6ce2027d1557d4bce35b", "5a4efe5f0dcb4397d29636f9519c59d38f8271a1ea834194ebca3a4d79808a25", .rewritten⟩,
  ⟨"ConLeche/Model/NatSem.lean", "Ix/Kernel/Model/NatSem.lean", "393cc6ff639246f6168bed2771f81e236456b842ad802d69e0177d6a4a8450b7", "497d6935246254ec0dc22540973a14b7c5df4a1d28a297f0996ed5e402a7e829", .rewritten⟩,
  ⟨"ConLeche/Model/NatStep.lean", "Ix/Kernel/Model/NatStep.lean", "8d019bfdb02cd6ba43c72c5cb6762f438797205410bab2dbafb742b9e56bb474", "1ea3199fb533dafc9d2c473c7a01b04ffb9c9a03af243b8189df42b0c3876a98", .rewritten⟩,
  ⟨"ConLeche/Model/NatWf.lean", "Ix/Kernel/Model/NatWf.lean", "0883b4f53add26aea3f304307e1e86fad24cb2cc3239172f583479cc02af1015", "74706e9d311f0ffc833245024b8bc8e6c05a256b6c9689f3b89342d3350b3217", .rewritten⟩,
  ⟨"ConLeche/Model/ProjCons.lean", "Ix/Kernel/Model/ProjCons.lean", "8b64987eda361e1ee2e5580ac2beb60f21b5bb90dae7bd05df3c7bcb61ed491f", "3922c2985c2fb84fdd6a5de17e8f3527ce5f2469183350e40678068acbedae46", .rewritten⟩,
  ⟨"ConLeche/Model/ProjInstall.lean", "Ix/Kernel/Model/ProjInstall.lean", "71424b796950957cc256f8a5bb09d1c5914cff0df82967d56a86b88b465bc948", "9794664cee662dc7b7832f3c590646995152f6f7d88f9f5d1dd675865fdf14de", .rewritten⟩,
  ⟨"ConLeche/Model/ProjRename.lean", "Ix/Kernel/Model/ProjRename.lean", "cb34e671232134111fe2de40cb51bba60859ec88c8bc5bbf3b9805403428e901", "11328e0317901d224b0deb55fd978a8b0499fcefd425502fc50bbfd24cd0bc64", .rewritten⟩,
  ⟨"ConLeche/Model/RecRulesCons.lean", "Ix/Kernel/Model/RecRulesCons.lean", "9425ab673d5722fb0fc1f404a3d3ea371d00b76f865803deea5d8b7b5c1f7dd4", "6637deb0ed57492060072b600cdfbbdf6c6abc578c0c35a17a2fda293ca0ed18", .rewritten⟩,
  ⟨"ConLeche/Model/ReduceOps.lean", "Ix/Kernel/Model/ReduceOps.lean", "0260fb9316b3e9619179b11c98431403183d958ee0ee674ec54eeafbaf78f4e1", "bd7f7cb3446485c0a7e2c7256f3f08ba279eafc5eb15f4a202492f59c3f2c084", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/CertsSound.lean", "Ix/Kernel/Model/Rules/CertsSound.lean", "ddbd8922e004a55f80781542ac5caba113f94526dfed8ef9e8b75a3ecf2bd410", "319d45bc01a94160d3d209173e6e7e5c75193210a93f1745f37814f203df5f4b", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/DefEqSound.lean", "Ix/Kernel/Model/Rules/DefEqSound.lean", "8e9d7d4b414e60318fe679189446c1fa1dc091e8874fb342d4ad257a137fabd1", "0580a43778c80cf2ace730e918d93528686ac21c3c3d95cc93a13d20559f5a13", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/DefEqSoundKit.lean", "Ix/Kernel/Model/Rules/DefEqSoundKit.lean", "4bcc4d17a6b452401539acce7f46f40ecaae0a3efc2e3b03084948a1792b1e5e", "e887efc23ec0bdb2e4e8b3645249808b65abf79d163160ff7fbfc0f8f6e46ee0", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/InferSound.lean", "Ix/Kernel/Model/Rules/InferSound.lean", "0a36573a39e7260bb996ae9d164c858d33194bf2a5cdf5faf550326a3d007e93", "8348ddbee9b9be532a1b4f90578918465abc4fe8fe1c68b2eaf3a46c39987dd2", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/InferSoundKit.lean", "Ix/Kernel/Model/Rules/InferSoundKit.lean", "21c282e35606fd4264ed27fc3b7db276bc443517731c03607cd82948dd13939e", "f1c3fa05b830f8268e005168138a6cea9cfe047b65c0a7857b3b7026dea64330", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/Inputs.lean", "Ix/Kernel/Model/Rules/Inputs.lean", "10851c48facc90e6377c8d8b6c1f15171be2c22aec6ed21273dc0d6f73ee870e", "b42b64ba973adf1a4462e1b20452e892a264e92aa6c2e238bce41e77542b840d", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/IotaSound.lean", "Ix/Kernel/Model/Rules/IotaSound.lean", "f10c7a66b947298f467a644ec529d3401d1b97ff0e056bd2f6a80005d6d64020", "9d00990c96f16741fad3f24d08af9fe74da965952a13c2e49e498b4bcc03b862", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/IotaSoundKit.lean", "Ix/Kernel/Model/Rules/IotaSoundKit.lean", "539334fddc086977616eedbb6db7350500551c2e4790d14f4c354730ef6ab628", "6acb95120ac5786bc47b37c9da44a7c16e812d0958613f4bddf9d0720ab075ba", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/Motive.lean", "Ix/Kernel/Model/Rules/Motive.lean", "a6bc7d723a240996a9b5927bc9a7f2d05d2a011dd2635b3f5e0f5a02aca8df0c", "f22cdc2ac2dfacb0dd2762550dde42bef142ccf91d9957b74ff1ebb923061a87", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/Recompose.lean", "Ix/Kernel/Model/Rules/Recompose.lean", "33c24cc06951cd0548f4cdcfac9a45d266600dfcb0afee7584372b1848bdb813", "af0c35945ce1171bc7c01b4649c0e5bae19f6d0b2d410951bf8e218b6acfaab6", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/RedSound.lean", "Ix/Kernel/Model/Rules/RedSound.lean", "68090a7a6a34a69d1d40a1531b82dd15809ab8cce53a15fe84eb3067c673b4c5", "a037e8f31e16b16afa3037a8d2b8a5ed9f8f44ca11642188f6add0c23fd1acf4", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/RedSoundKit.lean", "Ix/Kernel/Model/Rules/RedSoundKit.lean", "ffa515d6020d92500cdbe383c478d5e247e65df23e5ba28947c0cd6c770626e2", "d739947ce6fb9c704ef88b2908e2fb8a443cbee6ab9a360458f2e66f298f661d", .rewritten⟩,
  ⟨"ConLeche/Model/Rules/Sound.lean", "Ix/Kernel/Model/Rules/Sound.lean", "6ca1a6c0464e8e316bdf37edabf2a2e2b76cab8f93681ef096c38841bd3c2971", "eedcd1988da3379f9e9d72d1f9f8ce843398403eb8bac823828ec7937da67ad4", .rewritten⟩,
  ⟨"ConLeche/Model/Swap.lean", "Ix/Kernel/Model/Swap.lean", "e3b20faea9f82bca1830475d82312e73c5621a328efd08512ca81c5e3f7f9f26", "a1fd83821916468bee6ec63f59e8351210bc4c75c57b4e0bf6d539da7ef5dd9f", .rewritten⟩,
  ⟨"ConLeche/Model/Tiers.lean", "Ix/Kernel/Model/Tiers.lean", "4dce97b3e81b30e36effebd9bf9b524b8936ced9e22274c1129f974be8a8ea57", "ad332d56cf3d498edd62bc5bf2d5eadb40264aea37bff1e62690eff228636d25", .rewritten⟩,
  ⟨"ConLeche/Model/WellDenotedTransport.lean", "Ix/Kernel/Model/WellDenotedTransport.lean", "37079d34a070ef64ccaed9c2e8fd207b0f81b3978db381adfe2fc1e83ab5d13b", "f319632c11ade5174bd0e757a49fdd3a3ce324abc99114121c9b233f823379e3", .rewritten⟩,
  ⟨"ConLeche/Kernel/Name.lean", "Ix/Kernel/Name.lean", "46e1005573233f5306444d4c12a5b204614d46e3b7a13064804174e2960a433a", "8fb0e6a01e1ca5f8be6e87a03b8357488f93913f410c177d96d8d83288f93f5c", .rewritten⟩,
  ⟨"ConLeche/Kernel/NatOpPinSet.lean", "Ix/Kernel/NatOpPinSet.lean", "4fc2ff657643c87f8522549517f078600c901a5bcf0f3c66479c165b2c36e397", "2b62dd7d43567e95796bbeba9cd15c6968105d4bfceb4719b1bc39cdf0111b2d", .rewritten⟩,
  ⟨"ConLeche/PinGen/Certs.lean", "Ix/Kernel/PinGen/Certs.lean", "adf2595f9a23b7d788954010328928d2f75222e4c2ddb2a03b04c2147877036a", "b156d7304f472a71beedc225a5b5a0d207befb1de55a983671c82c9a69479d6b", .rewritten⟩,
  ⟨"ConLeche/Kernel/PropRead.lean", "Ix/Kernel/PropRead.lean", "95277d1575a6ede73e604f6e5bd1c8d83ff0e33bc621205a6feab50f8a28bd0b", "04f6a01f2c48e406a0614973607155a74977a2d46b02ee78e6d89fc2970f87b4", .rewritten⟩,
  ⟨"ConLeche/Kernel/PropWhen.lean", "Ix/Kernel/PropWhen.lean", "4268cb0e6a4e0cd6bb91bf96d73acf627426889461d4b1aa62105accbc9bb498", "e91bc78c08bc48e761a793d520820f413c112ff45a618164b38c83a93fddd9a1", .rewritten⟩,
  ⟨"ConLeche/Rules/Derived.lean", "Ix/Kernel/Rules/Derived.lean", "2c480a8bb117eba4abf524a044e12952878039c14e867e85a0b44c425941f32e", "33303ba41bcb4fa6b83306d0cc3f6891071f415077f2a750fdf8719b5ae66b53", .rewritten⟩,
  ⟨"ConLeche/Rules/Rel.lean", "Ix/Kernel/Rules/Rel.lean", "8e2fe3fb65e6a074e4e22c1e20eabb6f2768e6f075984861f0150cf30a1341d9", "fd4c4186dab76fcbbfbf49531a98db9a19272fb090ffc30b8166b92a382156b0", .rewritten⟩,
  ⟨"ConLeche/Semantics/BasisOk.lean", "Ix/Kernel/Semantics/BasisOk.lean", "012930d25dbe7a86ce667f4386f3989928ab2a0f03fe1b081dd022e95a5af510", "c9de6cb5d976cd245c08593d2b6f3f8867380a30a55aa64ff1baa0c58efdea0d", .rewritten⟩,
  ⟨"ConLeche/Semantics/BasisRules.lean", "Ix/Kernel/Semantics/BasisRules.lean", "dc24dcd858dceab1e6f0124d3ee54ac299114d3db5d3ec22adf6ea6eebd74a86", "8e41faf78456ef93e41be1414e60dabce406cda5258e7c5d476288e853e7a012", .rewritten⟩,
  ⟨"ConLeche/Semantics/BasisType.lean", "Ix/Kernel/Semantics/BasisType.lean", "7e8ab71a559fc5bc8583947ca229ddbd56b76bf2ecf2710a8c095c44b1ad0e85", "4e78d8e696a30777131e41623be9a99c26e819cd9f14a9fc7b7d1ba4659f1cdc", .rewritten⟩,
  ⟨"ConLeche/Semantics/Bridge/Decl.lean", "Ix/Kernel/Semantics/Bridge/Decl.lean", "87fed3e245e834399a2f7155415a082364c117bb6bd497b2e6652e2841857410", "40c4fe5400e32d13480795a6a451eb981a95559b6be0442472ee2c3bdd8572e3", .rewritten⟩,
  ⟨"ConLeche/Semantics/Bridge/DeclIndRun.lean", "Ix/Kernel/Semantics/Bridge/DeclIndRun.lean", "b4c61f9a13cc68d21a55724eac11e973fe0deb16ddc265bc2c5866bab5905dae", "2d510557ddda97a14e6145fc46b0ebcd1b7d4b49f992c56b9d4ec3ea1331a2e7", .rewritten⟩,
  ⟨"ConLeche/Semantics/Bridge/DeclRun.lean", "Ix/Kernel/Semantics/Bridge/DeclRun.lean", "69a922afc11e17927b22f833d2bf66d1d0f2dfb0ed85afe01f5878927423878e", "325afc9019dd82ce6b0924457283793f2dfcaf3e3e92d7630dcbcae76fcf7600", .rewritten⟩,
  ⟨"ConLeche/Semantics/Bridge/Sound.lean", "Ix/Kernel/Semantics/Bridge/Sound.lean", "a51dfb23358bf44d1e530505d1653f505f0b8552660a9c35aa43af01f1e25c01", "3350ee314b8351b984ec86162676ed0ad6cede5fba3811c7f7cb86b1429ae99d", .rewritten⟩,
  ⟨"ConLeche/Semantics/Canon.lean", "Ix/Kernel/Semantics/Canon.lean", "521380daaf64f694f8a041a30c597faa8898ca7e09e1714d121260fa715f8326", "cc1d47f1a539a6c52c4efbab4bed827fa95cf3cdb93a3572891c907ade474164", .rewritten⟩,
  ⟨"ConLeche/Semantics/ConstsBound.lean", "Ix/Kernel/Semantics/ConstsBound.lean", "1cae59f1fa649726955feda15cafd441c4dc091eb846fb0c1751f21d82a053f6", "d90164030d69253c3e8cf41f27328f1f952bd8c86ecb62e4395c1995b7eedc99", .rewritten⟩,
  ⟨"ConLeche/Semantics/Decl.lean", "Ix/Kernel/Semantics/Decl.lean", "45695912197f1df39ec5f3c271ebfe433d8e9b4f95501f107db99de277e3e77f", "64fd2365b065e860ff0c047f49881f832653db52932c543ac4e3a1db686144c9", .rewritten⟩,
  ⟨"ConLeche/Semantics/DeclEta.lean", "Ix/Kernel/Semantics/DeclEta.lean", "0c2110ed4d0846dc2efa9df1f234a84a548b343c4191c41c8ad13957a86b50f9", "9e42d13df505278a3671635f719002dd044468af90017f42e698ceebd85d5cb2", .rewritten⟩,
  ⟨"ConLeche/Semantics/DeclIndRun.lean", "Ix/Kernel/Semantics/DeclIndRun.lean", "f85a307a07b2c7a5b4b0aee9299b681afbb3f678440afd9ba34f7abe4d364551", "ee399845d8d8e27bae6d2ba18c98d01c4ed3b684bf48ef86e411bf38188ca444", .rewritten⟩,
  ⟨"ConLeche/Semantics/DeclRun.lean", "Ix/Kernel/Semantics/DeclRun.lean", "1ee91d5cc423b0d6c34d203eea37682e11776c2dce43efa6eeed21918697b3f0", "da3739442b5c2792ef39320fa04e87ae83250c338e6cb75d8386fa8ce48574e2", .rewritten⟩,
  ⟨"ConLeche/Semantics/DefEqList.lean", "Ix/Kernel/Semantics/DefEqList.lean", "1695a82ba7e7d5f9fdc4307e99ccda67f01ab9fb39517df7dff62d2424601892", "11626184de1639ce79a5e29689169534649c18799110b92f2e9d93fc5decdeae", .rewritten⟩,
  ⟨"ConLeche/Semantics/DefEqStep.lean", "Ix/Kernel/Semantics/DefEqStep.lean", "1c995e1ded980b84c05c954f8f39b27e585726519bb7ece470de09475268f73b", "608e2c967d26aab8c5bd1f50f8cc85a0681b29020c8a65a6bbf0a4b561fc31d6", .rewritten⟩,
  ⟨"ConLeche/Semantics/DenoteClosed.lean", "Ix/Kernel/Semantics/DenoteClosed.lean", "2d6b87eeb32a8aba907b1c865accd007d73b27953f9c40f4f0bd2fd059e41588", "515c0feff91d306765cde638f32be9bc942e5b296bb41a5b13fc960619816bb8", .rewritten⟩,
  ⟨"ConLeche/Semantics/DivModEval.lean", "Ix/Kernel/Semantics/DivModEval.lean", "9d28c9424a8bfb2e7a237444b2df74f620eb4e35d187a37cf38e4e43f8ab233a", "ab6e57695837bd86c0ad498db6f233a238e3ab25987e20e5201f22897e16e049", .rewritten⟩,
  ⟨"ConLeche/Semantics/EnvFacts.lean", "Ix/Kernel/Semantics/EnvFacts.lean", "8e3de0230aa6a44791ee4b4f70d2ec30481a46279794449fe3d0c4e78ac09f8b", "7136c41bbd3acfcdfef3187489173be466fe0bbf14c299562717e0242ee253a5", .rewritten⟩,
  ⟨"ConLeche/Semantics/EnvFactsCons.lean", "Ix/Kernel/Semantics/EnvFactsCons.lean", "b442ae915818a918a6ea3835edee8a9725b96fe40d11c819417120455440ab43", "66edff2ae91e4155579d499b98177e1b84263f3f3198e3a5103995c79835cd61", .rewritten⟩,
  ⟨"ConLeche/Semantics/EqTower.lean", "Ix/Kernel/Semantics/EqTower.lean", "553f77caeb6230dccd71f8058c88943add296d0a2cad07f55b712b81bf731927", "0717e86759c306a35ed870799526d5c4a58041e623f4cd29b970cd480e89f56e", .rewritten⟩,
  ⟨"ConLeche/Semantics/EraseInv.lean", "Ix/Kernel/Semantics/EraseInv.lean", "0eead13ca371f90b6fd9e9bd6f7f2c26fb27b007f051316b164a6cccabda6923", "9ca091b339591e2364e00cd1cc122ac97874dd9f4b2bae4bd1fa78f7bcbb46e3", .rewritten⟩,
  ⟨"ConLeche/Semantics/Frame.lean", "Ix/Kernel/Semantics/Frame.lean", "49f5e85775b8affe4e9754e12bc30e581e3193e8f1787e6c9d91ac463cc2eb7d", "38686908c7cc6d1d6564e4ee0059e641b4c529b13e687b0da4c9d64293a3ba43", .rewritten⟩,
  ⟨"ConLeche/Semantics/Hoist.lean", "Ix/Kernel/Semantics/Hoist.lean", "a3972db87b7f64d409d7fb121b8ce290f6568b99d55218e2e6f0fb2486a6ca9a", "b6c0e86090c5d39210ee6022cd62863ad7d774bd20293609164187a70e691e85", .rewritten⟩,
  ⟨"ConLeche/Semantics/IndBlockFacts.lean", "Ix/Kernel/Semantics/IndBlockFacts.lean", "9b00fe50549b297b169045fbc5a9f21042b07f8985b0ea0add15b53f1ebcae80", "e92f82294d65921cc6575c12765bfe5f1297a50b70c0cfac04be2c6702de72a0", .rewritten⟩,
  ⟨"ConLeche/Semantics/IndBlockRun.lean", "Ix/Kernel/Semantics/IndBlockRun.lean", "aecf908b0025be1febc417db7c92a61c073d7b313effc257cc4aef16576479b9", "f988a4fba9e2f6b621449a99eb290d2d950642392fc4c287014d7b07af062c92", .rewritten⟩,
  ⟨"ConLeche/Semantics/IndRecsCore.lean", "Ix/Kernel/Semantics/IndRecsCore.lean", "2d4e80032cf4a2b2bbfe266a2d0c18cffdcf6dba8c32def9c90fe2d037221ab4", "21819594b8296884854b96a04458163056408f998924985592fe19e853bb0b0a", .rewritten⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclNative.lean", "Ix/Kernel/Semantics/Inductives/DeclNative.lean", "eb1171230b628cd19479c1741d9cabbfde6c1c924ce33060e7ad75b4593139ce", "ee3fb576fbb08c54c993cb2fb1f60ba0c8884192e1e3acdb55ccfc9836cd9f81", .rewritten⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclStructEta.lean", "Ix/Kernel/Semantics/Inductives/DeclStructEta.lean", "fcfd962ff9c3e0ad1690f59f1ff744cde5bb41b6f1865888a7fea760a226af3c", "3cdf300515ee72ef4eeb6d314844aebe7a757524ec78da12c41d97dc7403f69f", .rewritten⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclSumEta.lean", "Ix/Kernel/Semantics/Inductives/DeclSumEta.lean", "7973a1d6fbf0ca597f90a1f931d6be015a067197ee7b2435e306a523352cfd22", "90ff86bdd8ed12df3157a2730de14f8cab63e25922fc816e55e52a1fcec586d0", .rewritten⟩,
  ⟨"ConLeche/Semantics/Install.lean", "Ix/Kernel/Semantics/Install.lean", "6698dcca50e4ca49bfb11240ad06e125561ee5aa4926fd9db70a0500f7fcb6d3", "83451376e95dbc11f5a8ecf423071011cd15e1923e405752c5bafa0732cf47f9", .rewritten⟩,
  ⟨"ConLeche/Semantics/Interp.lean", "Ix/Kernel/Semantics/Interp.lean", "4dbeae234bb16963229cef391c05f4b3ddfb85e85eb22cd8c41c81b35e95083f", "89495526f65fcae44010df3c5dde304349e51363625d79f7effd9e5562c52336", .rewritten⟩,
  ⟨"ConLeche/Semantics/Kit.lean", "Ix/Kernel/Semantics/Kit.lean", "c45d247ea013411919e6027fbb56c1439e491db4cf6ed0f41d60eb430302fe44", "743dd15c4c385c7cf9e0cf4e2d13714b33bd79e61a3729e95388a160cbef9b79", .rewritten⟩,
  ⟨"ConLeche/Semantics/LitParams.lean", "Ix/Kernel/Semantics/LitParams.lean", "951c08efa8634825711ef4b31eb87d1dc940a46847c5adb01334d127ac18c5fb", "ef605d05094a954b1dc200b89046b2a0770794d6d337ecd24ac0a6eb279f32b8", .rewritten⟩,
  ⟨"ConLeche/Semantics/LitStep.lean", "Ix/Kernel/Semantics/LitStep.lean", "6e343ff73a4efdb8c6cae1a441f6c8c077b37103369bb7f52c781f829d83be77", "6c9e4c67873fe1b69daddfcd62703b362a27bc3bfc8aa1dc4009ccf88c8bfba1", .rewritten⟩,
  ⟨"ConLeche/Semantics/NatFrag.lean", "Ix/Kernel/Semantics/NatFrag.lean", "489b4e54f178cbf46a4bd9ef553df01a04b752a01bd8ff27ed7d3047926250ee", "01d4cd65cc78b56876765eb144757ce88a89e7063f6b8018ee9e276ca0f6d639", .rewritten⟩,
  ⟨"ConLeche/Semantics/NoBVar.lean", "Ix/Kernel/Semantics/NoBVar.lean", "7e48ede47f9ee5063f2bfc1f47d6e8a10a6dfdcb4f3c051412a62f26c51b8c8d", "c85b6952d7e5c30db9cb0cff0b4b973d3224664090ffb98aa0828fdb27cd03d2", .rewritten⟩,
  ⟨"ConLeche/Semantics/ProjFnFacts.lean", "Ix/Kernel/Semantics/ProjFnFacts.lean", "299222b80a583f408f792b89fdcc467af2423613d7164fc0f723c2776a1eb4e7", "14da58ab6e804bfed50198c6e15c0dc1b0b17e1939ad97f848ff748fa814f847", .rewritten⟩,
  ⟨"ConLeche/Semantics/ProjPhase.lean", "Ix/Kernel/Semantics/ProjPhase.lean", "8dfa48429adcd7b8569e3f8959d6239d2c8647bbe2ca5251a0966060c33a4c50", "1736175c614590dc07c9b8f4c828be1815dc465893e8c80ca97a7dbe3536808e", .rewritten⟩,
  ⟨"ConLeche/Semantics/Sat.lean", "Ix/Kernel/Semantics/Sat.lean", "6e8233142c7642e27df388bb47de99b67c1398abf4fdf828cebac2ad1c3d6ed0", "c52d2e641441407715bf2e448aef0cbb72c70d76eb3879db86e9f80c17792d53", .rewritten⟩,
  ⟨"ConLeche/Semantics/Skeleton.lean", "Ix/Kernel/Semantics/Skeleton.lean", "5ee75be1db55d20bfc1f7e4a5a96fd4a1e4a36921d55564385ad28086de97158", "d5c346b722be4a08b90f5305a0350fdc8ef11c8befed337778401b65fd087d7f", .rewritten⟩,
  ⟨"ConLeche/Semantics/Syntax.lean", "Ix/Kernel/Semantics/Syntax.lean", "27d076ab2c00f78fdf14053c6b556005baaefd99617a5ab41291ac64e50afbdf", "1063a08b18f4b70d8c11f8b06a03982d785f89edc5d4f89aa6c469a332887df8", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixCaseI.lean", "Ix/Kernel/Semantics/Tower/FixCaseI.lean", "23dfe356300642ead68f9ee5997bd72246cb1917a7e06cb994bc2c2c67e41192", "48e8500ea059527aa39901b504d90708ba6d8276448a1f496e8a58558a5954bb", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixElemI.lean", "Ix/Kernel/Semantics/Tower/FixElemI.lean", "252dafa16cdebe0539beb6f772b21ff6411c07dc4a887bda138eaade3feb869a", "50b5ae1188ed8fe51e3419c960e402fc3dfd253ae6aaa448f97d4a6d0a5dfb8c", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixFamI.lean", "Ix/Kernel/Semantics/Tower/FixFamI.lean", "f05d85427465f0b8d62da4f4f099858ca99b82537ac9a2f069a7ade2c64cecdb", "108105d618aa1f4a6656fd22ab8fb71986b04c7d48bd795cb1a259f8c78c88e2", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixIhI.lean", "Ix/Kernel/Semantics/Tower/FixIhI.lean", "4035fb0f46670e5d3edb80a1225a8247f8a20eb1bd73b604912ab250b0d3a15d", "da62aff13fcc9eadb3b10d5a05a701d838f11e6ab8af1306cdc79f071a735e51", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixLeafI.lean", "Ix/Kernel/Semantics/Tower/FixLeafI.lean", "bb6ccf0e200e62e10c49ff25652198886b57e0adae2e0b77c1d59f06330897f7", "96e696cee04b76cd8ba7f0ef9fa3573c05b9585b6be1dfe3ca657d9b019f0a67", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixRecCoreI.lean", "Ix/Kernel/Semantics/Tower/FixRecCoreI.lean", "fae671af06ed6003433326eeca99c9079905d5bd49b2d12ed821a1e193862187", "fb174ab0e5ee6cb4a8ce3ca87f8d3f7f7d29aa6911e24108f25572332ddc90e9", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixRecI.lean", "Ix/Kernel/Semantics/Tower/FixRecI.lean", "8a7ea4fa6927ef43e2e54f8586448bc3cdd2a94dd703d8a2da69e0d8986c0c82", "4303cb72535bcf83132d1cf4380985adb97b54921b9b8dea94429c8d8b03f38e", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixSquashI.lean", "Ix/Kernel/Semantics/Tower/FixSquashI.lean", "101c7d7b6842d3adf1938e15ef25b5eca4e1156d8aacf1fcab2f698d50c86c95", "3e48d4f0bf30990b03d07150496473cec7d38b6eb1e94d70d8d98d3293fcbaf8", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/FixWire.lean", "Ix/Kernel/Semantics/Tower/FixWire.lean", "cc12d5b9ca87faf0a9fc9c3d1a3b13c133894dd924f784b42e1bae44c0ed627f", "d6dc829ba19b1cab6c8b2facabe896eb68aeeecb279cca8a2455b4c6f1d6c054", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/IdxEq.lean", "Ix/Kernel/Semantics/Tower/IdxEq.lean", "c2372388c5fda43c4041a90ad7c4025dc4701576afca0bc217789096d449b61b", "4726c0114fe3acd6faca0b3d499d81010d7677ac1d40fb420a4596dd7ce48bce", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/IhSpell.lean", "Ix/Kernel/Semantics/Tower/IhSpell.lean", "1dc017c51707b9e9893d3e7ccd867319fc6a7f42bc03e22bee01c9f59202293b", "4856d66d778bf720af05c418d649e47bf9af3b016c114d5f78295f92567c4df5", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumCase.lean", "Ix/Kernel/Semantics/Tower/SumCase.lean", "2d61358fecd1a925009af4546069d6d437fa16a19ccd3c27ac3ecf26a556ec25", "b2f195df943f6f1fa663347e424a8a1f81e9bce2d99242bda18bce90def924bf", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumLeaf.lean", "Ix/Kernel/Semantics/Tower/SumLeaf.lean", "1fa812c76f28d6724a1110bb9a9d97ffe374acec8b5377f57541334efad38ce7", "5b786b76ed4da32c88935ce3130341c1d62aff64c6cd5f235246dc3399520883", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumMk.lean", "Ix/Kernel/Semantics/Tower/SumMk.lean", "e4ccb6dfdd9c99485005677857a67fce3abce3261e7cdba75a13bbb185cfc78b", "39efda674f5c5b762ea4ffd7c728fcfc31eeda8509722190c58ad82b026941e8", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumRec.lean", "Ix/Kernel/Semantics/Tower/SumRec.lean", "b1aa1f4a4df003cce9f3b0d5edff859cf499f407b085eaa9ea71df350169c7c0", "076011bb2e92ef61f6e683ff2cff49e6eb0000c1f03ef72dc7d4e8ac0df8d436", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumRecCase.lean", "Ix/Kernel/Semantics/Tower/SumRecCase.lean", "bb8af169e1d83c0b991199deccae8b85d9ed55271e513c33984a632e049d25d2", "7414d01ec0da85ae97ec39b30d9c34d73b01796dfe0ce875c875dfd6cafbd293", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/SumWire.lean", "Ix/Kernel/Semantics/Tower/SumWire.lean", "bb83d1fe0b182ba32a93db7aef8a399565a248cb753ae5baf7f1d59e69689bba", "95794a2a5571fac27344cf561ba0c1b8a09ededb9c9e647f4bc28ceef15a59e8", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/TowerIntro.lean", "Ix/Kernel/Semantics/Tower/TowerIntro.lean", "81f2debcaa601e3fe1fcb485e44c14090b33a14022f97c05bde43b764944db9a", "7c08de93e9bd6e364a5e9444fbc4d23df3e8877cbbd3096d24f9c94c1776ab49", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/TowerLeaf.lean", "Ix/Kernel/Semantics/Tower/TowerLeaf.lean", "b2df2a78bc81cfcd87bf76c9afc12c34c2ba4b0cf0d1436725dc2183ba20c7a9", "ffad9a89e8702d432701d4237e33c06d0f46eb259228d5ca4212901101296e78", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/TowerMk.lean", "Ix/Kernel/Semantics/Tower/TowerMk.lean", "99897d47cfe78b408cff5fc59b398ad43399a80c499aa4fb57436268a99a0d64", "fccaddb6a9445d3fbdc00fc4cc131fb80557dd4935a4623774eb7431c1c6fd2d", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/TowerRec.lean", "Ix/Kernel/Semantics/Tower/TowerRec.lean", "617f9a9e0125408707a8f052a5fec7299ad106e5309ad1e6883700a9af3f34a5", "56b5a8a81f9bb66322bce747952d8cc45681a32226f136563e014572b171686e", .rewritten⟩,
  ⟨"ConLeche/Semantics/Tower/TowerWire.lean", "Ix/Kernel/Semantics/Tower/TowerWire.lean", "30b105dd85a6ce0601cb82cab8227fa311665944f5edee656ec3d43420499de4", "990554996855fb6ec5d6e15295bae7b6beaaa3cc8df807414337b484e77eaaa9", .rewritten⟩,
  ⟨"ConLeche/Semantics/Univ.lean", "Ix/Kernel/Semantics/Univ.lean", "898f7e15881abb126d6d7533f59990b4659ce1328aa7e2a1bad5c49c9fb7c6cd", "6f5ba289c316acfc559eaac013a83ffc6b5f9d61f59186c03bd992b5345c46e6", .rewritten⟩,
  ⟨"ConLeche/Semantics/WellDenoted.lean", "Ix/Kernel/Semantics/WellDenoted.lean", "25fcb0c72f7c8044542f364b5508702419b0ab693a2c9b4a30d05ab759fce2d4", "a41928769a351fbb0e7d3d23e3b0dba0eeb3142ec102a2bcbe93726a2d382662", .rewritten⟩,
  ⟨"ConLeche/SetModel/Container.lean", "Ix/Kernel/SetModel/Container.lean", "47b7bbab4764309ad1a11d7e6a3d2061c2968928367e2285e2a7e549bf7e6c0c", "6211b413aeb1ffdadea3ca4d999e1fecf6f01e536bb71288fc45ad9b20700b03", .rewritten⟩,
  ⟨"ConLeche/SetModel/Iter.lean", "Ix/Kernel/SetModel/Iter.lean", "0688fa56fad4dcac618589cd9bafc2860c43b95978dc6dcf6c3e292cafc4b149", "4b868a3053fcb7957be27b7afff8997d3c20c45d4bdbdcc4015e9b623144a060", .rewritten⟩,
  ⟨"ConLeche/SetModel/Ops.lean", "Ix/Kernel/SetModel/Ops.lean", "b19d965f92d1e281afd40a7ee4b2edd1a324b9bdf6d8f26425944dbafe987a11", "6f3cf6d54458c8f8390b2ff08dbcb0da5180e4258c355890eecb36db6dd9c719", .rewritten⟩,
  ⟨"ConLeche/SetModel/RecGraph.lean", "Ix/Kernel/SetModel/RecGraph.lean", "66de7b97c640cec3987f89c31ae19c4daa27b6da53ba6943767e0078802f1faf", "da8c4ff090e6b05cb4b50f77d8f4f0ae3e1ed2eadb35e8e8efaeafc61805cb15", .rewritten⟩,
  ⟨"ConLeche/SetModel/TaggedSum.lean", "Ix/Kernel/SetModel/TaggedSum.lean", "eb64def578bf85bc2b197b83648749996ebcd243be573752f617a5f91f3332d8", "c0609a82fd9a9d7572767e8c5604c7eea0ce112960433b9014cc157cdc2112c6", .rewritten⟩,
  ⟨"ConLeche/SetModel/TowerMono.lean", "Ix/Kernel/SetModel/TowerMono.lean", "e11d20f7f66a4ee6e9fcf07c5dd06450a0ee3bc7dda091a7f829672a192d3e7c", "e35d91fcbdfaf00bd6938065c651ae3463638b56089dfad2dcfca2ed3f294c35", .rewritten⟩,
  ⟨"ConLeche/SetModel/TupleTower.lean", "Ix/Kernel/SetModel/TupleTower.lean", "143b965d29faae965c16288021ba1cf401c3f10e76550386ddb81d9ca1f5cbee", "e87305dbf3dc839cb98680558af1370c059229e462934576ca60aa962b698366", .rewritten⟩,
  ⟨"ConLeche/SetModel/Value.lean", "Ix/Kernel/SetModel/Value.lean", "280afd97ddbec2330285a17b269c2171c9675c781e0dab2ffcb4b38383bac385", "83898b97c57619c87dc9925436b6230fc711385a9b6dfb3071f2295aa7c1a86e", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Basic.lean", "Ix/Kernel/SetTheory/Basic.lean", "0ae5172c477170a25c67626ecd2f29286976b0cc0ea77bfef69abad0f7414813", "dcb298b3061ccfa3f83c57e216cb6793207e32c74491ed371b18da74eff7206b", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Core.lean", "Ix/Kernel/SetTheory/Core.lean", "52f54c7f8664a0d00ba04083d428ff81c2b89e7e68fbd6e24ffb349ef441f19a", "600d396a6e21619f4c197a6cfa6dfca4d59bd0b4f02e9a40933eabd76c2ac42e", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Choice.lean", "Ix/Kernel/SetTheory/Derive/Choice.lean", "a8404566f4d831874e044dcfba6865b750fda3c9427e13c3d2b68d7ac45d5b48", "93cf9596aa5d54ee280d5ff58656eb3319b4abe989d3b95be5bd5c9f0eff28b6", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Empty.lean", "Ix/Kernel/SetTheory/Derive/Empty.lean", "259b3b365926256fbe8281a7066be601e419c3e492452b62086e0fd44e1a3f16", "bac256f8ade4cd984c43a02b3469bae1a036c59ab2b85ec2687b0d1b03bed608", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Graphs.lean", "Ix/Kernel/SetTheory/Derive/Graphs.lean", "f61433765add5a733b38e95e38e217273f526a5e710b7109f24eb0f83f70faaf", "f5b8730e8d7a087e6bf0a1d15cde087d6d568fc4fd8ccec20cd13d50ca4ce1b3", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Lfp.lean", "Ix/Kernel/SetTheory/Derive/Lfp.lean", "d6c1a824ee0b358f4007c2d297c4e29011c95914c2241d402f5bf27da333614f", "cb0fcb0c373297478e3704cde272f70c666336f4cc043d3e75739af023330a7e", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/LfpFam.lean", "Ix/Kernel/SetTheory/Derive/LfpFam.lean", "18fa2c12b37d9786b9a1961ed526e7d411869d93cfa241ebbdf2910d4418ac97", "42d818d8d22ff61968e8fe45b1a5d5dea2c4e42171e29774fecc11aa706b4aef", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Natrec.lean", "Ix/Kernel/SetTheory/Derive/Natrec.lean", "a37e6cf282ae06bb3bba7a26a2d692ac7ba310b3beb2571c84bb34ad9d0ae304", "8de9dc3e06012acbece3a40c1fd1103afde385f03dd24638d57f0a04b63bfccf", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Omega.lean", "Ix/Kernel/SetTheory/Derive/Omega.lean", "c0b20ecd0cc88a74ff6091e5a88506269b587bbc6f1919f72cc63083d2f7e55a", "41bb8999d9472dca1d6eadea98aa82e1c161384e0504a72873f1579ae21ffdba", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Pair.lean", "Ix/Kernel/SetTheory/Derive/Pair.lean", "851f954187fcc05ba2f43a6b81112df27c91e34f7de54352eaf461380fee1bd7", "6bbf4e28d9211d945c22141d2bb237abd0883ba811b368537551fdd8136f492c", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Pt.lean", "Ix/Kernel/SetTheory/Derive/Pt.lean", "93f9ed86375f7af7a004f3ef2612ce8c9d8c6626ce73dbf6c3d6702f95f67eae", "018b23818889651e9c0b74d4bec080079925045fb40e29e41c309de4703e7fb8", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Quot.lean", "Ix/Kernel/SetTheory/Derive/Quot.lean", "cadc387495c563d796ba4ca45cc0125cbe8ff5168d81bc47b364bd6776c3898b", "eef992a025d853ffe0b838b788861c375d49e5a37d81da0d0bf1a88b8b570dd9", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Sep.lean", "Ix/Kernel/SetTheory/Derive/Sep.lean", "a6a452a34028ff2e194987de8fc5bc8f847ff8950f962b5d33c6c6ee5045a52e", "c59b042f24d028bb48d021a8eae6594f9d8f146bbc92900627e8ce9c58129a10", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Sigma.lean", "Ix/Kernel/SetTheory/Derive/Sigma.lean", "1a844ecb6709ae0ccefd43a4eb8d6da92b3753033e882ce74cfbd27c6890545f", "882fde29de2c0ba8a7266788b8e24f09506dbb7fb355e258e17b8eb8f6f60766", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Univ.lean", "Ix/Kernel/SetTheory/Derive/Univ.lean", "e1084f7c82d9c0d144281491ceb05b015001d1215947d0d687e4dc07497ff911", "0625cbfe60e5340eb6ba8a4e0ffd42f7a065097fe9e530945bc02786657fba1a", .rewritten⟩,
  ⟨"ConLeche/SetTheory/Derive/Universe.lean", "Ix/Kernel/SetTheory/Derive/Universe.lean", "57a24b4144088ac14dabdb9b6f88c49cf251a0659f8d4c073aad6682baeb099d", "f8e83e824019dfc0eaa20960097b907f15ab805717538e6f6a01adfd8c07b471", .rewritten⟩,
  ⟨"ConLeche/Kernel/StdAxioms.lean", "Ix/Kernel/StdAxioms.lean", "4128b3cd64a01604ee4ae9570e4165b9e5ea16b9c287b19a3db0072819fcf4a2", "ab6509732a6bbd48aaa4ecbf7abc608d71980424473a0d67f4da9990dcee0a75", .rewritten⟩,
  ⟨"ConLeche/Term/Const.lean", "Ix/Kernel/Term/Const.lean", "2c5bcc4177d1c6a5e57a84e7d6d73dfe9d3da04b434e227d4755301b50aaa002", "4dcc28572ee33c5b00199a494b5fbf37cd0487908612716665fafebdd26e33a8", .rewritten⟩,
  ⟨"ConLeche/Term/Subst.lean", "Ix/Kernel/Term/Subst.lean", "cec1d84d0f921f107911a3eef0033bcb7f40c4c3c4c911e8ce5f198f27d74370", "611d4f093dffcc125919a1f2398be3768e2ed34db22a3dbd90d82aeeb1442499", .rewritten⟩,
  ⟨"ConLeche/Term/Syntax.lean", "Ix/Kernel/Term/Syntax.lean", "e51c4f3e3861bbd0bf3bcbd59e462f48cc8e28a10b9eaa8a385ab2418cd45ed8", "341d55949fdd9bc6a5b0e41741cef316d276a516b93820bd3d4a4372805fb36e", .rewritten⟩,
  ⟨"ConLeche/Kernel/TrustAxioms.lean", "Ix/Kernel/TrustAxioms.lean", "8a3cea4eecbf976204dfaf6fa063c9c0cb1b910954c14bd6bb8a6e6e406b05e3", "47a4048dba8e194419e63482e7e7e87de63944a1e2d00707e5fdb8e6630702f4", .rewritten⟩,
  ⟨"ConLeche/Kernel/TrustPins.lean", "Ix/Kernel/TrustPins.lean", "4177e539a845c9fbdbc94d88ab5b1f0ca2075aa0f6718db4b6a1347a67c681f2", "7a3e2ec45ea6acd5b59ff7566a686efb39639f586e9d1d2c9b0be90e6337258a", .rewritten⟩,
  ⟨"ConLeche/Kernel/TypeChecker.lean", "Ix/Kernel/TypeChecker.lean", "584a3d1499361565317c7d561a3c36ddfdc076d2ab67b4ef5abec74322ca2848", "d20c05bd2125d35402d091883dafb406ff06edefa4de7246f4570ab1f6085c0c", .rewritten⟩,
  ⟨"ConLeche/Verify/Abstract.lean", "Ix/Kernel/Verify/Abstract.lean", "f30d2d6e81fb6cde405ed7522ff1d74e445b3f2ea845cb94ce1dd9aa58f9580e", "dc68e564f0386e7783a1823a34f083137d575c118518355539b67cec0811e715", .rewritten⟩,
  ⟨"ConLeche/Verify/AbstractRange.lean", "Ix/Kernel/Verify/AbstractRange.lean", "1769afd8e72e71fa99e5238319aa2754743aa90b75d75a00ebc84a56d3de129f", "08e2f0b16ba7f591633591a8c31483d2a61cddf78ccddff6bd0e39a48e8dbc3c", .rewritten⟩,
  ⟨"ConLeche/Verify/BetaGate.lean", "Ix/Kernel/Verify/BetaGate.lean", "c81f01740d0885cb0416af5414b32af08186bf9369423fed4cb62d5101b7cdb9", "c8c4078841e0e8f736828865a0b5f5f3851719993690369fa2beb6066c314be3", .rewritten⟩,
  ⟨"ConLeche/Verify/BetaSpine.lean", "Ix/Kernel/Verify/BetaSpine.lean", "9babc7f372c7cf789b6d89d0561bcc74263b49f7c05cb2649bf37a029daf5fb7", "a2a12a14e5f71542581e8a1c36ec3f91e22c17b4cf7b3b9f44e3ccc72a2e5a2b", .rewritten⟩,
  ⟨"ConLeche/Verify/BinderLoop.lean", "Ix/Kernel/Verify/BinderLoop.lean", "abc19f63ca5f3b49b97d0e3cce6e0d8e0e3eb3fc5793d2355bc9a40ca7d4689b", "561ed571949ec5965804cc4f0c6500fe96e00f826a9592cf5a36823881261140", .rewritten⟩,
  ⟨"ConLeche/Verify/BridgeDecl.lean", "Ix/Kernel/Verify/BridgeDecl.lean", "8ebc6e4e5b4e8f380bda28509aee56f88151b9ed7966728be4692559befa158d", "292e87a70aa07a4ee41aacde7edad64b3350939efbc1728f2a6165d8f89d901a", .rewritten⟩,
  ⟨"ConLeche/Verify/BridgeWfImp.lean", "Ix/Kernel/Verify/BridgeWfImp.lean", "c7ac837bfc361db411c3cceea198674666245855b4dcad14dde4dd882d78c6a6", "4055f6da08a5d50b506c2c4075eeef41a06d63f39d2580035f08e8e473ba5445", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/AgreeFloor.lean", "Ix/Kernel/Verify/Cached/AgreeFloor.lean", "ac637eb894591c2c1d9b7cb8ceccab89b92776d69c999b47f638cafaeb324d99", "8413e74dee69e7361c4f82dd75b48e15de0105d5a8e26e017a249fcc4b0b1bd8", .adapted "4.34.0 fix: +1 line `import all Init.LetFun` after `import ConLeche.Verify.EnvBound` (letFun body not exposed in 4.34.0); port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Verify/Cached/BinderLoopC.lean", "Ix/Kernel/Verify/Cached/BinderLoopC.lean", "7d325928eb869176d448f8708ade4faf54be7c39a9e47b9072f6bd61eb7a791d", "a9f842df4cd6820dd1754bacf33aa1e49e556896c93194268766197967fb41de", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeC.lean", "Ix/Kernel/Verify/Cached/BridgeC.lean", "71e505aefecd755e3ce2c446bf841f280ee2fb5ff4437f11dcac284a7118c0f0", "8595ddda344579416b0f04a4fab599dce6716fa875afac6533431aa782bd4f2f", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS1.lean", "Ix/Kernel/Verify/Cached/BridgeCS1.lean", "0144764ede94cd97f254db9f94bcb07dd12aeb08ec8f708fe892e61332f2bf78", "c018aff5eb2f9abbba364a0d691f37f172e86cc80ec730be2c4def0871e3f0ab", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS2.lean", "Ix/Kernel/Verify/Cached/BridgeCS2.lean", "f9a16dbd9e9c2c70fc31f8d16dd9f446d82673b941e3c1a4656a60fcea6be440", "49cd44ba596966ef79d59d55ef29f5892bbcf6a913f897a410b2ec9f88b18762", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS3.lean", "Ix/Kernel/Verify/Cached/BridgeCS3.lean", "9d8f94b77b55a7b43f24a97743c90e585167313fe53d1816410ea0fda5dcd211", "fafc7a287caf91f0c2bf5a71545549e50009d0070cf8c8827966163ae49c930c", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS4.lean", "Ix/Kernel/Verify/Cached/BridgeCS4.lean", "c435b1f968ffc261a27d9d4540630683d55ea08905aff7d8b8042e494f531705", "868ddb8be82da1e2f414fa8b5e96ad1e9ded8193ef4a5de72bc60fde5eea9564", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCSDecl.lean", "Ix/Kernel/Verify/Cached/BridgeCSDecl.lean", "5d843a4f271d754afcd217003df137a4e4f9642507f7a44690b04512f8bc3f84", "0005b5849fab816b686c0fbddf3875a604f80b4d027e357f5b397c234f5a0406", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC1.lean", "Ix/Kernel/Verify/Cached/DiscC1.lean", "6d986949138cf13b9a704674ca0e6bd9a51528bfe023fb63307de8c023548984", "922096ca96471e3308cca5a2828070f6d3f9bfefce699138b31622e5a9d6b412", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC2.lean", "Ix/Kernel/Verify/Cached/DiscC2.lean", "ccb50ac29947c53bc4d0fea9b3fd463e82bf9237d02f1d13a83ea112e191faec", "bba1870e1118e965859f1f781e0826820df690104e6c723e235364ec9a07dfc3", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC3.lean", "Ix/Kernel/Verify/Cached/DiscC3.lean", "33336612439bf6f53503ca0ca08993cdba916aefd2eec7ddf15b00fe16a9efe5", "a2f52c33abb891dfb666ef632d6b577042b5abbcc83c4632a78e8947368ef77a", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC4.lean", "Ix/Kernel/Verify/Cached/DiscC4.lean", "9a2bd32ca036da125d79edcaefecdbd72700ba48875da7acfe69a212d0fde06c", "6ed0aac5ddc31f696d12904933d940a4252a73dd5a59b376736dbeb9e8ebcd54", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC5.lean", "Ix/Kernel/Verify/Cached/DiscC5.lean", "a123e647a381985059d5e71a0113da22c22c9d37f9aba8dbd7fa41d5b7643b86", "f9cc35378c4fed1c3a87fa143ae0d3d3d8cf77f3ea59798be25cbd167edfac89", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/DiscC6.lean", "Ix/Kernel/Verify/Cached/DiscC6.lean", "211cda73bb1f83a76b6d7ad834c78834525ba76cd44264e8e5956b0e67e1a8a1", "1e1e117ff7647a891a20129b2333ff916d60a585da7b023f5df3d40673f18693", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/Erase.lean", "Ix/Kernel/Verify/Cached/Erase.lean", "c2ce9dbe1b7b2cbaf010221661f9d8a79789ff93437c89744bee596d0b0af9d0", "f4d1cf36276ff869cb0170957936c3f379204f5bae0025a3943434142b253f25", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/GuardsC.lean", "Ix/Kernel/Verify/Cached/GuardsC.lean", "ef59f6b72bdc7b5d6c8cf164cbd11b46eb2f52bd5510d4540da6da8e9d3639e5", "0fb9dd44aef8de10c25ab76048864b992fa4caa94cc6d049032d3d4e2bc7e7ae", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/InstalledC.lean", "Ix/Kernel/Verify/Cached/InstalledC.lean", "9e1b2a7f0830ac4c45c779c850367a2956a39713f2d2f781651b09aac5a17d48", "769931971b0b7ac1e5e7873bb5dbbd7aaf2e8669b61c99274c4f297c636fefea", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/KnotC.lean", "Ix/Kernel/Verify/Cached/KnotC.lean", "97c186e24480141e23eb0b109172333485105b7bce3d69b54ba18771820f0e7a", "99abb93a13b49dccdb4cbeaaf31f275f467915aeb6ad98b3544865d0958e0f4f", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/KnotCongr.lean", "Ix/Kernel/Verify/Cached/KnotCongr.lean", "4e013683f0eb1e674819646ccd66d4265c49ae43d3c429831030368d8d3fd2e2", "286ee3258e5cb948341fa12f4771d953f015c67296a18d8249f8988346b78a47", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/MainC.lean", "Ix/Kernel/Verify/Cached/MainC.lean", "caa81163d62937350c069ba6c9a4c48bd76f2533296122b16e1f5e520aeb32f4", "7dd8e0a4944167c95fe19cf8d48e2f4c638335287e06b6a984a8732d57d641e4", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/OpsC.lean", "Ix/Kernel/Verify/Cached/OpsC.lean", "113b042315f6beaa325cd32544ed9090d178ca170bf862503c2ea54d5965c767", "31db286d0352bc81f8ebddd1399598d08473b92dd81fc91398af51c4870384e1", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/PushChain.lean", "Ix/Kernel/Verify/Cached/PushChain.lean", "6c33408f9e74de5ad4c19fc6bc060242d6b67d3f5338a1ab198a77b9c9216563", "8408aac50e47a7dc83b3951c251057d150c41d2aa4c169755d62fab483387b32", .adapted "4.34.0 fix: +1 line `import all Init.LetFun` after `import ConLeche.Verify.CheckerF` (letFun body not exposed in 4.34.0); port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Verify/Cached/SimC.lean", "Ix/Kernel/Verify/Cached/SimC.lean", "5821419432b77b53564e8002b1000dc8101f3cdb2c386769af92184ecccb1d5c", "cba8b4703b9ac5f631a721de52424af0191566e4c0158be2136e14c2f8ea7fa9", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/SimCEff.lean", "Ix/Kernel/Verify/Cached/SimCEff.lean", "d3a27826824654c59f9e100d5ef0f44a8262c33165b2da44a84beae215a0772e", "9db2796485fe68d5d4997c43afacef550ae6d1d65b2f0f67ab9c2e21dedd8cba", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/SimCS.lean", "Ix/Kernel/Verify/Cached/SimCS.lean", "499103a0f7f4515a44201589c1676bffa5d7ca56271666592a785a74632f1ca2", "506b679451044c09b990af8e765b6ccdc712ae05074b932a283613324d1eaa57", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/StreamThm.lean", "Ix/Kernel/Verify/Cached/StreamThm.lean", "61868dbdcd6ecff73af74102c0472f1be6558a1afb3c8a048b9d3c6ce92d14fa", "5448c4fb03d2fca31db0da477dfe640053b3f0a8b171714e657df30d1d8653b4", .rewritten⟩,
  ⟨"ConLeche/Verify/Cached/WalkersC.lean", "Ix/Kernel/Verify/Cached/WalkersC.lean", "fdf625ce57e07f01bd5825532ac1fd04d14b93bc6ff752daa506ca694d2587de", "1e18b861b163f90cee55beba1814e67c89cd90a7dac4522e418fde943d2ab6ce", .rewritten⟩,
  ⟨"ConLeche/Verify/CheckerF.lean", "Ix/Kernel/Verify/CheckerF.lean", "5d7e591e110d50ec45cd6f049ee2582c6f1df837c27d3a9a25726a153f32121b", "e680d4396f4c8e4262ae71bed494c7b33e98f8b7945207114f1351db8a1f64dc", .rewritten⟩,
  ⟨"ConLeche/Verify/CheckerSplit.lean", "Ix/Kernel/Verify/CheckerSplit.lean", "e9e3f93477e26da05eefb7f1a33da0090918b1ddf1e378b1911df590520a3fa3", "8a23cb7ec19bb390ef165fde2058df2b605f267399409009131b1b89a4ef552f", .rewritten⟩,
  ⟨"ConLeche/Verify/Close.lean", "Ix/Kernel/Verify/Close.lean", "05fd1fe8546c8f1dfb60fc84594d35f2bf35932147cbfe85d6aa9434fb523af6", "f973e764d27bd3d6a7be9b123c5553e95f83f6013254eb3c38aee5b0e63a0ded", .rewritten⟩,
  ⟨"ConLeche/Verify/Deep.lean", "Ix/Kernel/Verify/Deep.lean", "bec52c5a8cddc78724563d4195f4a82edad74f591bbf15aa28493a6444acf9e8", "cfc29aac6e06e76731f215be841318f0b99e27503305cfd058c3b80930e9c41a", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote.lean", "Ix/Kernel/Verify/Denote.lean", "9fce328e9015917a387ff9e981dcf653ca0f669d886acd9c70e2bfd9ed0e27b8", "43c3d068af45ad967ca24e16ed35758894f755b215c750078c0cac81459f693c", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/EnvExt.lean", "Ix/Kernel/Verify/Denote/EnvExt.lean", "3f18b4653c3fb218c20bfc2ec681bb37c3eb0fcbdc28c2160b7ab2b075b4a3fc", "27761b108e018570e6bc9a978672eadf71467c2c70c854bb374c44c807bc9853", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/IndFrame.lean", "Ix/Kernel/Verify/Denote/IndFrame.lean", "51f49c63af4504b9dde1f25d38569cdf3810b3dd374b71fbc7504322bc2c0843", "f1dd3c41f6701d6f497aed163005704aae5e3c545f003a0a83c47e8ab624ade9", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Inst.lean", "Ix/Kernel/Verify/Denote/Inst.lean", "2822637a806dbb869cf2806fb2408571b84b18b6bdf5bbb24dee7ab442ff83ad", "34748285920894c240dec9eb7a1bfa31b2fb017537ed8a85b1b4fd38f6521e36", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Install.lean", "Ix/Kernel/Verify/Denote/Install.lean", "4f1f29dd9b41a74bd455682343f8f2ae6fa2f9741783e7c17210dd4966c9a15b", "210b84a39a0f9adcace188af7e1f22dc861ea7a08ff081de31b0b5f5a0a180e7", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Levels.lean", "Ix/Kernel/Verify/Denote/Levels.lean", "ab071a2d022a80125b88b2443dad32c760da9bf4817745c592d5016c30f192ac", "535f62bfed2db4b1d22747e598614fbecc356d214724f29f560c0f076db7443b", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/OpenRevDenote.lean", "Ix/Kernel/Verify/Denote/OpenRevDenote.lean", "63767e971ee796e073ffcb3f2b0a3d4324e022b78f42d81d50b7a9b5b9964863", "fba9f38636217451adb246df182d54fab8b11b54edfbeeeaefd94d96393026d7", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/OpenVars.lean", "Ix/Kernel/Verify/Denote/OpenVars.lean", "ec17ae785476357a2911c1fc40429873177614a98bc1349635df4c187c645281", "709420c816151fab49f546ce202396a07535e0a54ccfb6757f2a8219133b5f13", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Pinned.lean", "Ix/Kernel/Verify/Denote/Pinned.lean", "62bf088209ac45cbd32f31fe13f86d2114dc3b59d93f3da84fffa2655d89a113", "9ddf60b7f36c40f38ade4de76a48eb6c4c92b79654e3a598c30f7d36b077d10f", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Rename.lean", "Ix/Kernel/Verify/Denote/Rename.lean", "ac914838976ff0ed079b3d13399edb3356971c24a3b543604da5af9e0c5e6684", "8b8c2f00a1052e22931766977ac4fd7114d275b69039a675b28b7105cc2051dd", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Shift.lean", "Ix/Kernel/Verify/Denote/Shift.lean", "fa34f824832d8939c2646d7d3e159936aaade9ac34436c72b8c2d59f680a092e", "97202d384e1ab5c7f7cb3f2c410a948806700d238d2e8e806320745d7dda3736", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/StrLit.lean", "Ix/Kernel/Verify/Denote/StrLit.lean", "2d4a5180c98c9a281b4325cb96bad2fc9d0f895081aed8bbccce1063c3fc4d94", "a4975ac5485f65e947ff3f9c3015e480e73de0c20bc077b4de20aa8cb514b8a7", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/SubstConst.lean", "Ix/Kernel/Verify/Denote/SubstConst.lean", "f8c0dc0fe0c260f946f189a2007dbdea272f8a7255123c588b8d8c4733e9cc25", "85f1bda87e3ebabcdf6dd4e4bccd174a2f10511ba8afd2c4be516c450e2321d0", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/Tele.lean", "Ix/Kernel/Verify/Denote/Tele.lean", "9c68290c5e3cd846792bab07734d1862aa194d65787a9ca1031830582ac65f08", "882e118497fbc7770d5d77e1d42ca7715c2dc3da8414027c985a39fc0222562e", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/TeleOpen.lean", "Ix/Kernel/Verify/Denote/TeleOpen.lean", "8a512b68c376e7d1ed9c1fa9506bf18ca60978933de3439857610ce3fe5b8192", "94ee7d7f931acde9afbeb4083de954f2da7c3a7af5ec214221f8c89745b9c192", .rewritten⟩,
  ⟨"ConLeche/Verify/Denote/VClosed.lean", "Ix/Kernel/Verify/Denote/VClosed.lean", "9f3e8a68dcedc6938ae8dacf240ebbfd58340bd4e97d0dcf9cab1e57703541d8", "89ed500cce2fe3cf3ff1e1daeeb48f0105587c3f8896040fbf11d47877284e37", .rewritten⟩,
  ⟨"ConLeche/Verify/DivModInv.lean", "Ix/Kernel/Verify/DivModInv.lean", "a3aae7ce4d07fdc0868895d1b3398b4db4df823dfc97de7bae8538c270d2d9c4", "13df99668a3fd9fbcb698ecfac8b4a2134b85854ab6b4ba2e7c94a06ede2f636", .rewritten⟩,
  ⟨"ConLeche/Verify/EnvBound.lean", "Ix/Kernel/Verify/EnvBound.lean", "ab90be94f8e688058e4394aa8eb118c22f3c3e6b649ee1f49fdf17a388deff16", "f0e28f32879b13969a73804258107d94736f1453e0f29d6cde90f6a45d819036", .rewritten⟩,
  ⟨"ConLeche/Verify/EnvGuards.lean", "Ix/Kernel/Verify/EnvGuards.lean", "5542c26343f10b6e0ac823516a70ec640ace6a535a4acba8e5dea536f76c2d31", "511bc5e83bff2a6ea3960ae155b3df302fe1fa6cd7f1b4d3ba2029e89ce58daf", .rewritten⟩,
  ⟨"ConLeche/Verify/EnvPreds.lean", "Ix/Kernel/Verify/EnvPreds.lean", "f9c5d6930a357f0a00c59040204a41ab4759751f545ccfe64307caf46068fac5", "5641ca1ee8df5d72cfe47cc3e68e1110c66cabf5d34eedbc55f097281204c244", .rewritten⟩,
  ⟨"ConLeche/Verify/EnvWF.lean", "Ix/Kernel/Verify/EnvWF.lean", "696c58025cd44fa1a3f45f932b11f2eceed3674009ee59d66f1083fe7c8bba3e", "501c5e4b98eb1ffb6566f6bd838fb460b3e063af9d1c2bf58df85539f4eed71a", .rewritten⟩,
  ⟨"ConLeche/Verify/ExceptBind.lean", "Ix/Kernel/Verify/ExceptBind.lean", "7817743fc7e58a457f0df27f2f1de6c78d5bcd0468f3cfba876c8c05170eb331", "939f0e180ffd5641ac24d02d04223dfe2aeb1e166e3cd1c7fc675c23e5b7878b", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Block.lean", "Ix/Kernel/Verify/Extend/Block.lean", "ff47e8a55a34765511acca2e5479d2ae98d8abf4b94b3d61dcc43a723719446d", "0cd05ba531258c023e4a18ddf2187b85d53e851c70e0b195ffaab14eec64faac", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Ind.lean", "Ix/Kernel/Verify/Extend/Ind.lean", "628055b10a186492c0f9b07b13763c8271ea617117c860a2184074ed01b5c675", "3e93fced549e639bf1cf1316b777a81784830862e4265686f944ecc04eda5705", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Inversions.lean", "Ix/Kernel/Verify/Extend/Inversions.lean", "4565a8d871d08b9ac44eef9e23b92db74b4d0e5cd412243a1928487ca6101006", "d599a46dbc93f91060b1f0d9e733e7d549fd3b01c8a6c3c8986b8e1de6e23a21", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Iota.lean", "Ix/Kernel/Verify/Extend/Iota.lean", "2bca1ad17469d71b5edb7c7d7c3757e42451465461fd5359291c637c25a6d3ca", "1a31d9ea075ac63778f308f19b4d2c2b4a4f1fe4008be4ae3e88c85bef352545", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Modeled.lean", "Ix/Kernel/Verify/Extend/Modeled.lean", "172513319d441792b44a631daf0b60d2516d3a1e813dbbb7a318faa667b9b9c3", "32407c466faca8c8a39a11c1e17313db22ca54d353ede7d77081d8864a7049c7", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Proj.lean", "Ix/Kernel/Verify/Extend/Proj.lean", "fab05f5a8214a4b254d48a96cdc054fa1d10a78a6523e1441a87172f3199657c", "e9415f1d12517c9b2df47d198d1858751048a3e893c0149dddd02665144fbffc", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Recs.lean", "Ix/Kernel/Verify/Extend/Recs.lean", "2ea81712337cc3c6f7ec909b585eb0db32c3ae3e0892bcb956f0718f5f5704cf", "7a8b0dade8c2f37e7536de243daaedf4f59710c77ec18cb04c3f0489bcd9d54d", .rewritten⟩,
  ⟨"ConLeche/Verify/Extend/Sibs.lean", "Ix/Kernel/Verify/Extend/Sibs.lean", "70a01b23daf271606d7b1d58a28ff737921f706bc1337a1d7792ea09e9f5f178", "6a0b3b7c99a3700669a748dc88896fdf3e7a73f835742f2c4e23eb80309a140b", .rewritten⟩,
  ⟨"ConLeche/Verify/FastOps.lean", "Ix/Kernel/Verify/FastOps.lean", "5e785b9ee46eda55c60426e56d5440e1fff7d51bfe99ef06c9b7e9d623a3ec93", "6d841f5d9455d8e469ecb9ba92f124664b9d3dca293c6619a64e29ebb5f233df", .rewritten⟩,
  ⟨"ConLeche/Verify/Frontend/Prepare.lean", "Ix/Kernel/Verify/Frontend/Prepare.lean", "e01c3dd6b3bf4df0feb4016725b6acbdba164a37ef69b561231b7eb92a838254", "fcd21d899e1cc4aa6d66abf0e20580f96a3b793d51da21bf39d0163b89bf8537", .rewritten⟩,
  ⟨"ConLeche/Verify/Fueled.lean", "Ix/Kernel/Verify/Fueled.lean", "eb235c760203e250a204738c0748df9d05873b50153e7de72524bc13e1dfcab4", "9f9a76da2cf30efa4e23c8138927596a6e71078de663f463728d0daa762b4082", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/FixInv.lean", "Ix/Kernel/Verify/Inductives/FixInv.lean", "10beadbbf1ed4a640dc13c7ba3cc3aeb4fdd79a9a94d56b1ec9ce40f3d8c0560", "a6cbea5ec7fda37862fad6695ceed1830a6d2d5d9439c41afc7b34e4067ced49", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/FixParts.lean", "Ix/Kernel/Verify/Inductives/FixParts.lean", "5421fddf4ae675962181ea57afb4dfaea1c9e8cfb749133a4d01a2cc3f3c89bc", "d5915ba4c0123b8d5ffa192af87ecb47ec310086642091f81c2f16768e3a9535", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/FixRec.lean", "Ix/Kernel/Verify/Inductives/FixRec.lean", "5528dd75656aea5b5b9428191cf7c10aac05285b31febf7748cb824c62c48774", "8d3f3a6547f19885fea26024da4e9ad51eba8c009fae22d89a3c3edf2bf7ac7e", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/FixWF.lean", "Ix/Kernel/Verify/Inductives/FixWF.lean", "ec31c598dd0511cb9bdb9629774770c569e2969aec17201c3c54f219499a21b4", "576321249439cba8b7ee91e001b3e08c77f5e5c41b8a9994606dc6e9c9b54fd2", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructBody.lean", "Ix/Kernel/Verify/Inductives/StructBody.lean", "6eb7e24988929a4cc06cb294a5e3e147dad885d52d1a33ac973bcde0da06bc31", "d69fa430d2af8654305e18f89e2cb69c64844950322b95abbacd96fa3c219e43", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructInv.lean", "Ix/Kernel/Verify/Inductives/StructInv.lean", "fc7b61be7d14d5289e9e3367091448c0c7b800f209e79d0c59861bfbadffd4cd", "f3dad1c20da1c6628cbf0874d9528fb958492ddbfe3dddb39a20813dbddeba27", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructPartsInv.lean", "Ix/Kernel/Verify/Inductives/StructPartsInv.lean", "9e58337548772eeaefa0c4011abd843458b23baa14ca70c4ed72489104eb2558", "c62193866564603f36b83209df9b4117e6e6bc26c4b95cb0859ebe79e6840190", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructRec.lean", "Ix/Kernel/Verify/Inductives/StructRec.lean", "e08d45f9a6c90acbdba6ae81494c9119026e63fd786747c3adedbcaef2e631ba", "e9f4fb4ecb2f07ef03188daff281c4945fbb7964bc5afb0e2bfdf60b9a8df241", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructResid.lean", "Ix/Kernel/Verify/Inductives/StructResid.lean", "9becf553659055eb1f549ac28f53eeef499561e581e63b1688239054b33539c5", "743a2282d705ffd63084b209c36951109e6ac375ceec10e726294fe8df051b6c", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/StructWF.lean", "Ix/Kernel/Verify/Inductives/StructWF.lean", "fc1ed334a9d05d12228c278ccfad46d7fc42640963195a7a0493e54162a82cdf", "f951a4103b153d81700618a44458d00b924d137819b373b985a39399a0ecf9ae", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/SumInv.lean", "Ix/Kernel/Verify/Inductives/SumInv.lean", "5b001178c420a86a5b4dbbcac0a20240a8e68fcacdd11ffea49a3b5a637b963a", "b2a020112bfb52c54d0a0925e521e5675803da8aa52477256eed838c7620f67a", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/SumRec.lean", "Ix/Kernel/Verify/Inductives/SumRec.lean", "766e0dc686a4d13adb756f1334ec1d35203034320711f56d72ebc9687cdd6ca9", "5710182d7ef8b1a17c123eb3b0e084542d3431cc8a8e296551d2450ae7298734", .rewritten⟩,
  ⟨"ConLeche/Verify/Inductives/SumWF.lean", "Ix/Kernel/Verify/Inductives/SumWF.lean", "010d5bc7231f89dac2865cb938f1e4332fc052bcc925c146e965e5c336c03f94", "354482ac18ed0051a2a5ed9822b973d250f8bf83366e23d477c132288788fbc7", .rewritten⟩,
  ⟨"ConLeche/Verify/InferIOLeaves.lean", "Ix/Kernel/Verify/InferIOLeaves.lean", "206ae056cbf95ff8c80b72ab99942c94e1afc4bfff9f11b1721f4b8a6d61fe7c", "74d1b5903c8ba3f6aee13bd07ea8988a1358ae7937992a256f92844394f81fb2", .rewritten⟩,
  ⟨"ConLeche/Verify/InferIOLemmas.lean", "Ix/Kernel/Verify/InferIOLemmas.lean", "be5bb5236c395b74e5dd944d6cce5a9e2a7cbafc04cb116de4748f672d327f24", "aa95f7e631f5ae83a77243ef3e60376183628e2fbaea9b40f30cc1941e96cd3d", .rewritten⟩,
  ⟨"ConLeche/Verify/InferLeaves.lean", "Ix/Kernel/Verify/InferLeaves.lean", "dce106cebdbb2e77c54c1dae0f7d01adcb34be2a0673fd868cd97819e1320520", "7f9b24e95b1897072a55fe7cc5e5124248d0c1023d88b564ea4c0e0e982a6fcf", .rewritten⟩,
  ⟨"ConLeche/Verify/InferLemmas.lean", "Ix/Kernel/Verify/InferLemmas.lean", "755e48be5f27d0963e2ea1725c6472b150bd73844df029c1ec00d886d8eb09c4", "1340b9a9dc84b7215df7291b59877f86c0011186be40e772a01a052946dadb11", .rewritten⟩,
  ⟨"ConLeche/Verify/InstLevels.lean", "Ix/Kernel/Verify/InstLevels.lean", "e8ca4a86775dbc51d1f4fb1aadc191165db0eef7416a276020562f90abb62343", "6e36d9fecac79199143d071f18da83641d8a17719f89f5d2cdad79978f5600cf", .rewritten⟩,
  ⟨"ConLeche/Verify/InstList.lean", "Ix/Kernel/Verify/InstList.lean", "6b0873f9acb9ce20e2828969ec1ba6964b03179e79632bc3ed153cd03b74329a", "384a9cdfc82fe281192e1f1b755b3853393e7d2c0c4624c1b9323a59377972f3", .rewritten⟩,
  ⟨"ConLeche/Verify/InstSpine.lean", "Ix/Kernel/Verify/InstSpine.lean", "8d0cab4083ddf450d86a9153c17fc52d2be5bd7755e163dc6031ad995d498f2b", "45f49041d6f641b26a576b3414bc19bd46d17565cc54aefc0ffc3afa91dbcb96", .rewritten⟩,
  ⟨"ConLeche/Verify/IotaWalkInv.lean", "Ix/Kernel/Verify/IotaWalkInv.lean", "219469e47f05e1649e8d857861924e8a515ea254aa849047472537e413403440", "339256e1eb2ab93b7bfa765efefab172378ad210d2f09c6e4fab50db4cfd4e4a", .rewritten⟩,
  ⟨"ConLeche/Verify/Knot.lean", "Ix/Kernel/Verify/Knot.lean", "76fa607a8d04e226ce6f94b5194a90b20ec4c2e60845e979ffcd7a07acd5dcb5", "64f3c3bd3d7200dc7ef3ee673c2d10c9a95d03d7ced755652d280836ea169287", .rewritten⟩,
  ⟨"ConLeche/Verify/Leaves.lean", "Ix/Kernel/Verify/Leaves.lean", "6805a06eab92a6cffa39547f1430d3725c9407624307ce85d85157dd4383440c", "7a55701b03877687c5cc462d62e0ec77feacb855df0d3a4951ec5d941cf75689", .rewritten⟩,
  ⟨"ConLeche/Verify/Level.lean", "Ix/Kernel/Verify/Level.lean", "ec7db26a95d7c6a8e367c98a4acda19599dcd10f959a6663767213de45355c46", "120b897f96e68def9577b080f6dd155eb5f5596de255887980e4fab44016875b", .adapted "adapted: `leqCore_sound` covers the `Geran.leq` answer of `rest`'s `(param, max)` case by `Geran.leq_sound` (the Ix module now at `Ix/Kernel/Verify/LevelGeran.lean`) and the new `eval_eq_levelEval`; every existing statement unchanged (cl-level); `public import ConLeche.Verify.LevelGeran`; port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩,
  ⟨"ConLeche/Verify/Mono.lean", "Ix/Kernel/Verify/Mono.lean", "5fd646c014f1f6b9f915edfef7d0e25343f9b4287108c4a1ac0f9c972123b773", "77ff58ba49f0520c660a9f017d6fac92f35828b0ea161d629a2164e5184e9c1a", .rewritten⟩,
  ⟨"ConLeche/Verify/NatOpFrag.lean", "Ix/Kernel/Verify/NatOpFrag.lean", "c91f4483da2355427108d61dc6fffe0691ccef0fc548a79940f08849cfc5bf63", "5a1cfe7a35ca6965e4a2fbff57ee12b6e65d4538caa234f3fb3b6bac889f69a6", .rewritten⟩,
  ⟨"ConLeche/Verify/OfReducePin.lean", "Ix/Kernel/Verify/OfReducePin.lean", "2fdafbe62768e8b30284d3734f988501dd22244f9b606f9ee0bc87356bb307ba", "61756dd9ad851ab38e318666c12d85b31a90d00a06f6fc98388b8c2c4176f91b", .rewritten⟩,
  ⟨"ConLeche/Verify/PairM.lean", "Ix/Kernel/Verify/PairM.lean", "9a880f34e35b88740e6c35dd62094b5abb2da20d5a7377d79e93ce4fd25d2d06", "29c0746554ccfc32862240532f85b174521e4e2909d0e175d1708c7c5cea6224", .rewritten⟩,
  ⟨"ConLeche/Verify/PinnedShapes.lean", "Ix/Kernel/Verify/PinnedShapes.lean", "3380806da7cb4fd5069003a3f8b0c3bb14ce2cad1f5729eb88ec73f472656110", "bbf74d2734d76417ca9247b5cf516149e56dc0e49e142234f210abfa8d80a326", .rewritten⟩,
  ⟨"ConLeche/Verify/ProjSlots.lean", "Ix/Kernel/Verify/ProjSlots.lean", "77065caf1bc6aea64df2b147eaa948e4d8ba30763927923f57c1f4cdd330f423", "08289e383aa3164316040ca0d99df9961adc6e7466d6e5d4c521ec59f1522b1d", .rewritten⟩,
  ⟨"ConLeche/Verify/ProjTele.lean", "Ix/Kernel/Verify/ProjTele.lean", "d57213eaefaab6904045447c32dfc828ba31c8a5b7aebfa055fd4943ec5abb4c", "c493e9ebb9cd927081a8a8c91bc14c884b2644c0ba69f94aa0894eb650ba4f94", .rewritten⟩,
  ⟨"ConLeche/Verify/PropRead.lean", "Ix/Kernel/Verify/PropRead.lean", "8877a1b56d76a487395546120b13abef55d0fce0c2017af2d9162abdc4da3eb7", "10cdd411da42201e72e304dafa02cb170bb23101629e5c8873c840d60fcc36c5", .rewritten⟩,
  ⟨"ConLeche/Verify/PropWhen.lean", "Ix/Kernel/Verify/PropWhen.lean", "2bdef3a7b198d3eaf45ec0127ef219cbd02c457ac70115bc820b57897af18e2c", "7bc97f83d1c4aeaef1da675bff2f2c48ca828c979b360b2888209ed1faf78dfe", .rewritten⟩,
  ⟨"ConLeche/Verify/ReducePinInv.lean", "Ix/Kernel/Verify/ReducePinInv.lean", "dc9544f069b8ba6521013aeca1eccfe3aa0bbb18764e3cc389435655c2d92dc2", "36ffcf7ed1a4bbe6f879a4489a776d13a2dec9bf1397d6bc24ccadb8aa6d300a", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/Bridge.lean", "Ix/Kernel/Verify/Rules/Bridge.lean", "5fe3e5dffe2ef09245ce49a781677556a890cb1a42e8ef17135d9ad1c25f12cc", "86189fb1d624ba8e6de4e7e4a3c1d9969268c681862329150e5af3b2ac5b41e5", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/Certs.lean", "Ix/Kernel/Verify/Rules/Certs.lean", "440547762127dbbf22c8ab670620d0f525c1cd6891dd9b64c2400abbc9d172d4", "05b9f0f36dc287cd7fd672e6f45174c34a5ae0268d5306abc31fde44a099b195", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/DefEqBridge.lean", "Ix/Kernel/Verify/Rules/DefEqBridge.lean", "2a9bb7f8408cc24f29c88e69163b352d789fc797637a9fa2fff57be1ea0dbb9d", "b722ea5dd761763f4c0b31aa77f2f0fb1382688831d326653d7ca6d968e1a040", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/DefEqStepInv.lean", "Ix/Kernel/Verify/Rules/DefEqStepInv.lean", "8c871230d21f73bdeef3e2a4b092a7cb5d40d49d9e9f9f9d9cd84a040db31a3c", "1fae9e87b46cf6004948fdb51542c282b3adc93c44d64dd739a00e624fb78317", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/Defs.lean", "Ix/Kernel/Verify/Rules/Defs.lean", "221374beb162f425eb491ef78b370aa31e4d82aee3d0937b227ab98fc0942637", "5d61789b0339dd8649d9ced6aff0068a774dc0fbcd770e7bb33611dec8d84db6", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/InferBridge.lean", "Ix/Kernel/Verify/Rules/InferBridge.lean", "a1bf6cda57e18f5723cc04983fa4b21ccae69844ca1049af5df0de98106fce66", "0de83ca72878301aa5be190a95f2e42c1cc81448a7367f64b6a5c1be451337db", .rewritten⟩,
  ⟨"ConLeche/Verify/Rules/RedBridge.lean", "Ix/Kernel/Verify/Rules/RedBridge.lean", "168d4abea30a7c206c490722bd15817139e7dc946e6c2d218141090132e1f952", "9fd43fb93a04af02ddfcc91ea8990d1afbfd06b1d1750a2d3dec2443b2ad93ec", .rewritten⟩,
  ⟨"ConLeche/Verify/Shift.lean", "Ix/Kernel/Verify/Shift.lean", "c4a302230ab8ef38f4d3e28d351ae220381cf4576cb040d8534c4c595b0b3f03", "85933d2564efb5d182147edbb463c71bcf25a672997b656e84aeeb60fecd022b", .rewritten⟩,
  ⟨"ConLeche/Verify/StdAxiomPin.lean", "Ix/Kernel/Verify/StdAxiomPin.lean", "36bac7fe07f3a55e45254d18843f55d7faf6a31545f71a0e29aff3558ae1de6c", "d012471779242d3078f5f008b7cd5fe6620dfe3cbba58f2f11da042284ef9429", .rewritten⟩,
  ⟨"ConLeche/Verify/StrLitExpr.lean", "Ix/Kernel/Verify/StrLitExpr.lean", "45e26505e9314ee05a5e92edfcaeb627c89981259f6259460bc58cbd5fa79712", "7ec5caf22c02e38842a4208041d33847f7658360bd40c86eec52504b338f14e5", .rewritten⟩,
  ⟨"ConLeche/Verify/Subst.lean", "Ix/Kernel/Verify/Subst.lean", "b5990a82183682bacb78298c0af7d160e4579ee7072b4765c1ab096450e5b6bd", "1b3405772e0598db66996013581e97d1a4c8212d1b107c9b52a7df593978111f", .rewritten⟩,
  ⟨"tests/ConLecheTests/Axioms.lean", "Tests/Ix/Kernel/Axioms.lean", "a408634434101042826736595647f89792e7be16da4916b2806928602db08887", "f2297854b44642ab34aace061fb6d286728164546b10630403657da2bb57ebbd", .adapted "adapted: namespace Tests.ConLeche.Axioms (Tests.Ix.Kernel.Axioms since the move); StreamConsts/StreamThm imports and 3 guards (no_False_declaration, no_False_theorem_accepted, Cached.checkDecls_consts) dropped; docstrings cut; port header added; then the vendoring rewrite of scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel, without its comment line)"⟩
-- END con-leche rows
]

/-- Con-leche tooling ported outside the inventory roots: the layering and
trust-surface fences (adapted to this repository's paths and, since
2026-10-01, to the vendored tree's layout; their headers list the changes)
and the lexer fixture (verbatim). -/
def conLecheTooling : Array PortRow := #[
  ⟨"tests/layering.sh", "scripts/layering.sh", "9b6dfa842951c290f9b832367a3cb2795d18dc66f3f68e8011dcfc844bb7ad61", "692d791a72e92ebe0037540578a1ba494fbfd7a471c1b8590d377de68452a16e", .adapted "scan the vendored con-leche tree under Ix/Kernel (scripts/vendor-conleche.py list) only, classified by upstream path; the dead base-to-model clause repaired; the boundary clause added; tolerant of an absent tree"⟩,
  ⟨"tests/trust-surface.sh", "scripts/trust-surface.sh", "f7c5406a102347a0618aec0e327999036098928075cb4bfac2edef726b81b912", "1f4ead90ed56042ce0958b1d1c38cd84d4fb876d1bb10fb35ed3be22d8f74a4d", .adapted "scan the vendored con-leche tree under Ix/Kernel (scripts/vendor-conleche.py list) only; Main.lean and Challenge.lean entries dropped; allowlist at the vendored paths; header condensed; tolerant of an absent tree"⟩,
  ⟨"tests/trust-surface/lexer.lean", "scripts/trust-surface/lexer.lean", "b8cd4b707f0cd1548475a7ff2a994d362d4715ae90be16fd94c2c50c809f422b", "b8cd4b707f0cd1548475a7ff2a994d362d4715ae90be16fd94c2c50c809f422b", .verbatim⟩
]

/-- Con-leche's licence, carried with the vendored tree. -/
def conLecheLicenses : Array PortRow := #[
  ⟨"LICENSE", "Ix/Kernel/LICENSE-CON-LECHE", "8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e", "8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e", .verbatim⟩
]

/-- The con-leche rows whose files add Argument's modifications copyright and
declare `Apache-2.0 AND (MIT OR Apache-2.0)`: the adapted main theorem and
axiom pin. -/
def conLecheModified (target : String) : Bool :=
  target == "Ix/Kernel/MainTheorem.lean" || target == "Tests/Ix/Kernel/Axioms.lean"

/-- The con-leche rows at `conLecheKeepProj.revision`: the seven ported
files upstream task #323 (`3ca9e2fe`) changed, pulled at int-5 (verbatim then,
rewritten since 2026-10-01).
(#323 also changes `ConLeche/Kernel/CoreGated.lean`, which is not vendored.) -/
def conLecheKeepProjTargets : Array String := #[
  "Ix/Kernel/Cached/CoreC.lean", "Ix/Kernel/Core.lean", "Ix/Kernel/Verify/BetaSpine.lean",
  "Ix/Kernel/Verify/Cached/DiscC4.lean", "Ix/Kernel/Verify/InferLeaves.lean",
  "Ix/Kernel/Verify/InferLemmas.lean", "Ix/Kernel/Verify/Rules/RedBridge.lean"]

def conLecheAtKeepProj (target : String) : Bool := conLecheKeepProjTargets.contains target

/-- Every imported file, by origin and licence. -/
def portSets : Array PortSet := #[
  { origin := oldBranch, license := "MIT OR Apache-2.0",
    rows := ported.map PortedFile.toRow ++ licenses },
  { origin := conLeche, license := "Apache-2.0",
    rows := conLecheRows.filter (fun row => !conLecheModified row.target && !conLecheAtKeepProj row.target) ++
      conLecheLicenses ++ conLecheTooling },
  { origin := conLeche, license := "Apache-2.0 AND (MIT OR Apache-2.0)",
    rows := conLecheRows.filter (conLecheModified ·.target) },
  { origin := conLecheKeepProj, license := "Apache-2.0",
    rows := conLecheRows.filter (conLecheAtKeepProj ·.target) }
]

end Tests.Ix.Kernel.ImportManifest
