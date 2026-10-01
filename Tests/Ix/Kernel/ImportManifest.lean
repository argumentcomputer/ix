/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Import provenance for `Ix.Kernel` and the ported `ConLeche` subtree

Every imported file has a row: its source path and SHA-256 at its origin's
revision, its destination path and SHA-256, and its transformation. Rows
are grouped into `PortSet`s, each with one origin (repository, revision,
and how `--source` reads it) and one licence, so rows from different
sources coexist. The file inventory, hashes, headers, licences and source
hashes are enforced by `Tests/Ix/Kernel/Provenance.lean`
(`lake exe kernel-provenance`).

**The old branch.** Recorded on 2026-09-17 from the `jcb/ix-kernel-consistency`
branch of the Ix repository at `oldBranch.revision` (the old workspace's
working copy was identical to the pin). The transformations are the namespace
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
every ported file states. License files are verbatim copies; the notice was
updated to this repository's paths on 2026-09-30.

The branch's own provenance chain is retained in `Ix/Kernel/NOTICE`: the
model was authored in the Lean4Ix working tree, and its `SetTheory` and
`SetModel` directories port con-leche revision `oldSetTheoryOrigin` under
Apache-2.0, which is why those 20 rows form their own set.

**Con-leche** (plans/ix-kernel-con-leche-port-v4.md, 2026-09-30). The
`ConLeche/**` subtree is ported in place from con-leche at
`conLeche.revision`, keeping its paths and namespace. A verbatim file is
byte-identical (equal hashes, no header); an adapted Lean file starts with
the con-leche form of the port header:

```
/-
Ported from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526.
Source: ConLeche/Kernel/Core.lean
Transformations: …
-/
module
```

`conLecheRows` is generated: `scripts/provenance-rows.py` turns a TSV
(`source_path`, `source_sha256`, `dest_path`, `dest_sha256`,
`transformation`) into rows and splices them between the markers below.
Con-leche's `LICENSE` travels with the subtree as `ConLeche/LICENSE`
(verbatim). The adapted files that carry Argument's modifications copyright
declare `Apache-2.0 AND (MIT OR Apache-2.0)` and form their own set, as the
old branch's set-theory rows do; every other con-leche row is Apache-2.0. -/

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

/-- Con-leche, the origin of the in-place port (`ConLeche/**`). The checkout
`plans/refs/con-leche` is clean at this revision. -/
def conLeche : Origin where
  label := "con-leche"
  repository := "https://github.com/leanprover/con-leche.git"
  revision := "ae0c0c4e4ce6a0081648aff03fe9c39d002c4526"
  vcs := .git

/-- The con-leche revision the old branch's `SetTheory`/`SetModel` came from.
Those rows keep this origin; do not claim a newer one for them. -/
def oldSetTheoryOrigin : String := "86cd20a65660d757cedc81561a44579099b565d0"

/-- How a ported file relates to its source. -/
inductive Transformation where
  /-- Byte-identical: no header, and the two recorded hashes are equal. -/
  | verbatim
  /-- Changed as summarized; an adapted Lean file starts with its origin's
  port header, and declares the set's licence if it declares one. -/
  | adapted (summary : String)
  deriving Repr, BEq

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
they are not imports from the older model branch inventoried below. -/
def authored : Array String := #[
  "Ix/Ixon/Types.lean", "Ix/Ixon/Types/Kinds.lean", "Ix/Ixon/Types/Modes.lean",
  "Ix/Ixon/Types/Contract.lean",
  "Ix/Ixon/Codec.lean", "Ix/Ixon/Wire.lean", "Ix/Ixon/Verify.lean", "Ix/Ixon/Audit.lean",
  "Ix/Ixon/Verify/Basic.lean", "Ix/Ixon/Verify/Expr.lean", "Ix/Ixon/Verify/ExprSpine.lean",
  "Ix/Ixon/Verify/Constant.lean", "Ix/Ixon/Verify/ConstantTables.lean",
  "Ix/Ixon/Verify/NonrecursiveConstant.lean", "Ix/Ixon/Verify/RecursorConstant.lean",
  "Ix/Ixon/Verify/MutualConstant.lean", "Ix/Ixon/Verify/Framing.lean",
  "Ix/Ixon/Bounded/Universe.lean", "Ix/Ixon/Verify/BoundedUniverse.lean",
  "Ix/Ixon/Bounded/Constant.lean", "Ix/Ixon/Verify/BoundedConstant.lean",
  "Ix/Ixon/Bounded/Size.lean", "Ix/Ixon/Verify/ReaderBounds.lean", "Ix/Ixon/Verify/ConstantBounds.lean",
  "Ix/Ixon/Verify/Work.lean", "Ix/Ixon/Verify/WorkTags.lean", "Ix/Ixon/Verify/WorkExpr.lean",
  "Ix/Ixon/Verify/WorkArray.lean", "Ix/Ixon/Verify/WorkUniverse.lean",
  "Ix/Ixon/Verify/WorkConstant.lean", "Ix/Ixon/Verify/WorkRecord.lean", "Ix/Ixon/Verify/WorkAdmission.lean",
  "Ix/Ixon/WireCheck.lean", "Ix/Ixon/Verify/WireCheck.lean",
  "Ix/Ixon/Canonical.lean", "Ix/Ixon/Verify/Canonical.lean",
  "Ix/Ixon/Admission.lean", "Ix/Ixon/Verify/Admission.lean", "Ix/Ixon/Admission/Audit.lean",
  "Ix/Ixon/Projection.lean", "Ix/Ixon/ProjectionProofs.lean", "Ix/Ixon/ProjectionAudit.lean",
  "Ix/Ixon/ReduceUniverse.lean", "Ix/Ixon/BlockOrder.lean", "Ix/Ixon/BlockOrderProofs.lean", "Ix/Ixon/BlockOrderAudit.lean",
  "Ix/Kernel/Ingress.lean", "Ix/Kernel/Ingress/Reading.lean",
  "Ix/Kernel/Ingress/Expr.lean", "Ix/Kernel/Ingress/Constant.lean",
  "Ix/Kernel/Certified/Ordinary/Stage.lean",
  "Ix/Kernel/Egress.lean", "Ix/Kernel/Egress/Layout.lean", "Ix/Kernel/Egress/Expr.lean",
  "Ix/Kernel/Egress/Constant.lean", "Ix/Kernel/Egress/Projection.lean",
  "Ix/Kernel.lean", "Ix/Kernel/Model.lean", "Ix/Kernel/Env.lean", "Ix/Kernel/Check.lean",
  "Ix/Kernel/Consistency.lean", "Ix/Kernel/Audit/Axioms.lean", "Ix/Kernel/Audit/Imports.lean",
  "Ix/Kernel/Audit/Runtime.lean", "Ix/Kernel/Audit/Roots.lean", "Ix/Address/Core.lean",
  "Ix/Kernel/Model/LetRules.lean", "Ix/Kernel/Level.lean", "Ix/Kernel/Certified/LevelNorm.lean", "Ix/Kernel/Claims.lean", "Ix/Kernel/Infer.lean",
  "Ix/Kernel/Annotate.lean", "Ix/Kernel/Arithmetic.lean", "Ix/Kernel/Revalue.lean",
  "Ix/Kernel/Inductive/Interleaved.lean", "Ix/Kernel/Search.lean", "Ix/Kernel/Certified/Checker.lean", "Ix/Kernel/Certified/Ordinary/Read.lean",
  "Ix/Kernel/Inductive/Ordinary.lean", "Ix/Kernel/Certified/Structure/Read.lean",
  "Ix/Kernel/Inductive/Structure.lean", "Ix/Kernel/Inductive/Natural.lean", "Ix/Kernel/Fidelity.lean",
  "Ix/Kernel/Model/QuotientValues.lean", "Ix/Kernel/Certified/Quotient/Install.lean",
  "Ix/Kernel/Certified/Standard/Install.lean", "Ix/Kernel/Certified/Basis/Empty.lean",
  "Ix/Kernel/Runtime/Expr.lean", "Ix/Kernel/Runtime/Stack.lean", "Ix/Kernel/Runtime/Close.lean",
  "Ix/Kernel/ConLeche/Reader.lean", "Ix/Kernel/ConLeche/Prelude.lean",
  "Ix/Kernel/ConLeche/PinData.lean", "Ix/Kernel/ConLeche/NatOpPinData.lean",
  "Ix/Ixon/ConLecheAdmission.lean",
  "Ix/Kernel/ConLeche/ReaderSpec.lean", "Ix/Kernel/ConLeche/Installed.lean",
  "Ix/Kernel/ConLeche/Values.lean", "Ix/Ixon/ConLecheConsistency.lean"
]

/-- Lean modules ported from the old branch. -/
def ported : Array PortedFile := #[
  ⟨"Ix/Theory/Certified/Basis/Equality.lean", "Ix/Kernel/Certified/Basis/EqualityChecked.lean", "66c404ed6c66211dfb60690cd072197238ab6305efa3a6dbcef7b5ddca5baf27", "5f49fa99eb80747ff180dd01380d869cd50c82e853aa1a9113ed8b150a538440"⟩,
  ⟨"Ix/Theory/Certified/Basis/Equality.lean", "Ix/Kernel/Certified/Basis/Equality.lean", "66c404ed6c66211dfb60690cd072197238ab6305efa3a6dbcef7b5ddca5baf27", "b8cee7826bb4495b4e7708200d4ab3d08bf164c6ddabaf531f6bbc36e10f5784"⟩,
  ⟨"Ix/Theory/Certified/Basis/Iff.lean", "Ix/Kernel/Certified/Basis/Iff.lean", "e8f04f80953d924a7d1d36084d21fb8d9e03461d72eb23a9f32c220c9f151af7", "85e50f7a2d2487066022cbe313f304a2a118c12c661862eeeb69e27c0967487d"⟩,
  ⟨"Ix/Theory/Certified/Basis/Interface.lean", "Ix/Kernel/Certified/Basis/Interface.lean", "421d43c0a613c49819c3edc962a82da503b9509f0d5f1515b2b479787f1648de", "7856d31e9c69c04a8f03d318f2a17321ae8857edb06581c9a83aa30f5e5720d2"⟩,
  ⟨"Ix/Theory/Certified/Basis/Nonempty.lean", "Ix/Kernel/Certified/Basis/Nonempty.lean", "b717b2ea0c59eb6b359df24c0f45fbeeb2a9cafe0775fe319e8e38b4c2427065", "284ac37e35abca883356730e7bb108e5d8ed9fbe6f184d157d3cb1a0fd81b906"⟩,
  ⟨"Ix/Theory/Certified/LevelEq.lean", "Ix/Kernel/Certified/LevelEq.lean", "f2597b5a6c63ba437c90c77d3ea92d45ce9d340fc9e4fb615a8843fabdb1f7fb", "efbd7eb167a895a810c5c0dad3d02dfb26a821399ec300915718ed70b4d6df9f"⟩,
  ⟨"Ix/Theory/Certified/Level.lean", "Ix/Kernel/Certified/Level.lean", "d129fb7cbced78b6e03c65ec17d2199c83986266d84b4c08966ef489a69a0332", "b338a6e6c4c64f63aab9d0b180d03976dfc4853b78daf861e0b67fff991cc7f6"⟩,
  ⟨"Ix/Theory/Certified/Natural/Checked.lean", "Ix/Kernel/Certified/Natural/Checked.lean", "d1bff0ed4bc1231d76044bac3964947a6dd4d6272256537a1d69ccc9e061a53b", "54896cf569ce581fbccb2e9b7fdecb64e11a14148627a0f70a6e719965ec2626"⟩,
  ⟨"Ix/Theory/Certified/Natural/Publish.lean", "Ix/Kernel/Certified/Natural/Publish.lean", "6ac732a887610b95b85da5f6dbd516c7c261ecb1a53c8b20c1ccf526a16a54fb", "b03c5eae052a137679ada55579d7ad23201ef6040a9672f566b829624f0cb418"⟩,
  ⟨"Ix/Theory/Certified/Natural/Value.lean", "Ix/Kernel/Certified/Natural/Value.lean", "767478f45bbf8ab14125a40ec79f8e92bda04bf8dabba367643b44603984623c", "65605d1e58677fcfa8b81b9333126c9ebc1573ad6c2e2599c149c4b09d8ee243"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Checked.lean", "Ix/Kernel/Certified/Ordinary/Checked.lean", "057c155790636810073b2fee33877e581e1feda5192de32b2358b1838e14966d", "982b53fc057e89bbd06cbc6b0899a14d955a8439732899c2f99be7e1d47e9581"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Computation.lean", "Ix/Kernel/Certified/Ordinary/Computation.lean", "0ec36fa1fb5bf9d3865f4b389df1eb6e23b79fbe7b8e29a3a91ccd02794dd578", "f91eb0ba4e7434ece504489dd2613dc94d2d8efc90ce8ed823eba1f1dbbcb2ba"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Constructors.lean", "Ix/Kernel/Certified/Ordinary/Constructors.lean", "ce1fcbcd3644cc3485764cb9b3e39f271a146486db395668024f9e5c9f8b3b1a", "f64cda9e731d223284d33b8639721d897a10f9163bb63f3774f2eb8f98414587"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/ConstructorStage.lean", "Ix/Kernel/Certified/Ordinary/ConstructorStage.lean", "8612f402adad29023d40195337679f7cdd17915f500d11461e746f608d46fa37", "245b06c5b59448b020604474776a64d91660bcb5733f6afe3cd32f4cefec71f9"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Container.lean", "Ix/Kernel/Certified/Ordinary/Container.lean", "229fa390d45d0052ef899b5e609b8f86bc81e57213d72b5a02be6f8d223e859c", "05174d0a323ef376ec340856e4c546899bcc8c148dfa734207605beb4b9ec129"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Eliminator.lean", "Ix/Kernel/Certified/Ordinary/Eliminator.lean", "f447bab9bea15ef6d0ee1b68d3483b6d9403b7ddc9058449ce0601396bbd9ec8", "72ddcb287339570bd531034ca33e7156e750f7600418156269c9a5b1265525bb"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Family.lean", "Ix/Kernel/Certified/Ordinary/Family.lean", "8c563254b994b8f6c4b5ff2d4a2387072789634b3121b86a45c10149be9c8923", "14eba9e20c2b09e5d0008c4cd40e994c0b2178dbe62f190a8f239617c7eda57c"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/LargeElim.lean", "Ix/Kernel/Certified/Ordinary/LargeElim.lean", "cea67ca384c6c67bc8f110ca73a981fc2054a4eb8814a06bff194c46e35577cc", "f0652321fcef72a130070d1ef7329162e176224b7f7668a056a3b012e22e8c7e"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Reading.lean", "Ix/Kernel/Certified/Ordinary/Reading.lean", "ae00e1e0185abc8f2208f3d0665ab1d6119e58589b37ed8059ded5e72869fccc", "9a5b54e58b4b8712f53c749c1159b8a961e8a28542a3ea1e4f70c713f2480a8b"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorReading.lean", "Ix/Kernel/Certified/Ordinary/RecursorReading.lean", "7418c845cbea665fd05504ceec48dd13d252c84a554ea511ac45107823f79b98", "3bff55614bc237a5ead680475e81884aaa2d9b17bda5a4659bbadd07d2ae13c4"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorStage.lean", "Ix/Kernel/Certified/Ordinary/RecursorStage.lean", "e6b240ea2dd0365184be563f6e2894fc2e0bf560ee2fb5abf2bebf52058b736d", "f04bb95461e5f3e7eba8915b262ceddae1049ce0ea5a0796016843d375d7370a"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorSyntax.lean", "Ix/Kernel/Certified/Ordinary/RecursorSyntax.lean", "a15eb2395e6bd2a91dde535e931baaedc2e36a7e96a415905635da942316c18d", "990d3dbf8631c6d8b166fc7bd6c0fdd6783c34cce810978a3e53086dbb4dadb9"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RecursorValue.lean", "Ix/Kernel/Certified/Ordinary/RecursorValue.lean", "f0915684633f08b93588652dc5cc9d44ae0ad79e5de1bbbf2816511559d59a0a", "a0cd6610918ec7834009f6cfe1c1f89f4ea88bdd946436f9cf870f097e2d5d45"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleChecks.lean", "Ix/Kernel/Certified/Ordinary/RuleChecks.lean", "6e748d47998f1d3314f71c4a320f28a6bb400e8a3068e4d58357f38c16bb51ef", "560743864397bc554eb2aeccf9891d0bdfffdf49cfbac0f60d6935016af3b572"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleEquations.lean", "Ix/Kernel/Certified/Ordinary/RuleEquations.lean", "ffa708a84577d0edee7bf90abdbaeab41f025b74fd55b9faa430c0fc6ebf418f", "d9ceab6b6c4f08426035de5e1337bc547c78f27c4bb3a5f2eeb4e598ed7a49bc"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/RuleReading.lean", "Ix/Kernel/Certified/Ordinary/RuleReading.lean", "42ca1e10514a2c1e97f8e645dfc584fc1788e87bfb6fe9fc63cf82e5c6b491c3", "a79b3567fdc0fe765baada06bb9325e75bc9aefb765ad0d1ab4885803ea3ea29"⟩,
  ⟨"Ix/Theory/Certified/Ordinary/Shape.lean", "Ix/Kernel/Certified/Ordinary/Shape.lean", "b90dfc2e5e5366d9bac38b6a3afb80f5a5ebb4939d0f8a56cf967e48e4559f3a", "6365bac4079ac306cb36a0ab351dc6978c3fdd4c865a9db4eafe56c620bec6a0"⟩,
  ⟨"Ix/Theory/Certified/PropWhen.lean", "Ix/Kernel/Certified/PropWhen.lean", "ba546bec95eee9e01b85f28048290a9aad0d3d9d8d4f3041ca55554cb9975e3c", "970966c84576fa99dfdee890e94024d071b54cbe5debbfcded9059df222cd93c"⟩,
  ⟨"Ix/Theory/Certified/Quotient/Reading.lean", "Ix/Kernel/Certified/Quotient/Reading.lean", "879cd33813a146d4f42a27954a49b3a14c0b577f74e667225eb3c3b6949f3f8d", "ec3862875ccf3bec1c0bbb64713aac0d61cc7347f1a517f14c567ad54fad3095"⟩,
  ⟨"Ix/Theory/Certified/Quotient/Syntax.lean", "Ix/Kernel/Certified/Quotient/Syntax.lean", "1a7b4f53dc2c2ec0a7ab1798c10491943c851a8496aaa2be64fea60af9080ff8", "210d128cc4fb2b8ac9cea01db49fdf73f829d2d63674f6bf5be2e5f8adac943e"⟩,
  ⟨"Ix/Theory/Certified/Signature.lean", "Ix/Kernel/Certified/Signature.lean", "e06ebc68dbd7b7997ed9c85ea6cc8bfe541c7830cc1af06c12a4062fbc4c8f00", "ef38a7af27d54e0cc25e8f9f4fa8bc8f82603f30764985e7becf825223ad4ddb"⟩,
  ⟨"Ix/Theory/Certified/Standard/Checked.lean", "Ix/Kernel/Certified/Standard/Checked.lean", "3090dea2c13b7a4cfe48fc298121f8671a776166f2ce27b7736cba38e8a87c85", "46b41cd12a4f66708c41ac82b9d413a85ffcf93eb7af50707caf260d1755e0b4"⟩,
  ⟨"Ix/Theory/Certified/Standard/Realization.lean", "Ix/Kernel/Certified/Standard/Realization.lean", "f0b7a970b3a4a9d8f1eafcd807bf91707139024a089b88f227c6fb8930cba4fa", "13d67b3db5f33d0a3796513eb2fa4c3593ff9ca494d781e209423ed918e98696"⟩,
  ⟨"Ix/Theory/Certified/Structure/Checked.lean", "Ix/Kernel/Certified/Structure/Checked.lean", "bd8336b3506f61303e5f2068ad300bfbcff9fbbca3f4ea40fdd3a08e1caabf13", "5ae5234a499a82a6381172fb488ee46c4e5d554571e18d6af69b699e55eaa387"⟩,
  ⟨"Ix/Theory/Certified/Structure/Computation.lean", "Ix/Kernel/Certified/Structure/Computation.lean", "e9319a046b644a5412b4c0b88433af3522d5d7038ac24807477dd0045badcc92", "2b0e43d7a8bf68d3a47b21c28d7f6d6fa6453c1b7b4a712a87b1303b4c40eece"⟩,
  ⟨"Ix/Theory/Certified/Structure/Publish.lean", "Ix/Kernel/Certified/Structure/Publish.lean", "562aa6be637c211cbc44a79ea7051f5322e7a378cb54150a02fafff606b47d1c", "87804bcdfd3748f3d5e5906cd959a89a3faa6d26fd037533a211db47aec4c843"⟩,
  ⟨"Ix/Theory/Certified/Structure/Reading.lean", "Ix/Kernel/Certified/Structure/Reading.lean", "ea25446679471ed786d5487f1375ee2ccf07e7602b10787b4ff51b7fb7dd2f38", "b9a9f0945d015959d4e269c9103e6c6f909061e45038c955a6f2340f97c67b3b"⟩,
  ⟨"Ix/Theory/Certified/Structure/Syntax.lean", "Ix/Kernel/Certified/Structure/Syntax.lean", "e114fddb504393ee7975ce521a1e0218ece270c9cbece13850a334252f1ad3b9", "9b5e947e6b9de8a5b47fcbd9c7c220b8a074a70af39ffbca76fe37e01684427d"⟩,
  ⟨"Ix/Theory/Certified/Structure/Value.lean", "Ix/Kernel/Certified/Structure/Value.lean", "e89f5f99c5b1154812062665fba0704902400d8209a6300cad6c72533e163f53", "a32dbb5e22e725c381f56740e8d5bd64d3b29210d61c72d206ac1163360db5c1"⟩,
  ⟨"Ix/Theory/Certified/Telescope.lean", "Ix/Kernel/Certified/Telescope.lean", "03e54b24dc101b2ecd1800ac780fe544dbf20f04db8984854e5015480f7575c7", "ccf983904385ac678af6710604d2dc23de82d05a65e6f32aaa09de284330cb9d"⟩,
  ⟨"Ix/Theory/Const.lean", "Ix/Kernel/Const.lean", "1086a0bc1f440f13ed7d31f398a8dc0f74517900fb45a4f4379b1459d890f91f", "461a3b48f20c2fa18c6539fe21c8a0aa7609a0c2951a30ae06e77ad9c4310e1c"⟩,
  ⟨"Ix/Theory/Expr.lean", "Ix/Kernel/Expr.lean", "dd0d0e2cbeac112343e08d08fb4f226b8aaa1c3c8e65b73aa69858e4a71ec034", "fb0b557a963aa3f1e642b6b27149616c5abe412b08b7b96f1eaffd533ea0d435"⟩,
  ⟨"Ix/Theory/ExprSubstitution.lean", "Ix/Kernel/ExprSubstitution.lean", "78f0ee4169464c6f7f2e51fcf95eb8ba73349adbd871a10a3e5ec9007f35c779", "bc9dd8f5f6b58c60d575b645b6be03e247a7f2ff325cbe05271c8172e5e68937"⟩,
  ⟨"Ix/Theory/Inductive/Levels.lean", "Ix/Kernel/Inductive/Levels.lean", "84724e7502dc16a5d32000b32b46bc518c851ab0ce2e4600d56878def665a339", "ee06f871612287b2027bff4450434d5a394143d5a832754425dc804581410280"⟩,
  ⟨"Ix/Theory/Model/Annotated.lean", "Ix/Kernel/Model/Annotated.lean", "ed32d33dc81c5f1e0154689f322423d8660f8472067bd3bf19a3d875d082cdc1", "c17370091732e8d70afd68b3cdd39532793909a1f4e7ebe9aac399036c62ecd1"⟩,
  ⟨"Ix/Theory/Model/BetaSpine.lean", "Ix/Kernel/Model/BetaSpine.lean", "e6105986031ea47df35adfe77feb2f170303e4035027453cfba57a7d47a35838", "d7b1b9052c550b0d2be099f4e4c6629fcb15a11b59521a2e9bd34ff0d696d13b"⟩,
  ⟨"Ix/Theory/Model/BetaSubstitution.lean", "Ix/Kernel/Model/BetaSubstitution.lean", "9118fca2803baee20bb18d3154936cf16e61525c55cb640c9a5b35bf2c80ed45", "daba37d1ca2b9332058fc535adcf09a311d7f3fa213d79ed4ada82c729b3254b"⟩,
  ⟨"Ix/Theory/Model/Checking.lean", "Ix/Kernel/Model/Checking.lean", "e04fd5d5d2882717055cd309048dc69fabe512c2a73ba1aa331f452a95be9814", "4f1c80f4f966bf014e6c39ccd102dffa2d786b27829fa1b06f96ec84b52fd2dd"⟩,
  ⟨"Ix/Theory/Model/Context.lean", "Ix/Kernel/Model/Context.lean", "8c57825ebdb7e28cc54ce42e8924812e2c9988fe7eb0b0364acb4b3afe689585", "50f5dff863b89926dc6a927b9d502be0e2eab8f5ebedabd704e7625144f28495"⟩,
  ⟨"Ix/Theory/Model/ContextTransport.lean", "Ix/Kernel/Model/ContextTransport.lean", "0b8d81d3948b669fe9d401e61a699df38a9aba01d2140dfaaabaa5ccc911bd1b", "b2077f09aa2b356c7356e6795037f5e10e20ec2388b4fc60e5ec692a5ec0ea02"⟩,
  ⟨"Ix/Theory/Model/Environment.lean", "Ix/Kernel/Model/Environment.lean", "d04caed44db24b1e9d975887667fcfd391b18632ad86594b3b0dcece641db70c", "b7af247d74c2249ff43da1bdd962304d7cc989ba2cdc9443b522cf7b1052a6b4"⟩,
  ⟨"Ix/Theory/Model/Extension.lean", "Ix/Kernel/Model/Extension.lean", "5f495b1203494322850b8460f6d2cd947c371251f9aba7a74ea63372aafe232b", "325ae7a1f30f81a17e5e6ac719e6368438891348d92b8e6df99da00028ec4558"⟩,
  ⟨"Ix/Theory/Model/Inductive/Codes.lean", "Ix/Kernel/Model/Inductive/Codes.lean", "8ebf69a14c0f0b08d721ddd4d91d47c0fc213d5be8afbf628e0e6d6ea304a23e", "cf014ded566034230ce159cc8e4e093d45fe3ea3b01d8b804bb4ac1392c3d514"⟩,
  ⟨"Ix/Theory/Model/Inductive/Container.lean", "Ix/Kernel/Model/Inductive/Container.lean", "d91819e3511afeadc5afbcb15136cf4c4a648c00a0df5871391db77382123a7f", "7bf0b95caeaaa89941347c3a171d0e1713aca58a73b88ce8ddbcfcdf1204b3b4"⟩,
  ⟨"Ix/Theory/Model/Inductive/Recursor.lean", "Ix/Kernel/Model/Inductive/Recursor.lean", "9e3447aa42c3db2c4492691e4bc7f57073e13c27ff46081f48b073bc918739d9", "8e801cedd3aad08a42501a473b2414647c24784771e8eb9550383e93db75cd95"⟩,
  ⟨"Ix/Theory/Model/Inductive/Telescope.lean", "Ix/Kernel/Model/Inductive/Telescope.lean", "b75ffc42b152c5ed7bf3da8d70ca08317c435450ef7274d9e56e6fa25c6dfa94", "3d78cf24fae37e7a82128836a971e47e1b93dac7e818731e0ec009626c761665"⟩,
  ⟨"Ix/Theory/Model/Instantiation.lean", "Ix/Kernel/Model/Instantiation.lean", "042fcc537d6afa91a462c6dedfadc2c2b40140178a9d97cd50758f94147b6f77", "bd310c3957254db3f264dcc8305624962a4c96c8b6b0f03a2abf753e4de94a7f"⟩,
  ⟨"Ix/Theory/Model/Interpret.lean", "Ix/Kernel/Model/Interpret.lean", "f46a22934113337b8f4a05b5410cd3205d8430ec9fad97d4e8281b988aa38fa9", "a001b6965fb05827b6cf80b50fd804a3af87957f3cb72492889fb19baef4e8d5"⟩,
  ⟨"Ix/Theory/Model/Judgment.lean", "Ix/Kernel/Model/Judgment.lean", "f04301f42ca7bc22d861d0171ec677c34a08a94e73c8eea9d2b885c9c924e111", "1b7504ac05f16cd41c8fb0c145c7d13f0fd1e88c2e3686c3b58313d818313efa"⟩,
  ⟨"Ix/Theory/Model/LevelCongruence.lean", "Ix/Kernel/Model/LevelCongruence.lean", "b2f194118fc99d3fa0054174eb5b73095133955c6c09c32719e4ebef76a3d336", "d02d2e8d8978d5c7ad30edebd13e9d4bfb050a286980971021413859db21e474"⟩,
  ⟨"Ix/Theory/Model/PrimitiveValues.lean", "Ix/Kernel/Model/PrimitiveValues.lean", "451101f02ea9158fdb4ea81995bde5fcabb2c7496f00435d86cf84c876a77396", "5b167ada76ba6eebde5a63deb0eb4e83858b74688b55a9e704537a4dcf255697"⟩,
  ⟨"Ix/Theory/Model/ReferenceMap.lean", "Ix/Kernel/Model/ReferenceMap.lean", "74bef71492efbfce059d3eb35ea7d263f85baa24d33b51dcfd53dadd1a5ec95c", "dbef023f0d087436c251e9a7e8d4dee4220014fd971684edaf6d45ba06e601d2"⟩,
  ⟨"Ix/Theory/Model/SetModel/Container.lean", "Ix/Kernel/Model/SetModel/Container.lean", "08928de8de78f1fabc535b65e8511b068ad3c8b517055aa363674c2c90cebd4e", "ca45e2ff0f1edc09ad910fa697402fe11f831b79d4edf9c6216b2a8ef3ac6ab9"⟩,
  ⟨"Ix/Theory/Model/SetModel/Iter.lean", "Ix/Kernel/Model/SetModel/Iter.lean", "019ef9fa62f5d141ccc8c7e41259ff52dfba56412b3a57917ba60c28a2bfb378", "1fd1bd1ce3fbf52c7af70d725d2303a035dad90c8d37798c0188407b71c75d2a"⟩,
  ⟨"Ix/Theory/Model/SetModel/Ops.lean", "Ix/Kernel/Model/SetModel/Ops.lean", "6ce498a847103c32824e40f22e51db42163da98c09374f6a69e2a85a69f1e732", "11735021b32d4e927f6c4a50b200046c326b5c422d1d6172a201db652efbccb6"⟩,
  ⟨"Ix/Theory/Model/SetModel/RecGraph.lean", "Ix/Kernel/Model/SetModel/RecGraph.lean", "da698d1a7346eaaa2f5b4734de06c955a05791ff52728d554082814328bd5caa", "c5982fffb311ae91194757d0a03fb94fc570108028350b1e1e102c4ba52420e7"⟩,
  ⟨"Ix/Theory/Model/SetModel/TaggedSum.lean", "Ix/Kernel/Model/SetModel/TaggedSum.lean", "53b565da9a2ce8848ca2442e52bfa0ff13b3f044017858fe69be42a9b2614aff", "9ab768aa699042b068a459cfe99f0d47772b4fc43f9e958d393fa08de7644a21"⟩,
  ⟨"Ix/Theory/Model/SetModel/TupleTower.lean", "Ix/Kernel/Model/SetModel/TupleTower.lean", "1089b4ea6d9e7ff3ed9902a3c3d8f6697332b2aac23f94e503584b9cdf972750", "bb562d364a074fac120f5db08ac566efff06e6e95cdb05798806454f0bb9ce80"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Core.lean", "Ix/Kernel/Model/SetTheory/Core.lean", "9e8d3537a66ded9e4d9142765c9ebda3eb4c3a8f780927cea6657e076933657b", "a3df853f71dd17d713ea4d177f3331108404cd19bf681f5cefd87a3d26d146ae"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Choice.lean", "Ix/Kernel/Model/SetTheory/Derive/Choice.lean", "47e64bd1d52287230b993398ba5ee584d7b15e256b86f4fa0eaf1735c4510b93", "6fc3f03b725e0aa5c0d2d6bc5152fb36552f740d361d82f78ce8a34d110a0892"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Empty.lean", "Ix/Kernel/Model/SetTheory/Derive/Empty.lean", "b9a961b71e8a0576ceb00fbdc0288231d360576cd7afa72375606c793da15541", "18598a6e1a9fb28c02cccde80d7eaf58e4a75f5ef26ecce4035e10cd4e6c29e1"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Graphs.lean", "Ix/Kernel/Model/SetTheory/Derive/Graphs.lean", "5bff626e2b77ea3d83302dd8959ef0e0816e9d9da59d52d573134f139e69316c", "fe1556733b88b31eaea15d3563ba0861810247db48f532fedad2473f60dcc8d4"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/LfpFam.lean", "Ix/Kernel/Model/SetTheory/Derive/LfpFam.lean", "0657c96c6dffb7a49fec92c97769356595ec8a6f06b5f73594d4732d2fef8b8f", "245a8d17cfa8abec9e595b4889ba4bf74fd17dfe84dc6d1e61b66e7fa6aaecf3"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Lfp.lean", "Ix/Kernel/Model/SetTheory/Derive/Lfp.lean", "65e44e5bfe2fa0720b334cd31aff2c2eff511364feadfd5fd60c1ebf150b9a89", "b8cc7627688c32128ff84c234c7ef1c4577ccf19291146bb39ce6d0ceff99eac"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Omega.lean", "Ix/Kernel/Model/SetTheory/Derive/Omega.lean", "0cf178fada4077bfc8ba7dc257d8ceb77e7db8a452a9fba09eb736ad84f475be", "1c5662e3ac0c1a4a4b693fddc2320ae882695db4802d98afccd5b389ff1383c5"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Pair.lean", "Ix/Kernel/Model/SetTheory/Derive/Pair.lean", "a72c5b13f5657a8299b060bd344068f56c3e2fadfc3619e64b9bc28e98085c91", "7dd45c53e966fd7d7b2c117eb65033fe4082cfeb257f6e1e8ea8a8104de3227e"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Pt.lean", "Ix/Kernel/Model/SetTheory/Derive/Pt.lean", "520286bf987d29f56976d32ed2527ddf494ac80592fba05c1ffc4ad7627d9934", "422a54a0e32645d31489005911638543e3a40635afc3c5bef4700096b8598969"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Quot.lean", "Ix/Kernel/Model/SetTheory/Derive/Quot.lean", "356b3b639fad5c6a9990bf106a38d49b32d0b0ae80537aba2719aaab8f9d9c84", "42607a68dba1fa7e64f11ca5b7b05df87ee954333ca99c78e9859f889c1c356c"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Sep.lean", "Ix/Kernel/Model/SetTheory/Derive/Sep.lean", "38536c268957fe0ad6e0127a1f07677bbfe4a17de82d0a2738b9042db55be2c7", "6eef056423c2a2c0c86f8bd6cd27b75a52754cef785143dc2042251f1a29618a"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Sigma.lean", "Ix/Kernel/Model/SetTheory/Derive/Sigma.lean", "59cfd35485e1b90d199089aea2886fe7ed12bd9f02637d2d7cd5e21536ec6ef5", "35fd8ffc8b34e7d6a6c33d0e2808b85dc65ab8f974f9148960689aa1348d4d01"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Universe.lean", "Ix/Kernel/Model/SetTheory/Derive/Universe.lean", "c3eb55ee316ce142c16fa5c9a3e06ac45721767bad845ce8cd4c485ac7cce494", "31e12562c17d07630f72469e35b5fa8b47463fb8f321c20cbd00b182cb70cd2f"⟩,
  ⟨"Ix/Theory/Model/SetTheory/Derive/Univ.lean", "Ix/Kernel/Model/SetTheory/Derive/Univ.lean", "33e83e18da0a782904f42acc563c1c4259b60a1833bf2b22af41a28f1bd797e0", "59140f05a139f36e57fc8770e700ef53557d867771df0392911cad04ef0a8826"⟩,
  ⟨"Ix/Theory/Model/Signature.lean", "Ix/Kernel/Model/Signature.lean", "bb1a22e9c2e82a865b9c0c221f4f53356417a539099c42814f4290cfd71029c6", "ce5c71df5744183ccb6fbb4909031fb87e837ba556d5191a063f5f29011df8a0"⟩,
  ⟨"Ix/Theory/Model/Substitution.lean", "Ix/Kernel/Model/Substitution.lean", "e90eace7615fb232d1f948fd1f25bfccec833277d8df16239dbe7225ecd5adcd", "e099a74df59e17e099dc91baaac1d6ffcf81c89516fe92c746b890626050f3c4"⟩,
  ⟨"Ix/Theory/Model/Support.lean", "Ix/Kernel/Model/Support.lean", "85a181776d1c09e59f024b45faffdd2ac25129eea88644f499771befc3b215d0", "2a4fec506edacb6cf55933d3106df090b4e6d15224eebfa149120d9a300f9fc3"⟩,
  ⟨"Ix/Theory/Model/TelescopeSemantics.lean", "Ix/Kernel/Model/TelescopeSemantics.lean", "d6bd21fe9f80863e7ccf6cbf7bb374228309be2929be9b56130b2601840bc27c", "d87146f45b304aaeaefba2f6ed2593b3279004e3002f02d8a9cb909458406476"⟩,
  ⟨"Ix/Theory/Model/UniverseBounds.lean", "Ix/Kernel/Model/UniverseBounds.lean", "6122c479c70781d03dc890aa01fe62433a87a9e6b8ee18c04593f4b0394f8fcd", "4b702d3b0ca93165cd363ac2f6edb5b6815da9f77b76765eba4d39a3566a5d93"⟩,
  ⟨"Ix/Theory/Model/Value.lean", "Ix/Kernel/Model/Value.lean", "5165837492c4f96220f275ada33f881529c18c476f7485a02140f103967361fb", "d036f404789ed6123eb2b2badc6906b06ce60dfbd468a63f0b92592a6c973a4a"⟩,
  ⟨"Ix/Theory/Model/WellDenoted.lean", "Ix/Kernel/Model/WellDenoted.lean", "22161a9e497bd3c5398c26865ff7d0f2f92ba3d2faf0d7017a4b5440509868ee", "382b6cb6843246a9989abd50f653518284eef1d85f790ae71a6cdc401238f9e8"⟩,
  ⟨"Ix/Theory/Quot.lean", "Ix/Kernel/Quot.lean", "542671181d3ab2ba9999a8e0ea85778760f2bc145850513cf6fcad14d4ac7dd9", "da6a080e9b93ef3b4acbfdfbb21032237341c556412ddd60d6788ad3f871883f"⟩,
  ⟨"Ix/Theory/Ref.lean", "Ix/Kernel/Ref.lean", "72b21fcb84bf5653761ff1bbc305447c391c6446a0d5ffcab7151e42013b5844", "caf46bf8c993b544c75973b1091af72006573433faa23a38b35e6ed9fd422255"⟩,
  ⟨"Ix/Theory/Rename.lean", "Ix/Kernel/Rename.lean", "1adeda5dd1a733eaeda6e345ef4c5f0fbefaf80e1caaebedb79c1f73c4193c9e", "3b0c8ab150f98e855310a696712dd92f16790cbf82b826f11ee2f69a220a4e6c"⟩,
  ⟨"Ix/Theory/Std/Basic.lean", "Ix/Kernel/Std/Basic.lean", "6e82da238805fcdb9225996b96028f816444615a885d22747d1d860953c0c313", "d9fe83f1ec7d8e30d55befb54b79030f336d46a5b86be39d3a5c6038b05c5db1"⟩,
  ⟨"Ix/Theory/Store.lean", "Ix/Kernel/Store.lean", "2c47bffde6a5357f35ca24bcf194d554afa86ff3b62267c0961d61e65136015a", "23f6c6ffaa0582e37e8d116e9cbdc98d693ceff2baf16c081801dcb845faddd5"⟩,
  ⟨"Ix/Theory/StringLiteral.lean", "Ix/Kernel/StringLiteral.lean", "9b1d58085ef74448a85d0a56cf8e4991b5335cdeb39b7e55160d422f96ae48b2", "87ebb506d20f3193dbd005ea5b4822450e17acecd1434db3ff8dd227a6763006"⟩,
  ⟨"Ix/Theory/VLevel.lean", "Ix/Kernel/VLevel.lean", "8fd068d8f412a42c4f69461ebb7f56a4232fbcbe644dd3e43f4ea5ab554b2a3b", "0483937c0bf0154af1fdb54421be0ffdedbf005ecf3820cb743b973742aaed9a"⟩,
  ⟨"Ix/Theory/VLevelLemmas.lean", "Ix/Kernel/VLevelLemmas.lean", "9f17589c3888e03bd1e66d3d3ef04b86ea5761570a928e49bce1b71c5947c6b0", "a131cafa208faf7dbce493bbdbd08dfa93041d5b425e92598e4d724b50dd05e7"⟩
]

/-- License and notice files from the old branch. -/
def licenses : Array PortRow := #[
  ⟨"Ix/Theory/LICENSE", "Ix/Kernel/LICENSE", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", "cf9ee0e22d7f19885552c933d4097d500c9027fdddfea3bd675e90af212284e9", .verbatim⟩,
  ⟨"Ix/Theory/LICENSE-APACHE", "Ix/Kernel/LICENSE-APACHE", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4", .verbatim⟩,
  ⟨"Ix/Theory/LICENSE-MIT", "Ix/Kernel/LICENSE-MIT", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", "fb722e573ab676ffc697f17a01fb13888dad389fbc879314018380a7dbfc70d7", .verbatim⟩,
  ⟨"Ix/Theory/NOTICE", "Ix/Kernel/NOTICE", "046d7aefcc035fac38420bef9c4eded1591efe83b6d8e68739d70f055c8d7497", "1bf502e56514469e03c508e5358ad4e4f90cbc92bc4daf2a3e909963399952e0", .adapted "paths updated to this repository (2026-09-30): the ported directories, the hash record, and the file references outside this repository"⟩
]

/-- Files ported from con-leche at `conLeche.revision`: the import closure of
`ConLeche.model_exists` (439 modules verbatim, `Verify/Cached/AgreeFloor` and
`Verify/Cached/PushChain` with the one-line 4.34.0 fix, the adapted
`ConLeche/MainTheorem.lean`, and `ConLeche/Kernel/CheckerBase.lean` adapted
to import `NatOpPinSet` instead of `NatOpPins`, L4b), the eight frontend
modules the Ixon reader imports (`ConLeche/Frontend/**` and
`ConLeche/Verify/Frontend/Prepare.lean`, verbatim, L4a), the verbatim but
unbuilt `ConLeche/Kernel/NatOpPins.lean` (it splices upstream's JSON pin
dumps, which L4b replaced with the Ixon-generated
`Ix/Kernel/ConLeche/NatOpPinData.lean` and deleted with
`ConLeche/PinGen/Dump.lean`), and the adapted axiom pin
`Tests/ConLeche/Axioms.lean`. Generated from the L1-L3 TSV as re-recorded at
integration (`plans/review/int-2/rows.tsv`) plus L4a's rows
(`plans/review/int-3/rows.tsv`) and L4b's changes
(`plans/review/cl-l4b/rows-full.tsv`). L5 adds
`ConLeche/Verify/Cached/StreamThm.lean` (verbatim; the no-False theorem at the
stream), from `plans/review/cl-l5/rows.tsv`. -/
def conLecheRows : Array PortRow := #[
-- BEGIN con-leche rows (generated by scripts/provenance-rows.py)
  ⟨"ConLeche/Cached/CheckerC.lean", "ConLeche/Cached/CheckerC.lean", "47e379e20bd3649297d2971203b58d98e4d4e001c9cf62607286a931eaefef55", "47e379e20bd3649297d2971203b58d98e4d4e001c9cf62607286a931eaefef55", .verbatim⟩,
  ⟨"ConLeche/Cached/CoreC.lean", "ConLeche/Cached/CoreC.lean", "4b85c26ebaef7095747cbe614babd153a4a3e4f266c1f77dadcaa69ac5a7d8c8", "4b85c26ebaef7095747cbe614babd153a4a3e4f266c1f77dadcaa69ac5a7d8c8", .verbatim⟩,
  ⟨"ConLeche/Cached/ExprNodes.lean", "ConLeche/Cached/ExprNodes.lean", "6dcdebb32c53eb169c2772ae65b0b3f19094a1b487f555061c7a784bbe03bb3e", "6dcdebb32c53eb169c2772ae65b0b3f19094a1b487f555061c7a784bbe03bb3e", .verbatim⟩,
  ⟨"ConLeche/Cached/ExprOpsC.lean", "ConLeche/Cached/ExprOpsC.lean", "3077a19b38490a4d05d1bf8e1719009a06e15813fff54b760f1c9e5c1534d18d", "3077a19b38490a4d05d1bf8e1719009a06e15813fff54b760f1c9e5c1534d18d", .verbatim⟩,
  ⟨"ConLeche/Cached/Installed.lean", "ConLeche/Cached/Installed.lean", "be979a23cfab59998c6cc26d2ee10f88ef33091d3cb205bf73f383403185d214", "be979a23cfab59998c6cc26d2ee10f88ef33091d3cb205bf73f383403185d214", .verbatim⟩,
  ⟨"ConLeche/Cached/ParsedC.lean", "ConLeche/Cached/ParsedC.lean", "8a1b3fdb1381142e0c776d37c046ad2857244a23880883e830422c5a7499eddf", "8a1b3fdb1381142e0c776d37c046ad2857244a23880883e830422c5a7499eddf", .verbatim⟩,
  ⟨"ConLeche/Cached/StateC.lean", "ConLeche/Cached/StateC.lean", "94a2c0c31a2891112dee894b2310aa003ed7873d4c928bdc32f0fed0300ed88b", "94a2c0c31a2891112dee894b2310aa003ed7873d4c928bdc32f0fed0300ed88b", .verbatim⟩,
  ⟨"ConLeche/Denotes.lean", "ConLeche/Denotes.lean", "dcfb3577afd63cc7a4a42c1125b4739393f709a6f8a303cdb625dbc640190759", "dcfb3577afd63cc7a4a42c1125b4739393f709a6f8a303cdb625dbc640190759", .verbatim⟩,
  ⟨"ConLeche/Frontend/InModel.lean", "ConLeche/Frontend/InModel.lean", "aa0f6cddb2f4478d038e8f2c19aae65fc0bc81eb7adbe9189ed20a4185c0b358", "aa0f6cddb2f4478d038e8f2c19aae65fc0bc81eb7adbe9189ed20a4185c0b358", .verbatim⟩,
  ⟨"ConLeche/Frontend/InModel/Kit.lean", "ConLeche/Frontend/InModel/Kit.lean", "5602c1926326cb46b0f55e14a496609a284804e2fe8de5060b9edb5ab603f6de", "5602c1926326cb46b0f55e14a496609a284804e2fe8de5060b9edb5ab603f6de", .verbatim⟩,
  ⟨"ConLeche/Frontend/InModel/Mutual.lean", "ConLeche/Frontend/InModel/Mutual.lean", "8884e3c820d619c364ac6a3008b9e675374735720fb504da5e83beb102e4f466", "8884e3c820d619c364ac6a3008b9e675374735720fb504da5e83beb102e4f466", .verbatim⟩,
  ⟨"ConLeche/Frontend/InModel/Nested.lean", "ConLeche/Frontend/InModel/Nested.lean", "75ac54033a53fe4076d687ddebf05c601767892db01189082ba8e3e3e0d86fd4", "75ac54033a53fe4076d687ddebf05c601767892db01189082ba8e3e3e0d86fd4", .verbatim⟩,
  ⟨"ConLeche/Frontend/NatOpGround.lean", "ConLeche/Frontend/NatOpGround.lean", "4c9c4d081a0152d6dff1395485f29fdf26f90ed6f4cdcf5d0fd6064a326f2356", "4c9c4d081a0152d6dff1395485f29fdf26f90ed6f4cdcf5d0fd6064a326f2356", .verbatim⟩,
  ⟨"ConLeche/Frontend/Prepare.lean", "ConLeche/Frontend/Prepare.lean", "cb12fc5b5e5e0a7c1028cdd05869f46862faee514e2d89118eae622e7adec9ae", "cb12fc5b5e5e0a7c1028cdd05869f46862faee514e2d89118eae622e7adec9ae", .verbatim⟩,
  ⟨"ConLeche/Frontend/ProjRec.lean", "ConLeche/Frontend/ProjRec.lean", "83edeabc2c033ee5410bf76700d0cdf9983d7ad63056e54be4708373eafd91c3", "83edeabc2c033ee5410bf76700d0cdf9983d7ad63056e54be4708373eafd91c3", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis.lean", "ConLeche/Kernel/Basis.lean", "7b8ecf5df443fa2240726fe5d3b6decfb15c3c1c955c11fff7572bc7b196f294", "7b8ecf5df443fa2240726fe5d3b6decfb15c3c1c955c11fff7572bc7b196f294", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Builder.lean", "ConLeche/Kernel/Basis/Builder.lean", "20d3d1318701c6d29f585c453c66db60bc24ae5a2b2560ef451c2746eecbbe89", "20d3d1318701c6d29f585c453c66db60bc24ae5a2b2560ef451c2746eecbbe89", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Empty.lean", "ConLeche/Kernel/Basis/Empty.lean", "c87c9152504486ad01537c96e0f9d05236b7288e0724b17707cc41edeaf14db2", "c87c9152504486ad01537c96e0f9d05236b7288e0724b17707cc41edeaf14db2", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Eq.lean", "ConLeche/Kernel/Basis/Eq.lean", "ee75b1e0b9d16a8305f293e29cb3c153d9da0408ed49dd55def91f3105860659", "ee75b1e0b9d16a8305f293e29cb3c153d9da0408ed49dd55def91f3105860659", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/False.lean", "ConLeche/Kernel/Basis/False.lean", "802a9aa9804934878f7d214e21f8f6e1324ff9cbdfa2b6ebe589ad324e1c2fe5", "802a9aa9804934878f7d214e21f8f6e1324ff9cbdfa2b6ebe589ad324e1c2fe5", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Names.lean", "ConLeche/Kernel/Basis/Names.lean", "5788f567b8c6a0c240e985a026cc9a91c5afdd25681a1f4fb075e3c1706283cd", "5788f567b8c6a0c240e985a026cc9a91c5afdd25681a1f4fb075e3c1706283cd", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Nat.lean", "ConLeche/Kernel/Basis/Nat.lean", "b42c21a878217d2b45b0c654616c97724efe0ca7efbd74dcdf9d188ebf5e1ad0", "b42c21a878217d2b45b0c654616c97724efe0ca7efbd74dcdf9d188ebf5e1ad0", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/PUnit.lean", "ConLeche/Kernel/Basis/PUnit.lean", "79cba561d5abdb4bc30b66f529ea33be2803f3c3dfa732eb73b522481836e76f", "79cba561d5abdb4bc30b66f529ea33be2803f3c3dfa732eb73b522481836e76f", .verbatim⟩,
  ⟨"ConLeche/Kernel/Basis/Quot.lean", "ConLeche/Kernel/Basis/Quot.lean", "4abb3ced9c0870e4ab0706d516b3866262e34c826b86c634dd250988a9ae4eeb", "4abb3ced9c0870e4ab0706d516b3866262e34c826b86c634dd250988a9ae4eeb", .verbatim⟩,
  ⟨"ConLeche/Kernel/BasisA.lean", "ConLeche/Kernel/BasisA.lean", "3defab91fe906f628f21e1f377e70009093ee9b064fa1b3180b2994f77568e05", "3defab91fe906f628f21e1f377e70009093ee9b064fa1b3180b2994f77568e05", .verbatim⟩,
  ⟨"ConLeche/Kernel/BasisGen.lean", "ConLeche/Kernel/BasisGen.lean", "b931115c804693476b0ce0f457ba1925cdd2d5c6aca623baf692c9e20b1f06ca", "b931115c804693476b0ce0f457ba1925cdd2d5c6aca623baf692c9e20b1f06ca", .verbatim⟩,
  ⟨"ConLeche/Kernel/Canon.lean", "ConLeche/Kernel/Canon.lean", "54e7e6bb11ff89aad144f1ee8f67cabadea2a3d4650fce7cab906ec21a7f1c00", "54e7e6bb11ff89aad144f1ee8f67cabadea2a3d4650fce7cab906ec21a7f1c00", .verbatim⟩,
  ⟨"ConLeche/Kernel/Checker.lean", "ConLeche/Kernel/Checker.lean", "a8c2664b05e12be39acb295b92b0d47f7c9f93cd718fdd35cebcbed13c3d8171", "a8c2664b05e12be39acb295b92b0d47f7c9f93cd718fdd35cebcbed13c3d8171", .verbatim⟩,
  ⟨"ConLeche/Kernel/CheckerBase.lean", "ConLeche/Kernel/CheckerBase.lean", "36287a16d891918875877bc34460bbabe95be8d5047faa5662ddc3e63bed9959", "bd236b00d6abfcba06a094e0e0d5fcf372d53f4261709e9b3c83db541e2b47cc", .adapted "adapted: `public import ConLeche.Kernel.NatOpPins` replaced by `public import ConLeche.Kernel.NatOpPinSet` (the Nat-op pins are generated from Ixon, Ix/Kernel/ConLeche/NatOpPinData.lean; NatOpPins is kept verbatim and not built); port header added"⟩,
  ⟨"ConLeche/Kernel/CheckerSplit.lean", "ConLeche/Kernel/CheckerSplit.lean", "fa4a4c976de37b2b725a63e15f7eece2b1766cb16ff30d92668f0a8e8b7cd16f", "fa4a4c976de37b2b725a63e15f7eece2b1766cb16ff30d92668f0a8e8b7cd16f", .verbatim⟩,
  ⟨"ConLeche/Kernel/Core.lean", "ConLeche/Kernel/Core.lean", "dda2ae74ab914c095c63a3ec788cc0245827bac14f6a608c7faac6600136b4b3", "dda2ae74ab914c095c63a3ec788cc0245827bac14f6a608c7faac6600136b4b3", .verbatim⟩,
  ⟨"ConLeche/Kernel/CoreDefs.lean", "ConLeche/Kernel/CoreDefs.lean", "a543d9899b588131f6c5abdbea7c492861563f23644dda001d9b41a38186758d", "a543d9899b588131f6c5abdbea7c492861563f23644dda001d9b41a38186758d", .verbatim⟩,
  ⟨"ConLeche/Kernel/CoreIO.lean", "ConLeche/Kernel/CoreIO.lean", "9a735f4bc0ab465601cc32b0df3a73317a0bb1e021d8cb2b33ac6db52c1d4618", "9a735f4bc0ab465601cc32b0df3a73317a0bb1e021d8cb2b33ac6db52c1d4618", .verbatim⟩,
  ⟨"ConLeche/Kernel/DeclCheck.lean", "ConLeche/Kernel/DeclCheck.lean", "c529106553fd316337d5cc83ae0432b08178f488c1d7e1dc1eb8c676b3881df0", "c529106553fd316337d5cc83ae0432b08178f488c1d7e1dc1eb8c676b3881df0", .verbatim⟩,
  ⟨"ConLeche/Kernel/Env.lean", "ConLeche/Kernel/Env.lean", "d9fab0471d394c71bd0bbec808619f95b0842cf8b0b080fa0d06f9954fefef7c", "d9fab0471d394c71bd0bbec808619f95b0842cf8b0b080fa0d06f9954fefef7c", .verbatim⟩,
  ⟨"ConLeche/Kernel/Exclusive.lean", "ConLeche/Kernel/Exclusive.lean", "0c3679bafbeac89f644aa812f5db35b8acaf84077f39ea7548eb918b0e234f81", "0c3679bafbeac89f644aa812f5db35b8acaf84077f39ea7548eb918b0e234f81", .verbatim⟩,
  ⟨"ConLeche/Kernel/Expr.lean", "ConLeche/Kernel/Expr.lean", "49b5c5ab59de8027688faf385ab81284f4d968b344230060784abd69062d5eda", "49b5c5ab59de8027688faf385ab81284f4d968b344230060784abd69062d5eda", .verbatim⟩,
  ⟨"ConLeche/Kernel/ExprOps.lean", "ConLeche/Kernel/ExprOps.lean", "82fddb9060f6fa930799824eea235e8e6363fdacd561d4d2793c20c16750346c", "82fddb9060f6fa930799824eea235e8e6363fdacd561d4d2793c20c16750346c", .verbatim⟩,
  ⟨"ConLeche/Kernel/FEnv.lean", "ConLeche/Kernel/FEnv.lean", "5954d4b19a66fed120aa4da957c72c1366c5c24d3ffa51422cc57e86608513f4", "5954d4b19a66fed120aa4da957c72c1366c5c24d3ffa51422cc57e86608513f4", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/Modeled.lean", "ConLeche/Kernel/Inductives/Modeled.lean", "5afd66146f16634252ccafc80bf1a5e2eeed791fc794ec598d24745f9562d66d", "5afd66146f16634252ccafc80bf1a5e2eeed791fc794ec598d24745f9562d66d", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeInstall.lean", "ConLeche/Kernel/Inductives/NativeInstall.lean", "67eb53764350f826d6ecdbe1c5feac8d53261ea8e8cb79b0503123451d858c69", "67eb53764350f826d6ecdbe1c5feac8d53261ea8e8cb79b0503123451d858c69", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeInstallF.lean", "ConLeche/Kernel/Inductives/NativeInstallF.lean", "82ec5ee5bc8cc18c05b081af72a12a6a2509326382afaecef7a2f7e41e922ecc", "82ec5ee5bc8cc18c05b081af72a12a6a2509326382afaecef7a2f7e41e922ecc", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/NativeParts.lean", "ConLeche/Kernel/Inductives/NativeParts.lean", "2989380cbecdad3cb9fc07e0ffa91f224e00051586d5ae01069243444bd15775", "2989380cbecdad3cb9fc07e0ffa91f224e00051586d5ae01069243444bd15775", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/StructInstall.lean", "ConLeche/Kernel/Inductives/StructInstall.lean", "83e7ecc40470d0c1bbac4173e6e8605bdd37708fba5670aa0e69e10b6a5958b0", "83e7ecc40470d0c1bbac4173e6e8605bdd37708fba5670aa0e69e10b6a5958b0", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/StructInstallF.lean", "ConLeche/Kernel/Inductives/StructInstallF.lean", "d5efb8f0e8585335e4ae9620addecdb8769c068f550a81085824a0ff3bee0146", "d5efb8f0e8585335e4ae9620addecdb8769c068f550a81085824a0ff3bee0146", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/StructParts.lean", "ConLeche/Kernel/Inductives/StructParts.lean", "eeda8ddfce0c5af4706093057de5b28ffaee7abdd2a4afe85ecf013a52f5a000", "eeda8ddfce0c5af4706093057de5b28ffaee7abdd2a4afe85ecf013a52f5a000", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/SumInstall.lean", "ConLeche/Kernel/Inductives/SumInstall.lean", "6718f72cd716970e1df4ab4347cb8bd2d92f463282fcfb58eff22d053dc10690", "6718f72cd716970e1df4ab4347cb8bd2d92f463282fcfb58eff22d053dc10690", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/SumInstallF.lean", "ConLeche/Kernel/Inductives/SumInstallF.lean", "ad68353c7da5eb350d615e5938a55279aa628e233866a9e056f7129a419c72bc", "ad68353c7da5eb350d615e5938a55279aa628e233866a9e056f7129a419c72bc", .verbatim⟩,
  ⟨"ConLeche/Kernel/Inductives/SumParts.lean", "ConLeche/Kernel/Inductives/SumParts.lean", "c3dd816a698db3dab5413bc6f6701f69c13c3c7da79424450268a5ff0007dc59", "c3dd816a698db3dab5413bc6f6701f69c13c3c7da79424450268a5ff0007dc59", .verbatim⟩,
  ⟨"ConLeche/Kernel/Level.lean", "ConLeche/Kernel/Level.lean", "2ae9b97c4d67c9a476c7b6edd49a5bb6738f2d5c60d38f13ab692861a03364bc", "2ae9b97c4d67c9a476c7b6edd49a5bb6738f2d5c60d38f13ab692861a03364bc", .verbatim⟩,
  ⟨"ConLeche/Kernel/Name.lean", "ConLeche/Kernel/Name.lean", "46e1005573233f5306444d4c12a5b204614d46e3b7a13064804174e2960a433a", "46e1005573233f5306444d4c12a5b204614d46e3b7a13064804174e2960a433a", .verbatim⟩,
  ⟨"ConLeche/Kernel/NatOpPinSet.lean", "ConLeche/Kernel/NatOpPinSet.lean", "4fc2ff657643c87f8522549517f078600c901a5bcf0f3c66479c165b2c36e397", "4fc2ff657643c87f8522549517f078600c901a5bcf0f3c66479c165b2c36e397", .verbatim⟩,
  ⟨"ConLeche/Kernel/NatOpPins.lean", "ConLeche/Kernel/NatOpPins.lean", "06b1e7701a1a4a8c364d84c99ef670e32e553de22db5e1175f93fccf95595535", "06b1e7701a1a4a8c364d84c99ef670e32e553de22db5e1175f93fccf95595535", .verbatim⟩,
  ⟨"ConLeche/Kernel/PropRead.lean", "ConLeche/Kernel/PropRead.lean", "95277d1575a6ede73e604f6e5bd1c8d83ff0e33bc621205a6feab50f8a28bd0b", "95277d1575a6ede73e604f6e5bd1c8d83ff0e33bc621205a6feab50f8a28bd0b", .verbatim⟩,
  ⟨"ConLeche/Kernel/PropWhen.lean", "ConLeche/Kernel/PropWhen.lean", "4268cb0e6a4e0cd6bb91bf96d73acf627426889461d4b1aa62105accbc9bb498", "4268cb0e6a4e0cd6bb91bf96d73acf627426889461d4b1aa62105accbc9bb498", .verbatim⟩,
  ⟨"ConLeche/Kernel/StdAxioms.lean", "ConLeche/Kernel/StdAxioms.lean", "4128b3cd64a01604ee4ae9570e4165b9e5ea16b9c287b19a3db0072819fcf4a2", "4128b3cd64a01604ee4ae9570e4165b9e5ea16b9c287b19a3db0072819fcf4a2", .verbatim⟩,
  ⟨"ConLeche/Kernel/TrustAxioms.lean", "ConLeche/Kernel/TrustAxioms.lean", "8a3cea4eecbf976204dfaf6fa063c9c0cb1b910954c14bd6bb8a6e6e406b05e3", "8a3cea4eecbf976204dfaf6fa063c9c0cb1b910954c14bd6bb8a6e6e406b05e3", .verbatim⟩,
  ⟨"ConLeche/Kernel/TrustPins.lean", "ConLeche/Kernel/TrustPins.lean", "4177e539a845c9fbdbc94d88ab5b1f0ca2075aa0f6718db4b6a1347a67c681f2", "4177e539a845c9fbdbc94d88ab5b1f0ca2075aa0f6718db4b6a1347a67c681f2", .verbatim⟩,
  ⟨"ConLeche/Kernel/TypeChecker.lean", "ConLeche/Kernel/TypeChecker.lean", "584a3d1499361565317c7d561a3c36ddfdc076d2ab67b4ef5abec74322ca2848", "584a3d1499361565317c7d561a3c36ddfdc076d2ab67b4ef5abec74322ca2848", .verbatim⟩,
  ⟨"ConLeche/MainTheorem.lean", "ConLeche/MainTheorem.lean", "cf76ba7275a8be8846395654aa5b16275cc97329bdc45945d6a93e91f20fb229", "a7e3612f81660f72f4457bc4d76f228d0b024a9d8c4d712ea58065d2f1851152", .adapted "adapted: model_exists only; no_False_declaration and its frontend/StreamThm imports dropped; docstring cut; port header added"⟩,
  ⟨"ConLeche/Model/Annot/Bit.lean", "ConLeche/Model/Annot/Bit.lean", "4c0b92043d8dfd1fc8d5ae4a9b81663c61230259729ce714546d2d3ee6424d09", "4c0b92043d8dfd1fc8d5ae4a9b81663c61230259729ce714546d2d3ee6424d09", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitClosed.lean", "ConLeche/Model/Annot/BitClosed.lean", "f5d970148a7c9cc9b485187a03a521493c703d4beb61855433832443ba4283b1", "f5d970148a7c9cc9b485187a03a521493c703d4beb61855433832443ba4283b1", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitConsCross.lean", "ConLeche/Model/Annot/BitConsCross.lean", "29f10124c90bdbe6e8622e18470a97ad4f9d1d79a67c5007d90b99736a082332", "29f10124c90bdbe6e8622e18470a97ad4f9d1d79a67c5007d90b99736a082332", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitExtend.lean", "ConLeche/Model/Annot/BitExtend.lean", "3dca0c0a2b057abf1283e2ab27deacf900a05f21bb0af8280705023e69b3cad6", "3dca0c0a2b057abf1283e2ab27deacf900a05f21bb0af8280705023e69b3cad6", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitExtendTower.lean", "ConLeche/Model/Annot/BitExtendTower.lean", "2fbdcd5875996e2f0f47da134ef29882f9ac9ff8d769390c8a91f8cf267be5b4", "2fbdcd5875996e2f0f47da134ef29882f9ac9ff8d769390c8a91f8cf267be5b4", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitInst.lean", "ConLeche/Model/Annot/BitInst.lean", "70d98baa07165550d03849e909bb33822fdb142f5cc91b8006435646caa49294", "70d98baa07165550d03849e909bb33822fdb142f5cc91b8006435646caa49294", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitInstall.lean", "ConLeche/Model/Annot/BitInstall.lean", "8b4cdb526fa1a8824d9e274813ce42a6c84fcae4ee69408818b33dec4f9e9157", "8b4cdb526fa1a8824d9e274813ce42a6c84fcae4ee69408818b33dec4f9e9157", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitLemmas.lean", "ConLeche/Model/Annot/BitLemmas.lean", "9387a7aab8758e94992f6869c9124ebf91fe5f7370763eac5b1e1d3cc161bc16", "9387a7aab8758e94992f6869c9124ebf91fe5f7370763eac5b1e1d3cc161bc16", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitLevels.lean", "ConLeche/Model/Annot/BitLevels.lean", "1c74b01c06cd81294b7188f256863ab32bc237b649997cd14c44ee3d61aae904", "1c74b01c06cd81294b7188f256863ab32bc237b649997cd14c44ee3d61aae904", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitRename.lean", "ConLeche/Model/Annot/BitRename.lean", "fdcfd36b1689f4cd83782c6638f84c353272b051712e1dca0e916875f89e095b", "fdcfd36b1689f4cd83782c6638f84c353272b051712e1dca0e916875f89e095b", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/BitShift.lean", "ConLeche/Model/Annot/BitShift.lean", "7707b1cc24a4e5de6ad73281378cf54f4d823b450c29db00237d95d2e27c8fcd", "7707b1cc24a4e5de6ad73281378cf54f4d823b450c29db00237d95d2e27c8fcd", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/EnvModel.lean", "ConLeche/Model/Annot/EnvModel.lean", "d409cec291e9070c0bfb96415a9cd3e303f009e58f4f211ac05a0230c90e8beb", "d409cec291e9070c0bfb96415a9cd3e303f009e58f4f211ac05a0230c90e8beb", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/EnvModelM.lean", "ConLeche/Model/Annot/EnvModelM.lean", "435718225541385057f3fdcadc76d95aef4750c559e18485c0f62f5f399d54ae", "435718225541385057f3fdcadc76d95aef4750c559e18485c0f62f5f399d54ae", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/Laws.lean", "ConLeche/Model/Annot/Laws.lean", "826224bf057a7e32c98dc7adbda2657a34e9cfd2f17394190b4211c7b31a551c", "826224bf057a7e32c98dc7adbda2657a34e9cfd2f17394190b4211c7b31a551c", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/Valid.lean", "ConLeche/Model/Annot/Valid.lean", "dc16587e866652e3da8f62db46b285eef1caa7be0c325f56a8e64ff5946aa928", "dc16587e866652e3da8f62db46b285eef1caa7be0c325f56a8e64ff5946aa928", .verbatim⟩,
  ⟨"ConLeche/Model/Annot/ValidSpine.lean", "ConLeche/Model/Annot/ValidSpine.lean", "df908974921fe4d7da34a8b342ada80a9b9042f8b9b511b1d429081eb2494d29", "df908974921fe4d7da34a8b342ada80a9b9042f8b9b511b1d429081eb2494d29", .verbatim⟩,
  ⟨"ConLeche/Model/AxiomBits.lean", "ConLeche/Model/AxiomBits.lean", "b1de6902126d181ccf9b73219ab9e99e72add0347e1035a317f01e0d8678114b", "b1de6902126d181ccf9b73219ab9e99e72add0347e1035a317f01e0d8678114b", .verbatim⟩,
  ⟨"ConLeche/Model/AxiomMem.lean", "ConLeche/Model/AxiomMem.lean", "f91609e6b36b9b446980b2534d99fb198efd33a96c9c387b7023f42d5bb85bc0", "f91609e6b36b9b446980b2534d99fb198efd33a96c9c387b7023f42d5bb85bc0", .verbatim⟩,
  ⟨"ConLeche/Model/AxiomPin.lean", "ConLeche/Model/AxiomPin.lean", "3dd59f86a1be7b807049c12209ad2750977a8e392470518825e1d51b77020942", "3dd59f86a1be7b807049c12209ad2750977a8e392470518825e1d51b77020942", .verbatim⟩,
  ⟨"ConLeche/Model/AxiomReduce.lean", "ConLeche/Model/AxiomReduce.lean", "98d61ca524559ba5f9d392499b11831298f6467a32c40824df85cd83d78193ca", "98d61ca524559ba5f9d392499b11831298f6467a32c40824df85cd83d78193ca", .verbatim⟩,
  ⟨"ConLeche/Model/BasisBlocks.lean", "ConLeche/Model/BasisBlocks.lean", "fb7b30e909ef2e8dfc3b81f7b9e28516013a63add7517bb0ab31c43e1b1ed57d", "fb7b30e909ef2e8dfc3b81f7b9e28516013a63add7517bb0ab31c43e1b1ed57d", .verbatim⟩,
  ⟨"ConLeche/Model/BasisCons.lean", "ConLeche/Model/BasisCons.lean", "60a9b6a917aaef5cd3486eaee302c52bc5375984baaab10c35791aa56bf7b16e", "60a9b6a917aaef5cd3486eaee302c52bc5375984baaab10c35791aa56bf7b16e", .verbatim⟩,
  ⟨"ConLeche/Model/BasisEmpty.lean", "ConLeche/Model/BasisEmpty.lean", "ced691a8671145547b9ec8c2c123757239ecaca31ed3a0d3b72d23ee395d8001", "ced691a8671145547b9ec8c2c123757239ecaca31ed3a0d3b72d23ee395d8001", .verbatim⟩,
  ⟨"ConLeche/Model/BasisEq.lean", "ConLeche/Model/BasisEq.lean", "db47c03cf2234453eed377aba9631f8d202c25e926a889b5bcadcd39134a1075", "db47c03cf2234453eed377aba9631f8d202c25e926a889b5bcadcd39134a1075", .verbatim⟩,
  ⟨"ConLeche/Model/BasisFalse.lean", "ConLeche/Model/BasisFalse.lean", "48a082ef4029a4bb0866262a46b4118e7261a341569352223a32b10d4b19c0f0", "48a082ef4029a4bb0866262a46b4118e7261a341569352223a32b10d4b19c0f0", .verbatim⟩,
  ⟨"ConLeche/Model/BasisQuot.lean", "ConLeche/Model/BasisQuot.lean", "94ffec8c9768cc33703d0362e10c6e94bf0c6ff8ffb84738e8c5d501a16d98c3", "94ffec8c9768cc33703d0362e10c6e94bf0c6ff8ffb84738e8c5d501a16d98c3", .verbatim⟩,
  ⟨"ConLeche/Model/BasisStep.lean", "ConLeche/Model/BasisStep.lean", "b808b1764443050f6641a2109f724c69b82c8d5d0d78e9a196c1c927cb95ca8f", "b808b1764443050f6641a2109f724c69b82c8d5d0d78e9a196c1c927cb95ca8f", .verbatim⟩,
  ⟨"ConLeche/Model/BasisTypeOk.lean", "ConLeche/Model/BasisTypeOk.lean", "6ae64ee87cf0b210e5160a776ae9bf6b831e56821a677105fe29f5e966f8c308", "6ae64ee87cf0b210e5160a776ae9bf6b831e56821a677105fe29f5e966f8c308", .verbatim⟩,
  ⟨"ConLeche/Model/BitAgree.lean", "ConLeche/Model/BitAgree.lean", "d63d3b401e2a9ca41ee2e6fe8b3300c4a9a239b1b66d8debbe6f86ad90892106", "d63d3b401e2a9ca41ee2e6fe8b3300c4a9a239b1b66d8debbe6f86ad90892106", .verbatim⟩,
  ⟨"ConLeche/Model/Caps.lean", "ConLeche/Model/Caps.lean", "71b71a8f61851dbb371b40eaf1d3ac195698b3909ee61a125563ac303a846564", "71b71a8f61851dbb371b40eaf1d3ac195698b3909ee61a125563ac303a846564", .verbatim⟩,
  ⟨"ConLeche/Model/Capstone.lean", "ConLeche/Model/Capstone.lean", "7060906ee65fa49ee4091c38a24c5730992ab794df7593cc5cc950f3440e0605", "7060906ee65fa49ee4091c38a24c5730992ab794df7593cc5cc950f3440e0605", .verbatim⟩,
  ⟨"ConLeche/Model/Claims.lean", "ConLeche/Model/Claims.lean", "39097d5fda06bbdf6685cad8203fb6e9c7d70026740040f441e774bf414fae9c", "39097d5fda06bbdf6685cad8203fb6e9c7d70026740040f441e774bf414fae9c", .verbatim⟩,
  ⟨"ConLeche/Model/ClaimsIO.lean", "ConLeche/Model/ClaimsIO.lean", "d6fe36ed831e4d98a6566f3d081764714ef86e87bbd2e3b0216b40eb38cba8eb", "d6fe36ed831e4d98a6566f3d081764714ef86e87bbd2e3b0216b40eb38cba8eb", .verbatim⟩,
  ⟨"ConLeche/Model/CtxOkKit.lean", "ConLeche/Model/CtxOkKit.lean", "01cd1bbf4d3171ecfd4c8419e36a1991b65976a4788604b8703a70d4be7d8a42", "01cd1bbf4d3171ecfd4c8419e36a1991b65976a4788604b8703a70d4be7d8a42", .verbatim⟩,
  ⟨"ConLeche/Model/Currency.lean", "ConLeche/Model/Currency.lean", "af7f5feb54cbb293c0d6c1becb661c092986bc5f38245c463cf3a5e8e4d900b0", "af7f5feb54cbb293c0d6c1becb661c092986bc5f38245c463cf3a5e8e4d900b0", .verbatim⟩,
  ⟨"ConLeche/Model/DeclInd.lean", "ConLeche/Model/DeclInd.lean", "87aa0e2f6eefc06f582597d28c373ab0bdbc33c2d5647e1fe2b238dd004120c1", "87aa0e2f6eefc06f582597d28c373ab0bdbc33c2d5647e1fe2b238dd004120c1", .verbatim⟩,
  ⟨"ConLeche/Model/Denotes.lean", "ConLeche/Model/Denotes.lean", "d126aae5c78f1bb27ffa546de537148e10f4b9ba6b3b06885f947b15af164b96", "d126aae5c78f1bb27ffa546de537148e10f4b9ba6b3b06885f947b15af164b96", .verbatim⟩,
  ⟨"ConLeche/Model/DivMod.lean", "ConLeche/Model/DivMod.lean", "b7f8959f68019f52866c570e461f77e0b71971d4fb4edd93207a683ab82e1107", "b7f8959f68019f52866c570e461f77e0b71971d4fb4edd93207a683ab82e1107", .verbatim⟩,
  ⟨"ConLeche/Model/DivModCert.lean", "ConLeche/Model/DivModCert.lean", "2ca2f860363d900ed8362db10bb15b7f384f5c52ecddef3aba4d6b4b23fe5d63", "2ca2f860363d900ed8362db10bb15b7f384f5c52ecddef3aba4d6b4b23fe5d63", .verbatim⟩,
  ⟨"ConLeche/Model/EqTower.lean", "ConLeche/Model/EqTower.lean", "31859926f07185ef99822a24ab72c36a86cf6794c2fe4ba617a22b1567f06045", "31859926f07185ef99822a24ab72c36a86cf6794c2fe4ba617a22b1567f06045", .verbatim⟩,
  ⟨"ConLeche/Model/ErasePwInv.lean", "ConLeche/Model/ErasePwInv.lean", "eee1ffbfacfa1b99a5934c91732df6171076c617f18637bb4d2ba50740d2e9e0", "eee1ffbfacfa1b99a5934c91732df6171076c617f18637bb4d2ba50740d2e9e0", .verbatim⟩,
  ⟨"ConLeche/Model/Fold.lean", "ConLeche/Model/Fold.lean", "ce6a3384730396faea412b3fdeb0f2f99dbdade8774cdd6981a938abb696d484", "ce6a3384730396faea412b3fdeb0f2f99dbdade8774cdd6981a938abb696d484", .verbatim⟩,
  ⟨"ConLeche/Model/Harvest.lean", "ConLeche/Model/Harvest.lean", "bf7a439527c6784e96aa758e5ba0572e0a3d3f2ef9fabe491dacd97aa85fa803", "bf7a439527c6784e96aa758e5ba0572e0a3d3f2ef9fabe491dacd97aa85fa803", .verbatim⟩,
  ⟨"ConLeche/Model/IOLicense.lean", "ConLeche/Model/IOLicense.lean", "8b958cf40212d35f2254a8c2aae8861c681533653b0cb85bb01c2c349df22d7b", "8b958cf40212d35f2254a8c2aae8861c681533653b0cb85bb01c2c349df22d7b", .verbatim⟩,
  ⟨"ConLeche/Model/IndAnnotKit.lean", "ConLeche/Model/IndAnnotKit.lean", "6ec2754a62fc4d88bc371957f67f1986d1f9e75b3d36475d155a6565a3f8581b", "6ec2754a62fc4d88bc371957f67f1986d1f9e75b3d36475d155a6565a3f8581b", .verbatim⟩,
  ⟨"ConLeche/Model/IndAnnotMem.lean", "ConLeche/Model/IndAnnotMem.lean", "9e0464654bf3dd382b84b18b9ecca23f338da6fa746f66f91fc25e204585422a", "9e0464654bf3dd382b84b18b9ecca23f338da6fa746f66f91fc25e204585422a", .verbatim⟩,
  ⟨"ConLeche/Model/IndBottomNested.lean", "ConLeche/Model/IndBottomNested.lean", "4fa99d53305ed26f514ab8b17732876afb28bad887297604dff50c6b700f7aa8", "4fa99d53305ed26f514ab8b17732876afb28bad887297604dff50c6b700f7aa8", .verbatim⟩,
  ⟨"ConLeche/Model/IndBottomPlain.lean", "ConLeche/Model/IndBottomPlain.lean", "3b925a992f8f70c28fe6a98cabc5b1d7fb14aebb7b43a14dc162d97a89d3bde8", "3b925a992f8f70c28fe6a98cabc5b1d7fb14aebb7b43a14dc162d97a89d3bde8", .verbatim⟩,
  ⟨"ConLeche/Model/IndBottomProj.lean", "ConLeche/Model/IndBottomProj.lean", "970ef24ac75acdd03789b27d1ef4014fdd370386ef9f46ce85d3e34d1a110551", "970ef24ac75acdd03789b27d1ef4014fdd370386ef9f46ce85d3e34d1a110551", .verbatim⟩,
  ⟨"ConLeche/Model/IndCaps.lean", "ConLeche/Model/IndCaps.lean", "49c0da1fcecf6f68cf5b578d7ab778452a24ea58db9962b0af127fb34b0c1f50", "49c0da1fcecf6f68cf5b578d7ab778452a24ea58db9962b0af127fb34b0c1f50", .verbatim⟩,
  ⟨"ConLeche/Model/IndCons.lean", "ConLeche/Model/IndCons.lean", "86053208ac0344520fb4ad2ad1976ba6063fe6d541f72dbdc3510ff8a452899b", "86053208ac0344520fb4ad2ad1976ba6063fe6d541f72dbdc3510ff8a452899b", .verbatim⟩,
  ⟨"ConLeche/Model/IndCross.lean", "ConLeche/Model/IndCross.lean", "c278cdba4b18c55951ab1a5ec9ea875afcfabe98b820e6c8a5fb1c1cb5b5ce66", "c278cdba4b18c55951ab1a5ec9ea875afcfabe98b820e6c8a5fb1c1cb5b5ce66", .verbatim⟩,
  ⟨"ConLeche/Model/IndDomGrade.lean", "ConLeche/Model/IndDomGrade.lean", "ae66fc8750929e8c1f406eac8b63f8ff63ccbe1792c1df96e32c6c67384a8820", "ae66fc8750929e8c1f406eac8b63f8ff63ccbe1792c1df96e32c6c67384a8820", .verbatim⟩,
  ⟨"ConLeche/Model/IndEtaLaw.lean", "ConLeche/Model/IndEtaLaw.lean", "8218679b47c6e60e9404ae80b5cd180094cd75d9806f026d2a3a0d143e4e55c1", "8218679b47c6e60e9404ae80b5cd180094cd75d9806f026d2a3a0d143e4e55c1", .verbatim⟩,
  ⟨"ConLeche/Model/IndFieldGrade.lean", "ConLeche/Model/IndFieldGrade.lean", "febf413c5aa40e55162288d470ffa30ee2363fb0d30d5b7788c598b9f3b6b9a1", "febf413c5aa40e55162288d470ffa30ee2363fb0d30d5b7788c598b9f3b6b9a1", .verbatim⟩,
  ⟨"ConLeche/Model/IndFire.lean", "ConLeche/Model/IndFire.lean", "d72d4add39e09c9d3123d8a6b9269dcde4ebca5b6290b6f836de53a953e539a5", "d72d4add39e09c9d3123d8a6b9269dcde4ebca5b6290b6f836de53a953e539a5", .verbatim⟩,
  ⟨"ConLeche/Model/IndFrame.lean", "ConLeche/Model/IndFrame.lean", "85a60fdb6d2f7a323c7cf6f4564b154f5d10765f6e4572c8742f1118e5b943cf", "85a60fdb6d2f7a323c7cf6f4564b154f5d10765f6e4572c8742f1118e5b943cf", .verbatim⟩,
  ⟨"ConLeche/Model/IndGrade.lean", "ConLeche/Model/IndGrade.lean", "7298ab6e3bdd8750312e63098341e02c8ec01382f77da68a5844662f2f7df65b", "7298ab6e3bdd8750312e63098341e02c8ec01382f77da68a5844662f2f7df65b", .verbatim⟩,
  ⟨"ConLeche/Model/IndLamTower.lean", "ConLeche/Model/IndLamTower.lean", "19ce9d70c8f901f6bd80f6e408a123bed097ea4a6b84143efb1fa966a777e8ad", "19ce9d70c8f901f6bd80f6e408a123bed097ea4a6b84143efb1fa966a777e8ad", .verbatim⟩,
  ⟨"ConLeche/Model/IndMember.lean", "ConLeche/Model/IndMember.lean", "fc511632ccb6574d2a8ddea10a65a5bede3fcba647393b496b10d1f7b8900851", "fc511632ccb6574d2a8ddea10a65a5bede3fcba647393b496b10d1f7b8900851", .verbatim⟩,
  ⟨"ConLeche/Model/IndMembers.lean", "ConLeche/Model/IndMembers.lean", "d4218787e5230dbf5708a977c7cef5080ee27c72ae009669bbb15bbc3f760afb", "d4218787e5230dbf5708a977c7cef5080ee27c72ae009669bbb15bbc3f760afb", .verbatim⟩,
  ⟨"ConLeche/Model/IndNestedParam.lean", "ConLeche/Model/IndNestedParam.lean", "ad464417338f13a2ae936e80ecacaca5a2de091646a90ed62f55ffbeb35003b2", "ad464417338f13a2ae936e80ecacaca5a2de091646a90ed62f55ffbeb35003b2", .verbatim⟩,
  ⟨"ConLeche/Model/IndOpenRev.lean", "ConLeche/Model/IndOpenRev.lean", "d84c300b83436656b03410118845e3b185d5be232dcc24d8272bd70bf06fd2cf", "d84c300b83436656b03410118845e3b185d5be232dcc24d8272bd70bf06fd2cf", .verbatim⟩,
  ⟨"ConLeche/Model/IndOpenerGrade.lean", "ConLeche/Model/IndOpenerGrade.lean", "43d54021f803b4dbaf610fbb5cdedb1c5045e951f7140d18c8928e84b7fcd546", "43d54021f803b4dbaf610fbb5cdedb1c5045e951f7140d18c8928e84b7fcd546", .verbatim⟩,
  ⟨"ConLeche/Model/IndParamGrade.lean", "ConLeche/Model/IndParamGrade.lean", "09f8f37ccfb37f46892f34d50ed47522b917f0ab434b1f4dc1e01bb429e51185", "09f8f37ccfb37f46892f34d50ed47522b917f0ab434b1f4dc1e01bb429e51185", .verbatim⟩,
  ⟨"ConLeche/Model/IndPinGrade.lean", "ConLeche/Model/IndPinGrade.lean", "45ffe4f187db053ee0663157e1d6120d1bd9dc93f3736514b4e549d65510bab8", "45ffe4f187db053ee0663157e1d6120d1bd9dc93f3736514b4e549d65510bab8", .verbatim⟩,
  ⟨"ConLeche/Model/IndPinRow.lean", "ConLeche/Model/IndPinRow.lean", "66928c5a03347cfdf4f3a3cfb286d88d596eb2928b30eda6f2400fd64bad6a71", "66928c5a03347cfdf4f3a3cfb286d88d596eb2928b30eda6f2400fd64bad6a71", .verbatim⟩,
  ⟨"ConLeche/Model/IndPlainParam.lean", "ConLeche/Model/IndPlainParam.lean", "c4a1fbee14d4e1aa56b7b60e10f8488082095737826b185d68b5887198287ae6", "c4a1fbee14d4e1aa56b7b60e10f8488082095737826b185d68b5887198287ae6", .verbatim⟩,
  ⟨"ConLeche/Model/IndPoint.lean", "ConLeche/Model/IndPoint.lean", "8cedf437cdd6cfafadaae33e6b492242253e9036aad742d0ae863e74b568e25f", "8cedf437cdd6cfafadaae33e6b492242253e9036aad742d0ae863e74b568e25f", .verbatim⟩,
  ⟨"ConLeche/Model/IndPointKit.lean", "ConLeche/Model/IndPointKit.lean", "63ed5eda242822a447ce0d87d829aeb815cb6d522cbb3b206d5f9b747e3051f1", "63ed5eda242822a447ce0d87d829aeb815cb6d522cbb3b206d5f9b747e3051f1", .verbatim⟩,
  ⟨"ConLeche/Model/IndPrefixGrade.lean", "ConLeche/Model/IndPrefixGrade.lean", "8757f77a90bb5f7932946b2880b90bb3d1ae3d965481538c0754fe96f822c0b3", "8757f77a90bb5f7932946b2880b90bb3d1ae3d965481538c0754fe96f822c0b3", .verbatim⟩,
  ⟨"ConLeche/Model/IndProjCaps.lean", "ConLeche/Model/IndProjCaps.lean", "d29bc4a9ce00720901c81ccf435805370607eb7d9e6ab0a4b803ad12a16e6ffc", "d29bc4a9ce00720901c81ccf435805370607eb7d9e6ab0a4b803ad12a16e6ffc", .verbatim⟩,
  ⟨"ConLeche/Model/IndProjEta.lean", "ConLeche/Model/IndProjEta.lean", "3ff866c4170ccc91aa53f68af53c7a46710aa6affe7d265a0bd301b00c7182d5", "3ff866c4170ccc91aa53f68af53c7a46710aa6affe7d265a0bd301b00c7182d5", .verbatim⟩,
  ⟨"ConLeche/Model/IndProjKit.lean", "ConLeche/Model/IndProjKit.lean", "e9d3f6f35984ca5956520420e50d83f4c6dace6be5f4f8ba4da0858c88eef8a8", "e9d3f6f35984ca5956520420e50d83f4c6dace6be5f4f8ba4da0858c88eef8a8", .verbatim⟩,
  ⟨"ConLeche/Model/IndRecs.lean", "ConLeche/Model/IndRecs.lean", "1d78bf7b1ceac74be57cd850a355200566b5ac3e73bc6eb407e588561bfce9a1", "1d78bf7b1ceac74be57cd850a355200566b5ac3e73bc6eb407e588561bfce9a1", .verbatim⟩,
  ⟨"ConLeche/Model/IndReduct.lean", "ConLeche/Model/IndReduct.lean", "952bd5ae78676be2f68c4c62b57d08970f6fa189556691dfcc5e4071356901ff", "952bd5ae78676be2f68c4c62b57d08970f6fa189556691dfcc5e4071356901ff", .verbatim⟩,
  ⟨"ConLeche/Model/IndRename.lean", "ConLeche/Model/IndRename.lean", "9ec0fb808943d11beab0ce0a7bb58f58c716858570cd6ed394197ed0b91e832b", "9ec0fb808943d11beab0ce0a7bb58f58c716858570cd6ed394197ed0b91e832b", .verbatim⟩,
  ⟨"ConLeche/Model/IndRuns.lean", "ConLeche/Model/IndRuns.lean", "f1969872b53e644949d5658e0e4d76c29ff4cb9ffdc9001192d317bb6884a102", "f1969872b53e644949d5658e0e4d76c29ff4cb9ffdc9001192d317bb6884a102", .verbatim⟩,
  ⟨"ConLeche/Model/IndStageKit.lean", "ConLeche/Model/IndStageKit.lean", "9eddf840c0ec2048f2a815e95b9abeae09a51981ff02ac7bcbbae87ae445c526", "9eddf840c0ec2048f2a815e95b9abeae09a51981ff02ac7bcbbae87ae445c526", .verbatim⟩,
  ⟨"ConLeche/Model/IndSubst.lean", "ConLeche/Model/IndSubst.lean", "195e676febfe6257a7754fd9d3c2c1b009b5c393df0ae1f75b427ae49d292526", "195e676febfe6257a7754fd9d3c2c1b009b5c393df0ae1f75b427ae49d292526", .verbatim⟩,
  ⟨"ConLeche/Model/IndTele.lean", "ConLeche/Model/IndTele.lean", "0fbf988a6f997be32d1ccb26280f8c054ab423d29f79bae57bd6de8ff663fff3", "0fbf988a6f997be32d1ccb26280f8c054ab423d29f79bae57bd6de8ff663fff3", .verbatim⟩,
  ⟨"ConLeche/Model/IndTowerRead.lean", "ConLeche/Model/IndTowerRead.lean", "f097fa4821cc2aa2aa2a464dd49e5dcc071918a15599016e0e37991b0b76500f", "f097fa4821cc2aa2aa2a464dd49e5dcc071918a15599016e0e37991b0b76500f", .verbatim⟩,
  ⟨"ConLeche/Model/IndTransport.lean", "ConLeche/Model/IndTransport.lean", "132e5c52682e4d1f197dc8aedef734f90da092451a76e9a7b40b0383d6881284", "132e5c52682e4d1f197dc8aedef734f90da092451a76e9a7b40b0383d6881284", .verbatim⟩,
  ⟨"ConLeche/Model/IndUnitLaw.lean", "ConLeche/Model/IndUnitLaw.lean", "2203354bdd9e7a6e0c2b1269fe6ddbf16246275f71c5b27d9a3ef31c95e860a9", "2203354bdd9e7a6e0c2b1269fe6ddbf16246275f71c5b27d9a3ef31c95e860a9", .verbatim⟩,
  ⟨"ConLeche/Model/IndZipField.lean", "ConLeche/Model/IndZipField.lean", "4d798d25cf6a64866096bfd6b4888ae090727119c1019344a7f83773abdd7432", "4d798d25cf6a64866096bfd6b4888ae090727119c1019344a7f83773abdd7432", .verbatim⟩,
  ⟨"ConLeche/Model/IndZipper.lean", "ConLeche/Model/IndZipper.lean", "e16bdbec069ca8cf292656b0ea001f851525ebf9c17a6710918bc8cdb7a914c1", "e16bdbec069ca8cf292656b0ea001f851525ebf9c17a6710918bc8cdb7a914c1", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/DeclNative.lean", "ConLeche/Model/Inductives/DeclNative.lean", "3b4390f79bd232e493a865d44334c68052b9dbb1dfdb310fe2df86826a33e0e3", "3b4390f79bd232e493a865d44334c68052b9dbb1dfdb310fe2df86826a33e0e3", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/DeclStruct.lean", "ConLeche/Model/Inductives/DeclStruct.lean", "bd8ab51c1b68c966bd6893c2637bdd44615f2030d75b1864410e5f80055bf474", "bd8ab51c1b68c966bd6893c2637bdd44615f2030d75b1864410e5f80055bf474", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/DeclSum.lean", "ConLeche/Model/Inductives/DeclSum.lean", "8a793598c80400bcccf4133c10f850617ecc1484156c29a07bf16cf124229b7f", "8a793598c80400bcccf4133c10f850617ecc1484156c29a07bf16cf124229b7f", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixAssemblyKit.lean", "ConLeche/Model/Inductives/FixAssemblyKit.lean", "d3b169316df667e9acfa3df735d01a5854aea20953632a7f28db96137647b25c", "d3b169316df667e9acfa3df735d01a5854aea20953632a7f28db96137647b25c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixChainFacts.lean", "ConLeche/Model/Inductives/FixChainFacts.lean", "34f59e26f1dfeb3b1ef21b2a056c09ff1454b261cefd4cc5ea21dbcb4f100f71", "34f59e26f1dfeb3b1ef21b2a056c09ff1454b261cefd4cc5ea21dbcb4f100f71", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixChains.lean", "ConLeche/Model/Inductives/FixChains.lean", "ffaebd758e1a231293bbd218bd97656c42b98cca81e9253604edafb126b087d2", "ffaebd758e1a231293bbd218bd97656c42b98cca81e9253604edafb126b087d2", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorCross.lean", "ConLeche/Model/Inductives/FixCtorCross.lean", "bf92114562c5c52606402e184045e05a38cb89527dd7d008fcb4697bed81c610", "bf92114562c5c52606402e184045e05a38cb89527dd7d008fcb4697bed81c610", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorReads.lean", "ConLeche/Model/Inductives/FixCtorReads.lean", "18b1ffd0a0d13ab7fb6a74d9cb540673ff01ad8c8cb7dfff80d4c0ccf0516fcb", "18b1ffd0a0d13ab7fb6a74d9cb540673ff01ad8c8cb7dfff80d4c0ccf0516fcb", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixCtorsLoop.lean", "ConLeche/Model/Inductives/FixCtorsLoop.lean", "e0a0a96a8a9c6b9d14df1d7d011b300c50d0c3c0a197b283ae75331e3637c215", "e0a0a96a8a9c6b9d14df1d7d011b300c50d0c3c0a197b283ae75331e3637c215", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixData.lean", "ConLeche/Model/Inductives/FixData.lean", "8b147aae74f874efe509dcc11ed8f6d37750909f5e0dba00cff6c1bf94633372", "8b147aae74f874efe509dcc11ed8f6d37750909f5e0dba00cff6c1bf94633372", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixEntryLaw.lean", "ConLeche/Model/Inductives/FixEntryLaw.lean", "3f35447bc8091381a940567fd55a7c106d1762e253f853e95fa7026ebd097ee0", "3f35447bc8091381a940567fd55a7c106d1762e253f853e95fa7026ebd097ee0", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixIntro.lean", "ConLeche/Model/Inductives/FixIntro.lean", "1612df2a9ec2c599d602eb20a5116b1d29f053d1185b076b5625831cff8d114f", "1612df2a9ec2c599d602eb20a5116b1d29f053d1185b076b5625831cff8d114f", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixLeafOk.lean", "ConLeche/Model/Inductives/FixLeafOk.lean", "f2f951fd8de8c2cf91786193c6dd4f8576af6ac77f64639164b06ca117a437ed", "f2f951fd8de8c2cf91786193c6dd4f8576af6ac77f64639164b06ca117a437ed", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixNoBVar.lean", "ConLeche/Model/Inductives/FixNoBVar.lean", "6a0496d825cfec85e025bf5c94dc3d0add50c3999c30f219084e216a90c1443d", "6a0496d825cfec85e025bf5c94dc3d0add50c3999c30f219084e216a90c1443d", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRealChains.lean", "ConLeche/Model/Inductives/FixRealChains.lean", "43f0022f5f877dcc9b1b009d39811f7069679686a52ea0e5775d1a732816fc9c", "43f0022f5f877dcc9b1b009d39811f7069679686a52ea0e5775d1a732816fc9c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecData.lean", "ConLeche/Model/Inductives/FixRecData.lean", "6001059472406873238fa94371d15186e9692ce52aa899ced89bea69f4f5d4ef", "6001059472406873238fa94371d15186e9692ce52aa899ced89bea69f4f5d4ef", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecFrames.lean", "ConLeche/Model/Inductives/FixRecFrames.lean", "5bbaf042b29b35aeae8308904c6f7cfd7ebb0c6efbb3e217280008d23254594e", "5bbaf042b29b35aeae8308904c6f7cfd7ebb0c6efbb3e217280008d23254594e", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecKFrame.lean", "ConLeche/Model/Inductives/FixRecKFrame.lean", "edadfd90bb35caa546e814a49d2032e1d2a26d4402fd29cee3b1d5352a6a2275", "edadfd90bb35caa546e814a49d2032e1d2a26d4402fd29cee3b1d5352a6a2275", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecLaw.lean", "ConLeche/Model/Inductives/FixRecLaw.lean", "ced9a9fc4b250bd09c7d144bb0e766215f815b9818b5a37279b80c2be4465571", "ced9a9fc4b250bd09c7d144bb0e766215f815b9818b5a37279b80c2be4465571", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecLeaf.lean", "ConLeche/Model/Inductives/FixRecLeaf.lean", "0b884d43625d411e888e9dfe4fea37d6dbc942a4a6057f711466077f925aca1f", "0b884d43625d411e888e9dfe4fea37d6dbc942a4a6057f711466077f925aca1f", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecPre.lean", "ConLeche/Model/Inductives/FixRecPre.lean", "e0a91d01d96f52aebe19a25fb7821990100587acd435b8b4a4b62dba23f67d7e", "e0a91d01d96f52aebe19a25fb7821990100587acd435b8b4a4b62dba23f67d7e", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecRead.lean", "ConLeche/Model/Inductives/FixRecRead.lean", "2822b9a4c5f5225c9d992a01e9051b36e3472b8dd48182a7c8faaf2ccdf99224", "2822b9a4c5f5225c9d992a01e9051b36e3472b8dd48182a7c8faaf2ccdf99224", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRecReadDefs.lean", "ConLeche/Model/Inductives/FixRecReadDefs.lean", "d3c6db22721eb2810444c54d2a55f667818206e12f004d6e02042a1a861b39c5", "d3c6db22721eb2810444c54d2a55f667818206e12f004d6e02042a1a861b39c5", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleData.lean", "ConLeche/Model/Inductives/FixRuleData.lean", "fd5ff5a83662c75319ed00c43723f934d6dbeb4fb7c88a0353a9fb85e0fbcb54", "fd5ff5a83662c75319ed00c43723f934d6dbeb4fb7c88a0353a9fb85e0fbcb54", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleKit.lean", "ConLeche/Model/Inductives/FixRuleKit.lean", "f7a3b99e95223d00c217d22faf401e1bc0fa7c0395b5a29c8f40ffd59d2f41c4", "f7a3b99e95223d00c217d22faf401e1bc0fa7c0395b5a29c8f40ffd59d2f41c4", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixRuleOk.lean", "ConLeche/Model/Inductives/FixRuleOk.lean", "31db492fbfa40b7dd3148f9a0cc41a0c219c52ed8b2097e14e3eec6a9cec1827", "31db492fbfa40b7dd3148f9a0cc41a0c219c52ed8b2097e14e3eec6a9cec1827", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixShadow.lean", "ConLeche/Model/Inductives/FixShadow.lean", "be57d006087d80cbd9ba82f86391b524e296ab22261c7bb73a4088b9825daba0", "be57d006087d80cbd9ba82f86391b524e296ab22261c7bb73a4088b9825daba0", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixStageFormer.lean", "ConLeche/Model/Inductives/FixStageFormer.lean", "ed1db09bff63f723ed5649e5e070a74a3ae08aa2b2640b85313f81b227d5c3c5", "ed1db09bff63f723ed5649e5e070a74a3ae08aa2b2640b85313f81b227d5c3c5", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixStageRec.lean", "ConLeche/Model/Inductives/FixStageRec.lean", "cafe9f19cae0dfabd82f7c067c1aa9c111976ed22e5d8adfa3398f7213ae6f72", "cafe9f19cae0dfabd82f7c067c1aa9c111976ed22e5d8adfa3398f7213ae6f72", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixStageTable.lean", "ConLeche/Model/Inductives/FixStageTable.lean", "326fd9e8efd8f0290f23605ed2c7317764c65ad73056ec9e9cb9aca03d8a4ad8", "326fd9e8efd8f0290f23605ed2c7317764c65ad73056ec9e9cb9aca03d8a4ad8", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixTeleBound.lean", "ConLeche/Model/Inductives/FixTeleBound.lean", "8a79586948d129b36e7bacdf0b28473bb8ecd98cebac43d897f390ed25c743ab", "8a79586948d129b36e7bacdf0b28473bb8ecd98cebac43d897f390ed25c743ab", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixWitness.lean", "ConLeche/Model/Inductives/FixWitness.lean", "b93ddf0e2027ea7f4ab2cf60f2317451ee2b83a5087d038db70140010f7a0f91", "b93ddf0e2027ea7f4ab2cf60f2317451ee2b83a5087d038db70140010f7a0f91", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/FixZeroField.lean", "ConLeche/Model/Inductives/FixZeroField.lean", "a5a167bc14fb4586cfdbaf122b718c29505680cbfdf3c76d22fe50f7f32d42dd", "a5a167bc14fb4586cfdbaf122b718c29505680cbfdf3c76d22fe50f7f32d42dd", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructBits.lean", "ConLeche/Model/Inductives/StructBits.lean", "777b17489d082b5d52a32533f615b8f23b51fb796ba98651c42508d867810203", "777b17489d082b5d52a32533f615b8f23b51fb796ba98651c42508d867810203", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructBodyFrames.lean", "ConLeche/Model/Inductives/StructBodyFrames.lean", "8d061e66a4b9a3455df5ece71fee04e15e4cd67ac4fd68b0f9ccbbbd38ef1849", "8d061e66a4b9a3455df5ece71fee04e15e4cd67ac4fd68b0f9ccbbbd38ef1849", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructCaps.lean", "ConLeche/Model/Inductives/StructCaps.lean", "2389a893fb9b35cd6cf6f8a65ac48dae145248c10dac1835be6cb8dc9a510afb", "2389a893fb9b35cd6cf6f8a65ac48dae145248c10dac1835be6cb8dc9a510afb", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructCtorData.lean", "ConLeche/Model/Inductives/StructCtorData.lean", "1ed5465b8e9fa0bd71bbb74c8223ef716ef1c3037d47b5ac0dda279dfa979fdd", "1ed5465b8e9fa0bd71bbb74c8223ef716ef1c3037d47b5ac0dda279dfa979fdd", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructCtorFrames.lean", "ConLeche/Model/Inductives/StructCtorFrames.lean", "492795cb4b47a8c075a2de3852a4d803f29464c67765891638630b3630588f2e", "492795cb4b47a8c075a2de3852a4d803f29464c67765891638630b3630588f2e", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructData.lean", "ConLeche/Model/Inductives/StructData.lean", "cb6d8c3cb3c9c5cc10767f4257d7d6c3ac18cb38ee3eaa11ad1517399439789a", "cb6d8c3cb3c9c5cc10767f4257d7d6c3ac18cb38ee3eaa11ad1517399439789a", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryFree.lean", "ConLeche/Model/Inductives/StructEntryFree.lean", "07ddcec55697a5a127181cadbec2839b0fa2ee239baf21b8ba6528c44060cb1b", "07ddcec55697a5a127181cadbec2839b0fa2ee239baf21b8ba6528c44060cb1b", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryKit.lean", "ConLeche/Model/Inductives/StructEntryKit.lean", "c51fd31666a57050b752892ef983e8bffb17817e67a17b121771e7456e4ee09e", "c51fd31666a57050b752892ef983e8bffb17817e67a17b121771e7456e4ee09e", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructEntryKit2.lean", "ConLeche/Model/Inductives/StructEntryKit2.lean", "629ed74ecfe0497c92e8196c9347f4f5ba67e0b64b1a3bcecc1733767b1ecaff", "629ed74ecfe0497c92e8196c9347f4f5ba67e0b64b1a3bcecc1733767b1ecaff", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructFrame.lean", "ConLeche/Model/Inductives/StructFrame.lean", "22d1d0f9bfa63ac1f90939c50cc635724604543ff042aa0f2befb878b6725b2c", "22d1d0f9bfa63ac1f90939c50cc635724604543ff042aa0f2befb878b6725b2c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructFrames.lean", "ConLeche/Model/Inductives/StructFrames.lean", "49466ea295c66f08ac964821d0f5b89a21262cc31e0b5968a6f731749db12d4b", "49466ea295c66f08ac964821d0f5b89a21262cc31e0b5968a6f731749db12d4b", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructIntro.lean", "ConLeche/Model/Inductives/StructIntro.lean", "fada441b211e13d401491e0f4a7a83b5190079f6289f47858fb6139764db2e8c", "fada441b211e13d401491e0f4a7a83b5190079f6289f47858fb6139764db2e8c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructLaws.lean", "ConLeche/Model/Inductives/StructLaws.lean", "8b80cc1d871ee16731db80bf8bc6370212d2bb0395830b558632825a09f38402", "8b80cc1d871ee16731db80bf8bc6370212d2bb0395830b558632825a09f38402", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRead.lean", "ConLeche/Model/Inductives/StructRead.lean", "209a18b8c54bdcc477488ea526f2bcf0d694b013c7b48e7cbb57ab3b288e6f84", "209a18b8c54bdcc477488ea526f2bcf0d694b013c7b48e7cbb57ab3b288e6f84", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecFrames.lean", "ConLeche/Model/Inductives/StructRecFrames.lean", "05dc7f919a8ba3c63100599c742a31c7e6a282dd5927792676c660a4a9db532c", "05dc7f919a8ba3c63100599c742a31c7e6a282dd5927792676c660a4a9db532c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecKit2.lean", "ConLeche/Model/Inductives/StructRecKit2.lean", "eeb56cc1abd507b59f698a34e313b35ba6976605fa272ff669f3824cb1dc1c08", "eeb56cc1abd507b59f698a34e313b35ba6976605fa272ff669f3824cb1dc1c08", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecLam.lean", "ConLeche/Model/Inductives/StructRecLam.lean", "32b8dedcd161fc66b19ade8414048b75630102fee6cc963082dc74557bd93604", "32b8dedcd161fc66b19ade8414048b75630102fee6cc963082dc74557bd93604", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecLawKit.lean", "ConLeche/Model/Inductives/StructRecLawKit.lean", "6def26a2ad245269cce6fe1aca61bc9168c9c66f7ced4ee44a14870cd4fdc1f3", "6def26a2ad245269cce6fe1aca61bc9168c9c66f7ced4ee44a14870cd4fdc1f3", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecRead.lean", "ConLeche/Model/Inductives/StructRecRead.lean", "00bf9838724ddc65d60f5337872d809ee80dde2c05b3e372579f671997ed78e6", "00bf9838724ddc65d60f5337872d809ee80dde2c05b3e372579f671997ed78e6", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRecSpine.lean", "ConLeche/Model/Inductives/StructRecSpine.lean", "cc6e2e44311fe42e842091609fc4fc4a8a8d54ee9ac3264b0cf07d4f234b310f", "cc6e2e44311fe42e842091609fc4fc4a8a8d54ee9ac3264b0cf07d4f234b310f", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructRows.lean", "ConLeche/Model/Inductives/StructRows.lean", "bb058bb51a48ab5596b9aa3b969a01d38b367da995f9d45e727d5c43ceb0980f", "bb058bb51a48ab5596b9aa3b969a01d38b367da995f9d45e727d5c43ceb0980f", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructStageCtor.lean", "ConLeche/Model/Inductives/StructStageCtor.lean", "76c9251bc00a83916a08b8bfddfae15b83e3b47d11ac920886d7d7537b924bfb", "76c9251bc00a83916a08b8bfddfae15b83e3b47d11ac920886d7d7537b924bfb", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructStageFormer.lean", "ConLeche/Model/Inductives/StructStageFormer.lean", "940ef4d9445907ff76398c237de1c22143cb74d5bfc300c3fd1c94d92d20e82b", "940ef4d9445907ff76398c237de1c22143cb74d5bfc300c3fd1c94d92d20e82b", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructStageTable.lean", "ConLeche/Model/Inductives/StructStageTable.lean", "59d2b899af15fc8684d8dee3040562f833cdde30a23ee00498621b0b1c07d4dd", "59d2b899af15fc8684d8dee3040562f833cdde30a23ee00498621b0b1c07d4dd", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/StructTele.lean", "ConLeche/Model/Inductives/StructTele.lean", "2b01f4b2b1d9368fa02dbfe1e4a6d7d62b0bfe45ed427f1ff8c78b29a49f50ce", "2b01f4b2b1d9368fa02dbfe1e4a6d7d62b0bfe45ed427f1ff8c78b29a49f50ce", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumData.lean", "ConLeche/Model/Inductives/SumData.lean", "5d1b775c885bd19151b5cc973378eff0868583a46eba70703f17e2f7a7f12a0c", "5d1b775c885bd19151b5cc973378eff0868583a46eba70703f17e2f7a7f12a0c", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumIntro.lean", "ConLeche/Model/Inductives/SumIntro.lean", "170b78e7658026e74f6d38dceb19eca59c78ce32fbf17ae502ead47cd236987b", "170b78e7658026e74f6d38dceb19eca59c78ce32fbf17ae502ead47cd236987b", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumRecData.lean", "ConLeche/Model/Inductives/SumRecData.lean", "50a869c1a9b1eb290477e69d098c7624e19a1c4498b6091ed14dd7bc83c04b58", "50a869c1a9b1eb290477e69d098c7624e19a1c4498b6091ed14dd7bc83c04b58", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumRecFrames.lean", "ConLeche/Model/Inductives/SumRecFrames.lean", "bee9bf582ac0175761701d63553c37147e4f915a272d00fc1678957558f8619d", "bee9bf582ac0175761701d63553c37147e4f915a272d00fc1678957558f8619d", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumRecRead.lean", "ConLeche/Model/Inductives/SumRecRead.lean", "175413516667c9aeb3ad1711bcb98561dcb79357a1f4a1d374f832aad7211251", "175413516667c9aeb3ad1711bcb98561dcb79357a1f4a1d374f832aad7211251", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumStageCtor.lean", "ConLeche/Model/Inductives/SumStageCtor.lean", "2343c1bc9cdefa006c989b5ed31d9d9c8e19cd05fcc93cdb5caeca965efd2ddb", "2343c1bc9cdefa006c989b5ed31d9d9c8e19cd05fcc93cdb5caeca965efd2ddb", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumStageFormer.lean", "ConLeche/Model/Inductives/SumStageFormer.lean", "b3d0be5cee16b560d0ae08746c8c118c93cb81ebb7c0a1674ad6966938993d6d", "b3d0be5cee16b560d0ae08746c8c118c93cb81ebb7c0a1674ad6966938993d6d", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/SumStageRec.lean", "ConLeche/Model/Inductives/SumStageRec.lean", "41415eb4e185461e89eeb551b0054aeee13c4d4a2379855071598a6800fe0a05", "41415eb4e185461e89eeb551b0054aeee13c4d4a2379855071598a6800fe0a05", .verbatim⟩,
  ⟨"ConLeche/Model/Inductives/TowerCons.lean", "ConLeche/Model/Inductives/TowerCons.lean", "e241df5da452eab84338b3ebd2ec778f1d9fd992acf64b48411f220af35d4570", "e241df5da452eab84338b3ebd2ec778f1d9fd992acf64b48411f220af35d4570", .verbatim⟩,
  ⟨"ConLeche/Model/Install.lean", "ConLeche/Model/Install.lean", "dfe1bc8e1f14a53069fa8352e29c597ca08368ff4632010e81b918dc263b1ac0", "dfe1bc8e1f14a53069fa8352e29c597ca08368ff4632010e81b918dc263b1ac0", .verbatim⟩,
  ⟨"ConLeche/Model/IotaRuleNested.lean", "ConLeche/Model/IotaRuleNested.lean", "87eb689d3f0157f3c86f9613b1e5c2c1f77a2ba20ba5494354e7bb8280a66b9b", "87eb689d3f0157f3c86f9613b1e5c2c1f77a2ba20ba5494354e7bb8280a66b9b", .verbatim⟩,
  ⟨"ConLeche/Model/IotaRulePlain.lean", "ConLeche/Model/IotaRulePlain.lean", "a86243f77caaaa24156d44b05e020bdc7da20c37809718d2f1df48b4f8995efd", "a86243f77caaaa24156d44b05e020bdc7da20c37809718d2f1df48b4f8995efd", .verbatim⟩,
  ⟨"ConLeche/Model/Levels.lean", "ConLeche/Model/Levels.lean", "9ee30b0e11a6b940f2edb9b120095b747255ac03f53ad22e115df4e4c86e6fa3", "9ee30b0e11a6b940f2edb9b120095b747255ac03f53ad22e115df4e4c86e6fa3", .verbatim⟩,
  ⟨"ConLeche/Model/NatEqs.lean", "ConLeche/Model/NatEqs.lean", "889cea85622b941b548e58d93b9add12fe502f6a0f6e6ce2027d1557d4bce35b", "889cea85622b941b548e58d93b9add12fe502f6a0f6e6ce2027d1557d4bce35b", .verbatim⟩,
  ⟨"ConLeche/Model/NatSem.lean", "ConLeche/Model/NatSem.lean", "393cc6ff639246f6168bed2771f81e236456b842ad802d69e0177d6a4a8450b7", "393cc6ff639246f6168bed2771f81e236456b842ad802d69e0177d6a4a8450b7", .verbatim⟩,
  ⟨"ConLeche/Model/NatStep.lean", "ConLeche/Model/NatStep.lean", "8d019bfdb02cd6ba43c72c5cb6762f438797205410bab2dbafb742b9e56bb474", "8d019bfdb02cd6ba43c72c5cb6762f438797205410bab2dbafb742b9e56bb474", .verbatim⟩,
  ⟨"ConLeche/Model/NatWf.lean", "ConLeche/Model/NatWf.lean", "0883b4f53add26aea3f304307e1e86fad24cb2cc3239172f583479cc02af1015", "0883b4f53add26aea3f304307e1e86fad24cb2cc3239172f583479cc02af1015", .verbatim⟩,
  ⟨"ConLeche/Model/ProjCons.lean", "ConLeche/Model/ProjCons.lean", "8b64987eda361e1ee2e5580ac2beb60f21b5bb90dae7bd05df3c7bcb61ed491f", "8b64987eda361e1ee2e5580ac2beb60f21b5bb90dae7bd05df3c7bcb61ed491f", .verbatim⟩,
  ⟨"ConLeche/Model/ProjInstall.lean", "ConLeche/Model/ProjInstall.lean", "71424b796950957cc256f8a5bb09d1c5914cff0df82967d56a86b88b465bc948", "71424b796950957cc256f8a5bb09d1c5914cff0df82967d56a86b88b465bc948", .verbatim⟩,
  ⟨"ConLeche/Model/ProjRename.lean", "ConLeche/Model/ProjRename.lean", "cb34e671232134111fe2de40cb51bba60859ec88c8bc5bbf3b9805403428e901", "cb34e671232134111fe2de40cb51bba60859ec88c8bc5bbf3b9805403428e901", .verbatim⟩,
  ⟨"ConLeche/Model/RecRulesCons.lean", "ConLeche/Model/RecRulesCons.lean", "9425ab673d5722fb0fc1f404a3d3ea371d00b76f865803deea5d8b7b5c1f7dd4", "9425ab673d5722fb0fc1f404a3d3ea371d00b76f865803deea5d8b7b5c1f7dd4", .verbatim⟩,
  ⟨"ConLeche/Model/ReduceOps.lean", "ConLeche/Model/ReduceOps.lean", "0260fb9316b3e9619179b11c98431403183d958ee0ee674ec54eeafbaf78f4e1", "0260fb9316b3e9619179b11c98431403183d958ee0ee674ec54eeafbaf78f4e1", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/CertsSound.lean", "ConLeche/Model/Rules/CertsSound.lean", "ddbd8922e004a55f80781542ac5caba113f94526dfed8ef9e8b75a3ecf2bd410", "ddbd8922e004a55f80781542ac5caba113f94526dfed8ef9e8b75a3ecf2bd410", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/DefEqSound.lean", "ConLeche/Model/Rules/DefEqSound.lean", "8e9d7d4b414e60318fe679189446c1fa1dc091e8874fb342d4ad257a137fabd1", "8e9d7d4b414e60318fe679189446c1fa1dc091e8874fb342d4ad257a137fabd1", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/DefEqSoundKit.lean", "ConLeche/Model/Rules/DefEqSoundKit.lean", "4bcc4d17a6b452401539acce7f46f40ecaae0a3efc2e3b03084948a1792b1e5e", "4bcc4d17a6b452401539acce7f46f40ecaae0a3efc2e3b03084948a1792b1e5e", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/InferSound.lean", "ConLeche/Model/Rules/InferSound.lean", "0a36573a39e7260bb996ae9d164c858d33194bf2a5cdf5faf550326a3d007e93", "0a36573a39e7260bb996ae9d164c858d33194bf2a5cdf5faf550326a3d007e93", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/InferSoundKit.lean", "ConLeche/Model/Rules/InferSoundKit.lean", "21c282e35606fd4264ed27fc3b7db276bc443517731c03607cd82948dd13939e", "21c282e35606fd4264ed27fc3b7db276bc443517731c03607cd82948dd13939e", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/Inputs.lean", "ConLeche/Model/Rules/Inputs.lean", "10851c48facc90e6377c8d8b6c1f15171be2c22aec6ed21273dc0d6f73ee870e", "10851c48facc90e6377c8d8b6c1f15171be2c22aec6ed21273dc0d6f73ee870e", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/IotaSound.lean", "ConLeche/Model/Rules/IotaSound.lean", "f10c7a66b947298f467a644ec529d3401d1b97ff0e056bd2f6a80005d6d64020", "f10c7a66b947298f467a644ec529d3401d1b97ff0e056bd2f6a80005d6d64020", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/IotaSoundKit.lean", "ConLeche/Model/Rules/IotaSoundKit.lean", "539334fddc086977616eedbb6db7350500551c2e4790d14f4c354730ef6ab628", "539334fddc086977616eedbb6db7350500551c2e4790d14f4c354730ef6ab628", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/Motive.lean", "ConLeche/Model/Rules/Motive.lean", "a6bc7d723a240996a9b5927bc9a7f2d05d2a011dd2635b3f5e0f5a02aca8df0c", "a6bc7d723a240996a9b5927bc9a7f2d05d2a011dd2635b3f5e0f5a02aca8df0c", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/Recompose.lean", "ConLeche/Model/Rules/Recompose.lean", "33c24cc06951cd0548f4cdcfac9a45d266600dfcb0afee7584372b1848bdb813", "33c24cc06951cd0548f4cdcfac9a45d266600dfcb0afee7584372b1848bdb813", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/RedSound.lean", "ConLeche/Model/Rules/RedSound.lean", "68090a7a6a34a69d1d40a1531b82dd15809ab8cce53a15fe84eb3067c673b4c5", "68090a7a6a34a69d1d40a1531b82dd15809ab8cce53a15fe84eb3067c673b4c5", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/RedSoundKit.lean", "ConLeche/Model/Rules/RedSoundKit.lean", "ffa515d6020d92500cdbe383c478d5e247e65df23e5ba28947c0cd6c770626e2", "ffa515d6020d92500cdbe383c478d5e247e65df23e5ba28947c0cd6c770626e2", .verbatim⟩,
  ⟨"ConLeche/Model/Rules/Sound.lean", "ConLeche/Model/Rules/Sound.lean", "6ca1a6c0464e8e316bdf37edabf2a2e2b76cab8f93681ef096c38841bd3c2971", "6ca1a6c0464e8e316bdf37edabf2a2e2b76cab8f93681ef096c38841bd3c2971", .verbatim⟩,
  ⟨"ConLeche/Model/Swap.lean", "ConLeche/Model/Swap.lean", "e3b20faea9f82bca1830475d82312e73c5621a328efd08512ca81c5e3f7f9f26", "e3b20faea9f82bca1830475d82312e73c5621a328efd08512ca81c5e3f7f9f26", .verbatim⟩,
  ⟨"ConLeche/Model/Tiers.lean", "ConLeche/Model/Tiers.lean", "4dce97b3e81b30e36effebd9bf9b524b8936ced9e22274c1129f974be8a8ea57", "4dce97b3e81b30e36effebd9bf9b524b8936ced9e22274c1129f974be8a8ea57", .verbatim⟩,
  ⟨"ConLeche/Model/WellDenotedTransport.lean", "ConLeche/Model/WellDenotedTransport.lean", "37079d34a070ef64ccaed9c2e8fd207b0f81b3978db381adfe2fc1e83ab5d13b", "37079d34a070ef64ccaed9c2e8fd207b0f81b3978db381adfe2fc1e83ab5d13b", .verbatim⟩,
  ⟨"ConLeche/PinGen/Certs.lean", "ConLeche/PinGen/Certs.lean", "adf2595f9a23b7d788954010328928d2f75222e4c2ddb2a03b04c2147877036a", "adf2595f9a23b7d788954010328928d2f75222e4c2ddb2a03b04c2147877036a", .verbatim⟩,
  ⟨"ConLeche/Rules/Derived.lean", "ConLeche/Rules/Derived.lean", "2c480a8bb117eba4abf524a044e12952878039c14e867e85a0b44c425941f32e", "2c480a8bb117eba4abf524a044e12952878039c14e867e85a0b44c425941f32e", .verbatim⟩,
  ⟨"ConLeche/Rules/Rel.lean", "ConLeche/Rules/Rel.lean", "8e2fe3fb65e6a074e4e22c1e20eabb6f2768e6f075984861f0150cf30a1341d9", "8e2fe3fb65e6a074e4e22c1e20eabb6f2768e6f075984861f0150cf30a1341d9", .verbatim⟩,
  ⟨"ConLeche/Semantics/BasisOk.lean", "ConLeche/Semantics/BasisOk.lean", "012930d25dbe7a86ce667f4386f3989928ab2a0f03fe1b081dd022e95a5af510", "012930d25dbe7a86ce667f4386f3989928ab2a0f03fe1b081dd022e95a5af510", .verbatim⟩,
  ⟨"ConLeche/Semantics/BasisRules.lean", "ConLeche/Semantics/BasisRules.lean", "dc24dcd858dceab1e6f0124d3ee54ac299114d3db5d3ec22adf6ea6eebd74a86", "dc24dcd858dceab1e6f0124d3ee54ac299114d3db5d3ec22adf6ea6eebd74a86", .verbatim⟩,
  ⟨"ConLeche/Semantics/BasisType.lean", "ConLeche/Semantics/BasisType.lean", "7e8ab71a559fc5bc8583947ca229ddbd56b76bf2ecf2710a8c095c44b1ad0e85", "7e8ab71a559fc5bc8583947ca229ddbd56b76bf2ecf2710a8c095c44b1ad0e85", .verbatim⟩,
  ⟨"ConLeche/Semantics/Bridge/Decl.lean", "ConLeche/Semantics/Bridge/Decl.lean", "87fed3e245e834399a2f7155415a082364c117bb6bd497b2e6652e2841857410", "87fed3e245e834399a2f7155415a082364c117bb6bd497b2e6652e2841857410", .verbatim⟩,
  ⟨"ConLeche/Semantics/Bridge/DeclIndRun.lean", "ConLeche/Semantics/Bridge/DeclIndRun.lean", "b4c61f9a13cc68d21a55724eac11e973fe0deb16ddc265bc2c5866bab5905dae", "b4c61f9a13cc68d21a55724eac11e973fe0deb16ddc265bc2c5866bab5905dae", .verbatim⟩,
  ⟨"ConLeche/Semantics/Bridge/DeclRun.lean", "ConLeche/Semantics/Bridge/DeclRun.lean", "69a922afc11e17927b22f833d2bf66d1d0f2dfb0ed85afe01f5878927423878e", "69a922afc11e17927b22f833d2bf66d1d0f2dfb0ed85afe01f5878927423878e", .verbatim⟩,
  ⟨"ConLeche/Semantics/Bridge/Sound.lean", "ConLeche/Semantics/Bridge/Sound.lean", "a51dfb23358bf44d1e530505d1653f505f0b8552660a9c35aa43af01f1e25c01", "a51dfb23358bf44d1e530505d1653f505f0b8552660a9c35aa43af01f1e25c01", .verbatim⟩,
  ⟨"ConLeche/Semantics/Canon.lean", "ConLeche/Semantics/Canon.lean", "521380daaf64f694f8a041a30c597faa8898ca7e09e1714d121260fa715f8326", "521380daaf64f694f8a041a30c597faa8898ca7e09e1714d121260fa715f8326", .verbatim⟩,
  ⟨"ConLeche/Semantics/ConstsBound.lean", "ConLeche/Semantics/ConstsBound.lean", "1cae59f1fa649726955feda15cafd441c4dc091eb846fb0c1751f21d82a053f6", "1cae59f1fa649726955feda15cafd441c4dc091eb846fb0c1751f21d82a053f6", .verbatim⟩,
  ⟨"ConLeche/Semantics/Decl.lean", "ConLeche/Semantics/Decl.lean", "45695912197f1df39ec5f3c271ebfe433d8e9b4f95501f107db99de277e3e77f", "45695912197f1df39ec5f3c271ebfe433d8e9b4f95501f107db99de277e3e77f", .verbatim⟩,
  ⟨"ConLeche/Semantics/DeclEta.lean", "ConLeche/Semantics/DeclEta.lean", "0c2110ed4d0846dc2efa9df1f234a84a548b343c4191c41c8ad13957a86b50f9", "0c2110ed4d0846dc2efa9df1f234a84a548b343c4191c41c8ad13957a86b50f9", .verbatim⟩,
  ⟨"ConLeche/Semantics/DeclIndRun.lean", "ConLeche/Semantics/DeclIndRun.lean", "f85a307a07b2c7a5b4b0aee9299b681afbb3f678440afd9ba34f7abe4d364551", "f85a307a07b2c7a5b4b0aee9299b681afbb3f678440afd9ba34f7abe4d364551", .verbatim⟩,
  ⟨"ConLeche/Semantics/DeclRun.lean", "ConLeche/Semantics/DeclRun.lean", "1ee91d5cc423b0d6c34d203eea37682e11776c2dce43efa6eeed21918697b3f0", "1ee91d5cc423b0d6c34d203eea37682e11776c2dce43efa6eeed21918697b3f0", .verbatim⟩,
  ⟨"ConLeche/Semantics/DefEqList.lean", "ConLeche/Semantics/DefEqList.lean", "1695a82ba7e7d5f9fdc4307e99ccda67f01ab9fb39517df7dff62d2424601892", "1695a82ba7e7d5f9fdc4307e99ccda67f01ab9fb39517df7dff62d2424601892", .verbatim⟩,
  ⟨"ConLeche/Semantics/DefEqStep.lean", "ConLeche/Semantics/DefEqStep.lean", "1c995e1ded980b84c05c954f8f39b27e585726519bb7ece470de09475268f73b", "1c995e1ded980b84c05c954f8f39b27e585726519bb7ece470de09475268f73b", .verbatim⟩,
  ⟨"ConLeche/Semantics/DenoteClosed.lean", "ConLeche/Semantics/DenoteClosed.lean", "2d6b87eeb32a8aba907b1c865accd007d73b27953f9c40f4f0bd2fd059e41588", "2d6b87eeb32a8aba907b1c865accd007d73b27953f9c40f4f0bd2fd059e41588", .verbatim⟩,
  ⟨"ConLeche/Semantics/DivModEval.lean", "ConLeche/Semantics/DivModEval.lean", "9d28c9424a8bfb2e7a237444b2df74f620eb4e35d187a37cf38e4e43f8ab233a", "9d28c9424a8bfb2e7a237444b2df74f620eb4e35d187a37cf38e4e43f8ab233a", .verbatim⟩,
  ⟨"ConLeche/Semantics/EnvFacts.lean", "ConLeche/Semantics/EnvFacts.lean", "8e3de0230aa6a44791ee4b4f70d2ec30481a46279794449fe3d0c4e78ac09f8b", "8e3de0230aa6a44791ee4b4f70d2ec30481a46279794449fe3d0c4e78ac09f8b", .verbatim⟩,
  ⟨"ConLeche/Semantics/EnvFactsCons.lean", "ConLeche/Semantics/EnvFactsCons.lean", "b442ae915818a918a6ea3835edee8a9725b96fe40d11c819417120455440ab43", "b442ae915818a918a6ea3835edee8a9725b96fe40d11c819417120455440ab43", .verbatim⟩,
  ⟨"ConLeche/Semantics/EqTower.lean", "ConLeche/Semantics/EqTower.lean", "553f77caeb6230dccd71f8058c88943add296d0a2cad07f55b712b81bf731927", "553f77caeb6230dccd71f8058c88943add296d0a2cad07f55b712b81bf731927", .verbatim⟩,
  ⟨"ConLeche/Semantics/EraseInv.lean", "ConLeche/Semantics/EraseInv.lean", "0eead13ca371f90b6fd9e9bd6f7f2c26fb27b007f051316b164a6cccabda6923", "0eead13ca371f90b6fd9e9bd6f7f2c26fb27b007f051316b164a6cccabda6923", .verbatim⟩,
  ⟨"ConLeche/Semantics/Frame.lean", "ConLeche/Semantics/Frame.lean", "49f5e85775b8affe4e9754e12bc30e581e3193e8f1787e6c9d91ac463cc2eb7d", "49f5e85775b8affe4e9754e12bc30e581e3193e8f1787e6c9d91ac463cc2eb7d", .verbatim⟩,
  ⟨"ConLeche/Semantics/Hoist.lean", "ConLeche/Semantics/Hoist.lean", "a3972db87b7f64d409d7fb121b8ce290f6568b99d55218e2e6f0fb2486a6ca9a", "a3972db87b7f64d409d7fb121b8ce290f6568b99d55218e2e6f0fb2486a6ca9a", .verbatim⟩,
  ⟨"ConLeche/Semantics/IndBlockFacts.lean", "ConLeche/Semantics/IndBlockFacts.lean", "9b00fe50549b297b169045fbc5a9f21042b07f8985b0ea0add15b53f1ebcae80", "9b00fe50549b297b169045fbc5a9f21042b07f8985b0ea0add15b53f1ebcae80", .verbatim⟩,
  ⟨"ConLeche/Semantics/IndBlockRun.lean", "ConLeche/Semantics/IndBlockRun.lean", "aecf908b0025be1febc417db7c92a61c073d7b313effc257cc4aef16576479b9", "aecf908b0025be1febc417db7c92a61c073d7b313effc257cc4aef16576479b9", .verbatim⟩,
  ⟨"ConLeche/Semantics/IndRecsCore.lean", "ConLeche/Semantics/IndRecsCore.lean", "2d4e80032cf4a2b2bbfe266a2d0c18cffdcf6dba8c32def9c90fe2d037221ab4", "2d4e80032cf4a2b2bbfe266a2d0c18cffdcf6dba8c32def9c90fe2d037221ab4", .verbatim⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclNative.lean", "ConLeche/Semantics/Inductives/DeclNative.lean", "eb1171230b628cd19479c1741d9cabbfde6c1c924ce33060e7ad75b4593139ce", "eb1171230b628cd19479c1741d9cabbfde6c1c924ce33060e7ad75b4593139ce", .verbatim⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclStructEta.lean", "ConLeche/Semantics/Inductives/DeclStructEta.lean", "fcfd962ff9c3e0ad1690f59f1ff744cde5bb41b6f1865888a7fea760a226af3c", "fcfd962ff9c3e0ad1690f59f1ff744cde5bb41b6f1865888a7fea760a226af3c", .verbatim⟩,
  ⟨"ConLeche/Semantics/Inductives/DeclSumEta.lean", "ConLeche/Semantics/Inductives/DeclSumEta.lean", "7973a1d6fbf0ca597f90a1f931d6be015a067197ee7b2435e306a523352cfd22", "7973a1d6fbf0ca597f90a1f931d6be015a067197ee7b2435e306a523352cfd22", .verbatim⟩,
  ⟨"ConLeche/Semantics/Install.lean", "ConLeche/Semantics/Install.lean", "6698dcca50e4ca49bfb11240ad06e125561ee5aa4926fd9db70a0500f7fcb6d3", "6698dcca50e4ca49bfb11240ad06e125561ee5aa4926fd9db70a0500f7fcb6d3", .verbatim⟩,
  ⟨"ConLeche/Semantics/Interp.lean", "ConLeche/Semantics/Interp.lean", "4dbeae234bb16963229cef391c05f4b3ddfb85e85eb22cd8c41c81b35e95083f", "4dbeae234bb16963229cef391c05f4b3ddfb85e85eb22cd8c41c81b35e95083f", .verbatim⟩,
  ⟨"ConLeche/Semantics/Kit.lean", "ConLeche/Semantics/Kit.lean", "c45d247ea013411919e6027fbb56c1439e491db4cf6ed0f41d60eb430302fe44", "c45d247ea013411919e6027fbb56c1439e491db4cf6ed0f41d60eb430302fe44", .verbatim⟩,
  ⟨"ConLeche/Semantics/LitParams.lean", "ConLeche/Semantics/LitParams.lean", "951c08efa8634825711ef4b31eb87d1dc940a46847c5adb01334d127ac18c5fb", "951c08efa8634825711ef4b31eb87d1dc940a46847c5adb01334d127ac18c5fb", .verbatim⟩,
  ⟨"ConLeche/Semantics/LitStep.lean", "ConLeche/Semantics/LitStep.lean", "6e343ff73a4efdb8c6cae1a441f6c8c077b37103369bb7f52c781f829d83be77", "6e343ff73a4efdb8c6cae1a441f6c8c077b37103369bb7f52c781f829d83be77", .verbatim⟩,
  ⟨"ConLeche/Semantics/NatFrag.lean", "ConLeche/Semantics/NatFrag.lean", "489b4e54f178cbf46a4bd9ef553df01a04b752a01bd8ff27ed7d3047926250ee", "489b4e54f178cbf46a4bd9ef553df01a04b752a01bd8ff27ed7d3047926250ee", .verbatim⟩,
  ⟨"ConLeche/Semantics/NoBVar.lean", "ConLeche/Semantics/NoBVar.lean", "7e48ede47f9ee5063f2bfc1f47d6e8a10a6dfdcb4f3c051412a62f26c51b8c8d", "7e48ede47f9ee5063f2bfc1f47d6e8a10a6dfdcb4f3c051412a62f26c51b8c8d", .verbatim⟩,
  ⟨"ConLeche/Semantics/ProjFnFacts.lean", "ConLeche/Semantics/ProjFnFacts.lean", "299222b80a583f408f792b89fdcc467af2423613d7164fc0f723c2776a1eb4e7", "299222b80a583f408f792b89fdcc467af2423613d7164fc0f723c2776a1eb4e7", .verbatim⟩,
  ⟨"ConLeche/Semantics/ProjPhase.lean", "ConLeche/Semantics/ProjPhase.lean", "8dfa48429adcd7b8569e3f8959d6239d2c8647bbe2ca5251a0966060c33a4c50", "8dfa48429adcd7b8569e3f8959d6239d2c8647bbe2ca5251a0966060c33a4c50", .verbatim⟩,
  ⟨"ConLeche/Semantics/Sat.lean", "ConLeche/Semantics/Sat.lean", "6e8233142c7642e27df388bb47de99b67c1398abf4fdf828cebac2ad1c3d6ed0", "6e8233142c7642e27df388bb47de99b67c1398abf4fdf828cebac2ad1c3d6ed0", .verbatim⟩,
  ⟨"ConLeche/Semantics/Skeleton.lean", "ConLeche/Semantics/Skeleton.lean", "5ee75be1db55d20bfc1f7e4a5a96fd4a1e4a36921d55564385ad28086de97158", "5ee75be1db55d20bfc1f7e4a5a96fd4a1e4a36921d55564385ad28086de97158", .verbatim⟩,
  ⟨"ConLeche/Semantics/Syntax.lean", "ConLeche/Semantics/Syntax.lean", "27d076ab2c00f78fdf14053c6b556005baaefd99617a5ab41291ac64e50afbdf", "27d076ab2c00f78fdf14053c6b556005baaefd99617a5ab41291ac64e50afbdf", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixCaseI.lean", "ConLeche/Semantics/Tower/FixCaseI.lean", "23dfe356300642ead68f9ee5997bd72246cb1917a7e06cb994bc2c2c67e41192", "23dfe356300642ead68f9ee5997bd72246cb1917a7e06cb994bc2c2c67e41192", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixElemI.lean", "ConLeche/Semantics/Tower/FixElemI.lean", "252dafa16cdebe0539beb6f772b21ff6411c07dc4a887bda138eaade3feb869a", "252dafa16cdebe0539beb6f772b21ff6411c07dc4a887bda138eaade3feb869a", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixFamI.lean", "ConLeche/Semantics/Tower/FixFamI.lean", "f05d85427465f0b8d62da4f4f099858ca99b82537ac9a2f069a7ade2c64cecdb", "f05d85427465f0b8d62da4f4f099858ca99b82537ac9a2f069a7ade2c64cecdb", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixIhI.lean", "ConLeche/Semantics/Tower/FixIhI.lean", "4035fb0f46670e5d3edb80a1225a8247f8a20eb1bd73b604912ab250b0d3a15d", "4035fb0f46670e5d3edb80a1225a8247f8a20eb1bd73b604912ab250b0d3a15d", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixLeafI.lean", "ConLeche/Semantics/Tower/FixLeafI.lean", "bb6ccf0e200e62e10c49ff25652198886b57e0adae2e0b77c1d59f06330897f7", "bb6ccf0e200e62e10c49ff25652198886b57e0adae2e0b77c1d59f06330897f7", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixRecCoreI.lean", "ConLeche/Semantics/Tower/FixRecCoreI.lean", "fae671af06ed6003433326eeca99c9079905d5bd49b2d12ed821a1e193862187", "fae671af06ed6003433326eeca99c9079905d5bd49b2d12ed821a1e193862187", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixRecI.lean", "ConLeche/Semantics/Tower/FixRecI.lean", "8a7ea4fa6927ef43e2e54f8586448bc3cdd2a94dd703d8a2da69e0d8986c0c82", "8a7ea4fa6927ef43e2e54f8586448bc3cdd2a94dd703d8a2da69e0d8986c0c82", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixSquashI.lean", "ConLeche/Semantics/Tower/FixSquashI.lean", "101c7d7b6842d3adf1938e15ef25b5eca4e1156d8aacf1fcab2f698d50c86c95", "101c7d7b6842d3adf1938e15ef25b5eca4e1156d8aacf1fcab2f698d50c86c95", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/FixWire.lean", "ConLeche/Semantics/Tower/FixWire.lean", "cc12d5b9ca87faf0a9fc9c3d1a3b13c133894dd924f784b42e1bae44c0ed627f", "cc12d5b9ca87faf0a9fc9c3d1a3b13c133894dd924f784b42e1bae44c0ed627f", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/IdxEq.lean", "ConLeche/Semantics/Tower/IdxEq.lean", "c2372388c5fda43c4041a90ad7c4025dc4701576afca0bc217789096d449b61b", "c2372388c5fda43c4041a90ad7c4025dc4701576afca0bc217789096d449b61b", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/IhSpell.lean", "ConLeche/Semantics/Tower/IhSpell.lean", "1dc017c51707b9e9893d3e7ccd867319fc6a7f42bc03e22bee01c9f59202293b", "1dc017c51707b9e9893d3e7ccd867319fc6a7f42bc03e22bee01c9f59202293b", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumCase.lean", "ConLeche/Semantics/Tower/SumCase.lean", "2d61358fecd1a925009af4546069d6d437fa16a19ccd3c27ac3ecf26a556ec25", "2d61358fecd1a925009af4546069d6d437fa16a19ccd3c27ac3ecf26a556ec25", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumLeaf.lean", "ConLeche/Semantics/Tower/SumLeaf.lean", "1fa812c76f28d6724a1110bb9a9d97ffe374acec8b5377f57541334efad38ce7", "1fa812c76f28d6724a1110bb9a9d97ffe374acec8b5377f57541334efad38ce7", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumMk.lean", "ConLeche/Semantics/Tower/SumMk.lean", "e4ccb6dfdd9c99485005677857a67fce3abce3261e7cdba75a13bbb185cfc78b", "e4ccb6dfdd9c99485005677857a67fce3abce3261e7cdba75a13bbb185cfc78b", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumRec.lean", "ConLeche/Semantics/Tower/SumRec.lean", "b1aa1f4a4df003cce9f3b0d5edff859cf499f407b085eaa9ea71df350169c7c0", "b1aa1f4a4df003cce9f3b0d5edff859cf499f407b085eaa9ea71df350169c7c0", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumRecCase.lean", "ConLeche/Semantics/Tower/SumRecCase.lean", "bb8af169e1d83c0b991199deccae8b85d9ed55271e513c33984a632e049d25d2", "bb8af169e1d83c0b991199deccae8b85d9ed55271e513c33984a632e049d25d2", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/SumWire.lean", "ConLeche/Semantics/Tower/SumWire.lean", "bb83d1fe0b182ba32a93db7aef8a399565a248cb753ae5baf7f1d59e69689bba", "bb83d1fe0b182ba32a93db7aef8a399565a248cb753ae5baf7f1d59e69689bba", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/TowerIntro.lean", "ConLeche/Semantics/Tower/TowerIntro.lean", "81f2debcaa601e3fe1fcb485e44c14090b33a14022f97c05bde43b764944db9a", "81f2debcaa601e3fe1fcb485e44c14090b33a14022f97c05bde43b764944db9a", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/TowerLeaf.lean", "ConLeche/Semantics/Tower/TowerLeaf.lean", "b2df2a78bc81cfcd87bf76c9afc12c34c2ba4b0cf0d1436725dc2183ba20c7a9", "b2df2a78bc81cfcd87bf76c9afc12c34c2ba4b0cf0d1436725dc2183ba20c7a9", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/TowerMk.lean", "ConLeche/Semantics/Tower/TowerMk.lean", "99897d47cfe78b408cff5fc59b398ad43399a80c499aa4fb57436268a99a0d64", "99897d47cfe78b408cff5fc59b398ad43399a80c499aa4fb57436268a99a0d64", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/TowerRec.lean", "ConLeche/Semantics/Tower/TowerRec.lean", "617f9a9e0125408707a8f052a5fec7299ad106e5309ad1e6883700a9af3f34a5", "617f9a9e0125408707a8f052a5fec7299ad106e5309ad1e6883700a9af3f34a5", .verbatim⟩,
  ⟨"ConLeche/Semantics/Tower/TowerWire.lean", "ConLeche/Semantics/Tower/TowerWire.lean", "30b105dd85a6ce0601cb82cab8227fa311665944f5edee656ec3d43420499de4", "30b105dd85a6ce0601cb82cab8227fa311665944f5edee656ec3d43420499de4", .verbatim⟩,
  ⟨"ConLeche/Semantics/Univ.lean", "ConLeche/Semantics/Univ.lean", "898f7e15881abb126d6d7533f59990b4659ce1328aa7e2a1bad5c49c9fb7c6cd", "898f7e15881abb126d6d7533f59990b4659ce1328aa7e2a1bad5c49c9fb7c6cd", .verbatim⟩,
  ⟨"ConLeche/Semantics/WellDenoted.lean", "ConLeche/Semantics/WellDenoted.lean", "25fcb0c72f7c8044542f364b5508702419b0ab693a2c9b4a30d05ab759fce2d4", "25fcb0c72f7c8044542f364b5508702419b0ab693a2c9b4a30d05ab759fce2d4", .verbatim⟩,
  ⟨"ConLeche/SetModel/Container.lean", "ConLeche/SetModel/Container.lean", "47b7bbab4764309ad1a11d7e6a3d2061c2968928367e2285e2a7e549bf7e6c0c", "47b7bbab4764309ad1a11d7e6a3d2061c2968928367e2285e2a7e549bf7e6c0c", .verbatim⟩,
  ⟨"ConLeche/SetModel/Iter.lean", "ConLeche/SetModel/Iter.lean", "0688fa56fad4dcac618589cd9bafc2860c43b95978dc6dcf6c3e292cafc4b149", "0688fa56fad4dcac618589cd9bafc2860c43b95978dc6dcf6c3e292cafc4b149", .verbatim⟩,
  ⟨"ConLeche/SetModel/Ops.lean", "ConLeche/SetModel/Ops.lean", "b19d965f92d1e281afd40a7ee4b2edd1a324b9bdf6d8f26425944dbafe987a11", "b19d965f92d1e281afd40a7ee4b2edd1a324b9bdf6d8f26425944dbafe987a11", .verbatim⟩,
  ⟨"ConLeche/SetModel/RecGraph.lean", "ConLeche/SetModel/RecGraph.lean", "66de7b97c640cec3987f89c31ae19c4daa27b6da53ba6943767e0078802f1faf", "66de7b97c640cec3987f89c31ae19c4daa27b6da53ba6943767e0078802f1faf", .verbatim⟩,
  ⟨"ConLeche/SetModel/TaggedSum.lean", "ConLeche/SetModel/TaggedSum.lean", "eb64def578bf85bc2b197b83648749996ebcd243be573752f617a5f91f3332d8", "eb64def578bf85bc2b197b83648749996ebcd243be573752f617a5f91f3332d8", .verbatim⟩,
  ⟨"ConLeche/SetModel/TowerMono.lean", "ConLeche/SetModel/TowerMono.lean", "e11d20f7f66a4ee6e9fcf07c5dd06450a0ee3bc7dda091a7f829672a192d3e7c", "e11d20f7f66a4ee6e9fcf07c5dd06450a0ee3bc7dda091a7f829672a192d3e7c", .verbatim⟩,
  ⟨"ConLeche/SetModel/TupleTower.lean", "ConLeche/SetModel/TupleTower.lean", "143b965d29faae965c16288021ba1cf401c3f10e76550386ddb81d9ca1f5cbee", "143b965d29faae965c16288021ba1cf401c3f10e76550386ddb81d9ca1f5cbee", .verbatim⟩,
  ⟨"ConLeche/SetModel/Value.lean", "ConLeche/SetModel/Value.lean", "280afd97ddbec2330285a17b269c2171c9675c781e0dab2ffcb4b38383bac385", "280afd97ddbec2330285a17b269c2171c9675c781e0dab2ffcb4b38383bac385", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Basic.lean", "ConLeche/SetTheory/Basic.lean", "0ae5172c477170a25c67626ecd2f29286976b0cc0ea77bfef69abad0f7414813", "0ae5172c477170a25c67626ecd2f29286976b0cc0ea77bfef69abad0f7414813", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Core.lean", "ConLeche/SetTheory/Core.lean", "52f54c7f8664a0d00ba04083d428ff81c2b89e7e68fbd6e24ffb349ef441f19a", "52f54c7f8664a0d00ba04083d428ff81c2b89e7e68fbd6e24ffb349ef441f19a", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Choice.lean", "ConLeche/SetTheory/Derive/Choice.lean", "a8404566f4d831874e044dcfba6865b750fda3c9427e13c3d2b68d7ac45d5b48", "a8404566f4d831874e044dcfba6865b750fda3c9427e13c3d2b68d7ac45d5b48", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Empty.lean", "ConLeche/SetTheory/Derive/Empty.lean", "259b3b365926256fbe8281a7066be601e419c3e492452b62086e0fd44e1a3f16", "259b3b365926256fbe8281a7066be601e419c3e492452b62086e0fd44e1a3f16", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Graphs.lean", "ConLeche/SetTheory/Derive/Graphs.lean", "f61433765add5a733b38e95e38e217273f526a5e710b7109f24eb0f83f70faaf", "f61433765add5a733b38e95e38e217273f526a5e710b7109f24eb0f83f70faaf", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Lfp.lean", "ConLeche/SetTheory/Derive/Lfp.lean", "d6c1a824ee0b358f4007c2d297c4e29011c95914c2241d402f5bf27da333614f", "d6c1a824ee0b358f4007c2d297c4e29011c95914c2241d402f5bf27da333614f", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/LfpFam.lean", "ConLeche/SetTheory/Derive/LfpFam.lean", "18fa2c12b37d9786b9a1961ed526e7d411869d93cfa241ebbdf2910d4418ac97", "18fa2c12b37d9786b9a1961ed526e7d411869d93cfa241ebbdf2910d4418ac97", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Natrec.lean", "ConLeche/SetTheory/Derive/Natrec.lean", "a37e6cf282ae06bb3bba7a26a2d692ac7ba310b3beb2571c84bb34ad9d0ae304", "a37e6cf282ae06bb3bba7a26a2d692ac7ba310b3beb2571c84bb34ad9d0ae304", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Omega.lean", "ConLeche/SetTheory/Derive/Omega.lean", "c0b20ecd0cc88a74ff6091e5a88506269b587bbc6f1919f72cc63083d2f7e55a", "c0b20ecd0cc88a74ff6091e5a88506269b587bbc6f1919f72cc63083d2f7e55a", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Pair.lean", "ConLeche/SetTheory/Derive/Pair.lean", "851f954187fcc05ba2f43a6b81112df27c91e34f7de54352eaf461380fee1bd7", "851f954187fcc05ba2f43a6b81112df27c91e34f7de54352eaf461380fee1bd7", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Pt.lean", "ConLeche/SetTheory/Derive/Pt.lean", "93f9ed86375f7af7a004f3ef2612ce8c9d8c6626ce73dbf6c3d6702f95f67eae", "93f9ed86375f7af7a004f3ef2612ce8c9d8c6626ce73dbf6c3d6702f95f67eae", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Quot.lean", "ConLeche/SetTheory/Derive/Quot.lean", "cadc387495c563d796ba4ca45cc0125cbe8ff5168d81bc47b364bd6776c3898b", "cadc387495c563d796ba4ca45cc0125cbe8ff5168d81bc47b364bd6776c3898b", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Sep.lean", "ConLeche/SetTheory/Derive/Sep.lean", "a6a452a34028ff2e194987de8fc5bc8f847ff8950f962b5d33c6c6ee5045a52e", "a6a452a34028ff2e194987de8fc5bc8f847ff8950f962b5d33c6c6ee5045a52e", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Sigma.lean", "ConLeche/SetTheory/Derive/Sigma.lean", "1a844ecb6709ae0ccefd43a4eb8d6da92b3753033e882ce74cfbd27c6890545f", "1a844ecb6709ae0ccefd43a4eb8d6da92b3753033e882ce74cfbd27c6890545f", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Univ.lean", "ConLeche/SetTheory/Derive/Univ.lean", "e1084f7c82d9c0d144281491ceb05b015001d1215947d0d687e4dc07497ff911", "e1084f7c82d9c0d144281491ceb05b015001d1215947d0d687e4dc07497ff911", .verbatim⟩,
  ⟨"ConLeche/SetTheory/Derive/Universe.lean", "ConLeche/SetTheory/Derive/Universe.lean", "57a24b4144088ac14dabdb9b6f88c49cf251a0659f8d4c073aad6682baeb099d", "57a24b4144088ac14dabdb9b6f88c49cf251a0659f8d4c073aad6682baeb099d", .verbatim⟩,
  ⟨"ConLeche/Term/Const.lean", "ConLeche/Term/Const.lean", "2c5bcc4177d1c6a5e57a84e7d6d73dfe9d3da04b434e227d4755301b50aaa002", "2c5bcc4177d1c6a5e57a84e7d6d73dfe9d3da04b434e227d4755301b50aaa002", .verbatim⟩,
  ⟨"ConLeche/Term/Subst.lean", "ConLeche/Term/Subst.lean", "cec1d84d0f921f107911a3eef0033bcb7f40c4c3c4c911e8ce5f198f27d74370", "cec1d84d0f921f107911a3eef0033bcb7f40c4c3c4c911e8ce5f198f27d74370", .verbatim⟩,
  ⟨"ConLeche/Term/Syntax.lean", "ConLeche/Term/Syntax.lean", "e51c4f3e3861bbd0bf3bcbd59e462f48cc8e28a10b9eaa8a385ab2418cd45ed8", "e51c4f3e3861bbd0bf3bcbd59e462f48cc8e28a10b9eaa8a385ab2418cd45ed8", .verbatim⟩,
  ⟨"ConLeche/Verify/Abstract.lean", "ConLeche/Verify/Abstract.lean", "f30d2d6e81fb6cde405ed7522ff1d74e445b3f2ea845cb94ce1dd9aa58f9580e", "f30d2d6e81fb6cde405ed7522ff1d74e445b3f2ea845cb94ce1dd9aa58f9580e", .verbatim⟩,
  ⟨"ConLeche/Verify/AbstractRange.lean", "ConLeche/Verify/AbstractRange.lean", "1769afd8e72e71fa99e5238319aa2754743aa90b75d75a00ebc84a56d3de129f", "1769afd8e72e71fa99e5238319aa2754743aa90b75d75a00ebc84a56d3de129f", .verbatim⟩,
  ⟨"ConLeche/Verify/BetaGate.lean", "ConLeche/Verify/BetaGate.lean", "c81f01740d0885cb0416af5414b32af08186bf9369423fed4cb62d5101b7cdb9", "c81f01740d0885cb0416af5414b32af08186bf9369423fed4cb62d5101b7cdb9", .verbatim⟩,
  ⟨"ConLeche/Verify/BetaSpine.lean", "ConLeche/Verify/BetaSpine.lean", "db18c9315e079d8f553be858a53a4ad46a8db385a0747aa67fa0c9d8f76f46b4", "db18c9315e079d8f553be858a53a4ad46a8db385a0747aa67fa0c9d8f76f46b4", .verbatim⟩,
  ⟨"ConLeche/Verify/BinderLoop.lean", "ConLeche/Verify/BinderLoop.lean", "abc19f63ca5f3b49b97d0e3cce6e0d8e0e3eb3fc5793d2355bc9a40ca7d4689b", "abc19f63ca5f3b49b97d0e3cce6e0d8e0e3eb3fc5793d2355bc9a40ca7d4689b", .verbatim⟩,
  ⟨"ConLeche/Verify/BridgeDecl.lean", "ConLeche/Verify/BridgeDecl.lean", "8ebc6e4e5b4e8f380bda28509aee56f88151b9ed7966728be4692559befa158d", "8ebc6e4e5b4e8f380bda28509aee56f88151b9ed7966728be4692559befa158d", .verbatim⟩,
  ⟨"ConLeche/Verify/BridgeWfImp.lean", "ConLeche/Verify/BridgeWfImp.lean", "c7ac837bfc361db411c3cceea198674666245855b4dcad14dde4dd882d78c6a6", "c7ac837bfc361db411c3cceea198674666245855b4dcad14dde4dd882d78c6a6", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/AgreeFloor.lean", "ConLeche/Verify/Cached/AgreeFloor.lean", "ac637eb894591c2c1d9b7cb8ceccab89b92776d69c999b47f638cafaeb324d99", "fc70e7f2bbeeecb3a96f20d89b18e27cfcb12eb483f2b7dbb8c30b49a4b5b431", .adapted "4.34.0 fix: +1 line `import all Init.LetFun` after `import ConLeche.Verify.EnvBound` (letFun body not exposed in 4.34.0); port header added"⟩,
  ⟨"ConLeche/Verify/Cached/BinderLoopC.lean", "ConLeche/Verify/Cached/BinderLoopC.lean", "7d325928eb869176d448f8708ade4faf54be7c39a9e47b9072f6bd61eb7a791d", "7d325928eb869176d448f8708ade4faf54be7c39a9e47b9072f6bd61eb7a791d", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeC.lean", "ConLeche/Verify/Cached/BridgeC.lean", "71e505aefecd755e3ce2c446bf841f280ee2fb5ff4437f11dcac284a7118c0f0", "71e505aefecd755e3ce2c446bf841f280ee2fb5ff4437f11dcac284a7118c0f0", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS1.lean", "ConLeche/Verify/Cached/BridgeCS1.lean", "0144764ede94cd97f254db9f94bcb07dd12aeb08ec8f708fe892e61332f2bf78", "0144764ede94cd97f254db9f94bcb07dd12aeb08ec8f708fe892e61332f2bf78", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS2.lean", "ConLeche/Verify/Cached/BridgeCS2.lean", "f9a16dbd9e9c2c70fc31f8d16dd9f446d82673b941e3c1a4656a60fcea6be440", "f9a16dbd9e9c2c70fc31f8d16dd9f446d82673b941e3c1a4656a60fcea6be440", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS3.lean", "ConLeche/Verify/Cached/BridgeCS3.lean", "9d8f94b77b55a7b43f24a97743c90e585167313fe53d1816410ea0fda5dcd211", "9d8f94b77b55a7b43f24a97743c90e585167313fe53d1816410ea0fda5dcd211", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCS4.lean", "ConLeche/Verify/Cached/BridgeCS4.lean", "c435b1f968ffc261a27d9d4540630683d55ea08905aff7d8b8042e494f531705", "c435b1f968ffc261a27d9d4540630683d55ea08905aff7d8b8042e494f531705", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/BridgeCSDecl.lean", "ConLeche/Verify/Cached/BridgeCSDecl.lean", "5d843a4f271d754afcd217003df137a4e4f9642507f7a44690b04512f8bc3f84", "5d843a4f271d754afcd217003df137a4e4f9642507f7a44690b04512f8bc3f84", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC1.lean", "ConLeche/Verify/Cached/DiscC1.lean", "6d986949138cf13b9a704674ca0e6bd9a51528bfe023fb63307de8c023548984", "6d986949138cf13b9a704674ca0e6bd9a51528bfe023fb63307de8c023548984", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC2.lean", "ConLeche/Verify/Cached/DiscC2.lean", "ccb50ac29947c53bc4d0fea9b3fd463e82bf9237d02f1d13a83ea112e191faec", "ccb50ac29947c53bc4d0fea9b3fd463e82bf9237d02f1d13a83ea112e191faec", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC3.lean", "ConLeche/Verify/Cached/DiscC3.lean", "33336612439bf6f53503ca0ca08993cdba916aefd2eec7ddf15b00fe16a9efe5", "33336612439bf6f53503ca0ca08993cdba916aefd2eec7ddf15b00fe16a9efe5", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC4.lean", "ConLeche/Verify/Cached/DiscC4.lean", "cfaec051ea9cf47640a5a77f6133969456201befad464fa9458a567d9c3f21ee", "cfaec051ea9cf47640a5a77f6133969456201befad464fa9458a567d9c3f21ee", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC5.lean", "ConLeche/Verify/Cached/DiscC5.lean", "a123e647a381985059d5e71a0113da22c22c9d37f9aba8dbd7fa41d5b7643b86", "a123e647a381985059d5e71a0113da22c22c9d37f9aba8dbd7fa41d5b7643b86", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/DiscC6.lean", "ConLeche/Verify/Cached/DiscC6.lean", "211cda73bb1f83a76b6d7ad834c78834525ba76cd44264e8e5956b0e67e1a8a1", "211cda73bb1f83a76b6d7ad834c78834525ba76cd44264e8e5956b0e67e1a8a1", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/Erase.lean", "ConLeche/Verify/Cached/Erase.lean", "c2ce9dbe1b7b2cbaf010221661f9d8a79789ff93437c89744bee596d0b0af9d0", "c2ce9dbe1b7b2cbaf010221661f9d8a79789ff93437c89744bee596d0b0af9d0", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/GuardsC.lean", "ConLeche/Verify/Cached/GuardsC.lean", "ef59f6b72bdc7b5d6c8cf164cbd11b46eb2f52bd5510d4540da6da8e9d3639e5", "ef59f6b72bdc7b5d6c8cf164cbd11b46eb2f52bd5510d4540da6da8e9d3639e5", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/InstalledC.lean", "ConLeche/Verify/Cached/InstalledC.lean", "9e1b2a7f0830ac4c45c779c850367a2956a39713f2d2f781651b09aac5a17d48", "9e1b2a7f0830ac4c45c779c850367a2956a39713f2d2f781651b09aac5a17d48", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/KnotC.lean", "ConLeche/Verify/Cached/KnotC.lean", "97c186e24480141e23eb0b109172333485105b7bce3d69b54ba18771820f0e7a", "97c186e24480141e23eb0b109172333485105b7bce3d69b54ba18771820f0e7a", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/KnotCongr.lean", "ConLeche/Verify/Cached/KnotCongr.lean", "4e013683f0eb1e674819646ccd66d4265c49ae43d3c429831030368d8d3fd2e2", "4e013683f0eb1e674819646ccd66d4265c49ae43d3c429831030368d8d3fd2e2", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/MainC.lean", "ConLeche/Verify/Cached/MainC.lean", "caa81163d62937350c069ba6c9a4c48bd76f2533296122b16e1f5e520aeb32f4", "caa81163d62937350c069ba6c9a4c48bd76f2533296122b16e1f5e520aeb32f4", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/OpsC.lean", "ConLeche/Verify/Cached/OpsC.lean", "113b042315f6beaa325cd32544ed9090d178ca170bf862503c2ea54d5965c767", "113b042315f6beaa325cd32544ed9090d178ca170bf862503c2ea54d5965c767", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/PushChain.lean", "ConLeche/Verify/Cached/PushChain.lean", "6c33408f9e74de5ad4c19fc6bc060242d6b67d3f5338a1ab198a77b9c9216563", "398839cf0d04b37a0fa65371addcc97d6dfac01119bdf5f7596751ffae23e30e", .adapted "4.34.0 fix: +1 line `import all Init.LetFun` after `import ConLeche.Verify.CheckerF` (letFun body not exposed in 4.34.0); port header added"⟩,
  ⟨"ConLeche/Verify/Cached/SimC.lean", "ConLeche/Verify/Cached/SimC.lean", "5821419432b77b53564e8002b1000dc8101f3cdb2c386769af92184ecccb1d5c", "5821419432b77b53564e8002b1000dc8101f3cdb2c386769af92184ecccb1d5c", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/SimCEff.lean", "ConLeche/Verify/Cached/SimCEff.lean", "d3a27826824654c59f9e100d5ef0f44a8262c33165b2da44a84beae215a0772e", "d3a27826824654c59f9e100d5ef0f44a8262c33165b2da44a84beae215a0772e", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/SimCS.lean", "ConLeche/Verify/Cached/SimCS.lean", "499103a0f7f4515a44201589c1676bffa5d7ca56271666592a785a74632f1ca2", "499103a0f7f4515a44201589c1676bffa5d7ca56271666592a785a74632f1ca2", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/StreamThm.lean", "ConLeche/Verify/Cached/StreamThm.lean", "61868dbdcd6ecff73af74102c0472f1be6558a1afb3c8a048b9d3c6ce92d14fa", "61868dbdcd6ecff73af74102c0472f1be6558a1afb3c8a048b9d3c6ce92d14fa", .verbatim⟩,
  ⟨"ConLeche/Verify/Cached/WalkersC.lean", "ConLeche/Verify/Cached/WalkersC.lean", "fdf625ce57e07f01bd5825532ac1fd04d14b93bc6ff752daa506ca694d2587de", "fdf625ce57e07f01bd5825532ac1fd04d14b93bc6ff752daa506ca694d2587de", .verbatim⟩,
  ⟨"ConLeche/Verify/CheckerF.lean", "ConLeche/Verify/CheckerF.lean", "5d7e591e110d50ec45cd6f049ee2582c6f1df837c27d3a9a25726a153f32121b", "5d7e591e110d50ec45cd6f049ee2582c6f1df837c27d3a9a25726a153f32121b", .verbatim⟩,
  ⟨"ConLeche/Verify/CheckerSplit.lean", "ConLeche/Verify/CheckerSplit.lean", "e9e3f93477e26da05eefb7f1a33da0090918b1ddf1e378b1911df590520a3fa3", "e9e3f93477e26da05eefb7f1a33da0090918b1ddf1e378b1911df590520a3fa3", .verbatim⟩,
  ⟨"ConLeche/Verify/Close.lean", "ConLeche/Verify/Close.lean", "05fd1fe8546c8f1dfb60fc84594d35f2bf35932147cbfe85d6aa9434fb523af6", "05fd1fe8546c8f1dfb60fc84594d35f2bf35932147cbfe85d6aa9434fb523af6", .verbatim⟩,
  ⟨"ConLeche/Verify/Deep.lean", "ConLeche/Verify/Deep.lean", "bec52c5a8cddc78724563d4195f4a82edad74f591bbf15aa28493a6444acf9e8", "bec52c5a8cddc78724563d4195f4a82edad74f591bbf15aa28493a6444acf9e8", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote.lean", "ConLeche/Verify/Denote.lean", "9fce328e9015917a387ff9e981dcf653ca0f669d886acd9c70e2bfd9ed0e27b8", "9fce328e9015917a387ff9e981dcf653ca0f669d886acd9c70e2bfd9ed0e27b8", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/EnvExt.lean", "ConLeche/Verify/Denote/EnvExt.lean", "3f18b4653c3fb218c20bfc2ec681bb37c3eb0fcbdc28c2160b7ab2b075b4a3fc", "3f18b4653c3fb218c20bfc2ec681bb37c3eb0fcbdc28c2160b7ab2b075b4a3fc", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/IndFrame.lean", "ConLeche/Verify/Denote/IndFrame.lean", "51f49c63af4504b9dde1f25d38569cdf3810b3dd374b71fbc7504322bc2c0843", "51f49c63af4504b9dde1f25d38569cdf3810b3dd374b71fbc7504322bc2c0843", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Inst.lean", "ConLeche/Verify/Denote/Inst.lean", "2822637a806dbb869cf2806fb2408571b84b18b6bdf5bbb24dee7ab442ff83ad", "2822637a806dbb869cf2806fb2408571b84b18b6bdf5bbb24dee7ab442ff83ad", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Install.lean", "ConLeche/Verify/Denote/Install.lean", "4f1f29dd9b41a74bd455682343f8f2ae6fa2f9741783e7c17210dd4966c9a15b", "4f1f29dd9b41a74bd455682343f8f2ae6fa2f9741783e7c17210dd4966c9a15b", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Levels.lean", "ConLeche/Verify/Denote/Levels.lean", "ab071a2d022a80125b88b2443dad32c760da9bf4817745c592d5016c30f192ac", "ab071a2d022a80125b88b2443dad32c760da9bf4817745c592d5016c30f192ac", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/OpenRevDenote.lean", "ConLeche/Verify/Denote/OpenRevDenote.lean", "63767e971ee796e073ffcb3f2b0a3d4324e022b78f42d81d50b7a9b5b9964863", "63767e971ee796e073ffcb3f2b0a3d4324e022b78f42d81d50b7a9b5b9964863", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/OpenVars.lean", "ConLeche/Verify/Denote/OpenVars.lean", "ec17ae785476357a2911c1fc40429873177614a98bc1349635df4c187c645281", "ec17ae785476357a2911c1fc40429873177614a98bc1349635df4c187c645281", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Pinned.lean", "ConLeche/Verify/Denote/Pinned.lean", "62bf088209ac45cbd32f31fe13f86d2114dc3b59d93f3da84fffa2655d89a113", "62bf088209ac45cbd32f31fe13f86d2114dc3b59d93f3da84fffa2655d89a113", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Rename.lean", "ConLeche/Verify/Denote/Rename.lean", "ac914838976ff0ed079b3d13399edb3356971c24a3b543604da5af9e0c5e6684", "ac914838976ff0ed079b3d13399edb3356971c24a3b543604da5af9e0c5e6684", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Shift.lean", "ConLeche/Verify/Denote/Shift.lean", "fa34f824832d8939c2646d7d3e159936aaade9ac34436c72b8c2d59f680a092e", "fa34f824832d8939c2646d7d3e159936aaade9ac34436c72b8c2d59f680a092e", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/StrLit.lean", "ConLeche/Verify/Denote/StrLit.lean", "2d4a5180c98c9a281b4325cb96bad2fc9d0f895081aed8bbccce1063c3fc4d94", "2d4a5180c98c9a281b4325cb96bad2fc9d0f895081aed8bbccce1063c3fc4d94", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/SubstConst.lean", "ConLeche/Verify/Denote/SubstConst.lean", "f8c0dc0fe0c260f946f189a2007dbdea272f8a7255123c588b8d8c4733e9cc25", "f8c0dc0fe0c260f946f189a2007dbdea272f8a7255123c588b8d8c4733e9cc25", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/Tele.lean", "ConLeche/Verify/Denote/Tele.lean", "9c68290c5e3cd846792bab07734d1862aa194d65787a9ca1031830582ac65f08", "9c68290c5e3cd846792bab07734d1862aa194d65787a9ca1031830582ac65f08", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/TeleOpen.lean", "ConLeche/Verify/Denote/TeleOpen.lean", "8a512b68c376e7d1ed9c1fa9506bf18ca60978933de3439857610ce3fe5b8192", "8a512b68c376e7d1ed9c1fa9506bf18ca60978933de3439857610ce3fe5b8192", .verbatim⟩,
  ⟨"ConLeche/Verify/Denote/VClosed.lean", "ConLeche/Verify/Denote/VClosed.lean", "9f3e8a68dcedc6938ae8dacf240ebbfd58340bd4e97d0dcf9cab1e57703541d8", "9f3e8a68dcedc6938ae8dacf240ebbfd58340bd4e97d0dcf9cab1e57703541d8", .verbatim⟩,
  ⟨"ConLeche/Verify/DivModInv.lean", "ConLeche/Verify/DivModInv.lean", "a3aae7ce4d07fdc0868895d1b3398b4db4df823dfc97de7bae8538c270d2d9c4", "a3aae7ce4d07fdc0868895d1b3398b4db4df823dfc97de7bae8538c270d2d9c4", .verbatim⟩,
  ⟨"ConLeche/Verify/EnvBound.lean", "ConLeche/Verify/EnvBound.lean", "ab90be94f8e688058e4394aa8eb118c22f3c3e6b649ee1f49fdf17a388deff16", "ab90be94f8e688058e4394aa8eb118c22f3c3e6b649ee1f49fdf17a388deff16", .verbatim⟩,
  ⟨"ConLeche/Verify/EnvGuards.lean", "ConLeche/Verify/EnvGuards.lean", "5542c26343f10b6e0ac823516a70ec640ace6a535a4acba8e5dea536f76c2d31", "5542c26343f10b6e0ac823516a70ec640ace6a535a4acba8e5dea536f76c2d31", .verbatim⟩,
  ⟨"ConLeche/Verify/EnvPreds.lean", "ConLeche/Verify/EnvPreds.lean", "f9c5d6930a357f0a00c59040204a41ab4759751f545ccfe64307caf46068fac5", "f9c5d6930a357f0a00c59040204a41ab4759751f545ccfe64307caf46068fac5", .verbatim⟩,
  ⟨"ConLeche/Verify/EnvWF.lean", "ConLeche/Verify/EnvWF.lean", "696c58025cd44fa1a3f45f932b11f2eceed3674009ee59d66f1083fe7c8bba3e", "696c58025cd44fa1a3f45f932b11f2eceed3674009ee59d66f1083fe7c8bba3e", .verbatim⟩,
  ⟨"ConLeche/Verify/ExceptBind.lean", "ConLeche/Verify/ExceptBind.lean", "7817743fc7e58a457f0df27f2f1de6c78d5bcd0468f3cfba876c8c05170eb331", "7817743fc7e58a457f0df27f2f1de6c78d5bcd0468f3cfba876c8c05170eb331", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Block.lean", "ConLeche/Verify/Extend/Block.lean", "ff47e8a55a34765511acca2e5479d2ae98d8abf4b94b3d61dcc43a723719446d", "ff47e8a55a34765511acca2e5479d2ae98d8abf4b94b3d61dcc43a723719446d", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Ind.lean", "ConLeche/Verify/Extend/Ind.lean", "628055b10a186492c0f9b07b13763c8271ea617117c860a2184074ed01b5c675", "628055b10a186492c0f9b07b13763c8271ea617117c860a2184074ed01b5c675", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Inversions.lean", "ConLeche/Verify/Extend/Inversions.lean", "4565a8d871d08b9ac44eef9e23b92db74b4d0e5cd412243a1928487ca6101006", "4565a8d871d08b9ac44eef9e23b92db74b4d0e5cd412243a1928487ca6101006", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Iota.lean", "ConLeche/Verify/Extend/Iota.lean", "2bca1ad17469d71b5edb7c7d7c3757e42451465461fd5359291c637c25a6d3ca", "2bca1ad17469d71b5edb7c7d7c3757e42451465461fd5359291c637c25a6d3ca", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Modeled.lean", "ConLeche/Verify/Extend/Modeled.lean", "172513319d441792b44a631daf0b60d2516d3a1e813dbbb7a318faa667b9b9c3", "172513319d441792b44a631daf0b60d2516d3a1e813dbbb7a318faa667b9b9c3", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Proj.lean", "ConLeche/Verify/Extend/Proj.lean", "fab05f5a8214a4b254d48a96cdc054fa1d10a78a6523e1441a87172f3199657c", "fab05f5a8214a4b254d48a96cdc054fa1d10a78a6523e1441a87172f3199657c", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Recs.lean", "ConLeche/Verify/Extend/Recs.lean", "2ea81712337cc3c6f7ec909b585eb0db32c3ae3e0892bcb956f0718f5f5704cf", "2ea81712337cc3c6f7ec909b585eb0db32c3ae3e0892bcb956f0718f5f5704cf", .verbatim⟩,
  ⟨"ConLeche/Verify/Extend/Sibs.lean", "ConLeche/Verify/Extend/Sibs.lean", "70a01b23daf271606d7b1d58a28ff737921f706bc1337a1d7792ea09e9f5f178", "70a01b23daf271606d7b1d58a28ff737921f706bc1337a1d7792ea09e9f5f178", .verbatim⟩,
  ⟨"ConLeche/Verify/FastOps.lean", "ConLeche/Verify/FastOps.lean", "5e785b9ee46eda55c60426e56d5440e1fff7d51bfe99ef06c9b7e9d623a3ec93", "5e785b9ee46eda55c60426e56d5440e1fff7d51bfe99ef06c9b7e9d623a3ec93", .verbatim⟩,
  ⟨"ConLeche/Verify/Frontend/Prepare.lean", "ConLeche/Verify/Frontend/Prepare.lean", "e01c3dd6b3bf4df0feb4016725b6acbdba164a37ef69b561231b7eb92a838254", "e01c3dd6b3bf4df0feb4016725b6acbdba164a37ef69b561231b7eb92a838254", .verbatim⟩,
  ⟨"ConLeche/Verify/Fueled.lean", "ConLeche/Verify/Fueled.lean", "eb235c760203e250a204738c0748df9d05873b50153e7de72524bc13e1dfcab4", "eb235c760203e250a204738c0748df9d05873b50153e7de72524bc13e1dfcab4", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/FixInv.lean", "ConLeche/Verify/Inductives/FixInv.lean", "10beadbbf1ed4a640dc13c7ba3cc3aeb4fdd79a9a94d56b1ec9ce40f3d8c0560", "10beadbbf1ed4a640dc13c7ba3cc3aeb4fdd79a9a94d56b1ec9ce40f3d8c0560", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/FixParts.lean", "ConLeche/Verify/Inductives/FixParts.lean", "5421fddf4ae675962181ea57afb4dfaea1c9e8cfb749133a4d01a2cc3f3c89bc", "5421fddf4ae675962181ea57afb4dfaea1c9e8cfb749133a4d01a2cc3f3c89bc", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/FixRec.lean", "ConLeche/Verify/Inductives/FixRec.lean", "5528dd75656aea5b5b9428191cf7c10aac05285b31febf7748cb824c62c48774", "5528dd75656aea5b5b9428191cf7c10aac05285b31febf7748cb824c62c48774", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/FixWF.lean", "ConLeche/Verify/Inductives/FixWF.lean", "ec31c598dd0511cb9bdb9629774770c569e2969aec17201c3c54f219499a21b4", "ec31c598dd0511cb9bdb9629774770c569e2969aec17201c3c54f219499a21b4", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructBody.lean", "ConLeche/Verify/Inductives/StructBody.lean", "6eb7e24988929a4cc06cb294a5e3e147dad885d52d1a33ac973bcde0da06bc31", "6eb7e24988929a4cc06cb294a5e3e147dad885d52d1a33ac973bcde0da06bc31", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructInv.lean", "ConLeche/Verify/Inductives/StructInv.lean", "fc7b61be7d14d5289e9e3367091448c0c7b800f209e79d0c59861bfbadffd4cd", "fc7b61be7d14d5289e9e3367091448c0c7b800f209e79d0c59861bfbadffd4cd", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructPartsInv.lean", "ConLeche/Verify/Inductives/StructPartsInv.lean", "9e58337548772eeaefa0c4011abd843458b23baa14ca70c4ed72489104eb2558", "9e58337548772eeaefa0c4011abd843458b23baa14ca70c4ed72489104eb2558", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructRec.lean", "ConLeche/Verify/Inductives/StructRec.lean", "e08d45f9a6c90acbdba6ae81494c9119026e63fd786747c3adedbcaef2e631ba", "e08d45f9a6c90acbdba6ae81494c9119026e63fd786747c3adedbcaef2e631ba", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructResid.lean", "ConLeche/Verify/Inductives/StructResid.lean", "9becf553659055eb1f549ac28f53eeef499561e581e63b1688239054b33539c5", "9becf553659055eb1f549ac28f53eeef499561e581e63b1688239054b33539c5", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/StructWF.lean", "ConLeche/Verify/Inductives/StructWF.lean", "fc1ed334a9d05d12228c278ccfad46d7fc42640963195a7a0493e54162a82cdf", "fc1ed334a9d05d12228c278ccfad46d7fc42640963195a7a0493e54162a82cdf", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/SumInv.lean", "ConLeche/Verify/Inductives/SumInv.lean", "5b001178c420a86a5b4dbbcac0a20240a8e68fcacdd11ffea49a3b5a637b963a", "5b001178c420a86a5b4dbbcac0a20240a8e68fcacdd11ffea49a3b5a637b963a", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/SumRec.lean", "ConLeche/Verify/Inductives/SumRec.lean", "766e0dc686a4d13adb756f1334ec1d35203034320711f56d72ebc9687cdd6ca9", "766e0dc686a4d13adb756f1334ec1d35203034320711f56d72ebc9687cdd6ca9", .verbatim⟩,
  ⟨"ConLeche/Verify/Inductives/SumWF.lean", "ConLeche/Verify/Inductives/SumWF.lean", "010d5bc7231f89dac2865cb938f1e4332fc052bcc925c146e965e5c336c03f94", "010d5bc7231f89dac2865cb938f1e4332fc052bcc925c146e965e5c336c03f94", .verbatim⟩,
  ⟨"ConLeche/Verify/InferIOLeaves.lean", "ConLeche/Verify/InferIOLeaves.lean", "206ae056cbf95ff8c80b72ab99942c94e1afc4bfff9f11b1721f4b8a6d61fe7c", "206ae056cbf95ff8c80b72ab99942c94e1afc4bfff9f11b1721f4b8a6d61fe7c", .verbatim⟩,
  ⟨"ConLeche/Verify/InferIOLemmas.lean", "ConLeche/Verify/InferIOLemmas.lean", "be5bb5236c395b74e5dd944d6cce5a9e2a7cbafc04cb116de4748f672d327f24", "be5bb5236c395b74e5dd944d6cce5a9e2a7cbafc04cb116de4748f672d327f24", .verbatim⟩,
  ⟨"ConLeche/Verify/InferLeaves.lean", "ConLeche/Verify/InferLeaves.lean", "b3fc894e3298db8722da692fad6ea5f9bb17d01ec24c4af70150c6684c48b9e6", "b3fc894e3298db8722da692fad6ea5f9bb17d01ec24c4af70150c6684c48b9e6", .verbatim⟩,
  ⟨"ConLeche/Verify/InferLemmas.lean", "ConLeche/Verify/InferLemmas.lean", "87c7b7280b16e0318c8594ba8ee4000cdd766f887efc14ad500a353f6b7d063e", "87c7b7280b16e0318c8594ba8ee4000cdd766f887efc14ad500a353f6b7d063e", .verbatim⟩,
  ⟨"ConLeche/Verify/InstLevels.lean", "ConLeche/Verify/InstLevels.lean", "e8ca4a86775dbc51d1f4fb1aadc191165db0eef7416a276020562f90abb62343", "e8ca4a86775dbc51d1f4fb1aadc191165db0eef7416a276020562f90abb62343", .verbatim⟩,
  ⟨"ConLeche/Verify/InstList.lean", "ConLeche/Verify/InstList.lean", "6b0873f9acb9ce20e2828969ec1ba6964b03179e79632bc3ed153cd03b74329a", "6b0873f9acb9ce20e2828969ec1ba6964b03179e79632bc3ed153cd03b74329a", .verbatim⟩,
  ⟨"ConLeche/Verify/InstSpine.lean", "ConLeche/Verify/InstSpine.lean", "8d0cab4083ddf450d86a9153c17fc52d2be5bd7755e163dc6031ad995d498f2b", "8d0cab4083ddf450d86a9153c17fc52d2be5bd7755e163dc6031ad995d498f2b", .verbatim⟩,
  ⟨"ConLeche/Verify/IotaWalkInv.lean", "ConLeche/Verify/IotaWalkInv.lean", "219469e47f05e1649e8d857861924e8a515ea254aa849047472537e413403440", "219469e47f05e1649e8d857861924e8a515ea254aa849047472537e413403440", .verbatim⟩,
  ⟨"ConLeche/Verify/Knot.lean", "ConLeche/Verify/Knot.lean", "76fa607a8d04e226ce6f94b5194a90b20ec4c2e60845e979ffcd7a07acd5dcb5", "76fa607a8d04e226ce6f94b5194a90b20ec4c2e60845e979ffcd7a07acd5dcb5", .verbatim⟩,
  ⟨"ConLeche/Verify/Leaves.lean", "ConLeche/Verify/Leaves.lean", "6805a06eab92a6cffa39547f1430d3725c9407624307ce85d85157dd4383440c", "6805a06eab92a6cffa39547f1430d3725c9407624307ce85d85157dd4383440c", .verbatim⟩,
  ⟨"ConLeche/Verify/Level.lean", "ConLeche/Verify/Level.lean", "ec7db26a95d7c6a8e367c98a4acda19599dcd10f959a6663767213de45355c46", "ec7db26a95d7c6a8e367c98a4acda19599dcd10f959a6663767213de45355c46", .verbatim⟩,
  ⟨"ConLeche/Verify/Mono.lean", "ConLeche/Verify/Mono.lean", "5fd646c014f1f6b9f915edfef7d0e25343f9b4287108c4a1ac0f9c972123b773", "5fd646c014f1f6b9f915edfef7d0e25343f9b4287108c4a1ac0f9c972123b773", .verbatim⟩,
  ⟨"ConLeche/Verify/NatOpFrag.lean", "ConLeche/Verify/NatOpFrag.lean", "c91f4483da2355427108d61dc6fffe0691ccef0fc548a79940f08849cfc5bf63", "c91f4483da2355427108d61dc6fffe0691ccef0fc548a79940f08849cfc5bf63", .verbatim⟩,
  ⟨"ConLeche/Verify/OfReducePin.lean", "ConLeche/Verify/OfReducePin.lean", "2fdafbe62768e8b30284d3734f988501dd22244f9b606f9ee0bc87356bb307ba", "2fdafbe62768e8b30284d3734f988501dd22244f9b606f9ee0bc87356bb307ba", .verbatim⟩,
  ⟨"ConLeche/Verify/PairM.lean", "ConLeche/Verify/PairM.lean", "9a880f34e35b88740e6c35dd62094b5abb2da20d5a7377d79e93ce4fd25d2d06", "9a880f34e35b88740e6c35dd62094b5abb2da20d5a7377d79e93ce4fd25d2d06", .verbatim⟩,
  ⟨"ConLeche/Verify/PinnedShapes.lean", "ConLeche/Verify/PinnedShapes.lean", "3380806da7cb4fd5069003a3f8b0c3bb14ce2cad1f5729eb88ec73f472656110", "3380806da7cb4fd5069003a3f8b0c3bb14ce2cad1f5729eb88ec73f472656110", .verbatim⟩,
  ⟨"ConLeche/Verify/ProjSlots.lean", "ConLeche/Verify/ProjSlots.lean", "77065caf1bc6aea64df2b147eaa948e4d8ba30763927923f57c1f4cdd330f423", "77065caf1bc6aea64df2b147eaa948e4d8ba30763927923f57c1f4cdd330f423", .verbatim⟩,
  ⟨"ConLeche/Verify/ProjTele.lean", "ConLeche/Verify/ProjTele.lean", "d57213eaefaab6904045447c32dfc828ba31c8a5b7aebfa055fd4943ec5abb4c", "d57213eaefaab6904045447c32dfc828ba31c8a5b7aebfa055fd4943ec5abb4c", .verbatim⟩,
  ⟨"ConLeche/Verify/PropRead.lean", "ConLeche/Verify/PropRead.lean", "8877a1b56d76a487395546120b13abef55d0fce0c2017af2d9162abdc4da3eb7", "8877a1b56d76a487395546120b13abef55d0fce0c2017af2d9162abdc4da3eb7", .verbatim⟩,
  ⟨"ConLeche/Verify/PropWhen.lean", "ConLeche/Verify/PropWhen.lean", "2bdef3a7b198d3eaf45ec0127ef219cbd02c457ac70115bc820b57897af18e2c", "2bdef3a7b198d3eaf45ec0127ef219cbd02c457ac70115bc820b57897af18e2c", .verbatim⟩,
  ⟨"ConLeche/Verify/ReducePinInv.lean", "ConLeche/Verify/ReducePinInv.lean", "dc9544f069b8ba6521013aeca1eccfe3aa0bbb18764e3cc389435655c2d92dc2", "dc9544f069b8ba6521013aeca1eccfe3aa0bbb18764e3cc389435655c2d92dc2", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/Bridge.lean", "ConLeche/Verify/Rules/Bridge.lean", "5fe3e5dffe2ef09245ce49a781677556a890cb1a42e8ef17135d9ad1c25f12cc", "5fe3e5dffe2ef09245ce49a781677556a890cb1a42e8ef17135d9ad1c25f12cc", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/Certs.lean", "ConLeche/Verify/Rules/Certs.lean", "440547762127dbbf22c8ab670620d0f525c1cd6891dd9b64c2400abbc9d172d4", "440547762127dbbf22c8ab670620d0f525c1cd6891dd9b64c2400abbc9d172d4", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/DefEqBridge.lean", "ConLeche/Verify/Rules/DefEqBridge.lean", "2a9bb7f8408cc24f29c88e69163b352d789fc797637a9fa2fff57be1ea0dbb9d", "2a9bb7f8408cc24f29c88e69163b352d789fc797637a9fa2fff57be1ea0dbb9d", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/DefEqStepInv.lean", "ConLeche/Verify/Rules/DefEqStepInv.lean", "8c871230d21f73bdeef3e2a4b092a7cb5d40d49d9e9f9f9d9cd84a040db31a3c", "8c871230d21f73bdeef3e2a4b092a7cb5d40d49d9e9f9f9d9cd84a040db31a3c", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/Defs.lean", "ConLeche/Verify/Rules/Defs.lean", "221374beb162f425eb491ef78b370aa31e4d82aee3d0937b227ab98fc0942637", "221374beb162f425eb491ef78b370aa31e4d82aee3d0937b227ab98fc0942637", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/InferBridge.lean", "ConLeche/Verify/Rules/InferBridge.lean", "a1bf6cda57e18f5723cc04983fa4b21ccae69844ca1049af5df0de98106fce66", "a1bf6cda57e18f5723cc04983fa4b21ccae69844ca1049af5df0de98106fce66", .verbatim⟩,
  ⟨"ConLeche/Verify/Rules/RedBridge.lean", "ConLeche/Verify/Rules/RedBridge.lean", "84853eabb54d622d0a9775c3ee8d4be275a997c18503018233e92c151577bb3a", "84853eabb54d622d0a9775c3ee8d4be275a997c18503018233e92c151577bb3a", .verbatim⟩,
  ⟨"ConLeche/Verify/Shift.lean", "ConLeche/Verify/Shift.lean", "c4a302230ab8ef38f4d3e28d351ae220381cf4576cb040d8534c4c595b0b3f03", "c4a302230ab8ef38f4d3e28d351ae220381cf4576cb040d8534c4c595b0b3f03", .verbatim⟩,
  ⟨"ConLeche/Verify/StdAxiomPin.lean", "ConLeche/Verify/StdAxiomPin.lean", "36bac7fe07f3a55e45254d18843f55d7faf6a31545f71a0e29aff3558ae1de6c", "36bac7fe07f3a55e45254d18843f55d7faf6a31545f71a0e29aff3558ae1de6c", .verbatim⟩,
  ⟨"ConLeche/Verify/StrLitExpr.lean", "ConLeche/Verify/StrLitExpr.lean", "45e26505e9314ee05a5e92edfcaeb627c89981259f6259460bc58cbd5fa79712", "45e26505e9314ee05a5e92edfcaeb627c89981259f6259460bc58cbd5fa79712", .verbatim⟩,
  ⟨"ConLeche/Verify/Subst.lean", "ConLeche/Verify/Subst.lean", "b5990a82183682bacb78298c0af7d160e4579ee7072b4765c1ab096450e5b6bd", "b5990a82183682bacb78298c0af7d160e4579ee7072b4765c1ab096450e5b6bd", .verbatim⟩,
  ⟨"tests/ConLecheTests/Axioms.lean", "Tests/ConLeche/Axioms.lean", "a408634434101042826736595647f89792e7be16da4916b2806928602db08887", "233671487b4aee41c3277a195b31a1ae13a41e25c9c05586dbc16b5275cc79c7", .adapted "adapted: namespace Tests.ConLeche.Axioms; StreamConsts/StreamThm imports and 3 guards (no_False_declaration, no_False_theorem_accepted, Cached.checkDecls_consts) dropped; docstrings cut; port header added"⟩
-- END con-leche rows
]

/-- Con-leche tooling ported outside the inventory roots: the layering and
trust-surface fences (adapted to this repository's paths; their headers
list the changes) and the lexer fixture (verbatim). -/
def conLecheTooling : Array PortRow := #[
  ⟨"tests/layering.sh", "scripts/layering.sh", "9b6dfa842951c290f9b832367a3cb2795d18dc66f3f68e8011dcfc844bb7ad61", "5f3afe6db7691bee436f15d8556501c3f1525cb2371be7736956d32a59ecfed6", .adapted "scan ConLeche/** only; the dead base-to-model clause repaired; the boundary clause added; tolerant of an absent or partial subtree"⟩,
  ⟨"tests/trust-surface.sh", "scripts/trust-surface.sh", "f7c5406a102347a0618aec0e327999036098928075cb4bfac2edef726b81b912", "79cac42dcb4083659beb549383c4ac9e4dc1d4bd50bad74ffd7a4e0e7da01bb0", .adapted "scan ConLeche/** only; Main.lean and Challenge.lean entries dropped; header condensed; tolerant of an absent subtree"⟩,
  ⟨"tests/trust-surface/lexer.lean", "scripts/trust-surface/lexer.lean", "b8cd4b707f0cd1548475a7ff2a994d362d4715ae90be16fd94c2c50c809f422b", "b8cd4b707f0cd1548475a7ff2a994d362d4715ae90be16fd94c2c50c809f422b", .verbatim⟩
]

/-- Con-leche's licence, carried with the subtree. -/
def conLecheLicenses : Array PortRow := #[
  ⟨"LICENSE", "ConLeche/LICENSE", "8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e", "8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e", .verbatim⟩
]

/-- The con-leche rows whose files add Argument's modifications copyright and
declare `Apache-2.0 AND (MIT OR Apache-2.0)`: the adapted main theorem and
axiom pin. -/
def conLecheModified (target : String) : Bool :=
  target == "ConLeche/MainTheorem.lean" || target == "Tests/ConLeche/Axioms.lean"

/-- The old branch's set theory and set model, ported from con-leche
`oldSetTheoryOrigin`. -/
def setTheoryDerived (target : String) : Bool :=
  target.startsWith "Ix/Kernel/Model/SetTheory/" || target.startsWith "Ix/Kernel/Model/SetModel/"

/-- Every imported file, by origin and licence. -/
def portSets : Array PortSet := #[
  { origin := oldBranch, license := "MIT OR Apache-2.0",
    rows := (ported.filter (!setTheoryDerived ·.target)).map PortedFile.toRow ++ licenses },
  { origin := oldBranch, license := "Apache-2.0 AND (MIT OR Apache-2.0)",
    rows := (ported.filter (setTheoryDerived ·.target)).map PortedFile.toRow },
  { origin := conLeche, license := "Apache-2.0",
    rows := conLecheRows.filter (!conLecheModified ·.target) ++ conLecheLicenses ++ conLecheTooling },
  { origin := conLeche, license := "Apache-2.0 AND (MIT OR Apache-2.0)",
    rows := conLecheRows.filter (conLecheModified ·.target) }
]

end Tests.Ix.Kernel.ImportManifest
