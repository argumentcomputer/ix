# Certifying the Lean → Ix compiler: what `compile-certify` establishes

This document describes the compiler-certification lane (`Ix/CompileCert/**`) as it runs on real
compiler output: the two theorems it decides (W and S), the receipts they use and how far each is
trusted, and how to run the certifier. It does not describe what each Lean name denotes after
compilation (the output contract); that belongs to `docs/compiler-passes.md`.

The certified checker (`IxC/**`) proves Ix environments consistent: an environment it admits has a
set-theoretic model. The lane relates a Lean environment to the compiled Ixon environment so that
this consistency result speaks about the Lean declarations.

## 1. The two theorems

### 1.1 W: the compiled bytes are a faithful reading of the Lean declarations

For an *input* (a closed set of Lean declarations, the compiled records they reach, the name map
from Lean names to records), the decision `checkIndexed` (equivalently the list-based
`checkCompiled`) returns an `AcceptedAssociation` exactly when:

- the exact record bytes are admitted by the certified checker (`checkBytes`: decoding, reading,
  the verified fold);
- the source is closed and uniquely named, and the map covers it (`DirectDomain`);
- every Lean declaration's independent export (`directExport`: names through the map, universes
  canonicalised under a proved semantic guard, binder names and `mdata` erased) equals an entry of
  the certified reader's output (definition hints quotiented; a projection function of a
  structure-like the reader rewrites is compared with the raw record through the reader's proved
  `projRewrite` relation);
- whole inductive blocks match and every touched definition group is covered.

`checkIndexed_sound` (`Ix/CompileCert/Indexed.lean`) states this; `faithful_sound` is the same
statement for `checkCompiled`. W says the compiled constant *is* the Lean declaration, read through
the export. It does not by itself say that the Lean declaration's meaning is the compiled
constant's meaning in a model: that is S.

### 1.2 S: the Lean declarations' model is the pull-back of the compiled environment's model

For the same input, S takes in addition the **normalised source installation**
(`SourceNormalizedInstallation`): the Lean declarations exported under their own names, completed
with the certified modeller's helper declarations, projection functions of non-direct
structure-likes lowered to recursor form (each with a lowering receipt), and folded by the
certified checker itself. The decision `decideStrongCone` (`Ix/CompileCert/StrongCone.lean`)
checks, between the installed source environment and the admitted target environment plus
certifier-proposed support declarations, that names agree with the accepted map, that every
installed source row has a target row under the map whose type, value, recursor rules and
capabilities are the same terms up to the map and the universe image, that eta, unit and
projection-tower laws carry over, and that the Nat and reduction operations of the source are the
target's. Its success is a `StrongCone`, and `StrongCone.sound` states what that implies:

- W's conclusion for the input (above);
- the source fold accepted the installed declarations (`checkDecls … = .ok installed.env`);
- the target (artifact plus support) has a strong model, and **for every strong model of the
  target there is a strong model of the installed source whose annotations and values are the
  pull-back of the target's under the name map** (`artifact_strong_model_all`);
- every original Lean declaration of the input is installed as its exact export, or is a
  projection function whose installed replacement has a lowering receipt.

"Strong model" is the checker's `EnvModelM`: every field the certified checker's soundness uses
(typing, definitional equations, capabilities, recursor rules, projection towers, Nat operations,
`Nat.div`/`Nat.mod` laws, reduction axioms). So a Lean constant's meaning in the source model is,
by construction, the compiled constant's meaning in the target model.

### 1.3 W+: changed constants (`Ix/CompileCert/Changed.lean`)

Pass 3 changes some constants on purpose (`docs/compiler-passes.md` §4–§5): a Lean recursor of a
changed block holds its *image*, a definition; image-kind auxiliaries (`casesOn`, `below`,
`brecOn`, …), their users and transported clique members have values other than the export of
Lean's; theorems through them have other proofs. W's syntactic correspondence refuses them. W+
certifies them by Lean's own criterion, *Lean's kind and type, and Lean's defining equations hold*,
with theorem rows checked by the certified checker and no new trust:

- **theorem by statement** (`ThmStatementMatch`): the reader has a *theorem* under the exported
  name and universes whose statement is the exported one; the proof is not compared;
- **equations** (`EquationMatch`): the reader has a *definition* under the exported name and
  universes, and every defining equation is the statement of a theorem row: for a recursor, one
  per computation rule, stated by a pure function of Lean's `RecursorVal` (`leanRuleStatement`)
  and exported as everything else; for a definition, `@Eq T c value` (proof `Eq.refl`, or a
  **value row**: the same statement with a proof the certifier generates, below), or Lean's own
  `c.eq_def`;
- a declared type that is convertible to Lean's but not equal (Pass 3 inlines images in types too)
  is matched through a **type row** `@Eq (Sort ℓ) T_ix T_lean` (proof `Eq.refl`). A type row and a
  definition's `rfl` row are stated at the universe ℓ the certified checker itself infers for Lean's
  type (and for the compiled one), so that typing the row compares the two sorts by syntactic
  equality: at a smaller equivalent level the checker's `Level.leq` decides, exponential on the
  nested `imax` chain it infers for a long telescope (the Cutsat `brecOn(_k).go` of Lean's core);
- **changed blocks** (`ChangedBlockMatch`): every member and constructor of the Lean block is
  exported to the reader block holding it, which holds nothing else; every recursor of the Lean
  block is claimed an image (`ExportContext.images`, checked by the map). That the block
  transformation itself preserves the meaning of the types is trusted here and proved in M7.
- **value rows** (package V, `Ix/CompileCert/CliqueRows.lean`): a member of a transported
  definition clique (`docs/compiler-passes.md` §11.2 case 7) holds the transported value under
  Lean's name, which is not convertible to Lean's value, so its `rfl` row is refused. The certifier
  decompiles the clique's compiled constants from the artifact (the stored, transported terms),
  adds them to Lean's environment (Lean's kernel checks them) and builds a proof of `c = v` there:
  for a **well-founded** clique, well-founded induction on Lean's relation with the members'
  equations as the motive (a `PSum.casesOn` tree), each step `WellFounded.fix_eq` (or
  `WellFounded.Nat.fix_eq`) on both sides, one unfolding of either side the same body (the
  conjugation) and `congrArg`/`funext` from the induction hypothesis; for a **structural** clique,
  induction on the major premise with the block's recursor (mutual and nested motives), each
  case by unfolding both sides to the user's body and congruence with the induction hypotheses as
  leaves, a match on another variable split by `cases` on it. The proof is exported like any
  support row (`<name>._ix_val.<k>`), pre-screened and folded by the certified checker;
  `RflEquation` quantifies the proof away, so a member matched by its value row has `c = v` in every
  strong model (`model_equations`, `rflEquation_of_row`,
  `value_row_holds`) with no statement changed. A member whose value row is not generated or is
  refused keeps Lean's `eq_def` route (or its Unsupported class) and is listed as a residual:
  `partial_fixpoint` cliques (no generator), and structural cliques over a changed inductive block
  (their compiled constants reach the canonical block's recursor, which the generator does not add
  to Lean's environment).

The rows are either the artifact's own (a carried `eq_def`) or **support** declarations the
certifier builds (`<name>._ix_eq.<k>`, `<name>._ix_type`), pre-screened one by one and folded once
by the certified checker on top of the admitted declarations (`FoldedSupport`). The admission keeps
its fold's install phase (`prepareArtifactStaged`) and the support is installed and checked by
continuing it (`foldSupportStaged`): `checkDecls_append_of_phases` (`Ix/CompileCert/FoldCompose.lean`,
from `IxC`'s own lemmas on its fold) proves that this is the certified fold over the admitted
declarations and the support, so the artifact is not checked a second time (`--refold` folds both
again, the earlier behaviour). `checkIndexed'`
decides `AcceptedAssociation'` (four-way correspondence: direct ∨ raw ∨ theorem ∨ equations; whole
or changed blocks) and `checkIndexed'_sound` states it; `AcceptedAssociation'.model_equations` and
`model_statement` give the semantic reading: every row used is installed by the fold and, in every
strong model of the folded environment, each typed instance of its equation relates equal values
(`StrongInstalledModel.theorem_eq`). The uniqueness of the function the equations define is not
claimed. When nothing is changed the certifier decides the old `checkIndexed`, and
`faithful_sound`/`checkIndexed_sound` keep their meaning literally.

### 1.4 Unit of certification

W is decided once over every candidate of a library. S is decided **per cone**: a root, its
closed dependency cone as the source, and the records that cone reaches, admitted on their own. A
constant is **S-Certified** when some accepted cone contains it; the conclusion then holds for every
member of that cone. Since M7 WP-F the S decisions run on name indices and on the DAG (§2), so one
cone may be a whole library: `--strong-global` decides first one **global cone**, every constant W
certifies by the direct or raw route whose closure stays among them, and leaves to the cover only
what it did not certify (everything, if it is refused).

The source of a cone may be any closed set of declarations. A cover (S on every W-certified
constant) decides roots nothing uses whose cones overlap as **one cone whose source is the union
of theirs** (a batch: roots of the same namespace, an auxiliary declaration such as `f._simp_1`
or `f.eq_1` counted in `f`'s, the union within 3/2 of the largest cone); a batch that
cannot run or fails as one cone is dissolved and its roots are decided on their own cones. A cone
that contains a pin-certified Nat operation also takes its certificate ground, and a cone that
contains `Quot` takes Lean's `Eq`, listed first (the checker installs the quotient block only over
the pinned `Eq` basis, which the source fold installs where it meets Lean's `Eq`).

## 2. Receipts and their trust

| Receipt | What it says | How it is established |
| --- | --- | --- |
| admission (`checkBytes`) | the record bytes decode, read and fold | the certified checker, proved (`IxC`) |
| W association | each Lean declaration's export is a reader entry | decided; `checkIndexed_sound` proved in the lane |
| source installation | the exported Lean declarations fold | the certified checker's fold, run per cone |
| lowering receipt (`SourceProjectionLowering`) | a lowered projection function has the original header, the declared binder domains and the recursor form of the original field | decided in the lane; the equation `f p⃗ self = lowered p⃗ self` is a theorem **checked by Lean's kernel** at certification time (`addDeclCore`, checking on) |
| name map, support, Nat/DivMod/reduce receipt names, source pins | the arguments of the S checks | **proposed by the certifier, untrusted**: names are checked by `SemanticNamesAgree` and the installed association, support by the verified fold, receipts by the receipt checks, pins by the fold (sound for any pins) |
| W+ type and equation rows | a changed constant's declared type is Lean's (up to conversion) and Lean's computation rules / defining equation / `eq_def` hold | built by the certifier (untrusted), **checked by the certified checker** (the fold of the artifact plus the rows); `checkIndexed'_sound`, `model_equations` proved in the lane |
| source-named Nat pins (`Ix/CompileCert/SourceNatOpPinData.lean`) | the pin variant the source fold runs with: the eight pin-certified Nat operations' Lean values and certificate proofs under Lean's names | generated by `source-pin-gen` (`SourcePinGen.lean`) from Lean's own declarations and the theorems of `IxC/Kernel/PinGen/Certs.lean` as Lean elaborated them, exported by `exportSourceExpr`, closed over each operation's Lean cone by `kernel-pin-gen`'s rule; **untrusted**: the fold compares the pin by `isDefEq` and type-checks every certificate against the checker's own pinned statements; `check-cert` compares the committed data with a regeneration |
| S association (`decideStrongCone`) | the pull-back above | decided; `StrongCone.sound`, `artifact_strong_model_all` proved in the lane |

Trusted, outside the proofs: the host `Lean.Environment` the source is read from (as for every
use of `captureCone`); that `directExport`/`exportSourceExpr` is the intended reading of a Lean
declaration (erasing binder names, binder infos and `mdata`; universes canonicalised under the
proved guard); that a theorem the certifier lists as a lowering witness was accepted by Lean's
kernel; for W+, that Lean's `c.eq_def` is `c`'s unfolding equation (the relation checks that it is an
equation about `c`), for the members certified by the `equations:eq_def` route only (a member with an
accepted value row has `c = v` checked instead; the run lists the others in `<prefix>.values.tsv` and
its `V:` line) and, until M7, that the transformation of a changed block preserves the meaning
of its types; the Lean runtime that executes the decisions. That runtime includes, since M5 WP-B,
the compiler's `@[csimp]` substitutions through which the decisions run on the DAG (a shared
subterm visited once): the export (`exportExprWith ↦ exportExprWithShared`, `exportExpr ↦
exportExprShared`), the reference walk (`refsIn ↦ refsInShared`) and the comparisons
(`DirectEntry`'s and `Kernel.Expr`'s derived `DecidableEq` ↦ the certified kernel's memoised
`Kernel.Expr.beq`); each substitution is a proved equation (`exportExprWithShared_eq`,
`refsInShared_eq`, `DirectEntry.beqShared_iff`; decisions are subsingletons), and the memos rest on
`Init.Util`'s `withPtrAddr`/`withPtrEq`, as the certified kernel's own compiled equality does. The
tracked axiom audit (`Ix/CompileCert/Audit.lean`, `lake run check-cert`) checks that every root of
the lane uses only `propext`, `Classical.choice` and `Quot.sound`, and that no decision reaches a
hash-cached equality, both in the decisions' definitions and as executed (following every
registered `@[csimp]`).

Since M7 WP-F the S decisions run the same way (`Ix/CompileCert/SourceExportFast.lean`,
`SourceInstallFast.lean`, `StrongFast.lean`, the indexed normalisation in `SourceNormalization.lean`):
every lookup of the source export, the model proposal, the entry correspondence, the normalisation,
the name check, the support admission and the strong check goes through a name index (IxC's
`mkFEnv`, or a hash map built from the list with the first entry of a name winning, as `List.find?`
does: an equation, no uniqueness assumed); the dependency lists of the export and the strong
check's expression comparison walk the DAG with memos of the WP-B kind (keyed by addresses,
confirmed by identity, self-proving entries); `Kernel.ConstantInfo` and `Kernel.Declaration` are
compared field by field through `Kernel.Expr.beq` after a pointer test; the availability pass is
skipped when the Boolean checks accept (it is then implied, `availability_of_checks`). Each
substitute is proved equal to the function it replaces and installed by `@[csimp]`; `StrongCone.sound`
and every other statement read the original definitions. The trust is the same as WP-B's.

**Executable only (no proof):** which constants are offered to the decisions (record selection,
the expression-size budget — distinct `Expr` objects per declaration, the work of the DAG walks —,
the cone choice and budget), the classification of what is not
certified (class, blocking dependency, diagnostic), and every proposal. A wrong triage or proposal
can only leave a constant uncertified; Certified and S-Certified come only from an accepted
decision.

## 3. Verdicts

W: **certified**, **unsupported** (a named class, e.g. `partial`/`unsafe` definitions the
checker's reader declines; `target record not selected`, a name whose record goes with a block the
reader declined without being the cause, as the recursors of unsafe inductive blocks
(`Ix/CompileCert/Certifier.lean`; Mathlib: 6, e.g. `Lean.Expr.FoldConstsImpl.State.rec`); a declaration
over the size budget), **blocked** (by a dependency that
is not certified) or **rejected** (a diagnostic: the compiled constant is not the Lean
declaration). S, beside it: **S-certified**, **S-unsupported** (class), **S-blocked** (by a cone
member that fails, or by W), **S-rejected** (diagnostic). A W verdict other than certified carries
over to S (`W unsupported: …`, `W: …`, `W rejected: …`). A certified row's cause column names its
route: `direct`, `raw`, `theorem`, `equations:rfl`, `equations:value-row`, `equations:eq_def` (W+), with `, type-row` when the
declared type matched through a type row and `, changed-block` for an inductive of a changed block;
`direct/raw` when the old W decision accepted the input at once. A changed definition whose equation
rows the checker refuses is rejected, except a transported clique member without `eq_def` in Lean's
environment (unsupported, `changed definition: transported clique member without eq_def`). The
rows are pre-screened one by one with the stepping checker under a time budget per row
(`--row-budget`, 60 s): a row over its budget is not decided and never folded, and a changed
constant that would pass with its rows over the budget taken as accepted (those rows are all it
lacks) is unsupported (`changed constant: a type or equation row over the pre-screen time budget`, a
resource limit like the size budget); a definite refusal of another of its rows keeps it rejected.
The checker's pure code cannot be interrupted: a row over its budget keeps its core until the
command exits, right after its report.

S for changed constants is not decided yet (M7): S decides only the constants W certifies by the
`direct`/`raw` routes. A constant certified by a W+ route (a theorem or equation row, a type row, a
changed block) is **S-unsupported** (`certified by a W+ route; S for changed constants is M7`), is
put in no cone, and every cone that reaches it is S-blocked by it with that class; it is never
S-rejected for it.

## 4. Running it

```
lake build compile-certify
compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--row-budget <ms>] [--refold] [--no-value-rows] [--explain <name>]* [--receipts-only] \
  [--strong | --strong-only] [--strong-roots <A,B,...>] [--strong-every <k>] \
  [--strong-max-cone <n>] [--strong-tasks <n>] [--strong-plan] [--strong-global] [--explain-global]
```

- `--file` elaborates the file as `ix compile` does (`Benchmarks/Compile/CompileInitStd.lean`,
  `Benchmarks/Compile/CompileMathlib.lean`); `--modules` imports modules.
- `--budget` bounds the distinct `Expr` objects of one declaration (type, value and rule right-hand
  sides, each counted separately; default 2^28): a declaration over it is unsupported (`expression
  DAG over budget`). `<prefix>.sizes.tsv` lists every declaration with at least 4096 objects with its
  tree size (computed on the DAG): the tree size is reported, not budgeted.
- W writes `<prefix>.tsv` (one row per constant: name, address, verdict, cause),
  `<prefix>.classes.tsv`, `<prefix>.json`, the raw-projection measurement `<prefix>.proj.tsv` and
  the lowering receipts `<prefix>.receipts.tsv`/`.receipts.statements`; the JSON records the routes,
  the image claims, the W+ rows proposed and folded and the artifact names with no Lean constant
  (`ixOnly`, the canonical `_ix` constants among them; listed in `<prefix>.ixonly.tsv`) and the rows
  over the pre-screen time budget; `<prefix>.rows.tsv` gives each W+ row's pre-screen time and
  verdict; `<prefix>.values.tsv` gives each transported clique member's value row (accepted,
  refused, not generated, not exported, with the reason) and its route, the JSON's `valueRows` the
  members certified otherwise (the residual trust in Lean's `eq_def`); `--no-value-rows` proposes
  none (the members are matched by Lean's `eq_def` only, the earlier behaviour); `--explain <name>` also prints the rows of a changed constant, the checker's verdict on
  each and the first difference of type and value. The command exits as soon as its report is
  written, without waiting for a row left running past its budget (the checker cannot be
  interrupted).
- `--strong` then decides S: on every W-certified constant (a cover by cones, roots nothing uses
  first), on `--strong-roots`, or on a sample (`--strong-every k`: every k-th W-certified constant
  in name order plus the projection functions of non-direct structure-likes). It writes
  `<prefix>.strong.tsv` (name, W verdict, S verdict, cause), `<prefix>.strong.cones.tsv` (per cone:
  roots, members, records, support, witnesses, time per stage, outcome), `<prefix>.strong.classes.tsv`
  and `<prefix>.strong.json`. `--strong-only` skips the global W (each cone still runs its own W
  association) for probes.
- `--strong-plan` computes the cones S would run (the same order, batches and budget) without
  running any, each counted as accepted, and writes `<prefix>.strong.plan.tsv` (per cone: position,
  root, roots, members, the constants it is the first to contain, the running total) and
  `<prefix>.strong.plan.names.tsv` (per W-certified constant: its first cone, or why it has none);
  it writes no S verdict. With `--explain <name>`, the stages of that root's cone are timed one by
  one (input, admission, W, each step of the source installation, the proposal, the support and
  every family of the strong check).
- `--strong-global` decides one global cone before the cover (§1.4): its members are S-certified by
  that cone's `StrongCone.sound`; the cover then decides only what it did not certify, and everything
  if it is refused. Run it with a large stack (`ulimit -s unlimited`): the source normalisation recurses
  once per declaration. `--explain-global` times the global cone's stages (with `--strong-plan`, no
  verdict).
- Exit 0 iff something is certified, nothing is rejected, every raw projection on a non-direct
  structure-like has a receipt, and, with S, something is S-certified and nothing is S-rejected.

The lane's own gate is `lake run check-cert` (the audit, the strict build, the fixture checks, the
certifier on the fixture with and without `--strong`).

The source-named Nat pins are regenerated (after a toolchain change, say) by
`lake build source-pin-gen && lake exe source-pin-gen Ix/CompileCert/SourceNatOpPinData.lean`: the
generator loads the environment of `IxC.Kernel.PinGen.Certs`, generates the variant, installs each
operation's source cone through the normalised source installation with it (and refuses it without
pins), and writes the file only if every step passed.

## 5. Known limits of the S route (2026-10-07)

- **The pin-certified Nat operations** (`Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, `Nat.shiftRight`) are no longer a limit: the source fold runs with the source-named pins
  (§2), and on Init+Std-a3 each operation's own cone is S-Certified. The compiled pin variant
  (`Benchmarks/Kernel/PinGen.lean`) still cannot be used for the source: the compiled names merge alias
  fibers that Lean keeps apart (for example `LT.lt` and `LE.le` share one address).
- **Quotients** are no longer a limit: a cone that contains `Quot` also contains Lean's `Eq`, listed first,
  and the source fold installs it as the pinned `Eq` basis before it meets `Quot`. A cone that met `Quot`
  first, or a non-pinned `Eq`, is refused by the fold.
- **Axioms the checker does not install** (`sorryAx`): the fold installs no row for them on either side and
  declines every use, so no support is proposed and an S verdict on such an axiom's own cone says nothing
  about it.
- **Changed constants** (certified by W+, §3) are S-unsupported, and the constants whose cones reach them
  S-blocked by them: S's per-cone W association and strong checks compare the installed source with
  target rows that are, for a changed constant, not its Lean declaration's export. M7.
- **Proof-field projections of mutual or nested structure-likes** (theorems in Lean 4.34.1): refused by W
  before W+; W+ certifies them by the `theorem` route (the `LoweringDefs` fixture's `Sized.ok`), so S
  treats them as changed constants (above).
- **Cost.** Since M7 WP-F a cone costs about its admission and its certified fold (the source export,
  model proposal, correspondence and normalisation run on indices and the DAG, and the strong check takes
  seconds: 0.3 s on a 4,000-declaration cone that reaches the `String`/`TreeMap` lemma core, 1.2 s on one
  of 12,000, where it took 43 s and about 20 minutes before). On Init+Std-a3, `--strong-global` decides
  one cone of 116,727 members in about 10 minutes (admission 3, installation 6 of which the fold 3, the
  strong check 9 s; peak 10.6 GB), every W-certified constant in S's domain but the 25 users of W+
  constants. The per-cone cover (4,145 cones on Init+Std-a3 with W+ and WP-B, a constant in about 34 of them) remains the
  fallback.
  `--strong-max-cone` bounds the cone size of the cover; larger cones are S-unsupported (`cone over budget`) and their users S-blocked, never rejected.
