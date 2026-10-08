# Certifying the Lean → Ix compiler: what `compile-certify` establishes

This document describes the compiler-certification lane (`Ix/CompileCert/**`) as it runs on real
compiler output: W's export correspondence, W+'s statement and equation checks, and S's model
pull-back; the receipts and trust each requires; and how to run and read the certifier. The
[output contract](compiler-passes.md#11-the-output-contract) states what the compiler puts under
each Lean name. Its [changed-set record](compiler-passes.md#115-the-changed-set-record) records
transformations; a record entry alone is not a certification verdict. The
[compiler gate guide](compiler-gates.md) describes the regression suites and their limits.

The certified checker (`IxC/**`) proves Ix environments consistent: an environment it admits has a
set-theoretic model. The lane relates a Lean environment to the compiled Ixon environment so that
this consistency result speaks about the Lean declarations.

## 0. What is established

The per-output decisions below certify the particular closed source and admitted bytes supplied
to them. Separately, L1 proves properties of the Pass 1 implementation under its stated
hypotheses. Neither a successful library run nor the Pass 1 result is the remaining general
theorem that every successful compiler run preserves source meaning through every pass.

| Claim | Conclusion | Checked theorem and audit registration |
| --- | --- | --- |
| W (§1.1) | The source exports correspond to entries obtained by admitting the exact records; whole blocks and touched definition groups are covered. | [`checkIndexed_sound`](../Ix/CompileCert/Indexed.lean), [`faithful_sound`](../Ix/CompileCert/CheckCompiled.lean); `roots` (597), `m3Roots` (68). |
| W+ (§1.3) | The accepted direct/raw, theorem-statement or equation relation holds, with whole or changed-block correspondence; the typed theorem rows hold in every strong model of the artifact plus folded support. | [`checkIndexed'_sound`, `AcceptedAssociation'.model_equations`, `model_statement`](../Ix/CompileCert/Changed.lean); `m5Roots` (103), `vRoots` (8). |
| S, strong (§1.2) | Every strong target model supplies a strong installed-source model with the prescribed annotation and value pull-back. | [`StrongCone.sound`, `SourceNormalizedInstallation.artifact_strong_model_all`](../Ix/CompileCert/StrongCone.lean); `m4dRoots` (15). |
| S, value level (§1.5) | Every strong target model supplies a public value model of the installed source with value pull-back, public capability laws and universal rule simulation. | [`StrongCone'.sound`, `checkedChangedAssociation_values`](../Ix/CompileCert/StrongChanged.lean); `saRoots` (20). |
| L1, Pass 1 (§1.6) | SCCs, comparator/refinement properties, specified canonical classes and name maps, and nested discovery/position/evaporation properties, with the hypotheses below. | [`Canon.lean`](../Ix/CompileCert/Canon.lean) and its imported proofs; `l1Roots` (411), `hashRoots` (41). |

The numbers are entries in the named root arrays in
[`Audit.lean`](../Ix/CompileCert/Audit.lean), not a count of independent theorems or a measure of
compiler coverage. The audit follows each root's dependencies and permits only `propext`,
`Classical.choice` and `Quot.sound`. The decision audits also inspect the compiled substitutions
described in §2. An audit checks proof dependencies; it does not remove a theorem's source,
model, name-map or hash hypotheses.

For the semantic conclusions, fix a carrier `V` with `[Kernel.SetTheory V]`. “Every model” in
the S statements means every `StrongInstalledModel V` of the specified target environment,
which includes the checked support. The source interpretation is the normalised installation
with the exact-export or projection-lowering relation back to the original declarations. W+
alone establishes its checked statements and equations; equations need not determine a unique
function. §1.5 establishes the value pull-back by its additional check, without asserting the
annotation pull-back of §1.2.

The reader's `partial` and `unsafe` declaration classes are excluded by design from this
certification domain. More time or a larger size budget does not admit those classes. A
resource refusal of an otherwise eligible declaration is a separate limitation (§3).

## 1. The statements

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
  transformation itself preserves the meaning of the types remains trusted here; the general
  compiler proof obligation is described in §1.7.
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

### 1.5 S for changed constants, at the value level (`Ix/CompileCert/StrongChanged.lean`, M7 S+a)

`StrongCone.sound` cannot hold above a changed definition: the strong model's definition law
(`EnvModelM.defn_reads`) is an equality of annotation terms, and the annotation reading of a term
inlines the leaves of the constants it mentions, so a definition whose compiled value is not the
export of Lean's (an image-kind head, a rewritten user, a transported clique member) breaks the
annotation pull-back at itself and at every constant whose value mentions it. At the **value level**
nothing is inlined (`Kernel.Denotes` reads a constant through its value function), and that is the
level the plan states S at: for every model of the target, the source model `M_S(n) := M.cval (N n)`
satisfies membership, `False` empty and `Eq` equality, definitions denote their values, and the
recursor rules hold.

The decision `decideStrongCone'` takes a cone whose W association is **W+'s** (`AcceptedAssociation'`,
its support the W+ rows of the cone's members and any source-owned support, folded once by the
certified checker) and checks, between the installed source and that fold (`checkChangedAssociation`,
on the index and the DAG as `checkChangedAssociationF`): the names against W+'s map, and the
value-level part of the installed association (telescopes, types, the `False`/`Eq` pins,
capabilities, eta, recursors, constructors, rule level links) with one alternative for
definitions: an installed source definition `c := v` whose target value is not the image of `v`
passes when the target has a **theorem row** whose installed statement is `@Eq T (N c) r` with `r`
the image of `v` (`definitionRowF`; the row is named by an untrusted hint and nothing else about it
is assumed). W+'s `rfl` rows and certifier-generated value rows have this shape; Lean's `c.eq_def`
does not (an unfolding equation does not determine a value in an existence-only model). Theorems'
proofs are never compared, as in the strong check. `StrongCone'.sound` states what an accepted cone
implies:

- W+'s conclusion for the input (`checkIndexed'_sound`'s);
- the names agree with W+'s map; the source fold accepted the installed declarations;
- the target (the fold of the admitted artifact and the support) has a strong model, and **for every
  strong model of the target there is a public value model of the installed source whose values are
  the pull-back of the target's under the name map**, with the public capability (unit, eta) laws and
  the universal rule simulation (`checkedChangedAssociation_values`; a changed definition denotes its
  pulled-back value through its row, by `StrongInstalledModel.theorem_eq`);
- every original Lean declaration of the input is installed as its exact export or through a
  lowering receipt.

`StrongCone'.row_equations` is W+'s `model_equations` for the cone: the rows hold in every strong model
of the same target. What is weaker than §1.2: the source model is a value model with the capability
and rule laws, not an `EnvModelM` (no annotations, graded readings, towers or native Nat laws are
pulled back). `StrongCone.sound` is unchanged and still decides every cone without a changed constant.
Cones that reach a changed inductive block, an image recursor or a header matched through a type row
are not decided here: their rows fail the existing type, capability or recursor checks (S+b).

### 1.6 L1: Theorem 4.2 at Pass 1's level

The Pass 1 result is a family of theorems about the executable functions in
[`Ix/Compile/Canon`](../Ix/Compile/Canon), assembled in
[`Ix/CompileCert/Canon.lean`](../Ix/CompileCert/Canon.lean). In the statements below, the source
is the finite block/component presented to those functions, references and external addresses
are supplied by their environment, and a successful result is the actual return value of the
function. The result covers these clauses:

| Clause | Statement at this level | Principal theorem names |
| --- | --- | --- |
| Dependency components | The returned components are SCCs of the supplied block-restricted reference graph; their condensation is acyclic. The graph traversal has sufficient fuel. | `condensation_scc`, `condensation_acyclic`, `condensation_isSome`, `sccsOf_scc`, `blockComponents_scc`, `blockComponents_acyclic`, `blockComponents_ok`. |
| Comparison | At a fixed class context the pure comparator satisfies `TotalPre` on its successful-comparison domain: orientation and transitivity of successful comparisons. The fresh-cache comparison agrees on component entries satisfying its name hypotheses. | `constOrd_total`, `compareFresh_total`, `compareFresh_eq`. |
| Refinement | A successful result partitions the members into the coarsest consistent classes. Refinement succeeds when comparisons of distinct members succeed at every context. | `sortClasses_coarsest`, `sortClasses_ok`. |
| Seed and member order | With the name-hash seed, permuting the input members gives the same result. More generally, rule sets agreeing on levels and tie-breaks give the same ordered classes as sets; member order inside an equal class may differ. | `sortClasses_perm`, `sortClasses_setEq`. |
| Renaming and collapse | A renaming satisfying the stated reference/name relation preserves the ordered classes as sets. Collapsing equal classes has the specified quotient behavior. | `sortClasses_rename`, `sortClasses_collapse`, `sortClasses_collapse_single`. |
| Block driver | A successful `canonBlock` satisfies its component specification. Reordering members or declaring a component separately preserves its corresponding classes under the stated conditions. | `canonBlock_spec`, `canonBlock_coarsest`, `canonBlock_member_order`, `canonBlock_separate`. |
| Nested discovery and ownership | Expansion keeps originals first, appends auxiliaries in discovery order and records each auxiliary's discovering owner. The canonical nested component uses that expansion. | `expand_spec`, `expand_owner`, `componentNested_discovery`, `canonBlock_nested_discovery`. |
| Nested positions and evaporation | Every canonical auxiliary position is reached by a source position; each mapped position satisfies the signature-matching relation. Evaporation changes exactly the specified flags satisfying `Evaporates`. | `computePerm_spec`, `computePerm_onto`, `computePerm_some`, `evaporate_spec`, `canonBlock_evaporated_perm`. |
| Name maps | Members, suffixes, constructors and nested positions receive the specified mappings, including the specified absent/outside cases. | `cliqueNameMap_spec`, `blockNameMap_member`, `blockNameMap_suffix`, `blockNameMap_ctor`, `blockNameMap_nested`, `blockNameMap_other`, `nestedVal_aux`, `nestedVal_evaporated`, `nestedVal_outside`, `nestedVal_none`. |
| Definition and theorem cliques | The clique classes have the stated refinement/order properties; the theorem-statement ordering has its specified form. | `cliqueClasses_coarsest`, `cliqueClasses_ok`, `cliqueClasses_perm`, `cliqueClasses_setEq`, `statementOrder_spec`. |

These clauses retain the hypotheses in their individual declarations. In particular:

- `PreOn` and `TotalPre` describe comparisons that return `.ok`; they do not establish that
  every comparison succeeds. Refinement success has the separate comparison-success premise
  stated above.
- `AddrCongr` requires the external address lookup to answer alike for names equal under the
  implementation's `==`. `NameInj` requires component member/constructor names to identify their
  entries under that equality; `KeysDistinct` requires the relevant keys to be pairwise distinct
  under it. At this source version, `Ix.Name`'s `==` compares cached hashes. These are explicit
  conditions, not consequences of constructing a name with a hashing constructor.
- The block results use `NodupB` and `EnvWF`: the relevant keys are distinct, environment queries
  return declarations bearing the queried names, and an inductive's listed constructors have
  the specified names and owner. Successful-run clauses also retain their success equations.
- Comparator/refinement clauses use `portFixes = true` where stated. Exact seed-permutation
  equality uses `.byNameHash`; the nested-order results use `.discovery`. Renaming and collapse
  retain their term/reference relations, rather than allowing an arbitrary replacement of
  names or universe parameters.
- `refsConst_sound` needs no collision-free premise. Its completeness theorem uses
  `ConstHashCons`, built from `HashCons`: equal cached hashes of subterms imply equality of
  those subterms. This is a collision-freedom condition, stronger than consistent construction
  of cached hashes. The SCC statement about the supplied reference graph and the statement
  that this graph contains every syntactic occurrence are therefore distinct.
- The block name-map clauses use `NameMapKeys`, which bounds nested positions and separates
  member-phase keys, nested-position/suffix keys, and the two families under `==`.

None of these hypotheses is a new axiom: theorems quantify over them and the audit preserves
that fact. Applying the clauses to an arbitrary successful production compilation still needs
the corresponding source/runtime invariants. This result does not prove invariance of the
emitted declaration under the choice of representative beyond Pass 1, invariance under arbitrary
universe respelling, the equality of the auxiliary generator with the proved expansion, or the
complete compiler's block/output contract.

### 1.7 Remaining general compiler proof obligations

The per-output W/W+/S decisions above remain useful independently of a general compiler proof.
The remaining layers concern all inputs in the compiler theorem's original domain, not only
the libraries or fixtures which pass a gate:

| Layer | Obligation still needed for the complete compiler theorem |
| --- | --- |
| L2: canonical blocks and images | Prove totality of image construction on `Dom`, the original compiler theorem's domain. Connect production expansion and source/reference/name invariants to the canonical specification; prove the generated inductive, constructor and recursor/image declarations have the required syntax, typing and value behavior, including nested and mutual cases. |
| L3: rewriting and cliques | Establish the optimizer, image traversal, projection/recursor operations and clique transport's typing and value preservation; discharge the required substitution, telescope and recursion invariants at their actual call sites. |
| L4: composition and emission | Prove that the Lean compiler is total on `Dom`, every source name is faithful, and models pull back. This requires total generators and composition of the pass results through the production driver, ownership/name maps and emitted records, including failure behavior and the output contract. |

Individual lemmas in these layers do not make the layer complete. In particular, the general
changed-block meaning obligation in §2 is not discharged by an accepted W+ changed-block match
or by the value-level S check for the cones §1.5 supports. The end-to-end theorem also needs the
runtime refinements and invariant bridges used to apply the Pass 1 clauses above.

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
| value-level S association (`decideStrongCone'`, M7 S+a) | the value-level pull-back of §1.5, the changed definitions through their rows | decided; `StrongCone'.sound`, `checkedChangedAssociation_values`, `checkInstalledDefinitionsRows_sound` proved in the lane; the row names are an untrusted hint |

Trusted, outside the proofs: the host `Lean.Environment` the source is read from (as for every
use of `captureCone`); that `directExport`/`exportSourceExpr` is the intended reading of a Lean
declaration (erasing binder names, binder infos and `mdata`; universes canonicalised under the
proved guard); that a theorem the certifier lists as a lowering witness was accepted by Lean's
kernel; for W+, that Lean's `c.eq_def` is `c`'s unfolding equation (the relation checks that it is an
equation about `c`), for the members certified by the `equations:eq_def` route only (a member with an
accepted value row has `c = v` checked instead; the run lists the others in `<prefix>.values.tsv` and
its `V:` line) and, pending the general proof in §1.7, that the transformation of a changed block
preserves the meaning of its types; the Lean runtime that executes the decisions. That runtime includes, since M5 WP-B,
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

The positive verdict is evidence for the accepted decision's theorem. The other verdicts
explain why this run did not obtain that evidence; they are not four grades of a correctness
proof.

| Verdict | Reading |
| --- | --- |
| `certified` / `S-certified` | The corresponding association or cone was accepted. Read the route or cone cause to identify W, W+, strong S or value-level S. |
| `unsupported` / `S-unsupported` | A named source/reader class or route is outside this decision's domain, or a declared resource limit prevented a decision. The cause distinguishes these cases. |
| `blocked` / `S-blocked` | A required declaration or cone member lacks the needed verdict; the cause identifies the dependency. |
| `rejected` / `S-rejected` | A required check failed. This is a diagnostic to investigate, not an independently proved counterexample to compiler correctness. |

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

The strong cones decide only the constants W certifies by the `direct`/`raw` routes. A constant
certified by a W+ route (a theorem or equation row, a type row, a changed block) is put in no strong
cone. After those cones, S by default decides the W+-route constants outside a changed inductive
block at the value level (§1.5): a theorem by its statement; a definition by an `equations:` route
with a value row. Together with the constants left S-blocked by them, they form **one value cone**
(each root on its own cone if that one is refused). A member is then **S-certified** with the
cause `value cone <root>` (the strong verdicts keep `cone <root>`). What stays out has a class: a
W+-route constant over a changed inductive block (a member of a changed block, an image recursor,
a header matched through a type row) is S-unsupported `certified by a W+ route over a changed
inductive block (…); S for it is S+b`; a transported clique member W certifies by its `eq_def` only is
S-unsupported `transported clique member certified by its eq_def only (no value row); S for it needs
package V`; what reaches either is S-blocked by it with its class. The in-process control
`Config.strongChanged := false` disables the value-level stage: all W+-route constants then stay
S-unsupported (`certified by a W+ route; S for changed constants is M7`), and users stay S-blocked.

## 4. Running it

```
lake build compile-certify
compile-certify (--file <source.lean> | --modules <A,B,...>) <env.ixe> <out-prefix> \
  [--budget <nodes>] [--workers <n>] [--row-budget <ms>] [--refold] [--no-value-rows] [--explain <name>]* [--receipts-only] \
  [--strong | --strong-only] [--strong-roots <A,B,...>] [--strong-every <k>] \
  [--strong-max-cone <n>] [--strong-tasks <n>] [--strong-plan] [--strong-global] [--explain-global] [--strong-changed]
```

- `--file` elaborates the file as `ix compile` does (`Benchmarks/Compile/CompileInitStd.lean`,
  `Benchmarks/Compile/CompileMathlib.lean`); `--modules` imports modules.
- `--budget` bounds the distinct `Expr` objects of one declaration (type, value and rule right-hand
  sides, each counted separately; default 2^28): a declaration over it is unsupported (`expression
  DAG over budget`). `<prefix>.sizes.tsv` lists every declaration with at least 4096 objects with its
  tree size (computed on the DAG): the tree size is reported, not budgeted.
- W writes `<prefix>.tsv` (one row per source name present in the artifact: name, address, verdict, cause),
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
- S includes value-level certification of changed constants by default (§1.5, §3), after the
  strong cones: W+-route constants outside a changed inductive block and the constants left
  S-blocked by them form one value cone, each root on its own if it is refused. The JSON records
  `valueCertified`. `--strong-changed` remains an alias enabling `--strong`; no extra flag is needed.
- For a normal W/W+ run, exit 0 requires something certified, nothing rejected and no refused
  projection receipt. With S, it additionally requires something S-certified and nothing
  S-rejected. `--strong-only` skips the global W conditions and applies the S conditions to
  the cones it runs. The diagnostic modes differ: `--receipts-only` exits 0 when its receipt
  census has no refusals, without running a W or S association; `--strong-plan` returns 0
  from its planning path without an S verdict. The overall planning command still retains
  the W exit code unless the global W run was skipped.

For example, after building the executable, W+ for the benchmark input can be run as:

```sh
.lake/build/bin/compile-certify --file Benchmarks/Compile/CompileInitStd.lean \
  initstd-a3.ixe out/initstd --workers 16
```

Add `--strong --strong-global` for both S routes, with the large-stack setting
above. For a library exposed by imports, use `--modules A,B`; use `--file` when its elaborated
source file defines the intended environment. The Ixon input must correspond to that source
environment. Keep the command, toolchain, source and executable revisions, input digest, logs
and all output tables together when comparing runs.

The historical Mathlib W+ command in §6 used `--workers 16 --budget 16777216`. Its peak RSS was
about 84 GB; the Init+Std commands used about 8–11 GB. These are observations on those inputs
and binaries, not resource bounds. On a shared benchmark machine, reserve a Mathlib-scale run
and run only one such producer at a time. A lower `--row-budget` or `--strong-max-cone` can
change coverage to unsupported/blocked; it does not turn an unperformed check into an accepted
one. `--strong-plan` estimates cover structure and runs no S decision.

The lane's own gate is `lake run check-cert` (the audit, the strict build, the fixture checks, the
certifier on the fixture with and without `--strong`).

The source-named Nat pins are regenerated (after a toolchain change, say) by
`lake build source-pin-gen && lake exe source-pin-gen Ix/CompileCert/SourceNatOpPinData.lean`: the
generator loads the environment of `IxC.Kernel.PinGen.Certs`, generates the variant, installs each
operation's source cone through the normalised source installation with it (and refuses it without
pins), and writes the file only if every step passed.

## 5. Reading the output tables

All files share the chosen output prefix. W's `certified` word covers both the original W and
W+; the cause field supplies the route. Both S routes similarly use `S-certified`, distinguished
by `cone <root>` versus `value cone <root>`. The implementation of the report is in
[`Certifier.lean`](../Ix/CompileCert/Certifier.lean) and
[`StrongCertifier.lean`](../Ix/CompileCert/StrongCertifier.lean).

The per-name universe is the intersection of the loaded Lean environment and the artifact's
name map. Source names absent from the artifact are counted separately in JSON `notInArtifact`;
they receive no W or S verdict, and that count does not itself make the command fail. Check
`notInArtifact` alongside the verdict totals before claiming coverage of the whole loaded
source environment.

| File | Columns or fields and their interpretation |
| --- | --- |
| `.tsv` | `name`, `address`, `verdict`, `cause`: one row per source name present in the artifact. For a certified row, `cause` is the direct/raw/theorem/equations route, possibly with a type-row or changed-block suffix. Otherwise it describes the refusal or dependency. |
| `.classes.tsv` | `verdict`, `class`, `count`: groups negative verdicts by cause class; positive groups have `class = route: <route>`. |
| `.rows.tsv` | `owner`, `row`, `ms`, `verdict`: proposed W+ support rows and their pre-screen results. An accepted pre-screen is not the final association or support-fold verdict. A refused proposal may be unnecessary if another route succeeds. |
| `.values.tsv` | `name`, `encoding`, `value row`, `verdict`, `route or cause`, `detail`: transported clique members, whether a value row was generated/exported/accepted, and the final route. Written when such members were considered; inspect the residuals as well as the accepted count. |
| `.ixonly.tsv` | `name`, `address`, `kind`: names present in the artifact but absent from the loaded Lean environment. `_ix` means a name component starts with `_ix`; it is a reporting category, not a certification theorem or a list of omissions. |
| `.sizes.tsv` | `name`, `dagNodes`, `treeNodes`: declarations with at least 4,096 distinct expression objects. The budget uses `dagNodes`; the expanded `treeNodes` count is diagnostic. |
| `.proj.tsv` | `name`, `kind`, `structures`, `W verdict`: the raw-projection census. This does not replace the lowering-receipt result. |
| `.receipts.tsv` | `name`, `kind`, `class`, `lowering equation`, `elimination level`, `Lean kernel`, `receipt`, `cause`: the witness check and the lane's lowering-recipe check separately. Both must accept a required receipt. `.receipts.statements` records the witness statements and universe telescopes. |
| `.json` | `names` counts the source/artifact intersection; `notInArtifact` counts source names absent from the artifact. `perName` and `perAddress` give verdict totals, alongside `classes`, `routes`, `imageClaims`, `equationRows`, `ixOnly`, `valueRows`, `rawProjections`, `projectionReceipts`. `equationRows` separates proposed, folded and over-budget rows; `valueRows.residual` lists members relying on `eq_def` or not certified. |
| `.strong.tsv` | `name`, `W verdict`, `S verdict`, `cause`: inspect the cone/value-cone distinction. W may say `not run` in `--strong-only` mode; every accepted cone still performs its own W association. |
| `.strong.cones.tsv` | `root`, `roots`, `members`, `records`, `support`, `witnesses`, `ms`, the five stage columns (`ms input`, `ms admission`, `ms W`, `ms installation`, `ms strong`), `outcome`, `class`, `culprit`. A batch's `roots` may exceed one; `members` counts its union. The stage named `ms strong` also holds the value check's time for a value cone. |
| `.strong.classes.tsv`, `.strong.json` | Negative S classes; mode, cone counts, `coneMsTotal`, `notReached`, `wPlusRoute`, `valueCertified` and per-name totals. `valueCertified` counts newly certified members of accepted value cones, which can include users of changed constants. |
| `.strong.plan.tsv`, `.strong.plan.names.tsv` | Proposed cover order, roots, member counts, first coverage and cumulative coverage; each name's proposed first cone or reason for none. These are planning outputs and contain no S verdict. |

Read `perName` for a statement about source declarations. Different source names can share an
address, so `perAddress` is smaller and is not a declaration count. Its implementation retains
the first non-certified verdict encountered at an address, if any; it is not a severity maximum
over all aliases. Use the per-name rows to resolve mixed verdicts on an address.

For a concrete historical example, the Init+Std `is5` run in §6 certified the
`BVExpr.bitblast.goCache_Inv_of_Inv` family by `theorem`. This says that the certified reader's
theorem statement matches the source export; it does not say the compiled proof term equals
Lean's proof term. In that same run, all four proposed reflexivity rows for the transported
definition members were refused, yet all four members were certified by `equations:eq_def`
using the carried equations. Thus a refused `.rows.tsv` entry need not make its owner's final
`.tsv` verdict rejected. It also does not supply §1.5's value equality: an unfolding equation
alone is insufficient for that route. A later accepted `equations:value-row` must be read with
its final association/support fold and value-row record, not inferred from this older run.

For S, first check `mode` and `notReached`; a roots/sample run makes no verdict for unreached
W-certified constants. Then inspect `S-unsupported` and `S-blocked`, even if `S-rejected = 0`.
The historical indexed global run in §6.1 has no rejections but leaves 16 W+ constants
unsupported by that route and 25 of their users blocked. The value route needs its own
accepted decision to cover them; §6.2 records that later Init+Std decision. For a certification
run, exit code 0 means its applicable success conditions in §4 hold;
the diagnostic modes have the separate exit conditions listed there. Neither implies that
every source name is present and certified, every W+ definition has a value row, or every
W-certified name has an S verdict.

## 6. Library evidence

### 6.1 Historical runs from 2026-10-07

The following completed certification runs used Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. They are measurements of the listed certifier
revisions and a3 artifacts, not of every later revision. The four counts are **certified /
unsupported / blocked / rejected**, per source name present in the artifact; an S row reports
S verdicts.

| Input and decision | Certifier source | Counts | Wall time of command | Peak RSS reported by `time -v` |
| --- | --- | --- | --- | --- |
| Init+Std-a3 W+, `is5` | `a2251806c53786c0e00be486825d4e6dd5e82c92` | 116,768 / 926 / 0 / 0 | 5:25.63 | 7,984,884 kB |
| Mathlib-a3 W+, `ml5` | `a2251806c53786c0e00be486825d4e6dd5e82c92` | 778,612 / 4,461 / 42 / 0 | 3:08:53 | 84,053,884 kB |
| Init+Std-a3 W+ then indexed S with a global cone, `isG4` | `ed5ea197fa93ba31b3b05d16e2b2dcc852e2b83c` | S: 116,727 / 942 / 25 / 0 | 13:44.72, including W+ | About 10.6 GB |

Input identity:

| Artifact | SHA-256 |
| --- | --- |
| Init+Std-a3 | `a2e22ee7f8d0fcf0d607047dda7d83749f20886f2d03f1cbaf2ede3a7d1ba676` |
| Mathlib-a3, 2,376,572,399 bytes | `d0427adf7b995f7f48c6fe5fa069c5d3a3d5c10c6f061425729e87339f6bf6db` |

Both W+ runs used the same sealed executable, SHA-256
`f07935568376dd36c4da0fd7deb4739db80b30e3d499bb44b79fbac1d37a200a`, with 16 workers. The
Init+Std run used the default 2²⁸-object size budget; the Mathlib run used 16,777,216 objects.
The indexed S executable's SHA-256 was
`7c8d6bcc362d4e9a18358084e695797e7fe580abff37c9586fe75529876b5194`.
The reports record these different counting units:

| W+ run | Records admitted by `checkBytes` | Declarations from admission | Final certified source names | Final certified addresses | Support rows folded |
| --- | --- | --- | --- | --- | --- |
| `is5` | 99,384 | 96,252 | 116,768 | 98,492 | 0 |
| `ml5` | 684,845 | 665,888 | 778,612 | 678,352 | 465 |

Init+Std's 926 unsupported names were reader exclusions: 835 `partial`, 75 `unsafe`, eight
unsafe axioms and eight unsafe opaque declarations. Its certified routes were 116,752 direct,
12 theorem and four `equations:eq_def`. Mathlib's completed run had 42 rows over the pre-screen
budget; 21 declarations were unsupported only for missing those rows, and 42 users were
blocked. It admitted 53 image claims and accepted all 67 required projection receipts. None
of those totals asserts general correctness of every possible image transformation.

The S row is the strong route of §1.2, before the changed-value route of §1.5. Its global cone
contained 116,727 members and took 540,413 ms: input 9,759; admission 191,726; W 24,900;
installation 299,820; strong check 8,571. The 942 unsupported names comprise the 926 reader
exclusions and 16 W+ constants outside that route; the 25 blocked names are users of those
constants. There were no unreached W-certified names. This table does not claim a full-library
S+a measurement of the later certifier source or a full-library Mathlib S result.

Repeat evidence is scoped to the recorded outputs: the same W+ executable's second Init+Std
run (`is6`) produced byte-identical per-name verdicts; the four indexed-S global runs produced
the same per-name S table, and the last two used the gated `ed5ea197` executable. The listed
Mathlib W+ result is one run. This is not a statistical performance study. The `is5` run shared
the 64-thread machine with a gate and Mathlib loading (observed load 26–52); the indexed `isG4`
run was recorded alone. Do not treat differences between those wall times as a controlled
comparison, or extrapolate a forecast into an unmeasured library verdict.

### 6.2 Completed runs from 2026-10-08

The later completed records below use the same Lean toolchain and the same a3 artifact
hashes listed above. Counts retain the same certified / unsupported / blocked / rejected order.
The Init+Std row uses the default value-level stage; the Mathlib roots row is a bounded
diagnostic and does not cover the whole library.

| Input and decision | Certifier source | Counts and coverage | Wall time of command | Peak RSS reported by `time -v` |
| --- | --- | --- | --- | --- |
| Init+Std-a3, W+ then global S with the default value stage | `cfe49cb95ee8f0f953e253a4a47a50181dbc390f` | Both W and S: 116,768 / 926 / 0 / 0; all 117,694 names accounted for; `notReached = 0` | 12:00.92, including W+ | 10,610,344 kB |
| Mathlib-a3, complete W+ | `fc058f9357da4e14fd3ff9e4d506f417faf7957a` | 778,675 / 4,440 / 0 / 0; all 783,115 names accounted for | 53:43.70 | 80,292,724 kB |
| Mathlib-a3, exact 780 requested S roots (`--strong-only`) | `fc058f9357da4e14fd3ff9e4d506f417faf7957a` | S: 83,633 / 4,442 / 0 / 0; 695,040 names not reached | 21:19.30 | 45,796,756 kB |

The Init+Std command used `--budget 16777216 --workers 16 --row-budget 60000 --strong
--strong-global`, without `--strong-changed`. Its value cone certified 41 additional names;
four transported definition members had accepted value rows. `notInArtifact = 0`. The
complete per-name W and S maps and non-timing result fields matched the earlier explicit-flag
reference. This verifies the default-on route on this input, without establishing the
remaining general compiler theorem. Its executable SHA-256 is
`4e07b244a80aa520d5d819ebe1c8cd3006bd0d6fb1b757a5f0a31c5eb5c73e97`;
the retained output prefix is `out/sa-default-runtime-20261008t1455z/result`.

The complete Mathlib W+ run used the same size budget, 16 workers and a 60,000 ms row budget.
It folded 574 support rows, with zero rows over budget or left running, and accepted all 67
required projection receipts. Its 4,440 unsupported names are reader exclusions: 3,720 partial
definitions, 672 unsafe definitions, 19 unsafe inductives, 15 unsafe opaques, eight unsafe
axioms and six names whose records were not selected. `notInArtifact = 0`; nothing was blocked
or rejected. The executable SHA-256 is
`ac9ae09ca06b270acdb6408d31ba7d4416b6a579f87caefa9f7a5bbb7c8992a0`;
the retained output prefix is `out/certqueue-mathlib-w-20261008t0630z/result`.

The 780-root diagnostic used that same executable with `--strong-only`: its W column says
`not run`, and each executed cone performs its own W association. It executed 778 cones,
all accepted; two requested roots exceeded the 50,000-declaration per-cone budget and were
not executed. Those two resource refusals account for the increase from 4,440 to 4,442
unsupported names. Coverage was accounted against the complete W+ reference; the diagnostic
did not rerun global W. The 695,040 unreached names remain outside this diagnostic's S claim.
The retained output prefix is
`out/certqueue-sprobe-historical780-20261008t1720z/result`. No completed full-library Mathlib S result
is claimed by these records.

These are individual correctness-gated observations on a shared machine. The runs have
different scopes and revisions; their times do not establish an isolated speedup or a
statistical performance comparison. Per-record artifact checking, the complete W+ decision
and the S model checks are different operations and must be timed and reported separately.

## 7. Known limits of the S route (2026-10-08)

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
- **Changed constants** (certified by W+, §3) are outside the strong cones: their per-cone W association
  and strong checks compare the installed source with target rows that are, for a changed constant, not
  its Lean declaration's export, and the strong conclusion cannot hold above a changed definition (§1.5).
  S decides them at the value level by default (§1.5) except two classes: a changed
  inductive block, an image recursor or a type row (S+b, M7), and a transported clique member certified
  by its `eq_def` only, which has no value row (package V, M7).
- **Proof-field projections of mutual or nested structure-likes** (theorems in Lean 4.34.1): refused by W
  before W+; W+ certifies them by the `theorem` route (the `LoweringDefs` fixture's `Sized.ok`), so S
  treats them as changed constants (above): at the value level by default.
- **Cost.** Source export, model proposal, correspondence and normalisation run on indices and
  the DAG. Admission and the certified fold dominate the measured global-cone run in §6;
  those measurements are tied to their certifier revision and input. The per-cone cover
  remains the fallback when a global cone is unavailable or refused.
  `--strong-max-cone` bounds the cone size of the cover; larger cones are S-unsupported (`cone over budget`) and their users S-blocked, never rejected.
