# Compiler passes and output contract

This guide describes the compiler at source revision
`0404af52dc08b1a4db96d85d9895478da504de96` (Lean 4.34.1), as reviewed on
2026-10-08. Its compiler implementation was tested at `881c2b86`; its certification
configuration includes the separately tested default value-level S stage from
`cfe49cb9`. Later documentation commits do not create new runtime results. This
guide separates implemented transformations, their intended contract, checked
theorems and finite regression evidence.

Section 11 states what each output name and record means. The
[certification guide](compiler-certification.md) states what W, W+ and S establish
for an accepted output, with their hypotheses and trust boundaries. The
[Rust compiler guide](compiler-rust.md) maps the second implementation and its
remaining differences; the [gate guide](compiler-gates.md) gives the checks,
records and commands. The [format guide](Ixon.md) defines the representation.

## 0. Status

Both compilers run Pass 3. The image rewrite, definitional optimizations,
proof-justified canonical forms and clique transport are wired into the driver.
The old call-site surgery has been removed. An unset `IX_PASS3` selects the current
compiler; `images` is a deprecated spelling that warns, and `off` or any unknown
value is an error. See [Lean mode validation](../Ix/Compile/Pass/Names.lean) and
[Rust mode validation](../crates/compile/src/compile/pass3/names.rs).

| Area | Implemented behavior | Evidence and remaining boundary |
| --- | --- | --- |
| Pass 1 | Components, classes, order, nested discovery, cliques and name maps. | L1 proves the clauses summarized in §3, under the actual name, address, environment and success hypotheses. |
| Pass 2 | Canonical recursors and auxiliary families, with one constant per auxiliary. | Generator and kernel/round-trip fixtures exercise the implementation. General source, freshness, generated-family and runtime correspondence obligations remain. |
| Pass 3 | Images under Lean names; occurrence rewriting; canonical forms under reserved names; clique transport. | Dedicated image, pass, clique, ownership, changed-set, scheduling and parity suites. General typing and value-preservation proofs remain incomplete. |
| Composition | Source selection, dependency scheduling, claims, serialization and reference-closure packing. | Exact reference comparisons and closure/schedule tests on their stated inputs. No general end-to-end compiler theorem. |
| Per-output certification | W, W+, S and value-level S for supported changed constants; the value stage is included in S by default. | Accepted decisions have the theorems in the certification guide. They do not silently discharge the general compiler proof. |

The historical library classification was: Init+Std has no changed
inductive block and five transported cliques; Mathlib has six changed inductive
blocks and nine transported cliques. No proof-justified O7–O12 form was reported on
those library runs. These classifications retain the provenance of the earlier
measurements. The later combined compiler's reference-byte checks (§7.3) do not
redate every historical diagnostic or make the counts universal under future
toolchains. The tracked [changed-set reader](../Ix/Compile/ChangedSet.lean) and
[clique record](../Ix/Compile/Pass/Cliques.lean) define the corresponding records.

For certification, `--strong` includes the supported value-level changed checks;
`--strong-changed` remains an enabling alias. A programmatic
`Config.strongChanged := false` is the narrower direct/raw-only control, while an
invocation without a strong option runs W. These choices do not select a different
compiler. See [the current configuration](../Ix/CompileCert/Certifier.lean) and
[certification §1.5](compiler-certification.md#15-s-for-changed-constants-at-the-value-level-ixcompilecertstrongchangedlean-m7-sa).

### 0.1 The governing principle

Faithfulness comes first. When a canonical presentation cannot be recovered from
Lean's elaborated term by a supported transformation, keep the faithful form and
record the reason. A successful kernel type check alone does not show that a
different well-typed value preserves the source's meaning. Conversely, a known
non-canonical address does not make a faithful constant incorrect.

The fallback is the faithful form when that form can be compiled. A named refusal
is the result when the compiler cannot safely produce it; a refusal is not a
canonicalization success. Callers adapt to a compiled block. Their existence must
not change how the block itself is compiled (§6.3).

### 0.2 Reading the evidence

**Implemented** means the cited code runs. **Proved** names a checked Lean theorem
and retains its hypotheses. **Tested** identifies a finite suite or a source-pinned
measurement. **Argued** is a design argument with an outstanding proof obligation.
None of these words substitutes for the others.

L1 is the Pass 1 theorem family assembled in
[`Ix/CompileCert/Canon.lean`](../Ix/CompileCert/Canon.lean). The complete map and
the interpretation of its hypotheses are in
[certification §1.6](compiler-certification.md#16-l1-theorem-42-at-pass-1s-level).
The remaining general L2–L4 obligations are in
[certification §1.7](compiler-certification.md#17-remaining-general-compiler-proof-obligations).
In particular, constructor-consistent cached hashes do not imply collision freedom.
The proof's hash/name hypotheses and the runtime memo assumptions must be stated
where they are used.

The original general targets remain in force, beyond the conditional L1 clauses:

| Target | Outstanding statement |
| --- | --- |
| Representative independence (§3.5(iv)) | The canonical declaration of a class is invariant under the choice of representative, including the generated/emitted declaration beyond the Pass 1 class result. |
| L2 images, Theorem 4.3 | Image construction succeeds on every block of the existing `Dom`; for every assignment satisfying the canonical blocks' `IxBlockLaws`, each image denotes, belongs to the translated source recursor type and satisfies the source rules, including the nested cases. |
| L3 passes, Theorem 4.5 | The rewrite and passes are total on their stated `Dom`; each optimization preserves denotation under its side condition, and clique transport preserves provability of the restated obligation. |
| L4 compiler, Theorem 4.6 | The Lean compiler is total on `Dom`, every name is faithful and models pull back. Its own auxiliary generators must be proved total, with the semantics of the recursor families, `casesOn`, `recOn`, `below`, `brecOn`, `IndPredBelow`, `noConfusion` and `sizeOf`. |

Here `Dom` is the existing source domain of the general compiler theorem, not a
new restriction to tested libraries or an abbreviation for “the current bounded
program returned success.” Necessary internal freshness, closure, fuel and
runtime invariants must be derived for that domain. Conditional helper lemmas,
finite gates and per-output certification do not replace these targets.

## 1. The pipeline and the convention

### 1.1 The passes

The input is the prepared Lean declarations and their reference/recursion data.
Source selection keeps whole source units where required by
[`EnvScope`](../Ix/EnvScope.lean); it also supplies support referenced by generated
terms. The output is an `Ixon.Env`, its names/metadata/hints and, for the CLI,
the diagnostic changed-set file. The implementation is organized as follows.

| Stage | Input and result | Current modules |
| --- | --- | --- |
| P1a: components | Reference graph → strongly connected components. | [Canon/Graph](../Ix/Compile/Canon/Graph.lean), [Canon/Block](../Ix/Compile/Canon/Block.lean). |
| P1b: classes and order | Component and dependency addresses → ordered classes and representatives. | [Canon/Order](../Ix/Compile/Canon/Order.lean), [Canon/Classes](../Ix/Compile/Canon/Classes.lean). |
| P1c: nested members | Canonical component → discovery expansion, source-position map and evaporation flags. | [Canon/Nested](../Ix/Compile/Canon/Nested.lean), [Canon/Block](../Ix/Compile/Canon/Block.lean). |
| P1d/e: cliques and names | Member specifications → classes/order; block/clique positions → name map. | [Canon/Clique](../Ix/Compile/Canon/Clique.lean), [Canon/NameMap](../Ix/Compile/Canon/NameMap.lean). |
| P2: auxiliary generation | Canonical inductives → recursors, `casesOn`, `recOn`, `below`, `brecOn` and associated families. | [AuxGen](../Ix/AuxGen), [AuxGen/CompileAux](../Ix/AuxGen/CompileAux.lean). |
| P3a: images | Source recursors and canonical recursors → closed image declarations. | [Image](../Ix/Compile/Image), [Pass/ImageView](../Ix/Compile/Pass/ImageView.lean). |
| P3b: translation | Source occurrences → image-based baseline and inline provenance. | [Pass/Translate](../Ix/Compile/Pass/Translate.lean), [Pass/SideCar](../Ix/Compile/Pass/SideCar.lean). |
| Clique hook | Recovered clique → transported members, helpers or a recorded faithful fallback. | [Clique](../Ix/Compile/Clique), [Pass/Cliques](../Ix/Compile/Pass/Cliques.lean). |
| Occurrence/unit optimizations | Supported baseline shapes → definitional rewrite or separate proof-justified form. | [Pass/Opt](../Ix/Compile/Pass/Opt), [Pass/Driver](../Ix/Compile/Pass/Driver.lean). |
| Emission and fold | Compiled block outputs → sharing, claims, merged environment and serialization. | [CompileM](../Ix/CompileM.lean), [CompileDriver](../Ix/CompileDriver.lean), [Sharing](../Ix/Sharing), [Ixon](../Ix/Ixon.lean). |
| Diagnostics | Final driver state → changed-set JSON. | [ChangedSet](../Ix/Compile/ChangedSet.lean). |

These are functional stages, not a claim that the compiler materializes a separate
whole environment after each row. Occurrence optimization is fused with rewriting;
the clique hook and unit passes are coordinated by `prepareBlock`. There is no
`Pass/Emit.lean` or standalone `Compile/Fold.lean` implementing an additional stage.

### 1.2 The five-part docstring

A pass's contract should state five things:

1. Its input shape and exact output, including naming and universe handling.
2. Faithfulness: conversion or the precise propositional equality required, with
   a theorem reference where proved and an explicit obligation otherwise.
3. Canonicity: which presentation differences it removes and which it retains.
4. The recognized side condition and the faithful fallback or refusal.
5. The non-canonical causes and the tests that exercise both firing and decline.

The docstrings in [Pass/Opt](../Ix/Compile/Pass/Opt) follow this convention.
A paragraph headed “Faithfulness” is not by itself a formal proof.

### 1.3 Worked example: O1, permutation pass-through

Suppose Pass 1 changes a block only by permuting its members and the recursor image
has the selection form

```text
img(r) = λ ps ms mins is x. ρ ps ms[σ] mins[τ] is x.
```

At a full application of `r`, [O1](../Ix/Compile/Pass/Opt/O1.lean) emits the
canonical recursor application with those motive and minor permutations. For
`recOn` it uses the corresponding canonical `recOn`. Universe arguments come from
the image's instantiated recursor occurrence, not from a fresh guess about the
large-elimination level.

The conversion argument is β-reduction of the image wrapper. It removes the
permutation adapter without changing the baseline's value. The recognizer checks
the selection shape; when it does not apply, later passes or the image baseline
handle the occurrence. The pass does not infer a correspondence by equating binder
types alone: it reads the correspondence supplied by the image construction.

### 1.4 Pass order and the fixed point

The actual order is explicit in
[`Opt.Engine`](../Ix/Compile/Pass/Opt/Engine.lean):

```text
O1 → O11a → O2 → O3 → O4 → O6 → O8 → O7 → O9 → O10 → O12.
```

The first applicable pass wins at an occurrence. O11a deliberately precedes O2:
the specialized `sizeOf` result and the relocated-recursion result can both be
available there. O10 precedes O12 so equal handlers use the simpler collapse.
O5 is the universe-instantiation rule used by the passes, rather than another
entry in this list. O11b is a unit pass. Clique transport is a separate hook;
there is no later generic O13 occurrence pass in this engine.

`Translate.rw` rewrites the arguments before consulting the engine at a full
image-head application. If it declines, the image is instantiated and developed.
`engineN` bounds recursive optimization of calls synthesized by O2, and `engine`
uses a bound of 64. This is an implemented resource bound. The intended argument
that the generated relocation chain fits that bound is separate from a general
checked completeness theorem.

“Fixed point” here describes the intended normal form of this fused traversal;
it is not an implementation that repeatedly runs every pass over a whole term
until structural equality. Running arbitrary optimizations again over the
developed baseline would also lose the source occurrence that the recognizers
need. Any general idempotence/termination claim must cover the actual traversal,
its recursive O2 calls, fuel and fallback behavior.

The generic `RwState.opt?` callback can give a different answer with and without a
definition site. Its fallback retry remains meaningful. The production hookup
uses the ordered engine, allowing the specialized shortcut documented in
[`Translate`](../Ix/Compile/Pass/Translate.lean); this is not a contract that every
possible callback has that order.

### 1.5 The definitional passes as implemented

The following transformations target conversion with the image-based baseline.
Their source modules contain the shape checks and the conversion arguments;
the complete general semantic proof remains an L3 obligation.

| Pass | Supported shape and result |
| --- | --- |
| [O1](../Ix/Compile/Pass/Opt/O1.lean) | Permutation-only `rec`/`recOn`: canonical auxiliary with arguments permuted. |
| [O2](../Ix/Compile/Pass/Opt/O2.lean) | Split recursor: select component motives and adapt cross-component induction hypotheses by relocated calls. |
| [O3](../Ix/Compile/Pass/Opt/O3.lean) | `casesOn` without collapse: the canonical `casesOn`. |
| [O4](../Ix/Compile/Pass/Opt/O4.lean) | Selection-shaped `below`/`brecOn` family: select/permutate motives and handlers. Cross-field and changed `IndPredBelow` shapes can decline. |
| [O5](../Ix/Compile/Pass/Opt/O5.lean) | Instantiate the universe arguments read from the image, including a member gaining large elimination. |
| [O6](../Ix/Compile/Pass/Opt/O6.lean) | Selection-shaped `rec`/`recOn` for the supported change kinds. |
| [O11a](../Ix/Compile/Pass/Opt/O11a.lean) | Recognized split `sizeOf`: use the cross target's size instance instead of the generic relocated hypothesis. |

O2 and O11a share the source-minor helpers in
[`Ix/AuxSource.lean`](../Ix/AuxSource.lean). Retaining those helpers does not retain
the deleted surgery compiler. The minor correspondence, its source constructor,
field telescope and recursive target are actual recognizer inputs.

O11a emits references not necessarily present in the source `_sizeOf_N` body.
`prepareSizeOfScheduling` adds their producer edges at both aux-aware Lean driver
entries; `compileDecoratedConsts` can supply the already prepared source graph.
The addition is idempotent and does not rerun the source SCC partition. Rust has
the corresponding preparation. This is a scheduling dependency, not permission
to read an arbitrary later block.

When a `sizeOf` occurrence lacks the supported instance, telescope, cross-field or
minor shape, O11a declines to O2/the baseline and records the cause through
`declineCause?`. The wording “the constructor and minor type … cannot be read”
includes failure to place the minor in the source family; it does not mean the
minor expression is absent. The exact cause text is shared output evidence, not
a theorem hypothesis added to excuse arbitrary inputs.

### 1.6 The proof-justified passes as implemented

For these passes the intended equality is propositional, not conversion. The
implementation preserves the faithful baseline under the Lean name `c` and emits
the canonical form under `c._ix`. It records `PJ-FORM-<pass>` for `c`; ordinary
callers keep referring to `c`. The type of a dependency is not silently changed by
redirecting every reference to its `_ix` form.

`RwState.site` allows these occurrence passes only in a definition's value. Types,
theorem proofs and shared image expansions do not acquire a proof-justified
rewrite. With `inPlace := false` the traversal notes the firing and returns the
baseline. `compileCanon` rewrites the separate canonical definition in place and
includes its referenced helpers. See
[`Translate`](../Ix/Compile/Pass/Translate.lean) and
[`Driver`](../Ix/Compile/Pass/Driver.lean).

#### 1.6.1 The passes, their canonical forms and their proofs

| Pass | Canonical form | General equality obligation |
| --- | --- | --- |
| [O7](../Ix/Compile/Pass/Opt/O7.lean) | Collapsed `rec`/`recOn` with equal motives and minors per class. | Projection of the packed recursion equals the source component. |
| [O8](../Ix/Compile/Pass/Opt/O8.lean) | Canonical `casesOn` of a collapsed/lifted member. | Case elimination agrees on every constructor. |
| [O9](../Ix/Compile/Pass/Opt/O9.lean) | Split `brecOn` with a retyped/repathed handler. | Dictionary transport preserves the source handler's value. |
| [O10](../Ix/Compile/Pass/Opt/O10.lean) | Collapsed `brecOn` with one motive and handler per equal class. | The selected packed result equals the source result. |
| [O12](../Ix/Compile/Pass/Opt/O12.lean) | Projection of a shared pair-valued helper for unequal arms. | Each projection satisfies its source recursion. |
| [O11b](../Ix/Compile/Pass/Opt/O11b.lean) | `noConfusionType._ix` and its matching `noConfusion._ix`. | The paired canonical declarations implement the source distinction principle. |

These are implemented passes with regression controls, not a declaration that all
six general equality theorems are complete. The independent fixed-point lemma of
§5.2 is proved; it does not supply all of these obligations. The
[certification guide](compiler-certification.md#17-remaining-general-compiler-proof-obligations)
states the remaining general scope.

#### 1.6.2 Interaction with the clique hook

The clique hook runs before the ordinary occurrence rewrite at the block boundary.
Its canonical helper declarations are processed with the faithful rewrite policy;
they do not automatically receive an in-place O9/O10/O12 rewrite. Consequently a
fixture that exercises one of those passes in an ordinary definition is not
evidence that the pass fires inside a transported clique.

The passes are retained for the supported ordinary-definition shapes. Their
presence is no longer an open implementation choice. Extending their application
inside clique transport would require its own meaning argument and gates.

#### 1.6.3 Evidence

The tracked [pass fixtures](../Tests/Ix/Compile/Pass) and their runners compare
recognized canonical forms, faithful fallbacks, records and checker behavior.
The [gate guide](compiler-gates.md) distinguishes the ordinary tests from ignored
manual suites. A record of a non-canonical source name is expected when its
canonical form lives under `_ix`; it is not a failure to retain the source name.
No finite firing count proves the general equality obligations above.

## 2. Canonical form, defined

The following definitions specify the Pass 1 objects and the target representation.
Their established theorem clauses are in §3. The full emitted-output contract is §11.

### 2.1 Components (Def 2.1)

The reference graph has an edge `x → y` for an occurrence of `y` in `x`'s type,
value or recursor rules. It also records the declaration relationships used by
the graph: an inductive's constructors, a constructor's owner, recursor rule
constructors, and a projection's structure name. See
[`Canon.Expr`](../Ix/Compile/Canon/Expr.lean) and
[`Canon.Graph`](../Ix/Compile/Canon/Graph.lean).

Components are SCCs of the supplied graph. Within an inductive block this gives
the member graph restricted to its declarations and constructor dependencies.
The Tarjan traversal representative is not a canonical display key: the driver
uses `blockKey` (§6.1). Safe recursive definitions commonly elaborate to acyclic
definitions over an encoding constant, so a source recursion clique is not in
general a source reference SCC. It is recovered separately (§2.7).

`condensation_scc`, `condensation_acyclic`, `sccsOf_scc` and
`blockComponents_scc` prove the SCC properties of their supplied graph.
`refsConst_sound` needs no collision-free premise; `refsConst_complete` requires
`ConstHashCons`. Identifying the supplied graph with every syntactic occurrence
therefore has an additional explicit hypothesis. See
[`SccMain`](../Ix/CompileCert/Canon/SccMain.lean),
[`BlockComp`](../Ix/CompileCert/Canon/BlockComp.lean) and
[`Refs`](../Ix/CompileCert/Canon/Refs.lean).

### 2.2 Classes (Def 2.2) and the structural key

A partition of a component is consistent when members in each class compare equal
after in-component references are replaced by class positions and external
references by their supplied addresses. The classes are the coarsest consistent
partition. The lexicographic key in
[`Canon.Order`](../Ix/Compile/Canon/Order.lean) is:

| Kind | Key, after the kind tag |
| --- | --- |
| Definition | Definition kind, universe-parameter count, type, value. |
| Inductive | Universe count, parameter count, index count, constructor count, type, then constructors. |
| Constructor | Universe count, constructor index, parameter count, field count, type. |
| Recursor | Universe count, parameters, indices, motives, minors, `k`, type, then rules by field count and body. |

Definition < inductive < recursor is the mixed-kind order. Binder names and binder
information are metadata; ordinary `mdata` is ignored. Semantic-contract metadata
has its own `orderKey` and then compares its body. Universe parameters are compared
by position in each declaration's own list, and the compiler compares levels after
`canonUniv`.

For constants, universe arguments precede the reference comparison. Equal names
compare equal under the implementation's name equality; two in-block references
compare by current class position with a weak result; an in-block reference sorts
before an external one; external references compare by address. An unresolved
external reference is an error, not a name-order fallback. Projections compare
their structure reference in the corresponding way.

`MutConst.ctx` maps members to class indices and constructors to positions after
the member classes, reserving each class's maximum constructor count. The context
and name/reference relations used in a proof must describe those actual entries;
they cannot be replaced by an assumption that an arbitrary input never mentions
its constructors.

Two current-source boundaries matter. Rust still compares `is_rec` and `is_unsafe`
before the other inductive fields; the C6 choice remains unresolved (§8). The Lean
expression comparator's `letE` branch ignores `nonDep` at this source revision.
Neither a future repair nor a structural name-key replacement is included in the
theorems/source being described here. The general bridge from these keys to the
intended representation must account for those fields, rather than infer safety
from library parity alone.

### 2.3 Canonical order (Def 2.3), as a procedure

[`sortClasses`](../Ix/Compile/Canon/Classes.lean) begins with the members in one
class. The compiler's seed is name-hash order. A refinement round builds the
current class context, stably sorts each class with the structural comparator,
then groups adjacent equal members. Rounds split classes; the final ordered
partition is the result of this procedure. Each equal class is represented by its
least member in the selected name-hash order.

Strong comparisons do not depend on the current class indices and can be reused.
Weak comparisons depend on those indices and are not cached as permanent results.
The cache normalizes both its unordered pair key and the stored result's
orientation. A reversed lookup reverses the result back.

The procedure, not an arbitrary choice of a consistent fixed point, defines the
order. The coarsest-partition and seed/order results are separate proved clauses
with the hypotheses in §3.3. Exact equality of the entire list uses the name-hash
seed; the more general seed-independent statement compares the ordered classes
as sets, allowing a different order inside an equal class.

External addresses are compared at their first differing position. Thus a format
change can change the order as well as the addresses; the rejected two-key
alternative is not the compiler. Name-hash representative selection remains a
policy, not a proof that every downstream auxiliary or metadata choice is name
independent.

### 2.4 Member content (Def 2.4; D3/D16)

Canonicalization retains each representative's universe-parameter list and type
and value under the prescribed member/name mapping. It does not minimize the
universe telescope by deleting apparently unused parameters, reorder arbitrary
binders, or normalize arbitrary user computation. Constructor order within a
member is source order; member classes, component order and nested positions are
the separate decisions above.

The target is invariance under the supported change of presentation, not equality
under every logically equivalent definition. Metadata retains source names,
binder information, level spelling and the information needed by decompilation.
Proving independence of the *emitted declaration* from a representative choice
requires more than the Pass 1 partition theorem.

### 2.5 Nested auxiliaries in discovery order (Def 2.5; D2)

[`Canon.Nested.expand`](../Ix/Compile/Canon/Nested.lean) describes a FIFO expansion:

1. Initialize the queue with the members in the supplied order.
2. Visit each queued member's constructors in order. Peel the block parameters,
   then walk the constructor type in pre-order: function before argument, binder
   domain before body, and let type before value before body.
3. At a nested occurrence `I Ds is`, check that the inductive is external to the
   current queue and that a parameter mentions a queued member without capturing
   a constructor-local variable. Test the occurrence before descending into it.
4. Instantiate the external group's types and constructors at its levels and
   parameters. Append the new auxiliary members to the queue, record their
   discovering owner, and replace the occurrence by its auxiliary.
5. Reuse a previously seen occurrence instead of appending it again.

Discovery order is the order of those appends. Canonical discovery begins from
canonical member classes and their representative mapping. An external group is
opened in the order supplied by `GroupOf`; production uses the compiled registry
for that referenced block. It does not scan unrelated ambient declarations to
choose a different order.

The executable generator is
[`AuxGen.Nested`](../Ix/AuxGen/Nested.lean). Its current `replaceIfNested` records
every member of an external group, and each name of a collapsed class, under its
own occurrence key. The older description that only the triggering occurrence
was recorded is historical. `Dedup.compiler` remains a model of that older choice;
it is not a reason to call the current generator's sibling fix unfinished.

`computePerm` matches each source auxiliary signature against canonical signatures
and records a canonical position or `none`. It prefers matching levels, then the
specified level-insensitive fallback, with parameter comparison through
`auxSpecEq`. This is the function whose signature relation the L1 theorem proves;
it is not unrestricted definitional equality of arbitrary parameter terms.

`expand_spec` and `expand_owner` prove discovery/ownership properties of the pure
expansion. `computePerm_spec`, `computePerm_onto` and `computePerm_some` prove the
position-map clauses. See [Expand](../Ix/CompileCert/Canon/Expand.lean) and
[Perm](../Ix/CompileCert/Canon/Perm.lean). Connecting the production generator,
its finite source reads, name allocation and constructor-origin transport to
that specification remains a general obligation at this revision. Later allocator
and name-key work is not presumed here.

### 2.6 Evaporation

A source nested position evaporates in a component when it is owned there, has no
canonical position there, was exported by Lean, is not discovered canonically by
another component of the block, and its external head's recursor has one motive.
These are the conditions of `Evaporates` and `evaporate_spec` in
[`Evaporate`](../Ix/CompileCert/Canon/Evaporate.lean).

An evaporated source recursor is still a source declaration. Under Pass 3 its Lean
name denotes an image; it is not simply aliased to the external recursor with a
different telescope. The canonical auxiliary exists only where canonical
expansion requires it. The image construction performs any necessary relocation.

### 2.7 Definition cliques (M.1–M.6)

A clique is the source mutual group recognized through Lean's recursion encoding,
not merely a cycle in the elaborated reference graph. Its specification gives
each member's universe parameters, type, user body and pinned recursion choices.
[`Canon.Clique`](../Ix/Compile/Canon/Clique.lean) forms classes over those
specifications using the Pass 1 comparator. A structural `recArgPos` tie-break
compares after the whole type and body, as the source's `Member.asConst` specifies.

The permutation `σ` sends a Lean member position to its canonical position.
Equal specifications can form one class (O17), with alias members using the
representative's transported result. Theorem cliques use statement order first;
recovered specifications can resolve remaining order where available. A clique
without sufficient specification stays in Lean's form with `NOSPEC`; a recognized
order whose transport grammar fails stays in Lean's form with `SHAPE`.

`cliqueClasses_coarsest`, `cliqueClasses_perm`/`setEq` and `statementOrder_spec`
state the Pass 1 clauses in
[`CliqueClasses`](../Ix/CompileCert/Canon/CliqueClasses.lean). They do not prove
that recovering and transporting every production encoding preserves its value.

### 2.8 The Phase A decisions, with reasons

The implementation keeps first-difference address comparison and a name-hash seed
and representative. It uses canonical universe comparison and nested discovery
order, and emits one constant per auxiliary. These decisions separate anonymous
content from source metadata without claiming that every metadata byte is erased.

The Lean mixed-kind and cache-orientation repairs are enabled by
`Rules.compiler := Rules.phaseA`. The old `Rules.today` is an explicit comparison
mode for historical studies. It is not the production rule set. Rust's additional
C6 fields are still present; §8 records the unresolved choice rather than promise
a deletion that has not occurred.

## 3. The comparator is a total preorder

### 3.1 What runs today

The production Lean comparator is the executable one in
[`Canon.Order`](../Ix/Compile/Canon/Order.lean), with `Rules.compiler` and its
strong-result cache. The proof separates a pure comparison from the cached
implementation. `compareFresh_eq` relates them on the stated component entries;
the algorithm does not gain totality merely because a sort returned on a fixture.

### 3.2 At a fixed context, the key is a total preorder

[`Cache`](../Ix/CompileCert/Canon/Cache.lean) proves `constOrd_total` and
`compareFresh_total`, using the expression/reference/constant lemmas underneath
it. The relation is a total preorder on the successful domain of a comparison
that can fail; unresolved addresses remain errors. Cache coherence preserves the
pure result and its orientation.

The theorem retains `AddrCongr`, the applicable name-injectivity condition and
`portFixes = true`. `AddrCongr` says that names equal under the implementation's
`==` receive equal external lookup answers. `NameInj` requires the component's
member/constructor names to identify their entries under that equality. At this
source version, `Ix.Name` equality compares cached hashes. Those assumptions are
not automatic consequences of using hashing constructors.

“Strong” means independent of changing the in-block class indices within the
admitted run/context relation. It does not mean independent of changing the
external environment, the term or the rule set. The proof's cache invariant must
hold when the runtime cache is reused.

### 3.3 Coarsest refinement and seed-independent class order

[`Coarsest`](../Ix/CompileCert/Canon/Coarsest.lean) proves
`sortClasses_coarsest`. [`Terminate`](../Ix/CompileCert/Canon/Terminate.lean)
proves `sortClasses_ok` when distinct-member comparisons succeed at every context.
The successful-run statements retain their return equations and the relevant
`KeysDistinct`/`AddrCongr` conditions; this is not a theorem that arbitrary failed
comparisons produce a partition.

[`Seed`](../Ix/CompileCert/Canon/Seed.lean) proves `sortClasses_perm` for the
name-hash seed: permuting the input yields the same entire result. The more
general [`SeedFree`](../Ix/CompileCert/Canon/SeedFree.lean) result
`sortClasses_setEq` preserves the ordered classes as sets under the specified
agreement of levels and tie-break rules. It allows the order inside an equal
class to differ. The distinction matters when later code chooses a representative.

### 3.4 Comparator boundaries and historical defects

| Item | Current status | What must not be inferred |
| --- | --- | --- |
| C1: mixed kinds | Correct tag order when `portFixes = true`. The historical mode retains the old behavior for comparison. | No need to assume all arbitrary inputs are kind-homogeneous to hide the old bug. |
| C2: reversed cached pair | Compiler cache stores/reads normalized orientation; the cache proof covers it. | A hash pair key alone does not prove its entries identify the intended names. |
| C3: weak/strong order | Only strong results survive class refinement. | Weak results are not immutable facts about every later context. |
| C4: level spelling | Compiler compares `canonUniv` forms. | This does not prove every representative declaration or image is invariant under arbitrary universe respelling. |
| C5: external addresses | Compared at the first difference, by policy. | Format-version independence is not promised. |
| C6: Rust flags | `is_rec`/`is_unsafe` remain in Rust's inductive key. | Matching library bytes do not settle removing them or extending the specification. |
| C7: constructor references | The context gives constructor positions as specified by `MutCtx`. | Production reference/owner invariants still have to be connected to that context. |
| C8: semantic metadata | Compared by semantic contract key, then body. | Arbitrary source-contract transformations are not automatically authorized. |
| C9/C10: fixed point and stopping | The procedure defines the order; Lean refinement uses the proved splitting invariant. | A second implementation with a different stopping check is not formally refined by the Lean proof. |

The current ignored `letE.nonDep` comparison and the hash-based name/reference
identification are additional runtime-to-specification boundaries (§2.2, §0.2).
They are not repaired by stating a stronger theorem conclusion than the source has.

### 3.5 Pass 1, stated at the theorem level

The L1 result combines SCC correctness/termination, the comparator and refinement,
seed and supported renaming/collapse behavior, nested discovery/position maps,
block name maps and clique order. Principal block endpoints are
`canonBlock_spec`, `canonBlock_scc`, `canonBlock_acyclic`,
`canonBlock_coarsest`, `canonBlock_member_order` and `canonBlock_separate`.
The source map is [Canon](../Ix/CompileCert/Canon.lean).

In addition to the comparison hypotheses above, the block clauses use `NodupB`
and `EnvWF`: the relevant keys are distinct, a lookup returns a declaration bearing
the queried name, and listed constructors have the required name/owner relation.
Name-map clauses retain `NameMapKeys`, separating the member and nested/suffix key
families and bounding the nested positions. Renaming and collapse retain their
term/reference relations. Reference completeness retains `ConstHashCons`, and
discovery results use the discovery rule.

The precise clause-by-clause statement and exclusions are in
[certification §1.6](compiler-certification.md#16-l1-theorem-42-at-pass-1s-level).
No clause here asserts that all these assumptions have already been derived from
the general production input domain, or proves the generator, rewrite, Rust
mirror, emitted representative or full driver contract.

In particular, the original §3.5(iv) target is still outstanding: **the canonical
declaration of a class is invariant under the choice of representative**.
Proving equal ordered class sets is not this statement about the selected member's
complete generated/emitted declaration. The representative policy in §2.3 and the
conditional L1 summary do not remove or narrow that obligation.

### 3.6 Comparator and presentation tests

The canonicalization suites exercise mixed-kind order, reversed cache orientation,
partition/refinement behavior, nested ordering and presentation changes. The
registered tests and assertions are listed in
[the gate guide](compiler-gates.md#where-checks-run).

Historical seed sweeps and bounded enumeration motivated the design; they are not
an exhaustive test of all declarations or a substitute for the theorem map. The
current suite names and code, rather than old study totals, define the executable
coverage. A new record is accepted only after explaining the changed behavior and
running the relevant byte/meaning checks.

## 4. The image construction

A changed block is one whose canonical classes differ from Lean's grouping/order,
or whose nested positions moved or evaporated (`Pass.isChanged`). The canonical
block and its auxiliaries are retained at reserved display names. Images explain
the source eliminators in terms of those canonical declarations.

The image generator consumes a source lookup, an `ImageSpec` and the canonical
recursor types. Its output is a term over the source telescope, together with
computation-rule statements. See [Image/Spec](../Ix/Compile/Image/Spec.lean) and
[Image/Build](../Ix/Compile/Image/Build.lean). The lookup/specification consistency,
typing and value properties are general obligations, even when every image in a
fixture passes its type and `rfl` rule checks.

### 4.1 Eliminator choice (Def 3.3)

For a source motive type, choose the canonical recursor whose motive slot
represents that type. A nested/container occurrence can belong to the enclosing
canonical block's recursor rather than the recursor of the occurrence's head
constant. The container rule takes precedence; trying the head recursor first is
the `naiveElim` ablation in the generator's tests.

Canonical positions and source constructors come from the specification and the
read recursor telescope. They must agree with the generated declarations. The
implementation's successful reads are checks of particular shapes; they do not
alone prove the complete production correspondence.

### 4.2 The image of a recursor (Def 3.4)

Open the source recursor into parameters `ps`, motives `ms`, minors `mins`, indices
`is` and major premise `x`. Let the selected canonical recursor be `ρ`. Its motive
slot `j` collects the source motive positions `C_j` that map to that slot.

The construction uses these cases:

| Slot | Canonical motive | Result selection |
| --- | --- | --- |
| Single | The source motive. | Identity. |
| Several source motives | Their right-nested `PProd`; `And` for propositional motives. | The corresponding projection. |
| Single slot beside a tuple at a potentially nonzero result level | `PProd.{u,0} (m is x) True`. | First projection. |

The last lift places the singleton motive in the same `Sort (max 1 u)` as the
tuple slots. Omitting it, or using an unrelated `PLift` universe, is not an
equivalent construction.

For each canonical minor, read its fields and induction hypotheses. For every
source minor represented there, apply that minor to the corresponding fields and
one argument for each of its source induction hypotheses. If the canonical
recursor supplies the hypothesis, project the source component from it. Otherwise
build a relocated recursor application for the field's motive type, under its
reflexive binders. Pack the minor results just as the motive results are packed.

The result has the schematic form

```text
img(r) = λ ps ms mins is x.
  unwrap_source_slot (ρ.{levels} ps canonical_motives canonical_minors is x).
```

The generator develops its constructed wrappers (§4.3). Source motive slots unused
by the chosen component are not supplied to `ρ`. Constructor correspondence,
universe substitution and packing must retain the source telescope's binder
identity and dependencies, not merely a matching pretty type.

**Relocation bound.** `Build` uses the number of source motives plus one and returns
a named error if fuel is exhausted. The design argument is that a successful
relocation chain cannot revisit a motive while retaining the same context/state.
The complete argument must prove that reducing the fuel preserves the *same term
and final fresh-variable state*, and derive its context, name and environment
invariants from the general input. That bridge is not complete in this revision.
Structural recursion on a fuel argument makes the implementation total as an
error-returning function; it does not by itself prove the bound loses no valid case.

The [image fixtures](../Tests/Ix/Compile/Image.lean) cover permutation, split,
collapse, nested/evaporated cases, parameters, universes and reflexive fields,
including negative ablations. The general typing/rule theorem is not inferred
from their finite coverage.

### 4.3 The development

[`Image.Develop`](../Ix/Compile/Image/Develop.lean) performs hereditary substitution
of the image's arguments. It contracts β-redexes created when a substituted value
is applied, the corresponding constructor-projection redexes, and the specified
η wrappers at directly substituted heads. It does not perform arbitrary ι
reduction on a user's recursor call, or normalize all redexes already in the
user's arguments. The result of a hereditary β-step is not indiscriminately
η-contracted.

This precise reduction policy is part of the intended canonical form. A proof of
ordinary β-conversion does not establish equality with its exact bytes or its
preservation of user-written redexes. The mathematical finite-development and
typed-substitution arguments motivate the construction; the runtime traversal,
level-substitution composition, fresh-name behavior, memo keys and successful-fuel
refinement still require their explicit general bridges. Matching result hashes
in regression tests does not prove structural equality on arbitrary cached terms.

### 4.4 The two prototype corrections

Two retained negative controls explain necessary parts of the design: the
container eliminator must precede the head-recursion fallback, and mixed tuple
slots require the singleton lift in §4.2. `GenOptions.naiveElim` and `noLift` exist
only for such ablations; both are off for production.

Prototype counts and line numbers are historical, not the specification of the
current builder. The current [Build](../Ix/Compile/Image/Build.lean), its
[expression helpers](../Ix/Compile/Image/Expr.lean) and the image suite define the
construction and executable controls.

### 4.5 Call sites: inline rewrite or image constant

At a full application of an image-kind head, rewrite the arguments, try the
ordered passes, then instantiate and develop the image if no pass applies.
A bare or partial application keeps the source name, which already denotes the
stored image. There is no additional `a._ix` image constant for that occurrence;
`_ix` display names denote the canonical auxiliaries.

The declaration's type is rewritten by the same head substitution. Thus an image
or rewritten user whose source type itself mentions an image head can have a
stored type convertible to the intended source type under the correspondence,
rather than an identical source expression. The `brecOn` family's mentions of
`below` are the important example. The source kind is preserved except that a
recursor image is a definition; a source theorem remains a theorem (§11.2).

At each outermost rewritten occurrence the metadata retains the source occurrence
for decompilation. That recovery record is not a proof that the stored transformed
value equals the source value; the two questions have separate gates and theorems.

### 4.6 Other source auxiliaries and the baseline (Def 3.5–3.6)

For image-kind definitions such as `casesOn`, `recOn`, `below` and `brecOn`, use
Lean's own value with its head occurrences rewritten. For a recursor use §4.2's
generated image. The recursive `below`/`brecOn` families are included only where
the source family has them; `Names.imageKinds` defines the set.

Other declarations—`noConfusion`, the `sizeOf` family, matchers, injectivity
lemmas, constructor-index helpers and their callers—compile as ordinary source
declarations over the rewritten heads. That is the baseline. Lean's
`IndPredBelow` family also compiles as its own source block; the canonical family
has display names. It is not silently identified with a different inductive type.

The implementation is [Pass/Driver](../Ix/Compile/Pass/Driver.lean). A baseline
can be faithful while retaining source grouping. A proof-justified pass may add
a separate canonical form without replacing that baseline under the Lean name.

### 4.7 Six split-sensitive differences

| Source of difference | Current treatment |
| --- | --- |
| (a) Recursor grouping, arguments and recursive hypotheses | Images adapt the source telescope to canonical recursors; O1/O2/O6 recognize simpler forms. |
| (b) Which auxiliary families exist for a source versus a canonical block | Retain the source declaration where required; canonical families are separately named. `PENDING-SPLIT-AUX` can remain in the finite record. |
| (c) `noConfusion` representation of a split-off enumeration | O11b supports its recognized one-constructor case; other source forms remain faithful. |
| (d) Cross-component `sizeOf` recursion | O11a recognizes the supported size instance; other cases retain the baseline with a recorded decline. |
| (e) Reference/sharing tables of a rewritten expression | Compile the final expression's tables. The old surgery's dropped-argument leftovers are historical. |
| (f) Hypothesis paths and universe instantiation | Read the image/specification correspondence; do not reuse the deleted surgery's positional guesses. |

These descriptions identify mechanisms, not blanket equality claims for every
input. The [pass tests](../Tests/Ix/Compile/Pass), image tests and
[default non-canonical record](../Tests/Ix/Compile/NonCanonicalDefault.lean)
show which fixture differences remain.

### 4.8 Pass 3 as built

`editChangedBlock` moves canonical auxiliary names to `_ix` displays and records
the image-kind heads. `compileImageBlock`/`runImageBlock` install the images under
the source names and retain the independently compiled source form in
`Named.original`. `prepareBlock` handles clique planning, unit passes and ordinary
rewriting before expression compilation. All current compiler entries use this
pipeline; mode validation is stated in §0 and history is isolated in §7.4.

Input names containing a component beginning `_ix` are refused in the grounded
condensation passed to the driver. With several such names the diagnostic chooses
the least pretty-form message in both compilers. Ungrounded names instead have
the named groundedness failure, so their exclusion from that scan is not silent
acceptance.

The compiler works on `Ix.Expr`. It instantiates image universes before development
and canonicalizes the emitted level representation. Images need canonical
recursors and resolved dependency addresses; views may enter the shared cache
only when the required original block members have compiled (§6.3).

The inline metadata pair is `(_ix.inline, s)` and `(_ix.inline_meta, m)`:
`metaSharing[s]` holds the compiled source occurrence and `m` is its metadata-arena
root. Decompilation replays it; ordinary kernel ingress treats it as metadata.
`SideCar` supplies the display renaming and `ChangedSet` supplies diagnostics.
The format uses the existing metadata/arena representation, not an extra current
surgery-expression tag.

## 5. Transport of proof terms

### 5.0 The common frame

Let a source clique have Lean order `f₀ … fₙ₋₁` and canonical permutation `σ`.
The target is the same recursion encoding over the canonical packing, retaining
Lean's per-function choices. The transport `Φσ` changes only constructs owned by
that encoding, through four operations:

| Operation | Effect |
| --- | --- |
| Renaming | Encoding constants become the clique's canonical helper names. |
| Reassociation | Rebuild `PSum`/`PProd` packing, injections, cases and projection paths in canonical order. |
| Restatement | Express packing-dependent obligations over the new packing. |
| Regeneration | Rebuild supported path-dependent proof fragments for the new paths. |

This is not a pure name substitution. User binders, relations and values that only
resemble an encoding must retain their meaning. Ownership follows the recognized
source binder and the encoding's threaded copies, not type equality or a generic
projection shape.

The recognizer requires the grammar it can reconstruct. A grammar failure keeps
Lean's form with `SHAPE`. Reconstructing a well-typed canonical term is necessary
but does not establish value preservation on its own. The full transport's typing,
conversion and value argument is still a general L3 obligation. See
[`Clique.Transport`](../Ix/Compile/Clique/Transport.lean) and
[`Clique.Plan`](../Ix/Compile/Clique/Plan.lean).

### 5.1 Well-founded recursion

Lean packs the source functions into a well-founded recursion over a sum of
argument telescopes. Transport rebuilds that sum, its injections/case trees,
packed functional and the corresponding relation/obligations. Each function's
measure and chosen recursion data travel with that function; the transformation
does not rerun termination inference or a tactic to select different choices.

[`WF`](../Ix/Compile/Clique/WF.lean),
[`WFSchema`](../Ix/Compile/Clique/WFSchema.lean),
[`WFMatcher`](../Ix/Compile/Clique/WFMatcher.lean) and
[`WFConjugation`](../Ix/Compile/Clique/WFConjugation.lean) separate the recognized
shape, matcher reconstruction and conjugation. A recognized `_proof_k` obligation
is restated over canonical packing; unsupported proof internals are retained or
cause the recorded faithful fallback according to the transport result.

The intended value argument is well-founded induction: after corresponding
equations unfold, the packed functions have the same user body and corresponding
recursive calls. The induction hypothesis supplies equality of those calls.
This explains the needed theorem; it is not a declaration that the runtime
transport has already been proved correct for every recovered source clique.

The per-output W+ value-row generator is a separate mechanism. When it constructs
and the checker accepts a value row, the row gives the value equation described in
[certification §1.3](compiler-certification.md).
Failure to generate such a row does not magically convert an `eq_def` row into a
uniqueness theorem.

### 5.2 `partial_fixpoint`

The packing is a right-nested product. Permuting factors changes functional
projections and monotonicity proof paths. The transport rebuilds recognized path
proofs using the same deterministic construction, or uses the supported monotone
composition route where applicable. An unrecognized shape retains the faithful
form; the spelling `partial_fixpoint` does not mean an unsafe Lean `partial`
declaration.

There is a checked mathematical lemma here:
[`FixPerm`](../Ix/Compile/Clique/FixPerm.lean) defines `OrderIso` and proves
`fix_iso`, `fix_iso_proj` and `lfp_monotone_iso`, with their partial-order,
CCPO/complete-lattice and monotonicity assumptions. The product order isomorphisms
give concrete packing permutations. The theorem uses `Init.Internal.Order.Basic`
through `import all`, which is part of its source/audit surface.

The theorem says a fixed point is carried by the stated order isomorphism under
the stated hypotheses. Applying it to every term accepted by
[`PartialFixpoint`](../Ix/Compile/Clique/PartialFixpoint.lean) and
[`PFConjugation`](../Ix/Compile/Clique/PFConjugation.lean) still requires the
recognizer, typing and runtime-to-semantic correspondence. It is not a theorem
about arbitrary source elaborator output merely because the helper is imported.

### 5.3 Structural recursion

Structural cliques use the recursive type's `below`/`brecOn` dictionaries. Transport
permutes/repackages the dictionary components and replaces recursive-call reads
only where they are owned by the decoded dictionary. User tuples with the same
shape are not dictionaries of the encoding. Recovery follows the same ownership
discipline.

[`Structural`](../Ix/Compile/Clique/Structural.lean) records `StructLayout` and
repacking; [`Recover`](../Ix/Compile/Clique/Recover.lean) extracts specifications;
the shared [packing helpers](../Ix/Compile/Clique/Packing.lean) and
[packing matcher](../Ix/Compile/Clique/PackingMatch.lean) handle the actual paths.
The intended value proof is simultaneous structural induction, with dictionary
and recursive-call correspondence at each constructor.

**Carried equation lemmas.** When a structural clique repacks its type-former
group, a carried `eq_def` can mention the old packed group in its statement/proof.
The current `repacks` boundary keeps that route in Lean's form with `SHAPE`.
Transporting, reassociating or regenerating that proof is a remaining design
choice (D-M5-1), not an implemented extension asserted by this guide.

### 5.4 Theorems proved by mutual recursion

The theorem's statement remains the source statement; a transported proof must
prove it. Statement order can determine a canonical clique order even when there
is no ordinary definition-body specification. Complete ties use the specified
seed policy. Where recovery cannot justify an order, the plan is `NOSPEC`; where
transport cannot recognize the proof grammar, the plan is `SHAPE`.

[`Pass.Cliques`](../Ix/Compile/Pass/Cliques.lean) builds each plan from the clique's
own unit and records its outcome. The helper declarations and carried lemmas are
included only when reached. Lean's order-dependent encoding constants remain
under Lean's names for source users that need that statement; canonical helpers
use reserved names. The plan-table check can recompute a taken plan in Lean
(§6.3). A cached plan is not evidence that all theorem proofs are canonical.

### 5.5 Remaining presentation dependence

| Cause | Why a faithful term can retain source presentation |
| --- | --- |
| `TACTIC-ASYM` | Proof internals differ beyond the encoding grammar. |
| `GUESSLEX` | The source chose a different well-founded measure. |
| `RECARG` | The source chose a different structural recursive argument. |
| `ORDER-STMT` | An encoding constant or theorem statement explicitly follows the source packing. |
| `SHAPE` | The supported grammar cannot transport the relevant term. |
| `NOSPEC` | A specification/order was not recovered. |
| `LAZY` | An on-demand lemma changes the source unit being compiled. |

The cause vocabulary is defined in
[`NonCanonical`](../Tests/Ix/Compile/NonCanonical.lean). It classifies measured
fixture differences. It is neither a whitelist authorizing a wrong value nor a
proof that no other source term can fall outside the grammar.

### 5.6 What is measured about cliques

The clique suites exercise specification recovery, order, transport, theorem
proof checking, equal-specification aliases, carried lemmas, caller independence
and ownership controls. They were included in the combined compiler's fixture
gates (§7.3). The historical library classification in §0 does not measure all
these assertions for every library member.

The [ownership tests](../Tests/Ix/Compile/CliqueOwnership.lean) and validator phase
9 compare values on their specified distinguishing inputs. Phase 9 reports
members it cannot evaluate and only unfolds fixpoints to its stated depth (§9).
Kernel acceptance of a transported proof checks its statement, while a definition
of the right type can still compute the wrong function. Decompile replay checks
the provenance path and must not be substituted for inspecting the stored value.

### 5.7 The transport as implemented

The current module tree is `Ix/Compile/Clique`, with `Basic`, `Telescope`, `Whnf`,
`Dag`, `Packing`, `PackingMatch`, `Recover`, the three encoding implementations,
the conjugation/schema/matcher helpers, `Transport`, `Plan` and `FixPerm`.
[`Pass/Cliques`](../Ix/Compile/Pass/Cliques.lean) is the production hook; it is no
longer an unmerged experimental workspace.

The Lean and Rust module correspondence, ownership/context caches and nonported
details are described in [the Rust guide](compiler-rust.md). In particular, Rust
sorts the clique names by their complete pretty strings before assigning record
positions. The cached-key stable sort preserves relative order for equal pretty
keys; it is a cost optimization, not a new structural name comparison.

The Lean DAG helpers distinguish constructor consistency used by identity skips
from run-local key faithfulness required by hash-only memo hits. Fresh-allocating
visits are not memoized as if allocation were irrelevant, and depth/fuel remain
in keys where the computation depends on them. The helper regressions compare
hash results; they are not a structural equivalence theorem for arbitrary cached
inputs. See [`Clique.Dag`](../Ix/Compile/Clique/Dag.lean).

### 5.8 Fixture families and the general gap

The tracked clique and twin families include well-founded, structural,
`partial_fixpoint`, nested/reflexive, lattice and user-proof cases. The
[gate inventory](compiler-gates.md) lists which runners enforce which assertions,
including non-canonical causes and refusal behavior.

These controls give concrete negative/neighbour evidence and regression coverage.
They do not show that the recognized grammar contains every term Lean's elaborator
can generate, prove every monotonicity reconstruction, or close the general
recursor/telescope/substitution obligations. Those remain at their original
general scope; the tests do not narrow that scope to closed library examples.

## 6. Determinism: the compiler as a function of the closure

The target is that a block's output depends on its source unit and dependency
closure, not worker arrival order, unrelated ambient declarations or callers.
The current implementation has concrete protections and finite gates for this
target. L1's partition/order theorems alone are not a proof of every driver read,
name claim, auxiliary generator, memo table or emitted metadata field.

### 6.1 Global reads and order dependences: source audit

This table is a code audit at the source revision in the header. “Changed” means
the old mechanism is gone or corrected in the cited implementation; it does not
mean the general closure/output theorem has been proved. Content means anonymous
serialized content, while side-car includes names, metadata, hints and originals.

| Item | Current source and behavior | Status / remaining obligation |
| --- | --- | --- |
| D1: merge ownership | [`checkBlockClaims`, `mergeCompiledBlock`](../Ix/CompileDriver.lean) check primary/aux claims and head/block/recursor records against live state and earlier records of the same block. A different second address/record fails. `Named` metadata overrides remain intentional. | Implemented conflict checks; not every map is insert-once. Establish the full block-owned claim invariant when composing the general proof. |
| D2a: auxiliary promotion | [`auxBlockOutcome`, `compileConstNoAuxPure`, `promoteRemaining`](../Ix/CompileDriver.lean) still distinguish a previously generated auxiliary from an ordinary block and attach its own original form. | Present. Original-form failure can still be followed by promotion (§11.6); changing that behavior is owner-pending. |
| D2b: prerequisite precompile | Lean [`scheduleDeps`](../Ix/CompileDriver.lean) makes auxiliary seed closure ordinary dependencies. Rust [`precompile_aux_gen_prereqs`](../crates/compile/src/compile/env.rs) still performs a prepass. | Old Lean prepass removed; Rust is a real implementation difference. Byte gates cover measured successful inputs, not every failure-path correspondence. |
| D2c: phase/member selection | [`compileConstNoAuxPure`](../Ix/CompileDriver.lean) sorts members by `aliasPrecedes` before first-match selection; it still reads `auxGenExtraNames`. | The iteration-order issue is changed in Lean. Derive the claimed owner/phase/closure invariants generally; a source comment asserting them is not their proof. |
| D2d: already claimed names | Promotion still branches on `resolveAddrPure`; normal claims reject a different existing address. [`checkAuxSourceClaim`](../Ix/AuxGen/CompileAux.lean) rejects a source-name claim without forward provenance to the inductive owner. | Added source-ownership protection, not the complete generated-family freshness and claim-set theorem. |
| D3/D3b: surgery dispatch | `surgeryFree` and `compilingIsAuxRegen` are absent from the current compiler. [CompileM](../Ix/CompileM.lean) has the ordinary expression path with Pass 3 records. | Retired by slice 6; do not retain these as current global-mode dependencies. |
| D4: reverse alias lookup | Lean [`TcScopeSt.faultInAddr`](../Ix/AuxGen/Kernel.lean) faults recorded forward source identities in deterministic order and rejects absent provenance. The old `nameForAddr` scan is gone. Rust's [bridge](../crates/compile/src/compile/aux_gen/expr_utils.rs) retains its documented address/global-reverse retry boundary. | Lean source identity improved; Rust difference and general bridge correspondence remain. Stale comments mentioning `nameForAddr` do not establish an active Lean call site. |
| D5: provisional addresses | [`AddrMaps.resolve`](../Ix/AuxGen/Kernel.lean) uses a source name hash when no compiled address is available in the bridge. | Present. Prove these temporary identities cannot leak into the emitted reference meaning; no general leak-freedom claim from a passing byte gate. |
| D6: synthetic primitives | The [bridge's primitive setup](../Ix/AuxGen/Kernel.lean) constructs the required kernel primitives and display identities. | Present. Include their identity/meaning in the bridge proof; they are not additional freely chosen emitted aliases. |
| D7: kernel cache history | Lean uses a fresh block kernel context; Rust reuses worker-local state with its reset policy. See [driver](../Ix/CompileDriver.lean) and [Rust scheduler](../crates/compile/src/compile/env.rs). | Finite parity evidence; freshness of the Lean context is not a proof of the Rust cache refinement or all name-restoration paths. |
| D8: partial indexing | Generator and clique code still contain checked and unchecked array accesses and error-returning shape reads. | Totality/bounds must be proved at each caller or handled by a named error. Zero panics on a suite is not a totality theorem. |
| D9: SCC/ready keys | [`canonicalKey`, `blockKey`](../Ix/CompileDriver.lean) select the canonical member key; the sequential ready queue is least-key-first. Cross-subset compilation also uses that key. | Old Tarjan-root/first-Set-element output choices changed in Lean. Wave/Rust schedule independence remains a whole-output obligation. |
| D10: seed/representative | [Canon rules](../Ix/Compile/Canon/Order.lean) retain name-hash seed and least-name-hash representatives. | Intentional policy. L1 proves its stated class/order clauses; downstream representative independence is separate. |
| D11: aliases/provenance | [`registerAuxAliases`](../Ix/AuxGen/CompileAux.lean) checks source ownership and address consistency; when cloning target metadata it clears `original`, so the source acquires its own original during promotion. | The borrowed-original defect is repaired. Global address/metadata reads remain and need the owner/closure correspondence. |
| D12: in-block surgery plans | Legacy surgery plan production/merges are removed. [Pass 3 records](../Ix/CompileDriver.lean) have their own claim checks. | Retired mechanism; do not confuse remaining clique/image memos with a surgery plan. |
| D13: generator registry reads | [`Nested`](../Ix/AuxGen/Nested.lean) reads the canonical classes of referenced external groups; [`Below`](../Ix/AuxGen/Below.lean) and [`BRecOn`](../Ix/AuxGen/BRecOn.lean) distinguish compile-local metadata from decompile-only registry use. | The required referenced entries must be available and source-determined. A comment calling a branch decompile-only does not prove every generator read is in closure. |
| D14: reverse output index | [`insertCanonicalAlias`](../Ix/CompileM.lean), used by `assembleEnv`, retains the earliest alias in seed order. | Old last-wins map iteration changed. This canonical reverse alias is not structural injectivity of arbitrary cached names. |
| D15: conflicting wave reports | Live claims decide which conflicting block first registers and which reports the error. | The conflict is refused; diagnostic owner/order need not be a unique canonical successful result. |
| D16: Rust rollback | [`block_txn`](../crates/compile/src/compile/block_txn.rs) surrounds the normal scheduled block branch and rolls back its newly published named claims/records on error. | Implemented for that branch. Anonymous content caches can remain; the separate promotion-path exception is not repaired by this transaction. |
| D17: expression height | [`exprCompileDepth`](../Ix/CompileM.lean) retains its structural definition with a memoized `implemented_by` runtime height. | Implemented and included in the source-specific library gates in §7.3. The runtime refinement still belongs in the full compiler trust/proof account. |

The worklist now distinguishes removed paths, actual improvements and remaining
invariants. It is not a request to reopen removed surgery or to change pending
failure behavior as part of documentation.

### 6.2 The definition the compiler targets

For each dependency-closed block unit `B`, let `compileBlock(B)` include its
canonical classes, generated families, images, transported helpers and records.
The compiler target is the dependency-ordered fold of those outputs, checking
compatible name/record claims before merge. A canonical alias is the least alias
in the specified seed order among the aliases actually emitted.

More explicitly, the target definition is
`compile(L) = foldl step ∅ (blocks L)`, with
`step acc B = acc ∪ out(B)` and
`out(B) = compileBlock(input(B), resolvedClosure(B))`. Here `closure(B)` follows
type/value/rule references transitively and includes the logical units and
source-determined auxiliary support of reached blocks. Its resolved data includes
addresses and the applicable image/name/permutation information. Compatible
per-name assignments must agree; an incompatible assignment is an error.
The intended theorem is equality across every admissible topological order,
wave partition and worker count, and agreement of a selected closure with the
corresponding whole-environment output. This remains a general composition
obligation, not an additional already-proved L1 clause.

This definition has two distinct obligations:

1. Block computation reads only its permitted source/dependency data and computes
   a result independent of unrelated state and callers.
2. Compatible successful block results commute under the accepted schedule and
   merge policy, including metadata, originals, hints and failure bookkeeping.

L1 supplies the relevant component/class/name-map clauses under its hypotheses;
it does not prove this entire fold. The normal Rust transaction, Lean live-claim
checks and cache admission rules are parts of the implementation to relate to the
definition. `--allow-partial` and the promotion exception require their own
explicit failure reading (§11.6), not the successful-fold theorem applied silently.

### 6.3 The block rule: what a block may read

A block may read its own source unit, the source and compiled data in its
dependency closure, and source-determined support needed by the generated terms.
It may not inspect dependents to select a different meaning. Definition cliques
are compiled as their own units. A caller that reaches both a transported member
and incompatible source encoding constants is refused by the named caller rule;
the clique does not demote itself because the caller exists.

**Source units and output packs differ.** `EnvScope`'s input selection may retain
whole mutual/auxiliary units needed for compilation. An output pack is the
reference closure of requested output addresses, with specified reached cut
points; it does not widen to all source-unit names. See
[`PackCmd`](../Ix/Cli/PackCmd.lean) and
[`Ixon.Env`](../crates/ixon/src/env.rs). The former Rust unit-pack implementation
is deleted.

**Memos.** A cache is intended to refine the same pure computation, not authorize
new inputs. The important lifetimes/admission rules are:

| Cache | Scope and condition |
| --- | --- |
| Lean clique plans | A clique's own source/dependency unit; a taken table entry can be recomputed by `p3CheckPlans`. |
| Lean block views | Shared admission only after all required original block members have compiled; taken entries can be rebuilt and compared. |
| Lean expansions | Share only the admitted view-derived expansion; per-rewrite tables also retain local answers. |
| Occurrence rewrite | Per rewrite, keyed by term, record mode and definition site. The bare/partial-head early return precedes the normal cache insertion, so not every visit is cached. |
| Rust shared view/optimizer/image data | Stable-view admission is checked before building; optimizer/image sharing uses identity of the admitted `Arc` view. Local no-site/per-rewrite caches retain their narrower lifetime. |
| Clique structural helpers | Keys include the relevant context, depth or fuel; fresh-allocating traversals cannot be cached as if their state effects disappeared. |

The concrete definitions are [Pass/Driver](../Ix/Compile/Pass/Driver.lean),
[Pass/Cliques](../Ix/Compile/Pass/Cliques.lean),
[Pass/Translate](../Ix/Compile/Pass/Translate.lean),
[Clique/Dag](../Ix/Compile/Clique/Dag.lean) and the
[Rust guide's cache account](compiler-rust.md).
Some equality checks use cached hashes; recomputation and matching hashes are
regression evidence under that representation, not a new structural equality
proof on arbitrary names/terms. Pointer-confirmed cache reuse has its own identity
condition and must not be described as hash-only reuse.

`IX_PASS3_CHECK_PLANS=1` is a **Lean-only** check mode. It recomputes taken
plans/views/expansions, and its named check failure is fatal to the compile. The
full plan-cache suite compares checked sequential/parallel runs to a reference
and includes corrupt-entry controls. This is a finite refinement test, not a
Rust check mode or a proof of all cache invariants.

The schedule identity and caller-independence suites are already implemented and
registered; they are not future tests “to add.” The [gate guide](compiler-gates.md)
states full versus quick schedule scope, source selection, exact bytes, refusal
checks and corruption controls. Passing those suites does not close D2a–D14's
remaining general obligations.

Semantic source contracts have their own inspection boundary in
`inspectSemanticSource`. Annotated inductive/constructor/recursor transformations
are refused there; accepted body kinds still require the specified inspection and
transport path. There is no blanket claim that every annotation is preserved by
every Pass 3 transformation.

## 7. What is canonical and what is only faithful; the non-canonical set

### 7.1 The table

“Canonical” below identifies the representation target and the implemented
normalization for the stated shape. Its general proof status is §3/§5/§6; it does
not upgrade the complete compiler to a proved canonicalizer.

| Output | Canonical target / faithful boundary |
| --- | --- |
| Inductive member classes and positions | Pass 1 canonical form under its stated hypotheses; full generated/emitted correspondence remains. |
| Canonical auxiliary families | Canonical block generation and one-constant packaging; intended canonical target, with generator proof obligations. |
| Source image-kind names of changed blocks | Faithful images of the source grouping (`IMAGE`), not the canonical auxiliary's name/address. |
| Definitional-pass results | Canonical recognized forms of the baseline; other occurrences retain the image baseline. |
| Proof-justified forms | Canonical target under `c._ix`; the source name retains the faithful baseline (`PJ-FORM-<pass>`), with ordinary callers unchanged (`INHERITED`). |
| Transported clique members | Canonical packing for the recovered specification; source-dependent measures, recursive arguments and proof internals can remain. |
| Source encoding constants and packing-dependent statements | Faithful source form (`ORDER-STMT`). |
| Unrecognized clique order/grammar | Faithful form (`NOSPEC`, `SHAPE`). |
| `sizeOf` declines, bare/partial uses, changed `IndPredBelow`, lazy lemmas | Faithful form with the applicable recorded cause. |
| Failed/refused blocks | No successful declaration contract; read the failure and promotion exception explicitly. |

The supported change-of-presentation relation (Def 4.3) includes the specified
member permutation, renaming, component separation and equal-class collapse,
with their reference relations. It is not all extensional equivalence of Lean
programs or arbitrary theorem proof replacement. On-demand auxiliary realization
changes the source unit and therefore is not a comparison of identical inputs.

### 7.2 The non-canonical set (tracked fixture)

The current default record is
[`NonCanonicalDefault.nonCanonical`](../Tests/Ix/Compile/NonCanonicalDefault.lean):
**959 entries**, with **16 represented causes**. The cause type has **19
constructors/tag families**, including parameterized `PJ-FORM-<pass>`.
The default entries have this histogram:

| Cause | Entries | Cause | Entries |
| --- | ---: | --- | ---: |
| `IMAGE` | 493 | `INHERITED` | 155 |
| `ORDER-STMT` | 86 | `PENDING-SPLIT-AUX` | 55 |
| `O11A-PENDING` | 42 | `PENDING-COLLAPSE` | 30 |
| `LAZY` | 24 | `INDPRED-BELOW` | 21 |
| `PENDING-SURGERY` | 16 | `PENDING-NOCONFUSION` | 14 |
| `COLLAPSE-ARMS` | 11 | `RECARG` | 5 |
| `GUESSLEX` | 2 | `SHAPE` | 2 |
| `TACTIC-ASYM` | 2 | `BARE` | 1 |

These are source record counts, not a fresh run. Cause strings beginning
`PENDING-` are historical vocabulary retained in current fixtures; in particular,
`PENDING-SURGERY` is not evidence of a surviving surgery compiler.

[`NonCanonical.lean`](../Tests/Ix/Compile/NonCanonical.lean) defines
`NonCanonicalEntry`: fixture, presentations, relative constant name, canonical
role, cause and evidence (addresses, first differing path, checker booleans and
note). It also retains the **157-row `transportOracle`**, and the targeted
`nonCanonicalOn` and `nonCanonicalPasses` records. The deleted 497-row
`nonCanonicalOff` record is history, not a second current default.

The twins consumer matches the actual differences against the default keys in
both directions. Other consumers check their own projections of a record; an
evidence field present in the data is not automatically an asserted condition.
See [record inventory](compiler-gates.md#exact-records-and-re-recording).
The proposed additional four rows on a separate compiler repair branch are not
part of this source snapshot or its 959-row record.

### 7.3 Current gates and evidence scope

The default Lean/Rust suites now compare Pass 3 to Pass 3. Important checks include
twins/non-canonical exactness, image rules, pass and clique fixtures, ownership,
changed-set consistency, closure/caller independence, scheduling, cache controls,
auxiliary validation and certification audits. Their commands and exact predicates
are in [compiler-gates](compiler-gates.md).

`pass3-rust-parity` enforces the compared non-synthetic `Named` fields, one-sided
names, failure-name membership, non-canonical `(name,cause)` pairs and selected
root pack bytes. Synthetic `Muts` counts and a printed whole-file byte comparison
are diagnostics there. Do not read “0 defects” from that suite as an unqualified
whole-file byte theorem. `--rust-check` ALIGNED, frozen-reference `cmp`, the
closure/full-environment byte tests and the corpus parity phase have their own
explicit whole-byte assertions.

The completed compiler and certification runs are source-specific:

| Tested source | Accepted finite evidence |
| --- | --- |
| Combined `881c2b86be98ab77fa29d58daef7a6a798a556d7` | Full 63-stage compiler integration and seven supplemental suites passed, including full Lean schedule/cache controls, release Rust checks, certification/kernel/model/fidelity checks and Init+Std mode/byte/pin controls. Both default Mathlib compilers matched the frozen reference by size, SHA-256 and exact `cmp`; complete source/native/import postchecks passed. The earlier attempt that added a previously absent benchmark import remains a provenance failure, not the accepted gate. |
| Default-S follow-up `cfe49cb95ee8f0f953e253a4a47a50181dbc390f` | Strict build, primary tests, certification and lint passed; both Init+Std compiler outputs remained exact. With `--strong --strong-global` and no `--strong-changed`, all 117,694 per-name results match the explicit-flag baseline: W and S each 116,768 certified / 926 unsupported / 0 blocked / 0 rejected; S has 0 not reached and 41 value-certified names. Non-timing cone/equation multisets also match. This is the configured Init+Std result, not a completed full Mathlib S result. |

The [Rust guide's recorded results](compiler-rust.md#recorded-source-specific-results)
and [certification library evidence](compiler-certification.md#6-library-evidence)
give the corresponding scope and limits. Documentation-only successors preserve
the source account; they do not stand in for a new runtime measurement.

Earlier worker evidence remains attributed to its own tips. M6 slice-6
`9c28e0eeb2dcaf23288672435d50fad267d0f83b` supplied its package's gates,
including `pass3`'s 67 units / 0 problems and `clique-ownership`'s 53 cases
(44 transported, nine kept in Lean's form) / 0 failures. PERF `bae05065` supplied
its full gate set and before/after measurements; the later stable-sort tip
`3a889b60251f3d3c8742ba9aa88a5f3dbf7ade7e` supplied focused Rust and library
byte gates. These earlier results are not substituted for the combined gate.
None of the accepted finite checks is a general meaning proof.

### 7.4 Dated migration history

Pass 3 became the Lean default on 2026-10-06. The legacy mode was retained briefly
for paired migration comparisons. On 2026-10-07 slice 6 made Pass 3 the only mode
of both compilers, deleted the legacy call-site surgery and retired its off-mode
records. Those old modes and `-a2` reference bytes cannot be reproduced by asking
the current compiler for `IX_PASS3=off`; that request is refused.

The `-a3` reference artifacts adopted by the migration are:

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| Init+Std | 256,128,289 | `a2e22ee7f8d0fcf0d607047dda7d83749f20886f2d03f1cbaf2ede3a7d1ba676` |
| Mathlib | 2,376,572,399 | `d0427adf7b995f7f48c6fe5fa069c5d3a3d5c10c6f061425729e87339f6bf6db` |

The migration's recorded classification was 41 changed names/19 additions on
Init+Std and 783 changed names/356 additions on Mathlib, with no removed input
names. It attributed movement to images and their users, transported members and
carried lemmas, encoding constants and their dependents; canonical `_ix` names
accounted for the additions. These are retained historical observations from the
earlier design record; the accepted combined 881 gate independently reproduced
the reference bytes and its own registered assertions (§7.3). A matching artifact
does not by itself remeasure every historical classification. Record the actual
source/loader manifest and byte gate for each new run.

## 8. Decisions and remaining choices

| Decision | Current interpretation |
| --- | --- |
| First-difference addresses; name-hash seed/representative | Retained. The alternative two-key and name-free seed designs are not implemented policy. |
| C1/C2 repairs; canonical universe comparison; discovery order | Implemented in the compiler rules. |
| Sibling nested occurrence registration | Implemented in the production nested generator; old single-trigger behavior is historical. |
| Pinned clique choices | Compare after type and body; preserve source measures/recursive arguments rather than rerun inference. |
| Development | Hereditary substitution at created β/projection/η sites, no arbitrary ι reduction. |
| Bare/partial occurrences | Keep the source image name. |
| Proof-justified forms | Source name keeps the faithful form; emit the canonical form under `_ix`; callers do not demote the callee. |
| Image kind | Preserve theorem kind; a source recursor's image is a definition. |
| O9/O10/O12 | Retained for their supported shapes beside clique transport. |
| O12 helper spelling | The current `f._ix.fg` shares the reserved helper namespace; incompatible claims are refused. This text makes no new spelling decision. |
| Caller mixing incompatible encodings | Named refusal, without changing the callee's clique plan. |
| Output packing | Reference closure, distinct from source-unit input selection. |

The following choices remain open and are not made by this guide: C6's Rust
`is_rec`/`is_unsafe` keys; the failed-original promotion behavior; D-M5-1's
structural carried-proof alternative; the phase-9 inverse-image bridge and its
additional large-library coverage; the requested whole-scope corpus/large-run
reconciliation; and the placement of additional tracked integration/CI machinery.
Existing implemented gates remain required while those choices are pending.

## 9. The validators

[`ix validate-lean`](../Ix/Cli/ValidateLeanCmd.lean) has **nine phases**:

| Phase | Assertion / scope |
| --- | --- |
| 1 Compile | Run the current pure-Lean pipeline and report failures. |
| 2 Serde | The reader/writer reproduce the stored bytes. |
| 3 Kernel anonymous round trip | Every selected constant through `Ix.Tc` ingress/egress. |
| 4 Kernel metadata round trip | Named entries against the source; collapsed blocks have the implemented anonymous routing. |
| 5 Decompile | Recover source forms, including inline records/images; default comparison uses per-name digests, with `--full-oracle` for the structural route. |
| 6 Oracle | Unchanged-block auxiliaries equal independently recompiled source declarations by address. |
| 7 Image rules | Stored changed-block recursor images satisfy the generated computation-rule checks; canonical auxiliaries have display names. |
| 8 Provenance | `Named.original` agrees with the source-form compile and the checked packaging/leak conditions. |
| 9 Clique values | Evaluate stored transported members against the source on the distinguishing inputs and limited unfolding the validator supports. |

Phase 9 counts unsupported/unevaluable members and reasons. It does not check all
carried lemmas, source encoding constants, O7–O12 canonical forms, or arbitrary
inputs/deep fixpoint unfolding. Its passed summary must be read with those counts.
The pending inverse-image bridge for changed-inductive clique cases is not
established by unrelated fixture passes.

Phase 4 excludes entries with `Named.original`, inline rewrite records and reserved
display names from its direct source comparison; the other phases cover the
specified provenance/replay questions. For collapsed blocks, the anonymous route
is gated and the metadata-route verdict is diagnostic. Phase 7's rule checks run
in the executable `Ix.Tc`; the certified checker's separate admission/theorems
must not be inferred from that phase's name.

Source-file mode supplies an independent source oracle. With `--ixe`, phases 1/4/9
are skipped and phases 6–8 use decompiled source forms, a weaker oracle. Explicit
phase skips, caps, namespace filters and `--local` change coverage. A PASS on that
scope is not the unfiltered nine-phase result. `--local` selects the file's source
closure plus required support through `EnvScope`; the former blanket statement
that all current closure producers omit recursors is not the current selection
contract.

[`ix validate`](../Ix/Cli/ValidateCmd.lean) invokes Rust's separate eight-phase
auxiliary-validation pipeline: compile, auxiliary congruence, ephemeral-leak
checks, group canonicity, debug decompile, auxiliary round trip, no-debug/serde
decompile (including the per-constant fidelity leg), and nested detection.
Its phase numbers are not aliases for the Lean nine-phase table. It compiles Rust
Pass 3, resolves changed auxiliaries at `_ix` display names and counts introduced
reserved declarations separately where required. The shared FFI implementation is
[`lean_env.rs`](../crates/ffi/src/lean_env.rs).

The `aux-cert` suite uses local fixture closures by default. Its whole-file mode
adds the stated local/whole bridge; a local run does not prove that bridge by
itself. The [gate guide](compiler-gates.md) distinguishes these modes and their
records. The certified checker and W/W+/S lane answer the separate per-output
meaning questions in [compiler-certification](compiler-certification.md);
validator success alone is not those accepted decisions.

## 10. Performance

The measured compiler costs include source preparation, block work, sharing,
merge and serialization. Thread-time totals and wall-time phases are different
quantities and must not be added as if they were disjoint elapsed time. Some Rust
writer timers are nested; the [Rust guide](compiler-rust.md) describes that scope.

The earlier bottleneck profile motivated memoized DAG helpers, stable view reuse,
avoiding repeated optimizer preparation and repeated string-key formatting, and
byte-neutral writer work. Those implementations are present. Fresh-variable
order, traversal order, fuel and metadata provenance constrain such optimizations;
an unchanged hash on a fixture is not their semantic proof.

The following **earlier source-pinned PERF measurements** on the shared box used
**32 configured compiler workers**. They are retained history, separate from the
later combined 881 and default-S gate evidence in §7.3:

| Compiler / sealed source | Timer scope | Init+Std | Mathlib |
| --- | --- | ---: | ---: |
| Lean, `bae05065` | CLI-reported **compile phase**, excluding its separate serialization phase. | 66.524 s | 536.982 s |
| Rust, `3a889b60251f3d3c8742ba9aa88a5f3dbf7ade7e` | CLI-reported **compile-and-write total**, with both `IX_COMPILE_WORKERS=32` and `RAYON_NUM_THREADS=32`. | 19.174 s | 91.400 s |

The exact `-a3` bytes were checked. Configured worker count is not a claim that
32 workers were continuously runnable. These are different timer scopes on
busy-box runs, not a controlled speedup ratio or timings of combined 881.
Earlier slower observations remain part of the evidence; the bounded Rust repeat
and external load/cleanup context must not
be discarded to suggest repeated-run statistics. Lean whole-command timing also
includes its CLI's cached dependency-build call; Rust's `--no-build` command has
a different setup scope. Compile, serialization and whole-command rows must be
labeled separately.

[BENCHMARKS.md](../BENCHMARKS.md) is the home for reproducible benchmark recipes
and a future reconciled quiet-window table. Its historical rows must be read with
their recorded source/toolchain/mode. Quiet-box measurement and final release
reconciliation are still pending; no new numbers were measured for this document.
The current full-Mathlib Lean `Ix.Tc`/Rust CLI typechecker timing pair remains
unmeasured. Historical Ixon-v3 checker rows and the certified per-record kernel's
timing measure different paths; W+ and S cone costs are separate again.

## 11. The output contract

This section states what a compiled artifact is intended to mean and identifies
the implementing paths and known exception. It is the contract a checker tests
or establishes for a particular output, not a claim that the complete compiler
already has a general correctness proof. The certified interpretation of accepted
W/W+/S decisions is [compiler-certification](compiler-certification.md); the
validators have the scope of §9.

A *block* is a component of the source reference graph. A block is *changed* when
`Pass.isChanged` detects different canonical classes or moved/evaporated nested
positions. Its *logical unit* includes its auxiliaries. The *independent export*
of `c` is Lean's declaration compiled without Pass 3 rewriting, with references
resolved by name in the same artifact. These terms do not redefine output packing,
which remains reference closure (§6.3).

### 11.1 Names, addresses and kinds

An `Ixon.Env` holds anonymous constants by address and a name table whose `Named`
entry supplies an address and metadata. Several source names can share an address,
for example when a class collapses. `insertCanonicalAlias` chooses the reverse
index's earliest alias in seed order. Primary/aux address claims are checked before
the Lean merge; an incompatible second claim fails the block. Intentional `Named`
metadata overrides and the promotion exception are described separately below.

An address comparison and a cached `Ix.Name` comparison have the implementation's
hash semantics. The per-output certification lane does not acquire a new hash
injectivity axiom from this description; its audited reading/checking statements
retain their own trust boundary.

### 11.2 What the Ix constant under a Lean name denotes, by case

The principal paths are in [Pass/Driver](../Ix/Compile/Pass/Driver.lean),
[Pass/Cliques](../Ix/Compile/Pass/Cliques.lean),
[Translate](../Ix/Compile/Pass/Translate.lean) and
[CompileDriver](../Ix/CompileDriver.lean).

| # | Case | Meaning and implementing path |
| --- | --- | --- |
| 1 | Unchanged block, no image-head references, not a transported member. | The independent export: source kind, universe parameters, type and value/rules, with canonical block/member/sharing representation and source presentation data in metadata. `prepareBlock`/`prepareCliques` leave the term on this path. |
| 1b | Source auxiliary of an unchanged inductive block. | Pass 2's regenerated constant under the source name; its own independent source form is attached as `Named.original` by the promotion path. `compileMutualAuxTail`, `compileConstNoAuxPure`, `promoteAuxDriver`. Oracle/W checks compare the actual regenerated and source forms; no general generator theorem is asserted here. |
| 2 | Inductive or constructor of a changed block. | The canonical inductive/constructor of its class. Collapsed members share the class address. `compileBlockWithAux` and Pass 1 supply the classes. |
| 3 | Image-kind auxiliary of a changed block. | The image: generated for recursors; otherwise the source auxiliary's own value with head occurrences rewritten. It is over the source telescope and universe parameters. Its stored type receives the same head rewrite, so a type mentioning `below`, for example, can be convertible rather than textually equal to the source type. A source theorem stays a theorem; a source recursor becomes a definition with abbreviation hints and source safety. `Names.imageKinds`, `compileImageBlock`, `imageDeclWith`, `imageInfo`, `runImageBlock`. `Named.original` is the source form without rewrite. |
| 3b | Other source auxiliaries of a changed block. | The ordinary rewritten baseline of case 5: `noConfusion`, `sizeOf`, matchers, injectivity/index helpers and the source `IndPredBelow` block. The canonical `IndPredBelow` family has separate display names. |
| 4 | Canonical reserved names. | Declarations with no independent source-name counterpart: Pass 2 display auxiliaries, canonical `IndPredBelow`, transported clique functionals/helpers/lemmas, proof-justified `c._ix` forms and their helpers, O11b's paired canonical declarations. Image terms reference the canonical recursors here. Dependencies keep their source names unless the specific transformation introduces a particular canonical helper. `ixAuxName`, `moveToDisplay`, `planClique`, `compileCanon`, `unitPasses`. An incompatible existing reserved-name claim fails. |
| 5 | Ordinary constant referencing an image head. | Source declaration with full head applications rewritten by the ordered definitional passes or instantiated images. Bare/partial applications keep the source name of the image. Outermost rewritten occurrences carry inline provenance. Kind and universe parameters stay source-owned; statements receive the same head rewrite. `prepareBlock`, `rewriteBlock`, `rw`; recorded in `p3Rewritten`. |
| 5b | O11a declines on a split `sizeOf` recursion. | O2/the faithful image baseline remains, with the actual decline recorded through `declineLookup` and `p3NonCanonical`. The diagnostic is not a canonical result. |
| 6 | Proof-justified occurrence/unit pass. | The source name keeps case 5's faithful baseline. A canonical form is emitted at `c._ix`, with `PJ-FORM-<pass>` for the source name. Callers retain source references; no blanket redirection to `_ix` occurs. `RwState.site`, `inPlace`, `pjFired`, `compileCanon`, `unitPasses`, `p3PjForms`. |
| 7 | Member of a transported definition/theorem clique. | Source kind, universe parameters and type, with transported value/proof `Φσ`. The hook checks the source type up to its alpha/metadata comparison. Root inline metadata retains the source value. An equal-specification alias uses its representative's transported declaration under its own source name. `planClique`, `prepareCliques`, `withValue`, `Clique.transport`. |
| 7b | Equation lemma carried with the clique. | Source theorem statement with the transported proof and source inline record. Reached packed lemmas are regenerated at canonical helper names. Repacked structural groups retain the `SHAPE` boundary of §5.3. `memberEqLemmas`, `packedLemmas`, `scheduleCliques`, `planClique`. |
| 7c | Source encoding constants of a transported clique. | Source form under source names, because their statements follow source order (`ORDER-STMT`). Uncarried source lemmas can still refer to them. `isEncodingName`, `encodingOwner?`. |
| 7d | Clique plan is baseline, unchanged or not encoded. | Ordinary source/image baseline. `.baseline` records `NOSPEC` or `SHAPE`; `.unchanged` needs no transport; `.notEncoded` is outside the recognized input-clique route. `CliqueOutcome`, `planClique`. |
| 8 | Caller mixing a transported member with incompatible source encoding constants outside its unit. | Named refusal: `Pass 3 cliques: caller refused (block rule, callers adapt): …`. The compiler does not change the clique to accommodate that caller. `cliqueCallers`, `callerRefusalPrefix`. |
| 9 | Compile/claim/missing-dependency failure. | Record the block members as failed in `ungrounded`. The normal Lean branch does not merge its failed block result; the normal Rust scheduled branch rolls back its newly published named claims/records. Content caches and earlier successful dependencies are not a guarantee of an empty environment. The promotion exception in §11.6 remains. `compile-lean` writes no artifact with failures unless `--allow-partial`. |
| 10 | Grounded input name has a reserved `_ix` component/prefix. | Refuse the compile with the least pretty-form diagnostic selected by `reservedInput?`/`pass3ReservedInput?`. The scan is over the supplied grounded condensation; excluded ungrounded inputs remain named failures, not accepted declarations. |

Case 3 includes `rec`, nested `rec_N`, `casesOn`, `recOn` and the applicable
`below`/`brecOn` families with `.go`/`.eq`, restricted to source names actually
present. `below`/`brecOn` are image-kind only for recursive source blocks.
Case 4 uses `_ix` display names such as `x._ix.rec`, canonical-position nested
names, `g._ix._mutual`, `g._ix.mutual`, `x._ix._f`, transformed matchers and
`_ix_retyped` helpers. [Names](../Ix/Compile/Pass/Names.lean) defines their spelling.

### 11.3 The records the output carries

**Inside the artifact:**

- `Named.addr` is the compiled address. `constMeta` holds source names, binder
  information, metadata, level spelling, inline records, mutual-member metadata
  and auxiliary layout. `hints` is the exact per-name reducibility information.
- `Named.original` holds the address and metadata of the independently compiled
  source form for an image or promoted regenerated auxiliary. An alias must not
  borrow a different source declaration's original (§6.1 D11).
- `_ix.inline`/`_ix.inline_meta` identify the source occurrence and its metadata
  root in `metaSharing`, at an ordinary rewrite or at a transported member/carried
  lemma's value root. Decompilation replays the source; a value checker must read
  the stored transformed term when evaluating transformation correctness.
- `_ix.clique` is the string record on a transported canonical functional:
  encoding, source order, `sigma`, order source, classes, aliases and causes.
  `CliquePlan.record` constructs it. It is a diagnostic/provenance record, not a
  proof term.

**Outside the artifact:**

- `CompileEnv.p3NonCanonical` is a compile-time decline map, currently populated
  by O11a declines and exposed in the changed-set file. Repeated causes for the
  same member use the last inserted cause in rewrite/merge order. It is not an
  insert-once record of every decline and is not serialized in `.ixe`.
- `<stem>.changed.json` describes the final driver's changes (§11.5).
- The tracked non-canonical fixture records (§7.2) are test data, not emitted
  compiler output. Their 959-row default and 157-row transport oracle have
  different consumers and do not constitute a runtime exception list.

The representation is documented in [Ixon](Ixon.md). The implementing fields are
in [CompileM](../Ix/CompileM.lean), [SideCar](../Ix/Compile/Pass/SideCar.lean),
[Cliques](../Ix/Compile/Pass/Cliques.lean) and
[ChangedSet](../Ix/Compile/ChangedSet.lean).

### 11.4 Identity requirements a checker may rely on

1. **Full declaration identity includes kind.** A source name keeps source kind,
   universe parameters and type under the specified head rewrite, with the
   explicit recursor-image-to-definition exception and the failure cases above.
   A theorem image stays a theorem. A transported member changes the value/proof,
   not its other source `ConstantInfo` fields. A checker may refuse any other kind
   change; the adversarial controls exercise that refusal.
2. **Binder ownership is source identity.** The transformation must touch only
   the recursion binder and the encoding-owned threaded copies/dictionaries.
   Equal types, positions or user-shaped tuples do not grant ownership. The
   [ownership suite](../Tests/Ix/Compile/CliqueOwnership.lean),
   [recovery](../Ix/Compile/Clique/Recover.lean) and §9's value checks exercise this
   contract; they do not establish the complete general transport theorem.
3. **Canonical and faithful-only forms remain distinct.** The categories and
   causes are §7.1–§7.2. A source image, order-dependent source encoding or retained
   baseline can satisfy faithfulness without sharing the canonical form's address.
   A claimed canonical helper must still meet its declared typing/value contract;
   being named `_ix` is not evidence of correctness.
4. **Not promised by canonicity:** arbitrary theorem-proof identity; a canonical
   address under presentation changes outside Def 4.3; or an unchanged block
   address when the actual source unit gains an on-demand auxiliary. These limits
   do not narrow the general compiler meaning obligation to the passing fixtures.

W/W+/S check particular correspondence/meaning statements independently of the
compiler's diagnostic labels. The remaining general proofs must establish the
contract on their original domains, including production invariants and runtime
refinements; this guide adds no hidden freshness/hash/domain premise to discharge
them.

### 11.5 The changed-set record

`compile-lean` writes `<stem>.changed.json` next to the `.ixe`.
[`ChangedSet.pathFor`, `ofCompile`](../Ix/Compile/ChangedSet.lean) derive the path
and contents from final driver state. The record changes no `.ixe` byte and is
available from the compile result independently of the CLI writer.

The format is `ix-changed-set/1`, with deterministically sorted arrays:

```json
{"format":"ix-changed-set/1","mode":"pass3","counts":{},"blocks":[],"cliques":[],"entries":[]}
```

`blocks` contains changed source groups, their names/hashes/addresses and image
heads. `cliques` contains input clique order, outcome, encoding, reason, permutation,
carried lemmas, aliases, the clique record and stored canonical helpers.
An entry contains `name`, `hash`, `change`, `differs`, `cause`, `addr`, `original`,
`ref` and `detail`. `name` is the pretty form; `hash` is the cached Ix name hash
used by this implementation, not a structural identity theorem. Distinct names
can have equal pretty forms, so consumers must not discard the other identity data.

| Change | `differs` | Source / reading |
| --- | --- | --- |
| `image` | true | `p3Heads`; source auxiliary name holding an image; `IMAGE`. |
| `rewritten` | true | `p3Rewritten`; ordinary declaration with an image-head rewrite. |
| `decline` | true | `p3NonCanonical`; O11a decline with its actual diagnostic. |
| `transported` | true | Transported clique member, with any recorded cause. |
| `carried` | true | Carried equation lemma of that clique. |
| `canonical` | true | Reserved-name helper with no independent source-name counterpart. |
| `pj-form` | false | Source name retaining its baseline; reference points to its `_ix` form. |
| `inherited` | false | Input reference to a proof-justified-form source name; caller keeps that source reference. |
| `lean-form` | false | Baseline clique (`NOSPEC`/`SHAPE`) or source encoding constant (`ORDER-STMT`). |
| `refused` | false | `ungrounded` with the named clique-caller refusal. |
| `failed` | false | Other `ungrounded` member failure. |

`differs` is the compiler's claim about the independent export, not a byte
comparison or a certification verdict. A name can have more than one change claim.
Entries are sorted by `(name.pretty, name-hash string, change.tag, cause-or-empty,
ref.pretty-or-empty)`; this ordering is not a checked uniqueness guarantee.
Failure/refusal rows have `differs: false` and `addr: null`; this does not claim
that an artifact declaration equals the source. Several ordinary-claim loops
skip failed names, but the record builder does not globally remove every other
claim for a failed name. The known promotion exception means that absence from
the *artifact* cannot be inferred solely from such an entry in a partial output.

The groundedness scan reports missing input dependencies, rejected dependencies,
out-of-scope variables/levels and metavariables as named
`UNGROUNDED-INPUT: …` failures. Both compilers preserve those failures rather than
silently count-and-drop the names. The CLI's partial-output policy still applies.

The [changed-set suite](../Tests/Ix/Compile/ChangedSet.lean) checks the record's
artifact/name consistency, inline and reserved-name coverage, record and artifact
equality at 1 and 32 workers, the historical twelve Init+Std name fragments and
optional CLI-record equality. It has no dedicated failed/refused serialization
or global supersession control. A consumer can cross-check addresses, source
image-kind membership, original forms, inline replay, clique membership and
helper records. Those checks do not prove the intended transformed value merely
by finding a matching diagnostic entry.

**The certifier does not read this file.** W+ checks its association, type rows
and equation/value rows against the folded artifact/support. The value-level
stage included in S by default checks its separate supported-value conclusion;
it does not turn the compiler's `differs` claim into a certificate. Listing a
name here cannot make it Certified; omitting a name cannot by itself make it Rejected.
The record is useful for diagnosis and coverage accounting. Its cause texts,
plan classifications and `differs` claims remain compiler reports until checked
by the relevant independent condition. See
[certification §1.3 and §5](compiler-certification.md).

### 11.6 Known exception and reconciled inconsistencies

**Promotion failure remains an exception.** If original-form compilation of an
already regenerated auxiliary block fails, the driver records failure but can
still promote names that the owning inductive's auxiliary tail registered.
[`CompileDriver`](../Ix/CompileDriver.lean)'s sequential branch and
`applyAuxOutcome` both retain this behavior; Rust's promotion branch has the
corresponding separation. Normal scheduled-block rollback does not repair it.
`compile-lean` refuses to write an artifact by default, but `--allow-partial` can
expose those retained names. Changing this behavior and the affected refusal/
dependent records remains owner-pending; the contract must show the exception.

Other inconsistencies in the earlier text are resolved as follows:

- Size-of producer edges are part of current Pass 3 scheduling at the relevant
  driver entries, not a choice between current on/off compiler modes.
- O11a's diagnostic describes a failed source-minor placement and retains its
  exact emitted wording; it is not reinterpreted as a missing expression.
- Reserved-input diagnostics use the least pretty-form message on the supplied
  grounded condensation. Groundedness failures outside it remain failures.
- Bare/partial occurrences reference the stored source image; there is no extra
  `a._ix` image constant. Canonical display auxiliaries and source images differ.
- Repeated decline causes are last-wins. Address claims, intentional metadata
  overrides, memos and decline maps do not all have one merge policy.
- A failed normal Rust block can leave anonymous content-cache entries while
  withdrawing its new named claims. “Publishes nothing” must not be read as a
  theorem that every global map or partial artifact is empty.

## Appendix: open obligations and history

The remaining general proof work includes production source/reference closure;
structural name and occurrence identity; capture-avoiding substitution and fresh
family allocation; generated declaration/constructor/recursor correspondence;
image typing, level substitution and relocation bounds; telescope and recursion
semantics for the optimizers; clique ownership/transport; and the driver/emission
composition. Runtime memo/bridge refinements and the Rust mirror remain explicit.
Their domains are not narrowed to the libraries or closed terms that pass tests.

The pending choices in §8, gates for subsequent compiler changes, quiet-window
benchmarks and release reconciliation remain separate deliverables. The accepted
combined 881 and default-S results are exactly those in §7.3. No later allocator, `nonDep`, tagged
occurrence-key or L2/L3 proof branch is included by implication in this revision.
The current 959-row record must not be described as the proposed 963-row record.

Historical comparator modes, prototype ablations, the default flip and slice-6
surgery deletion explain the current design. They do not describe a supported
second compiler. Old study totals and proposed module names have been replaced
above by current definitions and registered assertions; retained migration numbers
are explicitly historical (§7.4).

Product documentation cites tracked source, theorem declarations and guides.
Working notes are useful provenance for maintainers, but an untracked report is
not the only public statement of a theorem or the evidence for claiming an
unimplemented transformation. When source, toolchain, format, theorem hypotheses
or gate scope changes, reconcile these sections and the
[record/reference process](compiler-gates.md#toolchain-format-and-lane-changes)
together.
