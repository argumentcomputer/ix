# Compiler shape corpus

`lake build aux-shape-sweep` builds the Lean generator and driver in
`Tests/Ix/Compile/Corpus/`. Run it from the compiler checkout, using that checkout's
Lean toolchain and built `ix` and `kernel-check-ixe` executables. There is no Python
runtime dependency. Generated sources and results belong in a fresh output
directory; existing manifests are never used as an implicit successful resume.

The merge-test `compiler closure and corpus` partition runs the selected/whole
closure end-to-end suite, the corpus driver's self-checks, and the exact
checker-support regression in both rewrite modes. It does not run a broad shape
sweep. The main test job also runs the strict report, index-safety, provenance,
and selected-closure unit controls.

## Coverage

The catalog contains 1,395 base shapes:

- The original 1,325 blackbox shapes, including all 792 single-inductive cells,
  42 deriving variants, 110 nested/container cells, 110 nested deriving variants,
  and 271 declarative templates from the other historical families.
- All 70 base shapes from the second-round neighborhood investigation. Their
  mutual member lists preserve permutation generation in Lean.

The templates in `Corpus/Data/` are input data, not precomputed acceptance
results. The parameterized grids, token substitution, mutual permutations,
candidate generation, elaboration filter, assembly, execution, comparisons,
aggregation, and matrix reporting are implemented in Lean. The historical
declaration and extra texts can be compared exactly with `verify-legacy`.

`--select curated` chooses 279 shapes: all 36 sort/recursion cells, all 110
container/form cells, all 44 original mutual cases, all 70 second-round neighbors,
and representatives of every remaining family. The earlier approximately 120
estimate cannot contain these required grids. `--select smoke` is a separate
four-shape development sample: an ordinary recursive type, a mutual cycle, a
nested List type, and an enumeration. `--select all` includes the full catalog;
a comma-separated list selects explicit IDs and rejects unknown IDs.

The separate `AuxCert` suite retains all 28 whitebox and 10 blackbox minimal
reproductions, plus four existing neighbors. This generator does not replace
their reviewed assertions or known-refusal expectations.

## Generate and assemble

```sh
lake build aux-shape-sweep ix kernel-check-ixe
lake env .lake/build/bin/aux-shape-sweep self-check
lake env .lake/build/bin/aux-shape-sweep inventory
lake env .lake/build/bin/aux-shape-sweep generate --select curated --dir out/corpus-curated
lake env .lake/build/bin/aux-shape-sweep filter --dir out/corpus-curated --jobs 4 --timeout 90
lake env .lake/build/bin/aux-shape-sweep assemble --dir out/corpus-curated
```

Generation writes `shapes.json`, `candidates.json`, and each base/extra probe.
Each extra is elaborated independently with its base declaration. Filtering
records every result and log in `elaboration.json`; normal Lean source rejection
is distinguished from process failure, panic, timeout, or signal. Assembly
requires complete, unique, consistent results. Rejected bases are recorded in
`rejected-shapes.json`; every omitted extra has a reason in `cases.json`.

Accepted bases receive a renamed variant. Mutual shapes also receive every
nonidentity member permutation, with stable lexicographic variant IDs. Renaming
uses whole placeholder tokens, never arbitrary substring replacement. Permuted
sources explicitly omit extra probes that refer to position-numbered nested
auxiliaries, because those source names follow a different first member. That
omission is recorded per case; it does not suppress an address comparison.

Each generated directory is a dependency-free Lake project pinned to the
checkout's `lean-toolchain`. `compile-lean` can therefore build its generated
input without modifying the compiler checkout's modules. Assembly does not assume
that individually accepted extras also compose: the runner elaborates every
assembled source again, and a failure remains visible.

For development parity with the historical read-only catalog:

```sh
lake env .lake/build/bin/aux-shape-sweep verify-legacy \
  --legacy plans/review/auxgen-audit/blackbox/corpus/shapes.json
lake env .lake/build/bin/aux-shape-sweep verify-round2 \
  --legacy plans/review/auxgen-audit/blackbox/corpus/R2
```

## Execute and account for every outcome

```sh
lake env .lake/build/bin/aux-shape-sweep run --dir out/corpus-curated \
  --revision EXACT_COMPILER_COMMIT --mode both --jobs 4 --workers 1 --timeout 900
lake env .lake/build/bin/aux-shape-sweep compare --dir out/corpus-curated --mode both
lake env .lake/build/bin/aux-shape-sweep matrix --dir out/corpus-curated
```

`run-config.json` records the compiler revision, executable SHA-256 digests, Lean version, exact case list,
switch modes, phase selection, process limits, scope, and reviewed expectations.
`--ix PATH` and `--cert PATH` can select already-built binaries from the reviewed
compiler checkout; both are fingerprinted even when using a smaller phase set.
The driver prebuilds the selected generated modules once before bounded concurrent
cases, recording preparation success or failure. Checker summaries must attest to
nonempty work, and unmatched selections are infrastructure errors. If a case
stops after an infrastructure failure, its completed phases are retained and every
remaining requested phase is explicitly not run. `--local` is an explicit alternate compilation scope; the default is whole
environment compilation. The output environment must contain fixture-owned names.

Default phases are `elaborate,compile,rust,determinism,parity,check-rs,check-rs-anon,
check-lean,certified,closure,pack,validate,validate-lean`. `--phases` can choose a
smaller explicit set; it must include `elaborate,compile`. `closure` and `parity`
also require `rust`. Every phase receives a verdict, including `not-selected`,
`not-applicable`, and `not-run`. No missing output counts as success.

The primary compiler is Lean with Pass 3 off and/or on. The Rust compiler is an
explicit legacy baseline. Off-mode Lean/Rust outputs must have identical bytes;
on-mode parity is recorded as not applicable because Rust retains legacy surgery.
Repeated Lean compilation checks complete serialized byte equality in each mode.

Variant comparison retains complete fixture-owned name/address maps and address
multisets, with no generated-name exclusions. Rename comparisons undo only whole
name components. Mutual declaration permutations are a different domain: source
recursor aliases may acquire different motive/minor telescopes, and their full
name maps are measured differences, not a universal alpha-renaming assertion.
The verdict of a permutation is canonical agreement, defined below. Source-facing
adapters retain each source's own semantics, checked by the validation phases;
metadata/original and packing differences require separate retained artifact
comparisons.

### Permutation comparison

Each compile phase writes `compile-records.json`: for every fixture-owned name,
its address, the kind of the constant at that address (`iprj`/`cprj`/`rprj`/
`dprj` projections with their stored block, or `defn`/`recr`/...), and the
address of `Named.original` when present. `compare` reads the base's and the
permutation's records in the same switch mode and requires:

1. **Roots.** The records whose constant is a datatype or constructor projection
   (`iprj`/`cprj`) have the same names on both sides and equal addresses. A base
   with no roots fails.
2. **Canonical auxiliaries.** A record's *key* is owner plus suffix: `X._ix.S`
   has key `X/S`; a record `X.S` whose longest datatype-root prefix is `X` has
   the same key. The *canonical record* of a key is `X._ix.S` when present, else
   `X.S`. A side *nominates* a key when it has the `_ix` record (Pass 3 on: the
   compiler's canonical auxiliaries of a changed block, D14 in
   `compiler-passes.md` §4.8), or when `X.S` is canonical under Lean's name:
   with Pass 3 off, `X.S` carries `Named.original` (an auxiliary regenerated
   from the canonical block, with Lean's own form as its original); with Pass 3
   on, `X.S` has `Named.original` equal to its own address (an unchanged block,
   whose Lean form is canonical). A Lean-named record of a changed block with
   Pass 3 on is an image (original differs from address) and nominates nothing.
   Every key nominated by either side must have a canonical record on both
   sides, at one address. Two different addresses under one key on one side fail.
3. **Nested auxiliaries.** Suffixes beginning with a numbered nested auxiliary
   (`rec_N`, `below_N`, `brecOn_N`, and their `.go`/`.eq`) are spelled by Lean
   under the source block's first member. The `_ix` spelling is meant to be
   `rep₀._ix.rec_N` (`compiler-passes.md` §4.8) and is for `NM_three`
   (`B._ix.rec_N` whichever member comes first), but it can still move with the
   source order (measured: the base of `F2_twoaux` has `A._ix.rec_1`, its
   permutation `B._ix.rec_1`, at one address), so owners are matched, not
   compared by name. Owners with a nominated nested record take part; they
   correspond by name, and the one owner left on each side corresponds to the
   other; any other leftover fails. For corresponding owners: with Pass 3 on,
   every nominated nested record is compared per canonical position (the
   canonical record of `rec_N` on each side, `_ix` first); with Pass 3 off, the
   regenerated Lean-named records of each family (`rec_*`, `below_*`,
   `brecOn_*.eq`, ...) must have equal address multisets, because Lean numbers
   them in the source's own discovery order (measured: `NM_three`'s
   permutations carry the same three `below_N` addresses under other indices).
4. Everything else is measured, not asserted: the full name map, Lean-named
   images with Pass 3 on (Lean's telescope), Lean's own non-regenerated
   auxiliaries (with Pass 3 off: `below_N`/`brecOn_N`, `_sizeOf_N`,
   `noConfusion`, user aliases), and `Named.original` itself. `_ix` records
   whose owner is not a datatype root (definition-clique encodings,
   `compiler-passes.md` §5) are listed per row as `outOfScope`.

A row passes when the roots and canonical auxiliaries agree; its name-map
differences are still recorded. `compare` prints how many permutations agree,
how many of those differ in their name maps, and how many roots and canonical
auxiliaries it compared. `self-check` has a valid and an invalid control for
each requirement, with Pass 3 off and on. `records --env FILE --ns PREFIX`
prints the same records for any environment, for investigation.

Source ownership is inventoried by elaborating each source serially before
parallel oracle work. Namespace classification uses the visible form of private
names, while `source-ownership/*.json` preserves every original string/numeric
name component. Imported declarations in the same namespace are excluded.
Generated images are included only when the exact original prefix before `_ix`
is a source-owned declaration. This preserves private identity and includes
canonical nested helpers whose index/spelling changed from the source auxiliary.
Each compiled output records public/private source counts, generated-image counts
and complete original identities in `compile-ownership.json`; omitting an owned
source declaration is an infrastructure failure.

Both executable kernels check all fixture-owned names. The certified checker
checks every record of the supplied artifact, and the shared strict
`KernelReport` parser validates its exit status, complete JSON protocol, unique
record addresses, and explicit owning-address coverage. Textual CHECK_IXE_ROOTS
is unset because displayed private names cannot preserve numeric components.
Coverage uses the environment's name-to-primary-record mapping, not the checker's
capped display-name list. Per-name accept/decline/reject/blocked outcomes remain
in `certified-names.json`; documented certified declines are distinct from passes.

Selected compilation scopes include explicit checker-support ground in addition
to ordinary dependencies and compiler support. For example, the pinned Nat.land
certificate needs Nat.mul even when no source dependency mentions it. The
untrusted policy in `Ix.Common.CheckerSupport` selects existing source records;
the certified checker still verifies them and its unchanged pins. Raw dependency
and default whole-file selection remain unchanged. Run
`lake exe checker-support-regression` for the exact Single corpus regression,
whole-output record equality, both switch modes, and raw-closure negative controls.

The closure phase ports the legacy Rust `compile --consts` driver, comparing
complete `Named` records against Rust whole output and checking each produced
closure with both executable kernels. It is explicitly labeled as that backend;
it does not establish raw-dependency or Lean per-root closure behavior. The
separate in-process compiler determinism suite covers those Lean producer paths.
Pack checks every fixture-owned root, including ordinary users and auxiliaries,
with both executable kernels. Per-root manifests preserve failures and log paths.

`compare` retains all renamed/permuted address differences and missing names,
including source-numbered auxiliaries and string-bearing derived code. It reports
per-name and address-multiset results. There are no historical `_N` or `Repr`
regex exclusions. A difference is evidence to classify, not a semantic-equivalence
claim. The matrix separates families, phases, switch modes, and verdict classes.

An optional `--expected FILE` contains reviewed exact case/mode/phase records:

```json
[{"caseId":"EXACT_ID","mode":"on","phase":"compile",
  "diagnostic":"EXACT_REPRODUCIBLE_DIAGNOSTIC","cause":"DOCUMENTED_FINDING"}]
```

Only a failing phase with exactly that complete diagnostic can become
`known-unsupported`; matching one message cannot hide additional failures in the
same phase. Timing-bearing or otherwise unstable diagnostics remain failures
until a stable, complete classification can be reviewed.
Infrastructure errors cannot be exempted, empty causes are invalid, and an
unexpected pass fails as a stale expectation. These entries do not erase
downstream unrun required phases. Without an entry, a new failure remains a
failure. Source rejection and certified decline have separate classifications.

Large reproducible `.ixe` files are removed after their checks; sources, logs,
names/addresses, per-root results, and verdict manifests remain. `--keep-envs`
retains the environments for investigation and requires sufficient disk space.

## Aggregate and broad runs

`aggregate --dir DIR --size 45` writes family-grouped sources,
`aggregates.json`, and an exact member manifest. A fresh generated directory can
run those cases with `run --cases aggregates.json`; this uses the same oracle and
parity machinery. The matrix reads `run-cases.json`, the exact executed case
manifest, including aggregate family IDs. Missing, duplicate, unknown, or empty
phase ledgers fail before summarization. Aggregate compilation is separate evidence from per-case and
metamorphic comparisons.

A broad run uses `generate --select all`, then the same filter/assemble/run/compare
pipeline. Coordinate the pinned compiler revision, CPU allocation, and disk budget
before starting it. A successful smoke is development evidence, not a substitute
for the complete sweep or the 38 tracked minimal reproduction gates.
