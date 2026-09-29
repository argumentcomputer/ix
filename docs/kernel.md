# Certified Lean kernel

`Ix.Kernel.check` checks an ordered list of anonymous declarations and returns
an environment only when it can construct its model extension. The three
public consistency theorems apply to this executed function. `Ix.Kernel` is
being developed to replace `Ix.Tc`; the runtime consumer migration and the
removal of lean4ix are still pending.

The implementation sequence and remaining gates are in
[`plans/ix-certified-roadmap.md`](../plans/ix-certified-roadmap.md). This page
records the current contract and the disposition of the old verification
system. It does not certify the Lean-to-Ixon compiler, Rust checker, or IxVM.

## Data and evidence

| Layer | Meaning | Established by |
| --- | --- | --- |
| `Decl`, `Block`, `Const`, `VExpr`, `VLevel`, `ConstRef` | The supplied declarations, member/constructor positions, terms, and positional universes | Input data, without a typing assumption |
| `Ix.Ixon.Types`, `Ingress.Context`, `ExprReads`, `BlockReads` | Pure production Ixon data and its exact reading after table, projection, sharing, and literal resolution | `readExpr_reading`, `readBlock_reading`, and reading determinism |
| `Egress.Record`, expression/declaration layouts | Raw payloads plus the sharing, table, and let-spelling choices needed to reconstruct the source | Checked writer readings and `records_roundtrip`, with exact list equality |
| `AExpr`, `PropWhen` | A reading with a condition at each binder describing when its codomain is a proposition | `annotate_erase` proves exact erasure; separate scope checks include annotation conditions |
| `Typed`, `TypedSort`, `Reduced`, `Conv` | Search results with erased semantic evidence for this environment and context | `inferA`, normalization, conversion, and the declaration checkers |
| Admission candidate | An ordinary inductive shape, structure description, or standard primitive interface | A reader proposes it; validation and exact generated-block comparison justify installation |
| `Certified.Ordinary.Stage` | The family/constructor stage, optionally extended with a supplied recursor at its actual reference | Each stage constructs its model and constructor reading; Nat and structure facts share this interface |
| `Env`, `ConstantEntry`, `Environment` | Concrete storage and its functional lookup view, including types, bodies, equations, and facts | Admission constructs `AdmissionClaim` and exact `Block.Installed` readings |
| `Model`, `SetTheory`, interpretation | A simultaneous realization of the installed entries in an explicit set theory | Model extension and the closed acceptance theorem |

An annotation is not a typing certificate. Its erasure theorem says exactly
which raw expression was read; `inferA` checks binder conditions. Similarly,
recognizing a familiar inductive name or shape is not admission evidence.

`StepClaim` extends realizability and well-formedness. `AdmissionClaim` also
preserves every old lookup. The separate fidelity theorems
`checkDecl_installed`, `checkDecls_installed`, and `check_installed` establish
the supplied universes, erased types and definition bodies at their exact
references, including nested constructors. They do not reconstruct bytes or
authenticate addresses. Specialized publication lemmas describe the additional
equations and facts. `ConvClaim` is conditional on formed inputs; composing
it requires a formed intermediate term.

## Supported profile

The current checked input is a list of `Decl β`, for any `β` with decidable
equality. `checkAddressed` specializes it to opaque `Address` keys.
`checkEnv` reads ordered production Ixon constant pairs and literal blobs
through the pure `Ix.Ixon.Types` boundary.

| Input | Current behavior |
| --- | --- |
| Single safe definition, theorem, or opaque | Check its declared type and body; theorems must have a propositional type |
| Variables, universes, constants, applications, lambdas, Pi types, lets | Check scope, universe arity, typing, and binder conditions |
| Ordinary inductive family | Check the family and constructors independently; validate positivity, universe constraints, and the complete supplied declarations |
| Supplied ordinary recursor | Associate by the major premise; check its complete type, metadata, rules, elimination, and freshness at its own reference |
| Structure-shaped ordinary block | Publish projection typing, iota, and eta when the field and Prop restrictions hold; otherwise try ordinary admission |
| Natural numbers | Recognize the natural-number interface; literals name their admitted family; literal/constructor conversion and recursor iota are supported |
| Equality | Ordinary admission plus K-like reduction through checked constructor synthesis and proof irrelevance |
| Quotient | Check the four primitive declarations and soundness against the admitted Eq/quotient interfaces; prove lift and eliminator computation |
| `propext`, `Classical.choice` | Check the generated types against admitted Eq/Iff/Nonempty interfaces and construct their realizations |
| Arbitrary axioms, unsafe/partial declarations, general mutual or nested inductives | Decline outside the supported profile |
| String literals, full Lean universe conversion, full Mathlib | Not a current coverage guarantee |

The tracked positive fixtures include False, True, And, Or, Nat, List, Eq,
Prod, dependent subtypes, standard axioms, and quotient computation. Each
feature has malformed or unsupported controls. Passing those fixtures is a
supported-profile check, not a completeness theorem about Lean.

Declarations must arrive in dependency order. References to unavailable
constants and duplicate addresses are rejected. An inductive block's own
members are handled by its admission construction. Ixon ingress preserves
physical member and constructor references. Production stores an inductive
family and its recursor separately; the driver consumes an associated pair
together and checks all intervening records afterward in their relative
order. Every external reference must resolve against the checked prefix.
The existing combined family/recursor fixture layout remains supported.

`Ix.Tc` and Rust discover a recursor's owner through its major premise and
compare the complete generated candidate. The certified ordinary reader
uses the same association, restricted to syntactic telescopes in its current
profile; it never normalizes an open peeled body in an empty context.
Association cannot authorize acceptance. A missing recursor admits only the
family and constructors, with Nat or structure facts when applicable. It
does not generate a replacement recursor. Mutual/nested auxiliary recursors
and adding a separate recursor later through single-declaration admission
remain outside this interface.

`checkEnv_reading` establishes `Ingress.Installed`: unique constant and blob
keys, exact source readings, and each primary record installed at its own
reference. Projection records must name the proper owner, member kind, and
position and have empty tables. Sharing edges must decrease; indexes resolve
without narrowing. `checkEnv_has_model` applies to this executed Ixon entry
point. Nat payloads are little-endian; strings and nonstandard binder modes
decline. Address authentication, wire canonicality, and unused table entries
are outside this reading contract.

`Egress.readRecords` retains the layout choices that expanded raw terms lose.
`Egress.writeRecords` reconstructs declaration payloads from those terms,
checks their complete readings against the retained tables, and validates
each reconstructed projection's actual variant and owner. It preserves every
address, record position, declaration field, sharing node, repeated or unused
table slot, and let nondependency hint. Numeric reconstruction rejects values
outside `UInt64`; constructor and rule lists cannot silently truncate.

`Egress.records_roundtrip` proves exact source recovery after any successful
read at the same fuel and with the same reference/blob context. The writer
uses a blank `Context.source`; it does not copy the original primary record.
Its retained sharing and universe tables still carry source layout. The
reading/writing operations do not establish typing, dependency order, key
uniqueness, byte canonicality, or address authentication; use `checkEnv` for
declaration admission. Unused table entries remain outside validation. The
serializer profile includes all declaration variants with ordinary Lean
expression modes; the admission profile remains the smaller one above.

The certified environment retains the checked body of every definition-like
declaration, including theorem and opaque declarations. Delta reduction can
unfold such a stored body. This is the current kernel transparency policy;
host reducibility hints and a theorem/opaque opacity policy are not inputs
to this API. Consumer parity must record any operational differences this
causes.

The recursor K flag is also an explicit policy difference. Ix.Kernel rejects
`k = true` for a shape without K support, but permits `k = false` for an
eligible shape and can still derive a K-like step from typing and proof
irrelevance. Ix.Tc requires the flag to equal its computed eligibility. The
differential suite uses canonical flags for its shared positive corpus and
retains noncanonical Eq/True flags and a forged Nat flag as separate controls.

## Outcomes and fuel

Acceptance carries the model theorem. `Error.rejected` records an
independently established input defect, such as bad scope, a missing
reference, a duplicate address, wrong universe arity, or a sort used as a
function. `Error.declined` records exhausted fuel, an unsupported form, or
conversion that search did not establish. An unsuccessful conservative
conversion procedure does not prove that two terms are unequal.

`Config.fuel` is a recursive depth bound, not an operation budget. Nested
checks retain exhaustion. Normalization returns any proved reduction along
with its stopping cause; a partial reduction can still support a successful
conversion. Failure of an optional strategy does not block a subsequent
proved success. There is no fallback whose Ix.Tc or Rust result is labeled
certified.

`checkAgainst` reuses evidence that the expected type is formed in the exact
current context. Rule checkers establish the common type once and use it for
both endpoints. `checkType_acceptance` proves that obtaining formation first
preserves successful `checkType` results at the same fuel; the first failure
reported can differ when both independent checks fail.

## Mathematical and execution boundary

`check_has_model` and `checkDecls_has_model` are relative to an explicit
`SetTheory V`. It supplies the set-theoretic operations and a countable tower
of Grothendieck universes. `no_proof_of_False` rules out an accepted
inhabitant of a type interpreted as empty. The separate
[`Models/SetTheory`](../Models/SetTheory) package constructs the model with
Mathlib under its stated `OmegaInaccessibles` hypothesis.

The frozen roots permit exactly Lean's standard logical axioms (`propext`,
`Classical.choice`, `Quot.sound`), without `sorryAx`, `Lean.ofReduceBool`, or
project axioms. Type/body/constructor dependency traversal, frozen theorem
statements, import auditing, and compiled runtime auditing are independent
checks. Axiom sets alone do not establish that theorem premises are useful.

The execution foundation is Lean's kernel, compiler, runtime, and core data
representations. At this K3 checkpoint the public runtime closure contains 920 compiled
functions, 16 inherited externs, one inherited unsafe declaration, and no
`implemented_by` or `csimp` replacement. The allowed inherited operations
are listed and explained in
[`Ix/Kernel/Audit/Roots.lean`](../Ix/Kernel/Audit/Roots.lean). No project FFI,
Rust checker, or BLAKE3 operation is reached by the certified checker. An
address is only a key inside this boundary; it is never hashed there. The
Ixon ingress closure contains 962 compiled functions, 23 inherited externs,
two inherited unsafe array accessors, and no `implemented_by` or `csimp`.
The separate reader/writer closure contains 202 compiled functions, 21
inherited externs, and the same two array accessors, also without project
replacements. Its bounded conversions additionally use `UInt64.ofNat`.

Byte decoding, canonicality, address reconstruction, claims, and receipts
have no acceptance theorem at this checkpoint. K3's exact Ixon readings,
admission, and layout-preserving egress are implemented. K4 will connect
supported bytes and pure serialization/decoding;
K5 will connect authenticated subjects and receipts. A theorem about an
accepted raw environment does not by itself prove any of those contracts.

## Validation

```sh
lake -d IxKernel build --wfail
lake -d IxKernel exe kernel-provenance
lake run check-kernel --with-model
```

The standalone package reads the repository's kernel sources and has no
external packages. Its default strict build checks all kernel modules,
frozen audits (including negative controls), and ten fixture modules.
Provenance validates the port inventory, inspected target hashes, source
pins, headers, and license files. `--source PATH` additionally checks the
old source checkout against the recorded source hashes.

The host-only `kernel-differential` executable compares 38 cases against
Ix.Tc: shared positive inputs for every K2 route, corrupted variants, and
explicit differences for search outcomes, ordering, duplicate storage,
unsupported declarations, K metadata, and opaque transparency. It checks
raw declarations through a test adapter, not production Ixon ingress. The
adapter assigns synthetic reference identities, uses Ix.Tc's homogeneous
storage groups, preserves the source K flag, and configures the fixture
primitive references. Neither its translation nor the oracle is a premise
of a certified theorem.

The host-only `kernel-ingress` executable compiles tutorial declarations with
`Ix.CompileM`, serializes and reloads them through the production codec, and
runs `checkEnv`. Its 26 cases cover eight ordinary families, definition and
reduction examples, family-only dependencies, and mutations of recursor
rules, field counts, metadata, and K flags. The compiler, loader, and host
ordering remain untrusted producers. Each case also passes through the
certified reader and writer, comparing complete records and exact production
Ixon bytes; this includes cases whose declarations are declined or rejected.
Pure egress fixtures cover layout duplication, unused entries, sharing,
projection variants, numeric overflow, count mismatches, and changed raw
payloads behind retained table slots. Exact Ixon bytes and outcomes are
retained in `.lake/build/kernel-ingress.jsonl`.

`lake run check-kernel` writes exact raw input trees, outcomes and reasons
to `.lake/build/kernel-differential.jsonl`. The CI job **Certified Lean
kernel** runs the host/standalone/provenance/model gate and uploads that
file and the ingress JSONL. The 2026-09-29 K2 release run passed in a fresh jj workspace with no
project Lean artifacts: 134 standalone jobs, 144 host fixture/provenance
jobs, 342 differential build jobs, 38 comparison cases, and 975 model jobs
including its full axiom audit. That run reused pinned third-party package
caches and unchanged Rust artifacts. No dependency revision changed.
The later K3 incremental full gate passed 144 standalone jobs, 154 host
fixture/provenance jobs, 457 runner build jobs, all 38 differential and 26
ingress cases, and the 975-job model gate. Provenance covers 97 ported,
35 authored modules, and four license files. This run was not a clean build.
Native performance commands and retained
operation counts are documented in
[`Benchmarks/Kernel/README.md`](../Benchmarks/Kernel/README.md). Diagnostic
tracing runs in disposable source copies and is excluded from the certified
runtime. Timings use uninstrumented native executables.

## Removal ledger: lean4ix and Ix.Tc

The root dependency is named `lean4lean` by Lake, fetches
`argumentcomputer/lean4ix` at `a4188d7c2979378d85c6bb41fdd96c3a48a71371`, and
exports `Lean4Lean.*`. TruthMines independently fetches
`digama0/lean4lean` at `e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00`. Both must
leave. The following inventory was checked against the P03 tree on
2026-09-29; all removal rows remain pending.

| Existing surface | Replacement or disposition | Removal gate |
| --- | --- | --- |
| `Ix/Tc/Verify/**` checker statements and proof frontier | Executed `Ix.Kernel` acceptance/model/fidelity roots; retain useful adversarial inputs in kernel fixtures | D01 after K2 gates; behavior outside K2 remains in runtime tests until D02 |
| `Ix/Tc/Verify/Audit/{Basic,Completed,Conditional,Statements,SorryFrontier}.lean` | Kernel axiom/import/runtime audits already supply strict mechanisms and negative controls; discard upstream/native/sorry allowances | D01; no retained helper imports the old audit namespace |
| `Ix/Compile/Verify/{Codec,ExprCodec,ExprSpineCodec,ConstantCodec,ConstantTablesCodec,NonrecursiveConstantCodec,RecursorConstantCodec,MutualConstantCodec}.lean` | Retain useful pure codec proofs under the K4 owner, with exact domains and fresh audits; see contract table below | Port before D01 deletion |
| `Ix/Compile/Verify/{Catalog,IxonValue,SourceValue,Reference}.lean` | Reuse structural wire/table definitions where needed; replace Lean4Lean value relations with K3 exact readings; retire the old semantic square | K3/K4 contracts before D01 |
| Remaining `Ix/Compile/Verify/**`, including `Compile*`, `Arena`, `Sharing`, `Statements`, and its audits | Retire the old compiler/specification proof machinery; do not relabel it as an Ix.Kernel compiler-correctness theorem | D01 after selected structural contracts are retained |
| Root `lakefile.lean` / `lake-manifest.json` | Remove `require lean4lean`, `IxTcVerify`, `IxCompileVerify`, `Lean4LeanBench`, `bench-lean4lean`, the proof dynlib target, and the `build-all` exception | D01; regenerate lockfile and strict fresh host build |
| `ix_ffi_dyn`, `crates/ffi-dyn`, workspace `Cargo.toml` / `Cargo.lock` | Remove the proof-only loader and crate; ordinary host FFI remains independently owned | D01 after final consumer scan and Rust workspace checks |
| `Benchmarks/Lean4Lean.lean`, `Benchmarks/Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Remove replay library, executable, smoke runner and registration; keep kernel-supported test inputs | D01; host runner and benchmark tests |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Remove backend selection, registry, help and active instructions; expose measured Ix.Kernel/Rust comparison through their respective drivers | D01; CLI dispatch and help checks |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Remove the package/member from the generator source | D01; regenerate and assert absence |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}` | Remove the independent upstream dependency and generated driver | D01 regeneration |
| `Benchmarks/Compile/{lake-manifest.json,TruthMines/lake-manifest.json,TruthMines/Members/Lean4Lean.lean}` | Remove both inherited dependency paths and the generated compile member | D01 regeneration and fresh benchmark configuration build |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml` | Replace proof-frontier jobs with strict kernel/model/provenance/differential gates; remove the old runner entry | K2 introduces replacement gate; D01 removes obsolete jobs |
| `flake.nix` | Remove the `lean4lean` target-name/build override and dependency closure | D01; fresh Nix build without stale Lean4Lean artifacts |
| `docs/ffi.md`, `docs/tc-k0-backedge-audit.md`, this ledger | Remove obsolete active commands; mark historical proof claims retired and document the replacement's actual scope | D01/D02 |
| `Ix/Tc.lean`, remaining `Ix/Tc/**`, `Tests/Ix/Tc/**`, CLI, AuxGen, IxVM claim harness, and validation round trips | Move runtime consumers, primitive tables, names/metadata bridges, and behavior tests to their new owners; switch the differential oracle to Rust | D02 after K3/K4 and K6 consumer parity; delete Ix.Tc last |
| Kernel/model LICENSE and NOTICE; explanatory attribution in Rust, IxVM, tests and historical documentation | Retain attribution; a historical mention is not an active import or dependency | No deletion required; active-reference scanner distinguishes these |

The only Lake consumer of `ix_ffi_dyn` in this inventory is
`ix_native_decide_dynlib`, attached to `IxTcVerify`. Recheck at removal time
so integration from main cannot leave an orphaned consumer.

### Contracts to preserve before deleting compiler verification

| Old contract | Selected replacement | Explicit limits |
| --- | --- | --- |
| `deUniv_serUniv` | K4 universe serializer/decoder inverse using the production codec | Keep compressed-successor and UInt64 wire bounds |
| `deExpr_serExpr` | K4 full expression-spine inverse | Keep wire-sized vectors, spine counts, binder bits, and exact whole-buffer consumption |
| `deConstant_serConstant` | K4 all constant variants and side-table inverse | Keep count/address/table bounds; do not silently restrict the old all-variant theorem to singleton definitions |
| `Reads` / `Writes` | Reuse compositional cursor and append laws under the codec owner | These prove codec behavior, not semantic typing |
| `ExprTableWF`, decreasing sharing bounds, reference/universe table resolution | K3 checked resolution plus exact erasure to the supplied Ixon declaration | Detect bad indexes, missing payloads, sharing cycles/forward entries, and unsupported modes before certification |
| Binder-mode erasure relation | K3 explicit accepted mode policy and exact reading; K7 for nonstandard semantic modes | No Lean4Lean interpretation is retained as a hidden premise |
| Production compiler refinement/value-preservation and end-to-end semantic square | Retired as part of D01; a separate compiler-correctness project would need new source semantics and proofs | Ix.Kernel acceptance does not prove that the compiler preserved the original Lean declaration |

The codec chain currently imports `Catalog` from `ExprSpineCodec`, and
`Catalog` imports `IxonValue`. Extract the structural `wireWF` definitions
before porting that chain; merely renaming the codec namespace would keep a
transitive Lean4Lean dependency. The selected codec roots' current audit
lists only the three standard axioms. Other compiler roots permit native
hash/name axioms; those allowances are not inherited by the new boundary.

D01 finishes only when active source imports, every tracked Lake manifest,
generator source/output, build target, backend dispatch, CI and Nix
configuration have no removed consumer. Run the normal host tests, the
clean kernel/model gate, benchmark regeneration, and affected Rust/Nix
checks. D02 additionally requires no active `Ix.Tc` source dependency and
the documented consumer parity corpus, including the ordered-reference
policy. Neither gate is satisfied by deleting the dependency URL alone.
