# Bounded source coverage and artifact reproducibility

C1 and C2 are delivered by `source-coverage` and `check-source-coverage`. The producer
compiles fixed Ixon inputs through the actual validated pipeline and observes
each executable stage. The separate Lean checker runs it twice in fresh
processes, compares every artifact byte, checks the reviewed
[matrix](../fixtures/source-coverage/expected.json), and independently inspects
the five native exits, including two unchanged upstream computations.

## Coverage matrix

Root prefixes below identify the full roots in the matrix. The first eleven
rows are synthetic canonical Ixon, built with the ordinary sharing/address
gate. Two rows retain original production bytes from the [Std contact](corpus-contact.md).
The final five rows are [pinned upstream Lean exports](../fixtures/ixon-upstream/README.md).

| Case | Ixon root prefix | Last accepted stage | Nat result | Exact rejection after that stage |
| --- | --- | --- | --- | --- |
| `scalar-zero` | `11f9a7889be4f23e` | ELF + native check | 0 | — |
| `scalar-42` | `2e926c5f48aec39e` | ELF + native check | 42 | — |
| `scalar-max` | `b1657e7f011436f0` | ELF + native check | `2^64 - 1` | — |
| `scalar-overflow` | `e25089a56add5d2b` | baseline IxIR₂ | `2^64` | scalar selector: `unsupportedScalarShape` |
| `direct-call` | `7af1bc632982b71b` | baseline IxIR₂ | 42 | scalar selector: `unsupportedScalarShape` |
| `ctor-zero` | `c95daf35af17a422` | baseline IxIR₂ | 11 | scalar selector: missing constructor schema |
| `ctor-succ` | `89a90ce06c7c1c06` | baseline IxIR₂ | 22 | scalar selector: missing constructor schema |
| `nat-zero` | `a71f22b953667431` | baseline IxIR₂ | 11 | scalar selector: missing constructor schema |
| `nat-succ` | `c95c2bb1a4ce38e2` | baseline IxIR₂ | 22 | scalar selector: missing constructor schema |
| `bare-literal` | `a29b2725659eda05` | Ixon | — | usage: `freezeNeeded` |
| `extern` | `2b2d31a29f10197c` | usage | — | validated erasure: extern ownership ABI |
| `std-contact` | `1bc7e2215a1967d8` | Ixon | — | usage: `freezeNeeded` |
| `std-failure-closure` | `131533e96baa7f50` | addressed IxIR₀, before source certification | — | erasure validation: missing `Covered` at root |
| `upstream-applyClosed` | `b81b754f02c1b632` | ELF + native check | 3 | — |
| `upstream-captureClosed` | `5628cfe1b4f959fb` | baseline IxIR₂ | 2 | closed Nat selector: `capturedPap` |
| `upstream-letClosed` | `6c737171f1a3c482` | ELF + native check | 4 | — |
| `upstream-addClosed` | `799b7939dcc3c158` | addressed IxIR₀, before source certification | — | erasure validation: missing `Covered` at dependency `1ce12e12485a4793…` |
| `upstream-recClosed` | `1248f5d1b9eb3c50` | addressed IxIR₀, before source certification | — | erasure validation: missing `Covered` at root |

The full contact root is an environment content root; other rows name a
constant root. The full Std catalog now rejects at constant
`a3b83ad0799bcd3d1c70c01df44141d79e7358e1f23d7d7e5cf9e01dbdc73c85`.
The selector's schema error is recorded as `missingConstructorSchema`. These
programs already passed compiler validation with the derived constructor
schemas; the current scalar selector validates with its own empty schema
context. The gate preserves this exact boundary.

The direct-call input forces an ordinary call and two tail calls in the
stored program. The four dispatch inputs retain constructor switches; the
Nat cases also retain Nat switches. All twelve compiler-accepted inputs
exercise PAP/application. Feature counts inventory the entire emitted graph.
Independent stage execution checks the selected branch's result.

### C3: identical erased blocks

Whole-program IxIR₀ readdressing now permits reuse only when the complete
symbolic block, ordered materialized members, and derived member keys agree.
Each producer retains its own map and block audit; duplicate output rows are
preserved for the existing exact-image and first-binding lookup theorems.
Block/member role collisions and differing preimages still reject, independently
of hash injectivity. Caller, stable, external, and transient namespaces retain
their existing protections.

Both unchanged `addClosed` and the 17-constant Std slice retain three producer
maps to the identical erased member. They now pass addressing and fail the next
source erasure certificate check. `addClosed` rejects dependency
`1ce12e12485a4793aa5baf4f197f5d5ceb5fb8e166f1a06640b87f9c91dad725`;
the Std slice rejects its entry root. Their complete raw and addressed artifacts
are recorded with `source_erasure_certified: false`. `recClosed` retains its
root-level certificate rejection and now records the same intermediate artifact
boundary. These outputs do not establish validated erasure or source acceptance.

Compiled regressions cover repeated erased singletons, renamed two-member
cycles, complete producer maps, namespace protection, and injected conflicting
block/member candidates. The coverage gate compares two fresh complete artifact
sets, independently checks duplicate producers and member rows, and preserves
the unchanged original source bytes and writer pin.

## Observations and bounds

Ixon, raw/addressed IxIR₀, owned raw/addressed IxIR₁, and logical/physical
baseline IxIR₂ must agree on each Nat result. Upstream observations recognize
the complete constructor chain and follow both address maps; they do not
treat any constructor with a matching tag as Nat. IxIR₁ and IxIR₂ heap counters
agree; both IxIR₂ interpretations also have equal complete stores and
remaining execution budgets.

| Cases | Allocations / frees / RC operations | Peak live nodes | Control steps / heap work |
| --- | --- | --- | --- |
| Four scalar cases | 1 / 1 / 1 | 1 | 6 / 2 |
| Direct call | 1 / 1 / 1 | 1 | 9 / 2 |
| Constructor zero | 3 / 3 / 3 | 2 | 14 / 4 |
| Constructor successor | 3 / 3 / 3 | 2 | 15 / 5 |
| Nat zero and successor | 2 / 2 / 2 | 2 | 13 / 4 |
| Upstream fresh closure | 5 / 1 / 3 | 4 | 13 / 2 |
| Upstream shared capture | 5 / 2 / 8 | 5 | 15 / 5 |
| Upstream let-bound closure | 6 / 1 / 3 | 5 | 14 / 2 |

The first nine successful cases return scalar literals with zero live nodes.
The upstream results retain 4, 3, and 5 live constructor nodes respectively.
Releasing those actual results produces allocation/free counts of 5/5, 5/5,
and 6/6 and RC counts of 7, 11, and 8. Every case has zero live nodes after
complete result release, with no reuse or reset operations.
These are bounded baseline observations, not native heap/FIP theorems.
No optional optimizer runs. The input snapshot records all resource limits,
fuel budgets, the Nat-block option, and configured literal inputs.

The report also runs the existing generated IxIR₀ corpus: 280 cases,
180 differential successes and 100 expected lowering rejections. Its seed,
fingerprint, and summary remain pinned. Generated IR coverage is reported
separately from source coverage.

## C2: fresh closure classification

The original 17-constant slice contains two usage failures, rooted at
`131533e96baa7f50…` and `b2f8855b5e76a480…`. In the first, the fourth argument
of a four-argument reference application is a fresh `many` lambda whose body
is `app (var 1) (var 0)`. Its only captured value is shared and the body
synthesizes shared. The old checker nevertheless classified every lambda as
unique, so the known shared parameter produced `freezeNeeded`. The second
failure has the same fresh reusable closure pattern.

`UsageCheck.closureWorld` now classifies a fresh lambda as shared when its
parameter is `many` or erased and its body synthesizes shared. Existing binder,
erasure, move, and capture checks run first. This matches the existing shared
PAP representation. `check_lam_shared` proves the actual checker inversion:
accepted shared lambdas have the stated parameter and body classification,
and every unique outer context entry has zero runtime demand. The new axiom
fences contain only `propext` and `Quot.sound`; no new axiom or native proof
assumption is introduced.

Focused checks cover fresh arguments, shared captures, let-bound closures,
and erased parameters. Affine/linear callable parameters, unique results,
runtime unique captures, and bare literal publication retain their restrictions.
The existing higher-order telescope limitation also remains; this change does
not establish a general typed ownership checker.

The three accepted Lean entries use the same upstream `twice` function and
exercise fresh, capturing, and let-bound closures. Each packed closure has six
constants and no assumptions. The pinned writer's Rust kernel accepts all
five checked work constants in each; a second clean project reproduces every
manifest and piece byte. All five original exports, including the neighboring
`Nat.add` and `Nat.rec` failures, enter Compilatrix without mode edits or source
constant reconstruction.

Checked baseline IxIR₂ remains recorded in full with its addressed IxIR₁ root
and HPT records. C3 additionally selects `applyClosed` and `letClosed` under the
[closed Nat call policy](source-native-upstream.md). Both retain real native
successors and direct calls, exact source results, and complete baseline heap
reclamation. `captureClosed` retains that baseline and a precise captured-PAP
fallback. These entries are closed computations; they do not take runtime inputs.

## Reviewed production transition

The 54-constant Std contact retains its original catalog validation and
byte/address goldens. Its failing root has a closed dependency slice of 17
constants. The gate checks closure, idempotent dependency discovery, and that removing any non-root member breaks
closure. This is a minimal dependency-closed slice under single deletion,
not a claim of minimal source syntax. C2 preserves all original bytes and
ingress counters. C3 permits checked reuse of the identical erased blocks, so
the slice now passes addressing and rejects erasure certification at its root.
The upstream `Nat.add` entry reaches a missing dependency certificate as
recorded above. The full
54-constant catalog still rejects with `freezeNeeded` at the later root listed
above. Coverage policy version 2 explicitly records both transitions.

Compiling the isolated failing constant instead gives
`typeBinderRuntimeUse .linear`. Missing definitions change the type and
erasure context, so that one-constant input is a different failure. Neither
the original contact nor C2 introduces an implicit freeze.

## Complete artifact comparison

Each producer invocation reconstructs its sources and compiles them with no
persistent compiler cache. The checker requires the same complete file
inventory and byte-identical reports, per-case snapshots, and objects.
Snapshots contain:

- original canonical Ixon bytes, literal inputs, and compilation policy;
- upstream manifest/piece bytes, Lean source bytes and hash, writer pin,
  complete dependency closure, and original stored constant records;
- raw and addressed IxIR₀ declarations/main, mutual-block preimages, groups,
  and the complete address map;
- raw and addressed IxIR₁ declarations/main, graph root, ordinary/mutual
  artifacts, reserved addresses, and the complete address map;
- HPT producer limits/statistics, candidate facts, and actual checked
  certificate/cache records with their canonical bytes, keys, and dependencies;
- structural IxIR₂ programs, validation statistics, parameter worlds,
  constructor schemas, recursor origins, and stage observations;
- native text and exact versioned provenance descriptors for selected cases.

Proof terms are erased. This compares their retained executable artifacts;
it does not serialize proofs. IxIR₂ JSON is a diagnostic without a decoder,
content address, or persistent cache role. The existing codec milestone
remains necessary before independently addressed IxIR₂ storage.

Native objects retain the actual addressed IxIR₁ graph root and lowering/pass
policy versions `1/1`. GNU readelf and objdump independently inspect them.
On x86-64 Linux the C harness links each object, checks its returned Nat, and
requires a non-executable stack.

## Run the gate

```sh
lake build source-coverage check-source-coverage
lake exe source-coverage /tmp/new-coverage
lake exe check-source-coverage \
  --fixture .lake/build/bin/source-coverage \
  --cc cc --harness fixtures/x86/native_harness.c
```

The producer requires a new output directory and completes all case checks
before writing outputs. Omit the two native flags on other host ABIs; the
deterministic artifact and binutils checks still run. `nix flake check` runs
this gate with the locked tools and enables native execution on x86-64 Linux.
The checker never rewrites the reviewed matrix.

C2 delivery on 2026-09-08 passed the 594-job local build, the two new
closure axiom fences, all compiled integration gates, and all 12 locked Nix
checks on x86_64 Linux. The final Nix coverage run includes the corrected
`raw-ixir0` labels for the two pre-certification address collisions. The
three upstream executable observations are at checked baseline IxIR₂; the
three scalar ELF checks and existing native reuse endpoints also pass.

The separate [source-recursion gate](source-recursion.md) adds eight
canonical synthetic Ixon list folds with checked direct-loop recovery,
hot/cold reuse, and complete literal/recovered artifact comparisons. D2 composes
source evaluation through the actual selected physical execution. R2 adds
shared-result reclamation and terminal allocation accounting, checked against
the same snapshots and reviewed cost matrix. R3 adds comparative physical
allocation/free laws before and after release without changing those artifacts.
R4 adds RC/peak bounds for the same actual shared-main executions, including
intermediate states and complete result release. The independent checker checks
both inequalities in the unchanged recursion snapshots. C2 extends this
coverage gate to 18 cases and explicitly reviews the production Std transition.
