# Bounded source coverage and artifact reproducibility

C1 is delivered by `source-coverage` and `check-source-coverage`. The producer
compiles fixed Ixon inputs through the actual validated pipeline and observes
each executable stage. The separate Lean checker runs it twice in fresh
processes, compares every artifact byte, checks the reviewed
[matrix](../fixtures/source-coverage/expected.json), and independently inspects
the three native exits.

## Coverage matrix

Root prefixes below identify the full roots in the matrix. The first eleven
rows are synthetic canonical Ixon, built with the ordinary sharing/address
gate; they are not upstream Lean exports. The final two rows use original
production-writer bytes from the [Std contact](corpus-contact.md).

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
| `std-failure-closure` | `131533e96baa7f50` | Ixon | — | usage: `freezeNeeded` |

The full contact root is an environment content root; other rows name a
constant root. Both production rows reject at constant
`131533e96baa7f50ba89d01892243e11a1221c8831e2f394eb14f89e9a54c6c4`.
The selector's schema error is recorded as `missingConstructorSchema`. These
programs already passed compiler validation with the derived constructor
schemas; the current scalar selector validates with its own empty schema
context. The gate preserves this exact boundary.

The direct-call input forces an ordinary call and two tail calls in the
stored program. The four dispatch inputs retain constructor switches; the
Nat cases also retain Nat switches. All nine compiler-accepted inputs
exercise PAP/application. Feature counts inventory the entire emitted graph.
Independent stage execution checks the selected branch's result.

## Observations and bounds

Ixon, raw/addressed IxIR₀, owned raw/addressed IxIR₁, and logical/physical
baseline IxIR₂ must agree on each Nat result. IxIR₁ and IxIR₂ heap counters
agree; both IxIR₂ interpretations also have equal complete stores and
remaining execution budgets.

| Cases | Allocations / frees / RC operations | Peak live nodes | Control steps / heap work |
| --- | --- | --- | --- |
| Four scalar cases | 1 / 1 / 1 | 1 | 6 / 2 |
| Direct call | 1 / 1 / 1 | 1 | 9 / 2 |
| Constructor zero | 3 / 3 / 3 | 2 | 14 / 4 |
| Constructor successor | 3 / 3 / 3 | 2 | 15 / 5 |
| Nat zero and successor | 2 / 2 / 2 | 2 | 13 / 4 |

Every successful case ends with zero live nodes, reuse, and reset counters.
These are bounded baseline observations, not native heap/FIP theorems.
No optional optimizer runs. The input snapshot records all resource limits,
fuel budgets, the Nat-block option, and configured literal inputs.

The report also runs the existing generated IxIR₀ corpus: 280 cases,
180 differential successes and 100 expected lowering rejections. Its seed,
fingerprint, and summary remain pinned. Generated IR coverage is reported
separately from source coverage.

## Preserved production failure

The 54-constant Std contact retains its original catalog validation and
byte/address goldens. Its failing root has a closed dependency slice of 17
constants. The gate checks closure, idempotent dependency discovery, the same
`freezeNeeded` rejection, and that removing any non-root member breaks
closure. This is a minimal dependency-closed slice under single deletion,
not a claim of minimal source syntax.

Compiling the isolated failing constant instead gives
`typeBinderRuntimeUse .linear`. Missing definitions change the type and
erasure context, so that one-constant input is a different failure. C1 does
not change usage modes or introduce an implicit freeze.

## Complete artifact comparison

Each producer invocation reconstructs its sources and compiles them with no
persistent compiler cache. The checker requires the same complete file
inventory and byte-identical reports, per-case snapshots, and objects.
Snapshots contain:

- original canonical Ixon bytes, literal inputs, and compilation policy;
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

The separate [source-recursion gate](source-recursion.md) adds eight
canonical synthetic Ixon list folds with checked direct-loop recovery,
hot/cold reuse, and complete literal/recovered artifact comparisons. D2 composes
source evaluation through the actual selected physical execution. R2 adds
shared-result reclamation and terminal allocation accounting, checked against
the same snapshots and reviewed cost matrix. R3 adds comparative physical
allocation/free laws before and after release without changing those artifacts.
R4 adds RC/peak bounds for the same actual shared-main executions, including
intermediate states and complete result release. The independent checker checks
both inequalities in the unchanged snapshots. This gate keeps the 13-case
matrix and the production Std rejection unchanged.
