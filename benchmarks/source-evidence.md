# Source preparation measurements

This suite separates source-unit preparation from certificate construction,
reuse, recovery, and whole-program assembly. It retains the existing six-case
modular report, complete source/certificate/artifact bytes, and all original
policy and admission boundaries. The optimization retains proofs of exact
canonical-address validation and completed preparation; persisted records
still reconstruct their evidence through independent checking.

```sh
lake build source-evidence check-source-evidence source-modular check-source-modular
.lake/build/bin/source-evidence run /tmp/source-evidence-smoke smoke
.lake/build/bin/check-source-evidence --fixture .lake/build/bin/source-evidence
.lake/build/bin/source-evidence run /tmp/source-evidence-reference reference
.lake/build/bin/source-evidence replay /tmp/source-evidence-reference /tmp/source-evidence-replay
```

Output directories must be new. These compiled entry points execute BLAKE3;
they cannot be replaced with interpreter-only `lean --run` invocations.

## Workloads and correctness

Both profiles run the existing six-case `source-modular` matrix. It covers
cold and unchanged builds, a source dependency edit, a literal-premise edit
with unchanged source addresses, mutual groups, and reachable source closures
of 34 and 611 declarations. Both edits match independent cold compilation;
all cases retain strict certificate recovery and source/IR execution checks.
The five smaller cases match complete monolithic artifacts. The 611-declaration
closure retains the monolithic rejection at 512 candidates.

The additional `smoke` profile uses width 32; `reference` uses widths 32, 64,
128, 256, and 600, in that order. Every generated declaration is reachable.
For each width, fresh, unchanged, restored, independently checked, and prepared
unit results must agree on full input, interface, source/literal/target context,
Nat identity, query, raw eraser output, and coverage order. The full compiled
artifact includes raw/addressed IxIR₀ and complete IxIR₁ declarations, maps,
artifacts, and main. All execution levels agree and IxIR₁ reclaims its store.

The suite also runs 38 source-preparation cases. Fifteen inspect exact
canonical-address reuse, including altered source bodies, reference tables,
sharing tables, dependency edits, and literal edits. The other 23 compare
fresh/prepared complete results or exact rejection reasons: five accept and
18 reject. They cover forged records, stale queries, missing/duplicate coverage,
depth and byte limits, absent dependencies/literals, current usage fuel and
resource bounds, and duplicate ownership despite valid canonical facts.
Literal edits may reuse canonical-address facts while still rebuilding the
affected certificates. Their complete checked units match an independent
cold build. The three axiom fences retain the existing logical/BLAKE3 basis.

## Clocks and process controls

The width profile records eighteen calls with `IO.monoNanosNow`: cold build,
unchanged build, store decoding, retained-unit checking, aggregate preflight,
cache-record preflight, fresh preparation, preparation with canonical facts,
canonical address checks, usage checks, input encoding, interface encoding,
checked-unit lookup, fresh record checking, prepared record checking, prepared
production, unit observations, and ordinary assembly.

The unit-level calls use already checked immutable imports from the cold build.
Prepared checking receives a completed preparation for its exact input,
imports, policy, and limits. Canonical reuse still executes current resource,
dependency, usage, literal, and input-byte checks. Fresh record checking
reconstructs preparation itself. Cold build, unchanged build, and retained
recovery use the public whole-build APIs and include their scheduling and
aggregate checks. Pure proof fields are erased at runtime.

These clocks **overlap in scope and are not additive**. Full builds include
preparation and checking, while the separate diagnostic calls repeat selected
operations. The order is fixed, with no per-stage warm-up or randomization;
shared inputs and cache state can affect observations. Serialization,
comparisons, execution, and file IO also contribute to the whole-process
envelope outside the named clocks.

For before/after claims, separately run the identical `source-modular`
six-case executable with the baseline and optimized compilers. Finish builds
and correctness checks first. Retain three fresh processes per variant, their
fixed order, every phase sample, phase ranges, wall/CPU time, peak RSS, host
policy, CPU affinity, environment, and tool/runtime identities. Whole-process
RSS does not isolate the memory cost of a preparation or cache. Report the
additional diagnostic worker separately. There is no CI timing threshold or
general compiler complexity claim.

## Retention and replay

Each width retains a source recipe, bounded canonical certificate store,
complete artifact snapshot, and deterministic summary. Replay requires exact
source bytes, decodes and freshly checks every retained unit, reassembles and
observes the program, and compares every retained certificate/artifact byte.
It also reruns the six-case modular recovery and dependency-edit checks.
Canonical facts and completed preparations are never deserialized as proofs.

The independent gate imports no compiler implementation. It compares two
fresh smoke producers against reviewed reports and complete files, replays
in another process, checks the clock inventory without thresholds, and rejects
five mutations of source, certificate, artifact, summary, and report files.
The existing modular gate retains its 40 certificate/resource rejections and
six file mutations; the assembly gate remains unchanged.

A reference bundle retains exact baseline/current source snapshots,
executable seeds, build evidence, tools and runtime closure, the fixed
collector and plan, every observation and artifact, validation logs, and a
verified replay from a fresh extracted source directory. Record the local
archive path, size, and SHA-256. Retained-seed replay checks evidence and
artifacts; it does not rebuild the compiler executables or require matching
clock readings. Recorded Nix runtime/tool store paths must remain available.
