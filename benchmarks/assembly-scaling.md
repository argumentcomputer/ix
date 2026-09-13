# Modular assembly measurements

This suite separates modular assembly from source-unit evidence construction
and compares indexed IxIR₁ addressing with its retained list implementation.
The compiler returns the same `ReaddressAll.CertifiedResult` and
`Pipeline.ValidatedCompilation` types. Admission limits, certificate policy,
canonical artifact encodings, and the native BLAKE3 assumption are unchanged.

```sh
lake build assembly-scaling check-assembly-scaling source-modular check-source-modular
.lake/build/bin/assembly-scaling run /tmp/assembly-smoke smoke
.lake/build/bin/check-assembly-scaling --fixture .lake/build/bin/assembly-scaling
.lake/build/bin/assembly-scaling run /tmp/assembly-reference reference
.lake/build/bin/assembly-scaling replay /tmp/assembly-reference /tmp/assembly-replay
```

Every output directory must be new. These compiled entry points execute
BLAKE3; they are not interpreter-only `lean --run` scripts.

## Workloads and comparisons

Both profiles run the existing six-case `source-modular` matrix, retaining
its original report and artifact format. It covers cold construction,
unchanged reuse, retained checking, a source dependency edit, a literal-premise
edit with unchanged source addresses, mutual groups, and the reachable
34- and 611-declaration source closures. The two edits are also compared with
independent cold builds. The smaller cases retain complete monolithic
artifact comparisons; the largest still fails monolithic admission at 512
candidates. The reviewed source-modular golden report is unchanged.

The additional `smoke` profile measures width 32. The `reference` profile
measures widths 32, 64, 128, 256, and 600, in that order. Group gateways and
the selected root make all generated declarations reachable. Each width
compares the complete raw IxIR₁ environment and main, addressed artifacts,
declarations, map, reserved identities, and main with ordinary assembly.
`runReferenceCertified` retains the original list builder, collision checks,
and audits; its complete output must equal the indexed result. Source,
raw/addressed IxIR₀, and owned IxIR₁ execution agree, including full store
reclamation.

The compiled regressions compare 20 accepted/rejected addressing inputs,
including stable externs, ordinary and cyclic content deduplication, member
order, reserved identities, and namespace collisions. They also check
duplicate-binding precedence and misses, plus 11 malformed result/input
mutations against both audit implementations. The audit equivalence theorems
apply to every input, not only this fixture inventory.

## Clocks and their scope

The width series records 16 calls with `IO.monoNanosNow`: source-unit build,
aggregate preflight, source-context construction, erasure with IxIR₀
addressing, imported evidence, member closure, entry certification, raw
IxIR₁ lowering, indexed addressing, reference addressing, audit-index
construction, indexed semantic checking, the additional indexed exact-image
checking, reference semantic checking, reference exact-source checking, and
ordinary total assembly.

These observations are **not additive**. Total assembly executes the
production path again; the separately measured addressers include their own
construction and checks. The reference exact-source audit includes another
semantic audit, while the indexed additional image check reuses the earlier
successful semantic check in production. The diagnostic calls run on shared
immutable inputs in a fixed order. Some context setup and result comparisons
also fall outside the individual clocks. Pure proof fields are erased at
runtime; a small member-closure timing is not a measurement of kernel proof
checking. Canonical serialization, JSON, artifact comparisons, and execution
observations contribute to the whole-process envelope.

Retain all samples, phase ranges, process wall/CPU time, peak RSS, host and
tool identities, CPU affinity, and environment overrides. Finish builds and
correctness checks before collecting three fresh processes. Separate
`source-modular` executable measurements can compare the identical six-case
process before and after the change, without the width-profile diagnostic
work. Report those process envelopes separately. There is no CI timing
threshold or general compiler complexity claim; large SCCs and repeated
source/IxIR₀ work retain their existing costs.

## Artifacts and replay

Each width retains exact source recipe and canonical certificate-store bytes,
the original complete modular artifact snapshot, raw/addressed IxIR₁
inspection snapshots, and a deterministic summary. Raw JSON is a diagnostic,
not a new accepted compiler wire format. Timing records are separate from
the deterministic report.

Replay regenerates the fixed source recipe, requires exact retained source
bytes, decodes the bounded store, independently checks its source-unit
certificates, assembles the program, compares the reference addresser, and
checks every retained artifact and certificate byte. It also runs the
existing six-case source-modular replay and dependency-edit checks.

The `assembly-scaling` Nix gate imports no compiler implementation. It runs
two fresh producers, compares the reviewed reports and complete files,
replays in another process, and rejects mutations of the retained source,
certificate store, raw target, addressed target, and whole artifact through
the public replay command. The existing source-modular gate retains its
40 certificate/resource rejections and six file mutations.

A reference bundle must retain the exact source archive and inventory,
producer/checker executable seeds, pinned tool/runtime closure, fixed
collection script and plan, all raw observations, validation logs, and fresh
source-directory replay. Seed replay verifies retained certificates and
artifacts; it does not claim to rebuild the Lean executables or reproduce
identical clock readings. The report records the local archive path, size,
and SHA-256 for retrieval.
