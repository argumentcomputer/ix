# Indexed modular assembly reference — 2026-09-13

For the fully reachable **611-declaration source closure in 11 units**, median
assembly and IxIR₁ lowering falls from **2,180.306 to 130.866 ms**
(**16.7×**). The complete 1,281,788-byte artifact, source recipes, certificate
stores, cache decisions, execution results, and admission limits are unchanged.
These are three fresh observations per compiler on one shared host.

The change indexes whole-program IxIR₁ construction and validation. It keeps
the original `ReaddressAll.CertifiedResult` and `Pipeline.ValidatedCompilation`
interfaces. Lean proves the indexed audits equal the original predicates for
arbitrary inputs, including malformed results. The builder preserves the
existing dependency/member order and exact-preimage collision checks; the
suite compares its complete output with the retained list builder.
Implementation and proof scope (`docs/modular-source.md#indexed-assembly-checks` on the archive branch of the pre-merge Compilatr.ix repository).

## Identical before/after workload

The baseline executable was freshly rebuilt from commit
the base commit of that date (pre-merge history, not kept by the squash). All 782 extracted repository files
were checked against that archive after the build. The pinned Blake3 package
cache was shared. The indexed executable uses the frozen working source
recorded in [provenance.json](provenance.json).

Each executable runs the same existing six-case `source-modular` matrix.
Every source, certificate, artifact, and deterministic summary file matches
between variants and the original reviewed report. Times below are median
milliseconds for `assembly_and_IxIR1_lowering`; source evidence construction
is outside this clock.

| Case | Source declarations | IxIR₁ declarations | Baseline ms | Indexed ms |
| --- | ---: | ---: | ---: | ---: |
| Baseline graph | 4 | 6 | 0.201 | 0.161 |
| Dependency edit | 4 | 6 | 0.176 | 0.135 |
| Literal-premise edit | 4 | 6 | 0.168 | 0.129 |
| Mutual groups | 4 | 7 | 0.331 | 0.268 |
| Width 32 | 34 | 66 | 7.038 | 1.425 |
| Width 600 | 611 | 1211 | 2180.306 | 130.866 |

At width 600, baseline assembly ranges from **2,149.649 to 2,207.232 ms**;
indexed assembly ranges from **130.099 to 131.795 ms**. The unchanged-reuse
assembly medians are **2,171.638 → 130.457 ms**, and restored assembly medians
are **2,190.407 → 131.024 ms**. Every sample and phase range is retained in
[summary.json](summary.json).

Source evidence still takes **1,372.440 → 1,377.288 ms** cold,
**473.113 → 476.399 ms** for unchanged reuse, and **919.550 → 919.864 ms**
for independently checking retained certificates. This optimization does not
reduce those costs. The median of each process's evidence-plus-assembly sum
is **3,552.746 → 1,507.387 ms** cold and **2,644.750 → 606.855 ms** unchanged.
Retained recovery, including store decoding, checking, and assembly, is
**3,108.644 → 1,053.606 ms**. These subtotals sum non-overlapping named clocks
within each sample before taking the median; they are not whole-process time.

## Assembly components

Three additional fresh processes run the five-width diagnostic profile.
They measure indexed addressing and `runReferenceCertified` on the same raw
IxIR₁ input, then verify the full artifacts against ordinary assembly.
The reference here is the retained implementation compiled into the current
diagnostic executable, distinct from the baseline executable comparison above.
All table entries are median milliseconds.

| Source declarations | Raw IxIR₁ declarations | Raw lowering | Reference addressing | Indexed addressing | Ordinary assembly |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 34 | 66 | 0.057 | 5.655 | 0.656 | 1.305 |
| 66 | 130 | 0.098 | 21.334 | 1.276 | 3.068 |
| 131 | 259 | 0.205 | 83.850 | 2.696 | 8.312 |
| 261 | 517 | 0.488 | 336.745 | 5.843 | 26.255 |
| 611 | 1211 | 1.031 | 1864.551 | 16.203 | 120.432 |

At 611 source declarations, complete indexed addressing ranges from
**16.171 to 16.243 ms**, versus **1,839.933 to 1,952.040 ms** for the reference.
Separately preparing audit indexes takes **3.738 ms**, indexed semantic
checking **3.082 ms**, and the additional exact-image check **2.516 ms**.
The original semantic and exact-source audits take **456.433 ms** and
**977.775 ms**, respectively; the latter repeats semantic checking.

Erasure with IxIR₀ addressing is now the largest measured assembly component
at **82.920 ms**. Aggregate preflight takes **10.292 ms** and imported evidence
transport **8.316 ms**. These remaining operations still repeat whole-program
work. The width series does not establish linear compiler complexity, remove
bounded mutual-block costs, or measure the compiler's own complete source
closure.

The diagnostic intervals overlap: ordinary assembly runs the production path
again, addressers include construction and audits, and explicit audits repeat
checks for measurement. Do not sum all sixteen phases. Indexed addressing
runs before reference addressing; explicit indexed/reference audits follow,
then ordinary assembly. The fixed order and shared immutable inputs can
affect caches. There is no per-stage warm-up or randomization. The
protocol (`benchmarks/assembly-scaling.md` on the archive branch of the pre-merge Compilatr.ix repository) specifies all clock scopes.

## Correctness and process observations

All **31 x86_64-linux Nix checks** pass, including the proof fence, full runtime
tests, new independent assembly gate, existing modular gate, and native
endpoints. The new regressions compare **20 construction cases**
(11 accepted and 9 rejected), preserve duplicate-binding precedence and
misses, and compare both audits on **11 malformed results/inputs**. The
independent gate rejects five persisted-file mutations through public replay;
the existing modular gate retains its 40 certificate/resource rejections and
six file mutations. [Validation evidence](validation.json).

The five smaller modular cases still match complete monolithic compilation.
The 611-declaration closure still rejects monolithic admission at the original
512-candidate bound. Dependency and literal-premise edits reuse the unaffected
unit and rebuild the three-unit dependent cone, with exact cold-build matches.
The literal edit preserves the source root but invalidates the changed
premises. Source, raw/addressed IxIR₀, and IxIR₁ execution agree, including full
store reclamation. No certificate policy, resource budget, axiom basis,
native symbol, or external contract was added or relaxed.

| Whole process | Wall seconds, all three runs | Peak RSS KiB, all three runs |
| --- | --- | --- |
| Baseline six-case matrix | 12.42, 12.41, 12.40 | 90956, 90464, 90452 |
| Indexed six-case matrix | 6.23, 6.21, 6.23 | 90540, 83948, 90248 |
| Additional diagnostic profile | 16.01, 15.92, 16.00 | 92192, 92456, 92424 |

The comparable six-case process median falls from **12.41 to 6.23 seconds**.
Each process includes multiple compilations, certificate recovery, semantic
execution, encoding, artifact comparisons, and IO. RSS describes the whole
process and does not isolate the index's memory cost. The additional profile
performs more work and has a separate process envelope.

Runs used CPU 0 on an AMD Ryzen 9 7950X3D, Linux 7.1.2, Lean 4.33.0,
`LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`, and `LC_ALL=C`. The recorded CPU
policy was `amd-pstate-epp`/`powersave` with boost enabled before and after
measurement. Repository builds and checks had finished; this was not a
dedicated host. Comparison order was baseline/indexed, indexed/baseline,
baseline/indexed, followed by the three diagnostic processes. Host snapshots,
tool versions, resolved paths, linkage, and runtime closure are in
[reproduction.json](reproduction.json). No timing threshold or statistical
significance claim is attached to these observations.

## Retention and replay

The machine-local, ignored archive is
`benchmarks/runs/assembly-scaling-2026-09-13.tar.gz` (**189,004,138 bytes**),
SHA-256 `68dbcee833934af0ae395647db31e574e246781b5fd304bcecda31718b0b3294`.
It has not been uploaded. Its 450 inventoried files include every raw sample,
complete artifact set, fixed collector and plan, process resources, logs,
baseline source/build evidence, current source snapshot, five executable
seeds, and tool/runtime identities. All inventory entries were independently
verified by reading the completed archive. [Retention record](retention.json).

Replay extracted and verified all **789 frozen source files** into a new
directory, checked retained executable identities, independently rechecked
certificates, and reproduced every profile and matrix artifact byte. Both
independent gates passed from that extracted source directory. This replay
uses retained executable seeds; it does not rebuild the Lean executables or
require clock readings to match. [Replay record](replay-verification.json).

After unpacking the archive, these commands use its retained seeds and a new
output directory. Replace the two paths; the recorded Nix runtime/tool store
paths must still be present. Extract `source.tar.gz` separately to recover the
exact source inventory and reviewed fixtures.

```sh
assembly_bundle=/path/to/assembly-scaling-reference-001
assembly_output=/path/to/new-assembly-replay
taskset -c 0 env LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=1 LC_ALL=C \
  "$assembly_bundle/seed/assembly-scaling" replay \
  "$assembly_bundle/profile-1" "$assembly_output"
```

The benchmark protocol (`benchmarks/assembly-scaling.md` on the archive branch of the pre-merge Compilatr.ix repository) provides
fresh build/producer/checker commands. Source and seed hashes and the exact
collection plan are retained in [provenance.json](provenance.json).
