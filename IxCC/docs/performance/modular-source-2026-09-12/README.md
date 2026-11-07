# Modular source certification reference

This I3 reference assembles **611 reachable source declarations in 11 bounded
units**, reuses unaffected source evidence after dependency edits, and checks
retained certificates in a fresh process. The same 611-declaration program
is rejected by the monolithic entry point at its unchanged **512-candidate**
limit. The implementation and proof contract are in
modular source certification (`docs/modular-source.md` at archive commit `7599a434`).

Three fresh reference processes ran from **2026-09-12T20:56:06Z** to
**2026-09-12T20:56:43Z**, after all 28 x86_64 Linux Nix checks passed. Every
process completed the same six cases and produced identical expected source,
certificate, and artifact bytes. All three runs are retained. These are
descriptive cost observations with a fixed case order and no statistical
speedup claim.

## Cases, identity, and evidence sizes

| Case | Units | Reachable constants | Proof obligations | Certificate store bytes |
| --- | ---: | ---: | ---: | ---: |
| Baseline | 4 | 4 | 4 | 2,963 |
| Source dependency edit | 4 | 4 | 4 | 2,963 |
| Literal-premise edit | 4 | 4 | 4 | 2,963 |
| Mutual groups | 2 | 4 | 5 | 2,169 |
| Wide 32 | 2 | 34 | 34 | 15,713 |
| Wide 600 | 11 | 611 | 611 | 279,203 |

The wide generators add group gateways and a root that reference every
generated definition. All listed constants belong to the selected source
dependency closure. The largest unit has 65 proof obligations. The mutual
case transports certificates from a two-member scope into a three-member
scope; executable members count toward both unit and aggregate budgets.

Both edits change the returned value from 37 to 38. The source edit changes
the leaf and dependent source identities. The literal-premise edit keeps
every source address and the root unchanged while changing the finite
literal environment. Both reuse the unaffected unit and rebuild the leaf,
dependent unit, and root. Their artifacts match independently cold builds.
Stale retained certificates are rejected in both cases.

Every case agrees at source evaluation, raw IxIR₀, addressed IxIR₀, and owned
IxIR₁ execution, with complete IxIR₁ reclamation. The five smaller cases also
match monolithic compilation exactly at complete raw/addressed IxIR₀
declarations, groups, blocks, maps and main, plus complete IxIR₁ artifacts,
declarations, address map and main. The larger case compares cold, unchanged,
and restored modular artifacts; monolithic compilation rejects at admission.
Its complete artifact inspection snapshot is 1,281,788 bytes.

## Observed costs

Values are medians in milliseconds across the three processes. The
[summary](summary.json) retains every raw phase observation, minimum and
maximum, deterministic case report, and whole-process resource record.

| Case | Build source evidence | Unchanged evidence reuse | Check retained evidence | Assembly and IxIR₁ lowering | Monolithic compilation |
| --- | ---: | ---: | ---: | ---: | ---: |
| Baseline | 0.661 | 0.340 | 0.390 | 0.196 | 0.155 |
| Source dependency edit | 0.572 | 0.328 | 0.381 | 0.167 | 0.151 |
| Literal-premise edit | 0.577 | 0.326 | 0.390 | 0.167 | 0.151 |
| Mutual groups | 0.888 | 0.370 | 0.593 | 0.311 | 0.328 |
| Wide 32 | 30.840 | 10.599 | 20.327 | 6.970 | 6.373 |
| Wide 600 | 1,370.746 | 471.773 | 907.647 | 2,177.091 | Rejected at 512 |

“Build source evidence” starts from an empty checked cache except in the two
edit rows, which start from the baseline's checked cache. It includes the
unit API's preparation, canonical-address checks, usage checking, imported
environment comparisons, coverage discovery, actual erasure, and certificate
checking. Executable checks construct proof-bearing Lean values; proof terms
are erased at runtime.

Unchanged reuse returns the existing checked unit values after exact input,
context, and resource checks. It still repeats preparation and canonical
identity work. Retained evidence checking starts from decoded records and
reconstructs certificates; decoding is measured separately, at 2.635 ms for
the wide-600 store. Assembly reruns whole-program erasure, readdressing, entry
certification, and IxIR₁ lowering. Its unchanged and restored observations
are also retained in the summary. The large case's unchanged assembly median
is 2,152.278 ms and its restored assembly median is 2,171.469 ms.

The small cases expose modular overhead. For wide-32, source-evidence build
and assembly separately take 30.840 ms and 6.970 ms, while the monolithic
entry point takes 6.373 ms. Unit preparation, exact canonical identity and
interface checking, and repeated passes have real cost. These APIs perform
different bookkeeping, and the reference does not establish a general
compiler speedup. The delivered benefit is bounded source composition and
reuse of checked evidence beyond the monolithic admission boundary.

The complete six-case process takes 12.27–12.37 seconds and peaks at
90,424–91,676 KiB RSS (maximum 89.53 MiB). This envelope includes fixture
generation, all repeated builds and execution checks, monolithic comparisons,
the rejection matrix, serialization, and IO. It is not a single compilation
latency or isolated phase-memory measurement. Phase clocks use
`IO.monoNanosNow` without overhead subtraction.

The recorded host is an AMD Ryzen 9 7950X3D running Linux 7.1.2/NixOS.
Processes use CPU 0, `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=1`, and `LC_ALL=C`.
The host reports `powersave`, `amd-pstate-epp`, and enabled boost. Case order
is fixed; thermal state, the SMT sibling, and other system activity are uncontrolled;
there is no CI timing threshold. Full host/tool observations are retained in
[provenance.json](provenance.json).

## Validation and replay

The [validation record](validation.json) lists all 28 passing x86_64 Linux
Nix checks. The modular gate imports no compiler implementation: it runs two
fresh producers, compares the reviewed report and complete artifacts, then
invokes retained checking in another process. It checks 40 malformed-evidence
and resource rejections, inclusive boundaries, both dependency edits, and six
file mutations through the public replay command.

After measurement, the exact source archive was extracted into a new
directory and all 732 repository-file identities were verified. Hashed producer
and checker executables were placed there. Retained certificates were checked
again and every artifact and certificate-store byte matched; the independent
gate also passed from that directory. This replays the checked artifacts with
recorded executable seeds. It does not rebuild those executables from Lean
or require new timing samples to match old observations.

To run the current implementation, use new output directories:

```sh
lake build source-modular check-source-modular
.lake/build/bin/source-modular run /tmp/modular-reference
.lake/build/bin/source-modular replay /tmp/modular-reference /tmp/modular-replay
.lake/build/bin/check-source-modular --fixture .lake/build/bin/source-modular
```

The raw archive (`benchmarks/runs/modular-source-2026-09-12.tar.gz` at archive commit `7599a434`)
is retained in ignored workspace storage: **74,835,897 bytes**, SHA-256
`4e92c953bab080eab11f15e74279ba87dfedc0749608d6dab1869180edf46d71`.
It is local retention, not an uploaded artifact-service URL. Its verified
inventory covers 133 files: source archive and manifest, executable seeds,
fixed collection plan and script, tool/runtime closure, environment records,
all three artifact sets and measurements, process logs, validation, and
fresh replay. The source archive includes the measured implementation and
reviewed fixtures over base revision
`c6ef19a4481aec6b81083210c6833e2758a35cc9`; its SHA-256 is
`0dcdd3c4ab369d0e2130459c14039f5259f93c483beaab1f4ba8164fe085f5b6`.
The source manifest identifies those exact bytes independently of the later
report and commit.

After extracting the archive, retained replay can be repeated into a new
directory using its `bin/source-modular` executable and `observations/run-1`
as the input. The archived `collect.py` records the fixed process commands,
identities, cost aggregation, and source-directory replay procedure; all
compiler and certificate decisions come from the Lean executables.

Automatic catalog/SCC partitioning, the compiler's complete source closure,
transactional source-cache storage, and avoiding repeated whole-program
assembly remain follow-up work. The reference stops at the existing
source-validated IxIR₁ boundary; native linking retains its separate ABI
contract.
