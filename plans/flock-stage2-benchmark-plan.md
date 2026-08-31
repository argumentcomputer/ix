# Flock Stage 2 matched benchmark plan

Snapshot: 2026-08-31

Status: paired harness, portable q=100 fixture, and bounded memory model are
implemented on `jcb/flock-stage2`; no q=100 Flock proof has been run

## Decision to make

Determine whether a Flock leaf can replace the current P3/Aiur Stage 2 lift
for a production q=100 IxVM shard, and only then decide whether Flock recursion
is worth implementing.

The primary comparison is one raw Stage 1 proof through two semantically
equivalent Stage 2 leaves:

```text
same persisted q=100 IxVM proof
  ├── P3 shape-0 lift  ──> uniform aggregate CheckEnv claim
  └── Flock leaf       ──> identical uniform aggregate CheckEnv claim
```

Both paths must run at reviewed, comparable security levels and must constrain
the same verifying key, ten-word P3 claim, proof, `CheckEnv` preimage, and
published output-claim digest. A verifier-only Flock proof is useful as a
lower-bound diagnostic, but it is not the binding comparison.

## What is and is not known

The standing P3 numbers are historical context, not the denominator for the
new result. Four real Init shards at q=100 / PoW 20 measured:

| P3 operation | Time | Peak RSS | Proof bytes |
| --- | ---: | ---: | ---: |
| shape-0 lift, each of four | 98.8-103.0 s | 186.8-195.8 GiB | 8,162,462 |
| lower pair joins | 48.5-48.9 s | about 102.5 GiB | 9,502,843 |
| four-shard root join | 85.8 s | 156.9 GiB | 9,455,498 |
| serialized four-shard tree | 10:23 | 195.8 GiB | 9,455,498 |

Those runs used an approximately 512 GiB box whose core count was not
recorded. Their raw shard proofs were about 20-23 MB. The current Flock input
is a different 4,432,373-byte compact proof, so comparing it directly with the
historical 101-second lift would confound input, revision, and hardware.

For Flock we currently have:

- one complete q=2 verifier-only leaf proof: 2.337 seconds in the Flock prover
  at `nu=12`;
- one q=100 verifier-only relation census: 56,237,892 live rows at exact
  `nu=24`;
- one successful q=100 cold preflight: about 12.9 minutes, including 680.4
  seconds in `ShapeBuilder::finish`; and
- a q=100 primary-allocation model of 296.65 GiB at the commit phase, or
  370.81 GiB after a mechanical 25 percent margin, excluding several
  important dynamic prover allocations; and
- no q=100 Flock proof time, peak proving RSS, proof size, or verification
  time.

The `nu=12` to `nu=24` increase and the row mix are scaling warnings. They are
not a runtime measurement. Likewise, cold Flock compilation is not comparable
to P3 proving.

## Benchmark ladder

### W0: verifier-core lower bound

Run the existing Flock relation over one real q=100 proof. It verifies every
P3 AIR/PCS/FRI phase but does not yet constrain the `CheckEnv` preimage or
publish the uniform aggregate claim.

W0 answers two narrow questions:

1. Can the current q=100 Flock prover finish within the available RAM and wall
   budget?
2. Is its cryptographic proving lower bound promising enough that adding the
   missing application semantics could still beat P3?

W0 must be labelled `flock-verifier-core`, never `flock-leaf`, in result data.
It cannot establish a Flock win because it proves less than the P3 lift.

### W1: matched semantic leaf

Complete the Flock leaf relation so it:

- opens, hashes, and strictly decodes the canonical `CheckEnv` bytes;
- binds those bytes to the digest already carried by the verified ten-word P3
  claim;
- reconstructs the required trees and checks the singleton/pass-through fold;
- publishes the same uniform aggregate output-claim digest as P3 shape 0; and
- rejects wrong preimages, trees, output digests, and inactive padding.

W1 is the binding single-shard comparison. The P3 and Flock outputs need not
have the same proof format, but independent host evaluation must show that
they name the identical `CheckEnv` value.

### W2: profile and padding corpus

Repeat W1 over a frozen corpus containing at least:

- the smallest available q=100 proof;
- a typical Init proof;
- a large Init proof;
- two distinct activation/height profiles;
- a representative Mathlib proof; and
- the largest observed proof that the proposed relation catalog accepts.

This determines whether the first result was representative and whether a
maximum or bucketed Flock relation loses its apparent win to padding.

### W3: four-shard and cluster comparison

Only after W1 and W2 pass, implement enough normalization and recursion to
compare the same four raw shards end to end:

```text
P3:   four shape-0 lifts + two lower joins + one root join
Flock: four semantic leaves + equivalent fixed nodes + one fixed root
```

Measure both serialized work and scheduled wall time. This is a separate gate:
a fast leaf does not imply that Flock child verification, normalization, and
recursive folding will be fast.

## Phase A: freeze the exact fixture

Prefer one of the four historical Init shards so the new run can also explain
the old baseline. The fixture bundle must contain:

- the `.ixe` environment and `.ixes` manifest;
- selected shard id and canonical owned-block list;
- persisted `Ixon.Proof` wrapper and every referenced store object;
- wrapper address, claim bytes, compact proof bytes, and their BLAKE3 digests;
- IxVM verifying-key digest and `verify_claim` index;
- P3 commitment and FRI parameters, including both PoW values; and
- canonical `CheckEnv` bytes plus all tree material needed by shape 0.

If the historical artifacts are unavailable, generate one new q=100 shard and
use that exact wrapper for both backends. In that case the old 101-second result
remains context only. Do not splice a Flock result from the current 4.43 MB
proof together with a P3 result from a different 20-23 MB proof.

The currently profiled wrapper is:

```text
becb4740c1adf82b1ece4fa3fd230d2992fb263119b8d4d4e78cdd8273bae76f
```

Its historical environment and manifest were recovered and validated. The
portable bundle currently lives at `/tmp/flock-stage2-q100-fixture` and
contains `environment.ixe`, `manifest.ixes`, `proof.ixp`, canonical claim and
tree bytes, and `fixture.json`. Its pinned identity is:

```text
environment: 267 B, 596ad56ae011537d11c08b573216f792f0dc9f67e6050a9ae9bd2adace657b72
manifest:    103 B, 5620c48ddfb233578370849ce09c44999bd9a099ef1ac579ad53f239fe0811a4
shard:       0 (one subject, one owned block)
wrapper:     4,432,411 B, becb4740c1adf82b1ece4fa3fd230d2992fb263119b8d4d4e78cdd8273bae76f
compact P3:  4,432,373 B, 5e65f3830cd1e20ef37d61ed150b970dc2d256c84e472697965a2d3cf2a2b187
claim:       CheckEnv(bb651ee637018cccd3d156ec6730fa83bb615cdd18edfaaf58312951b8d4b9a8, none)
claim bytes: 34 B, 7af7e3b13f68fe0d185b5f578a3767a63a2039f1bbbe286d8a92c87e2f027d14
```

The harness successfully re-imports the exported wrapper and reproduces every
identity. Copy the bundle to durable artifact storage before relying on it for
the remote run; `/tmp` is not retention. This is a valid paired W0/P3 fixture.
It is intentionally tiny and is not a representative Init corpus member for
W2.

## Phase B: build one paired benchmark harness

The `bench-flock-stage2` executable now supplies the paired process boundary.
It accepts:

```text
--ixe ENV.ixe
--ixes MANIFEST.ixes
--shard N
--proof ADDRESS | --proof-file WRAPPER.ixp
--backend p3-lift|flock-verifier-core
--queries 100
--json RESULT.json
--export-fixture DIR
```

`flock-leaf` remains intentionally unavailable until W1 has semantic parity.
The exporter produces the portable bundle described above. Both benchmark
arms run in a fresh process, validate the exact wrapper/manifest claim, use
the requested FRI parameters, verify valid output, reject a corrupted output,
and write a durable status row. The P3 arm uses production `Aggr.ixAggr`
shape 0. The Flock arm emits structured preparation, typed-witness, preflight,
manifest, same-witness prover, valid-verification, and corruption timings.

The current harness records process-tree RSS and leaves a `running` row if the
process is killed, but it does not yet stream completed inner Flock phases or
collect authoritative cgroup peak, CPU time, swap, affinity, NUMA policy, and
allocator identity. Those remain Phase B work before the production run.

The P3 path should reuse the production `ix_aggr` shape-0 implementation. The
Flock paths should use the production leaf APIs, not a benchmark-only relation.
Every path must independently validate the wrapper, reconstruct the expected
claim, prove, natively verify the result, and compare its output claim with the
host oracle.

Use the repository benchmark-row contract rather than scraping stdout. At
minimum, record:

```text
metadata:
  commit, dirty status, timestamp
  CPU model, physical cores, NUMA topology, physical RAM
  thread counts, affinity, NUMA policy, allocator, build profile
  backend and protocol/configuration digests
input:
  ixe/ixes/proof addresses, byte lengths, and digests
  shard id, P3 query/PoW parameters, activation profile
security:
  claimed soundness target and all backend parameters used to derive it
phases:
  input decode and native verification
  advice/typed-witness construction
  relation emission
  ShapeBuilder::finish or P3 system setup
  relation evaluation
  per-table witness materialization
  prover-input assembly
  cryptographic proving
  serialization
  valid verification
  corrupted-proof rejection
resources:
  wall time, CPU time, peak process-tree RSS, cgroup peak, swap, exit status
output:
  proof bytes, proof digest, relation digest, output-claim digest
```

Write the result row before teardown so an OOM or job timeout retains every
completed phase. Preserve `/usr/bin/time -v`, stdout/stderr, and scheduler or
cgroup accounting as corroborating artifacts, but make JSON authoritative.

Use these timing scopes consistently:

- `cold-end-to-end`: fresh process through a verified serialized output,
  including program/relation setup;
- `input-to-verified-output`: every input-dependent operation after reusable
  program setup, including decode, one native input verification,
  proof-to-advice expansion, typed-witness creation, relation filling, proving,
  serialization, and output verification; and
- `cryptographic-prover`: the backend's inner prove call, retained only as a
  diagnostic breakdown.

The binding latency comparison is `input-to-verified-output`. P3's static
system compilation and Flock's value-independent shape compilation may be
reported outside it only when the compiled object is genuinely reusable for a
different accepted witness. Native input validation remains a separate phase
inside that total so duplicated diagnostic preparation is visible.

### Flock cache scopes must be explicit

The current `--mode prove` performs a full preflight and then hits an
in-process cache for the exact same witness. It also repeats preparation on the
prove path. That invocation usefully reports:

- cold decode, relation construction, finalization, and evaluation;
- an exact-witness cached cryptographic-prover lower bound; and
- verification and proof size.

Its cold total therefore includes diagnostic duplicate work, while its inner
prover timing omits work a new witness would require. It does not represent a
production warm path for a different proof. Report three scopes separately:

1. `cold`: fresh process, no compiled relation available;
2. `same-witness-lower-bound`: the current in-process exact-witness hit; and
3. `warm-new-witness`: a value-independent compiled shape reused with a second
   proof in the same pinned profile.

Do not call scope 2 a cache result comparable to the P3 static recursion
system. Scope 3 requires separating the immutable shape/fill plan from witness
values or implementing an equivalently sound typed rebuild recipe. A cache
entry must bind the Flock revision, configuration, relation manifest, circuit
digest, bounds, and codec version, and must be verified before use.

### Instrument memory before the large run

Add a no-allocation or bounded-allocation estimate for the major q=100 prover
buffers using the exact `nu`, table count, column counts, field widths, and
temporary duplication in the pinned Flock revision. Report both the modeled
peak and the assumptions it omits. Use that estimate only to select a machine;
the measured cgroup/process-tree peak remains authoritative.

This checkpoint is implemented in `Stage2RelationSizingV1::memory_estimate`.
The model is pinned by a test that rebuilds every table and a second regression
test over the exact q=100 census:

| Accounted q=100 allocation | Size |
| --- | ---: |
| three live witness payloads | 103.47 GiB |
| live lincheck stripe writes | 51.18 GiB |
| compact stack, rounded at dense `M=39` | 64.00 GiB |
| initial Fast128 codeword, 35/64 integer lanes | 70.00 GiB |
| initial Merkle tree | 8.00 GiB |
| **accounted commit-phase model** | **296.65 GiB** |
| model with 25 percent arithmetic margin | 370.81 GiB |

The registry itself has `M=41`. Its three padded witness vectors reserve
3 x 256 GiB of virtual address space, while the full stripe capacities reserve
another 215 GiB. Including the compact stack, codeword, and tree, accounted
virtual reservations total about 1,125 GiB. Lazy/dirty pooled buffers avoid
touching most witness padding, so this is not a physical-RAM prediction.

The 296.65 GiB figure is also not a peak-RSS upper bound. It omits the
circuit/row arena, concurrently running wiring GKR, zerocheck/lincheck and
opening scratch, allocator metadata, retained scratch-pool buffers, and the
runtime/OS. A measured first run is still required.

## Phase C: local correctness gate

Before reserving a large machine:

1. run the paired harness at q=2 through P3 and `flock-verifier-core`;
2. once W1 exists, run both semantic leaves and compare the output claim;
3. check deterministic metadata and relation identity across repeat runs;
4. prove and verify at least two distinct witnesses in one relation profile;
5. corrupt the input proof, verifying key, claim, `CheckEnv` preimage, output
   digest, relation digest, and produced proof one at a time; and
6. exercise the benchmark watchdog with a deliberately tiny memory ceiling so
   an OOM produces a durable partial row rather than an ambiguous missing log.

Builds, tests, and Nix downloads happen before measured runs.

### Local q=2 checkpoint (2026-08-31)

The harness can now generate a parameter-matched input wrapper without putting
an ambiguously parameterized proof in the global store:

```console
bench-flock-stage2 --ixe environment.ixe --ixes manifest.ixes --shard 0 \
  --queries 2 --generate-proof proof.ixp
```

The generated wrapper is 246,251 bytes at
`587829aa0f4ddec580f31d57eeae1d7e5436962a0a0f25d16f8c184f3a0f2917`;
its 246,213-byte compact proof digests to
`dc6ad76393f37e06d5fe2e1848bdd73c30f2f134765597f5b54d8c734388bb3f`.
A portable copy is at `/tmp/flock-stage2-q2-fixture` pending durable artifact
storage.

Three alternating fresh-process samples (`P3, Flock, Flock, P3, P3, Flock`)
on an AMD Ryzen 9 7950X3D with 125 GiB physical RAM produced:

| Backend/scope | Input-to-verified-output median (range) | Inner prove median (range) | Peak RSS median (range) | Proof bytes median (range) | Valid verify median (range) |
| --- | ---: | ---: | ---: | ---: | ---: |
| P3 shape-0, uniform `CheckEnv` | 14.399 s (14.019-42.484) | 14.391 s (14.010-42.476) | 14.62 GiB (14.58-14.64) | 438,620 (437,084-438,620) | 2.340 ms (2.338-2.538) |
| Flock verifier core, same-witness lower bound | 24.287 s (24.272-24.769) | 20.258 s (20.149-20.801) | 26.43 GiB (26.36-26.52) | 516,563 (fixed) | 91.559 ms (79.302-120.051) |

At this small matched point, Flock's median end-to-end time is 1.69x P3,
inner proving is 1.41x P3, peak RSS is 1.81x P3, the proof is 17.8 percent
larger, and valid verification is 39.1x P3. This is unfavorable to Flock even
though its row proves only the verifier core and benefits from the
same-witness cache scope. It is not a q=100 scaling result and therefore does
not replace W0, but it removes the earlier apparent q=2 win: that 2.337-second
Flock prover number came from a much smaller synthetic `nu=12` relation. The
real matched q=2 wrapper produces 2,114,302 rows at `nu=20`.

Flock reproduced identical relation, circuit, and proof-bundle digests across
all three fresh processes. P3 proof digests and sizes varied, and one prove was
a 42.5-second outlier while the other two were about 14 seconds. The 20-bit
query-grinding search and resulting transcript/opening set are the likely
source; this is an inference, so the production benchmark must retain raw
grinding-phase data and use multiple samples rather than a single run.

The hard-failure path was exercised with an 8 GiB virtual-address ceiling on
the q=2 P3 arm. `HugeVec` allocation aborted the process with exit 134, while
`/tmp/flock-stage2-q2-p3-limited.json` remained valid JSON at status `running`
with the complete fixture/system metadata. This distinguishes a killed run
from a command that never started. It does not yet identify the last completed
inner phase; streamed checkpoints and external cgroup/scheduler exit metadata
remain required for the large run.

## Phase D: acquire the benchmark machine

The first q=100 proof needs one shared-memory node. A cluster with many small
workers cannot replace it because the current P3 and Flock provers are not
distributed across nodes.

Select the node from the memory estimate. The initial target is:

- 1 TiB physical RAM for the first q=100 Flock run; 512 GiB is now a risky
  floor because the accounted model plus 25 percent is already 370.81 GiB
  before the explicitly omitted dynamic allocations;
- enough local NVMe for the Nix closure, proof store, fixtures, logs, and
  temporary prover data;
- known physical core count and NUMA topology;
- cgroup v2 accounting and a job-level wall timeout;
- no swap for the measured cgroup;
- an exclusive reservation with no competing CPU- or memory-heavy jobs; and
- preferably bare metal, or otherwise a recorded VM type and tenancy model.

The existing approximately 512 GiB benchmark box remains useful for the paired
P3 run and a deliberately capped Flock feasibility probe, but should not be
treated as sufficient for an uncapped first Flock proof. Prefer a 1 TiB node
and run both backends there. A cluster becomes useful
afterward for corpus repetitions, provided paired P3/Flock runs stay on the
same hardware class. Do not compare a P3 result from one node type with Flock
from another.

The access request should ask for:

- a 24-hour initial exclusive window, extendable if the W0 proof is still
  making progress;
- repository and Nix-cache access;
- transfer of the frozen fixture/store bundle;
- permission to reserve the full node and inspect cgroup/NUMA metrics; and
- retention of the output directory after the job finishes or is killed.

## Phase E: W0 production probe

The existing command is sufficient for an initial lower-bound run; no disk
shape cache is required because the same process preflights, proves, and
verifies. Prefer the structured harness once Phase B lands, but this command
can answer whether the cryptographic prover finishes at all:

```console
export IX_F2_REPO=/absolute/path/to/ix
export IX_F2_OUT=/absolute/path/to/flock-stage2-results
export IX_F2_PROOF=becb4740c1adf82b1ece4fa3fd230d2992fb263119b8d4d4e78cdd8273bae76f
export IX_F2_THREADS=<physical-core-count>

cd "$IX_F2_REPO"
/usr/bin/time -v -o "$IX_F2_OUT/flock-core-1.time.txt" \
  env IX_FLOCK_TIMING=1 RAYON_NUM_THREADS="$IX_F2_THREADS" \
      LEAN_NUM_THREADS="$IX_F2_THREADS" \
  .lake/build/bin/ix flock-leaf "$IX_F2_PROOF" --mode prove
```

Run it under the repository cgroup watchdog or the cluster scheduler with a
memory ceiling below the node's physical limit and an initial six-hour wall
limit. A timeout is a censored lower bound, not a zero or failed measurement.
Keep the timing log, cgroup peak, and last completed phase. If the structured
harness is used, also keep its partial JSON row; the existing command does not
yet emit one.

W0 is a go signal for W1 only when the verifier-core lower bound leaves a
credible margin for the missing claim logic. Use the paired current-revision
P3 run as the reference:

- **strong go:** the Flock verifier-core `input-to-verified-output` lower bound
  is at most half the P3 lift time and peak RSS is at most 128 GiB;
- **gray zone:** Flock core finishes below the P3 lift but misses one of those
  margins; quantify claim-folding cost and concrete lowering optimizations
  before proceeding;
- **pause:** Flock core is already slower or larger than P3, exceeds the
  64 MiB proof bound, OOMs on the intended worker tier, or times out without a
  specific mechanical bottleneck that can plausibly reverse the result.

These are engineering allocation gates, not protocol claims. A paused result
can be revisited after an identified optimization, but it does not justify
starting recursion.

## Phase F: matched W1 run protocol

Once semantic parity and value-independent warm reuse exist:

1. pin one clean benchmark commit and record the complete Nix closure;
2. build and run correctness gates outside the timed window;
3. pin identical `RAYON_NUM_THREADS`, `LEAN_NUM_THREADS`, CPU affinity, NUMA
   policy, allocator, and memory ceiling for both backends;
4. run one untabulated warm-up per backend;
5. run three paired repetitions in alternating order, for example
   `p3-1, flock-1, flock-2, p3-2, p3-3, flock-3`;
6. use a fresh process and output path for every repetition;
7. wait for RSS to return near the pre-run baseline between jobs;
8. do not drop the OS page cache unless the same documented procedure is used
   for both paths; and
9. retain failed, OOM, and timeout runs rather than silently retrying them.

Report medians and ranges, not only the fastest run. The primary table is:

| Backend | Semantic output | Median per-proof wall | Cold setup | Peak RSS | Proof bytes | Verify time |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| P3 shape-0 lift | uniform `CheckEnv` | | | | | |
| Flock semantic leaf | identical uniform `CheckEnv` | | | | | |

Also report CPU-seconds, GiB-seconds, proofs per node-hour, and the reviewed
security margin. If a backend uses materially different security, fix the
parameters and rerun rather than normalizing an incomparable result after the
fact.

The existing adoption gate remains intentionally demanding:

| Metric | Minimum Flock gate | Target |
| --- | ---: | ---: |
| matched semantic leaf time | at most 50% of paired P3 | at most 10% |
| peak RSS | at most 128 GiB | at most 96 GiB |
| leaf artifact | no larger than paired P3 | at most 1 MiB |
| valid verification | no slower than paired P3 | materially faster |

A modest 10-20 percent improvement is not enough to justify a new recursion
protocol, cache, scheduler, terminal circuit, and migration path.

## Phase G: corpus and cluster execution

Use the cluster only after the single-node W1 result is promising:

- assign paired P3/Flock runs for one fixture to the same node class;
- randomize or alternate backend order within each node;
- use identical per-job core and RAM reservations;
- keep at least three successful samples per fixture/backend pair;
- record queue time separately from execution time; and
- aggregate total CPU-hours, GiB-hours, and critical-path wall time.

If W2 passes and recursion is implemented, reuse the four-shard
`bench-aggregate-policy` fixture and result schema for W3. Compare both one-node
serialized time and a fixed fleet budget. Equal wall time obtained by giving
one backend more nodes or more aggregate RAM is not a win; report the resource
multiplier explicitly.

## Deliverables

The review bundle should contain:

- the pinned benchmark commit and clean-status record;
- fixture manifest with every input digest/address;
- security-parameter worksheet for both proofs;
- host inventory and resource limits;
- raw JSON, timing files, logs, cgroup/scheduler accounting, and failure rows;
- median/range tables for W0, W1, and any W2/W3 runs;
- exact output-claim equality and valid/corrupted verification results;
- a list of deviations from this protocol; and
- a recommendation stated separately from the measurements.

## Immediate work order

1. **Done locally:** recover and export one self-contained q=100 shard fixture
   usable by P3 shape 0 and Flock; move it from `/tmp` to retained storage.
2. **Mostly done:** structured Flock timings, proof identity, valid/corrupt
   verification, and durable harness status; add streamed phase checkpoints
   and scheduler/cgroup accounting for hard OOM/timeout diagnosis.
3. **Done:** generate a real q=2 raw IxVM proof whose FRI parameters match the
   harness, run three alternating samples of both arms, and pin valid/corrupt
   verification plus identity. The result is unfavorable to Flock at q=2.
4. **Done:** exact-census q=100 primary-allocation model with geometry drift
   and numeric regression tests.
5. **Done for the local contract:** repeat-run identity is pinned and an
   artificial 8 GiB ceiling leaves a valid `running` row on allocator abort.
   Add streamed inner-phase checkpoints and cgroup/scheduler attribution for
   the production launcher.
6. Request an exclusive 1 TiB window and run W0 plus the paired P3 lift.
7. Decide from W0 whether to implement the missing `CheckEnv` relation for W1.
8. Start Flock recursion only after W1 and the profile corpus pass.
