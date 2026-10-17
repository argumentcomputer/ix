# BLS and BN254 PLONK wrapper implementation status

Updated 2026-10-17. Complete BLS12-381 and BN254 PLONK wrappers around the
actual Init KZG packets now prove and verify natively. The BN254 proof also
passes Solidity verification on Anvil with a constants-only SP1 adaptation.
The optional CUDA backend reaches 11.352 s median core proving versus 53.895 s
for its matched CPU baseline; stage profiling identifies the remaining CPU
work and transfer costs below. These measurements
supersede the earlier incomplete-proving status. The original BLS implementation
checkpoint and its OOM record are retained afterward as historical context.

Use this document for current measurements, validation, artifact identities and
remaining work. The [plan](bls-plonk-wrapper-plan.md) records circuit/CUDA design
and soundness decisions; the [compression README](../crates/proof-compression/README.md)
covers BLS/BN254 KZG, Ignition provisioning and cache operation; the
[helper README](../tools/bls-plonk-wrapper/README.md) gives PLONK build/run/profile
controls; and the [contract README](../contracts/plonk/README.md) gives EVM replay
instructions. Sections after **Original implementation checkpoint** are historical.

## Full Init benchmark

The `sb/bn254` working tree above `52c61479` regenerated both BLS KZG stages
from the saved Init FRI input using authenticated Filecoin parameters and
BLAKE3. The resulting profile exactly matches the bundled
`aggregate-filecoin-v6.bin`, with BLAKE3
`12ce28356f86ba34afb11b8e3b2c142f47ab9259e9c3f5751069bd1c41609084`.
The expected public digest came from the original Init claim, independently
of the wrapper witness. Both inner pairing obligations are constrained.

The wrapper compiled to **21,184,618 constraints**, domain **2^25**, two
public inputs and one extra commitment. This is the real Init profile,
distinct from the smaller conformance fixture measured below.

| Measurement | Result | Boundary |
| --- | ---: | --- |
| Core PLONK proving | 127.168 s | `plonk.Prove`, including the real constraint solver; keys and circuit already loaded |
| Prove command | 293.870 s | Fresh process, artifact checks/loading, witness assembly, proving, verification and output |
| Internal native verification | 2.754 ms | `plonk.Verify` with key, proof and public witness in memory |
| Decode/public-witness/verify median | 4.196 ms | Seven fresh verifier processes; timer starts after key loading |
| Complete verifier-process median | 25.508 ms | Seven fresh processes, including startup and key authentication/loading |
| Peak prover RSS | 53.63 GiB | GNU time maximum RSS |
| Native proof | 744 bytes | Compressed gnark proof |
| ix envelope | 784 bytes | Version tag, verification-key identifier and native proof |
| Solidity proof encoding | 1,184 bytes | Solidity-compatible encoding; EVM gas was not measured |

This was one proof run on 48 logical CPUs of an Intel Xeon Platinum 8559C,
with 499 GiB host RAM and local NVMe. The gnark backend used CPU only and
default parallelism. Keys were prepared before proof timing; the prover ran
in a fresh process and OS page-cache state was uncontrolled. No claim is
made about an in-memory warm-prover latency. The verifier repetitions had
warm file caches and no proving SRS or visible GPU. Their process timings
exclude the resource monitor's GPU-query overhead.

Preparation was measured separately:

| Preparation | Time |
| --- | ---: |
| Compile command | 19.60 s (18.30 s internal compilation) |
| Compiled witness diagnostic | 3.29 s |
| Authenticated SRS export | 9.33 s |
| Parameter/key preparation command | 1,217.16 s (20m 17s) |
| SRS import within preparation | 5.84 s |
| Lagrange conversion/cache publication within preparation | 1,139.22 s (18m 59s) |
| Circuit indexing within preparation | 32.71 s |

The preparation command also includes circuit loading, garbage collection,
key serialization, hashes and publication; its child timings do not include
all of that work. Peak preparation RSS was 28.43 GiB. Lagrange conversion is
a group inverse FFT over 33,554,432 points derived from the downloaded
monomial SRS. Its cached output is 3 GiB; the serialized proving key is
3,221,274,824 bytes, and the verifying key is 49,200 bytes.

The first and recursive KZG input-preparation processes took 225.34 s and
153.40 s respectively; both are excluded from the PLONK timings. Builds are
also excluded. The helper was built with Go 1.26.8 and the existing pinned
gnark/gnark-crypto versions. Its SHA-256 is
`6ee690f092a9b5fb1aa8672abe9af5450ac4f47a42b64fd073c4bbc826b3490b`.
The verification key SHA-256 is
`73d8ebbad3df955310fcf7c8b7d35cf04f6ecd5be513f55af25036b7349e5299`.

Fresh-process verification passed against the original claim digest. Changed
claims and a modified proof were rejected. The focused Filecoin backend and
Lagrange-cache/basis-conversion tests also passed before the full run.
The generated key has not been activated in a production verifier catalog;
complete CLI packaging and full-wrapper EVM verification remain separate work.

The local report is `target/plonk-bench/report.json`. Frozen executables,
input proofs, exported profile/witness, compiled circuit, SRS export,
Lagrange cache, proving/verifying keys, generated Solidity, proof and logs
are under `/opt/dlami/nvme/ix-bls-plonk-52c61479/`, with `report.json` and
`verification-timings.json` there. Successful preparation can be reused with
the frozen helper; artifact manifests enforce its executable identity.

## BN254 full Init benchmark and BLS comparison

The BN254 wrapper consumes the actual Init recursive KZG packet from the
authenticated Ignition validation run. Its inner verifier-file BLAKE3 is
`a4cf1b3b2489af6c939847d5060452bccb1f87ed8cff0fb90658e477549eafcd`.
Both pairing equations remain constrained, and the expected public digest is
derived from the original Init claim independently of the private witness.

The circuit has **17,996,081 constraints**, two public inputs and one extra
commitment in this benchmark configuration. Its **17,996,083 total rows exceed
2^24 by 1,218,867**. This proof used **2^25**; the subsequent classic-GLV
configuration below compiles to **2^24** and its completed proof benchmark is
recorded in [the updated comparison](#bn254-224-full-init-proof-benchmark).

| Measurement | BN254 | BLS12-381 |
| --- | ---: | ---: |
| Constraints | 17,996,081 | 21,184,618 |
| Padded domain | 2^25 | 2^25 |
| Core `plonk.Prove` | 104.332 s | 127.168 s |
| Complete fresh prover process | 143.592 s | 293.870 s |
| Internal native `plonk.Verify` | 1.196 ms | 2.754 ms |
| Decode/public-witness/verify median | 1.923 ms | 4.196 ms |
| Complete verifier-process median | 21.696 ms | 25.508 ms |
| Peak prover RSS | 47.18 GiB | 53.63 GiB |
| Native proof | 584 bytes | 744 bytes |
| ix envelope | 624 bytes | 784 bytes |
| Solidity proof encoding | 864 bytes | 1,184 bytes |

These are one proof sample per curve on the same 48 logical CPUs and native
CPU gnark backend, with default parallelism. BN254 core proving took 17.96%
less time; the complete prover process took 51.14% less time. The process
measurement includes artifact authentication/loading, witness construction,
proving, verification and output. Both runs used prepared keys in fresh
processes, with uncontrolled OS page-cache state. Neither is an in-memory
warm-prover measurement. Verification medians use seven fresh processes,
warm file caches and no resource-monitor subprocess in the timing interval.

### BN254 preparation and validated SP1 basis reuse

The published SP1 v6.1.0 PLONK archive supplies a candidate Lagrange basis for
the same `2^25` domain. The importer checked the entire basis against ix's
authenticated monomial SRS before publishing a cache. It checked canonical
point encodings, setup anchors and domain, then evaluated a transcript-bound
random linear relation using a scalar inverse FFT and two MSMs. Matching
anchors alone was not treated as sufficient validation. SP1's circuit keys
and monomial array were discarded; ix generated its own circuit keys.

| Preparation operation | Time |
| --- | ---: |
| SP1 archive download and key extraction | 36.127 s |
| Compile command | 16.960 s (15.714 s internal) |
| Compiled witness diagnostic | 3.586 s |
| Authenticated monomial SRS export | 7.364 s |
| Full SP1 basis validation and cache publication | 27.700 s |
| Parameter import and circuit-key preparation | 63.551 s |
| SRS import within preparation | 3.703 s |
| Validated Lagrange cache loading within preparation | 4.089 s |
| Circuit indexing within preparation | 20.137 s |

The final preparation command reported `reused_lagrange=true`. Its peak RSS
was 21.85 GiB; full basis import peaked at 14.87 GiB. Validation, download,
preparation, compilation and inner KZG proving are excluded from the proof
timings above. The monomial Ignition cache was already provisioned. BLS
computed its Lagrange basis locally, whereas BN254 imported validated public
points, so the preparation difference is not a curve-speed comparison.

The downloaded archive SHA-256 is
`b3e2f5b5dd5ca89675c73975d2d1cc4a0f9e7cde048ec5354dabc7b0694aa39b`;
the extracted legacy key SHA-256 is
`d0eb5d80e0ab8c392fbdaa4cd3f18765ab8de41266f04cc4ec7ebe27c09449f4`.
The complete candidate-vector SHA-256, including its serialized count, is
`2da3c5c898f5e3f6ea22e413c2cf7027516c4b470d2ccd5136a4299bf7765a50`.
The source is [SP1's v6.1.0 PLONK archive](https://sp1-circuits.s3-us-east-2.amazonaws.com/v6.1.0-plonk.tar.gz).

The frozen helper SHA-256 is
`a61d6e4dcaa95673c5506443efdf8c3aff661c5b26892a7a6f4ee1946a67da52`;
the generated verification-key SHA-256 is
`6a7e3d80d39367b1454c2cddd67f94e5338ffac92893fcb1dabf69ce956f0c7f`.
The proving key is 2,147,518,136 bytes; the verification key is 34,384 bytes.
The local report is `target/bn254-plonk/report.json`. Artifacts and logs are
under `/opt/dlami/nvme/ix-bn254-plonk-52c61479/`; final binaries are in
`bin-final`, and the circuit and keys are in `artifacts-final`.

Independent native verification and Rust catalog-based verification passed
without proving parameters configured. Wrong claims, altered proofs, unknown
keys, modified verification keys, wrong curve tags, missing catalogs and
missing or incorrectly pinned Ignition admissions were rejected. The catalog
used for these checks is isolated benchmark configuration; it is not a
production authorization. The generated Solidity verifier and encoding have
not been measured in an EVM, and a complete Lake-linked ix build remains
separate from the checked build configuration and worker/helper integration.

## BN254 pairing batching and reduction to 2^24

On 2026-10-16, component compilation of the same actual Init profile isolated
the cost of the two pairing checks and the opening MSMs. Counts are SCS
constraint differences; shared range checks affect component attribution.

| Baseline component | Added constraints |
| --- | ---: |
| Point validation and public binding | 168,592 |
| BLAKE3 transcript | 4,914,403 |
| Scalar relation | 462 |
| Opening MSMs | 9,735,484 |
| Outer pairing | 1,588,862 |
| Deferred pairing | 1,588,278 |

Removing the deferred pairing for free would leave 16,407,805 rows including
public inputs, giving batching only 369,411 rows of overhead before exceeding
`2^24`. The actual batching prototype exceeds that allowance.

| Complete circuit variant | Constraints | Total rows | Padded domain | Headroom below 2^24 |
| --- | ---: | ---: | ---: | ---: |
| Baseline gnark BN254 GLV+fake-GLV, separate pairings | 17,996,081 | 17,996,083 | 2^25 | -1,218,867 |
| Baseline arithmetic, randomized pairing batching | 17,530,146 | 17,530,148 | 2^25 | -752,932 |
| Classic GLV, separate pairings | 14,689,440 | 14,689,442 | 2^24 | 2,087,774 |
| Classic GLV, randomized pairing batching | 13,810,184 | 13,810,186 | 2^24 | 2,967,030 |

**The normal helper now selects classic GLV and retains separate pairings.**
This saves 3,306,641 constraints (18.37%) and crosses the domain boundary
without changing the inner transcript or introducing a batching challenge.
Gnark's `PreferClassicGLV` selects computed GLV multiplication instead of the
default BN254 rational-reconstruction path. Complete arithmetic, point
validation and both pairing obligations remain enabled. BLS already used the
classic path, so its arithmetic selection is unchanged.

The default helper compiled the real profile to 14,689,440 constraints, two
public inputs, one commitment and domain 16,777,216. Its compiled witness
diagnostic passed; changed claims and deferred operands were rejected by the
compiled constraints. Classic-GLV MSMs matched native arithmetic on 36 cases
covering zero, one, minus one and large scalars, infinity, equal/opposite points
and identity sums; an incorrect output was rejected. All three optimization
variants passed the real Init witness and rejected claim, evaluation,
commitment and deferred-operand mutations without native preverification.

Batching remains an internal measurement variant, with no CLI switch and no
production key. It requires identical ordered G2 anchors, binds a fresh
nonzero 512-bit BLAKE3 challenge to the inner profile, claim, final inner
transcript state and all four pairing operands, and uses complete scalar
multiplications and additions. Its tests reject independently invalid equations,
deliberate cancellation at a predetermined coefficient, mismatched anchors and
changes to every variable challenge input. Identity cases and zero-reduction
rejection are covered. See the [batching specification](bls-plonk-wrapper-plan.md#measured-bn254-candidates)
for the experimental transcript encoding and quantitative cost.

The reports are `target/plonk-batching/bn254-components.json` and
`target/plonk-batching/bn254-variants.json`. The normal compiled circuit and its
manifest are in `target/plonk-batching/artifacts-classic`; its frozen helper is
`target/plonk-batching/ix-bn254-plonk-wrapper`. The subsequent full benchmark
below generated the matching 2^24 Lagrange basis and circuit keys and proved
the actual Init witness. The preceding 104.33-second proof measurement belongs
to the original 2^25 configuration. Its imported SP1 2^25 basis cannot simply
be truncated. Both benchmark configurations remain available with their frozen
helpers.

## BN254 2^24 full Init proof benchmark

The classic-GLV wrapper with separate pairing checks completed a full native
PLONK proof and independent verification on 2026-10-16. The input is the same
authenticated Ignition/BLAKE3 Init packet and independently expected claim as
the earlier BN254 run. The compiled circuit has **14,689,440 constraints**, two
public inputs, one extra commitment and domain **2^24**. Randomized pairing
batching is disabled.

| Measurement | BN254 2^24 | BN254 2^25 | BLS12-381 2^25 |
| --- | ---: | ---: | ---: |
| Core `plonk.Prove` | **53.785 s** | 104.332 s | 127.168 s |
| Complete fresh prover process | **73.704 s** | 143.592 s | 293.870 s |
| Internal native `plonk.Verify` | 1.488 ms | 1.196 ms | 2.754 ms |
| Decode/public-witness/verify median | 1.813 ms | 1.923 ms | 4.196 ms |
| Complete verifier-process median | 22.519 ms | 21.696 ms | 25.508 ms |
| Peak prover RSS | **25.19 GiB** | 47.18 GiB | 53.63 GiB |
| Native proof | 584 bytes | 584 bytes | 744 bytes |
| ix envelope | 624 bytes | 624 bytes | 784 bytes |
| Solidity proof encoding | 864 bytes | 864 bytes | 1,184 bytes |

Relative to the earlier BN254 run, core proving took **48.45% less time**,
the complete process took **48.67% less time**, and peak RSS fell **46.60%**.
Relative to BLS, the reductions were **57.71%**, **74.92%** and **53.02%**.
The measurements use the same 48 logical CPUs, default parallelism and native
CPU gnark backend. Each configuration has one proof sample, with prepared
keys in a fresh process and uncontrolled OS page-cache state. Verification
medians use seven fresh processes with warm file caches and exclude resource
monitor overhead. The small verification-time differences between the two BN254
runs do not establish a speed improvement or regression.

Preparation was measured separately:

| Preparation operation | Time |
| --- | ---: |
| Authenticated monomial SRS export | 3.738 s |
| Complete parameter/key preparation command | **358.302 s (5m 58s)** |
| SRS import within preparation | 1.851 s |
| Lagrange conversion and cache publication | **325.258 s (5m 25s)** |
| Circuit indexing | 12.542 s |

The 2^24 basis was computed locally from admitted Ignition monomial powers;
the command reported `reused_lagrange=false`. The basis and keys are now cached.
Preparation peaked at 12.17 GiB RSS. The compiled circuit was reused from the
validated sizing run (13.096 seconds internal compilation) after checking its
hash and frozen-helper identity. Compilation, SRS export, basis conversion,
key generation and inner KZG proving are all excluded from proof timing.

The proving key is 1,073,776,312 bytes and the verifying key is 34,384 bytes.
The frozen helper SHA-256 is
`fad956a1680bd2e7a6412e3b8e65a3cb90a8ac9d0848daa52c97036916d3e957`;
the verifying-key SHA-256 is
`4f27f4cb17c22d0e73de231ffbda679314c76a2103f24468af5c700b599ff368`.
The authenticated exported SRS BLAKE3 is
`a71cd91e2cf082700740aa25a37896d8f68fafa4bec07b927720dea881705e0a`.

Fresh-process native and Rust catalog-based verification passed against the
original claim without proving parameters configured. Wrong claims, altered
proofs, unknown keys, modified keys, wrong curve tags, absent catalogs and
missing or incorrectly pinned admissions were rejected. The test catalog is
isolated; this does not activate the key for production. Complete CLI packaging
remains outside this benchmark. The subsequent EVM check is recorded below.

The report is `target/bn254-plonk-2p24/report.json`, with artifacts and logs
under `/opt/dlami/nvme/ix-bn254-plonk-2p24-52c61479/`. It contains the comparison,
stage resource records, seven verification samples, parameter receipt, artifact
hashes and catalog-check outcomes. Final executables are in `bin-final`, and
the circuit and prepared keys are in `artifacts-final`.

## BN254 CUDA PLONK implementation and actual-witness MSMs

The optional BN254 CUDA helper now implements gnark MSM/FFT hooks, an unfused
numerator and a fused quotient. It uses the existing transcript, blinding,
constraints, Ignition bases and verifying key. The standalone native library
uses pinned sppark and BLST sources; authenticated patches apply to private
copies of sppark and gnark. CPU remains the default backend.

The initial complete CUDA proof verified independently but took **72.076 s**,
against **53.889 s** for its matched CPU run. MSM callbacks consumed **61.850 s**;
the fused quotient took only **1.152 s**. Dense random-scalar microbenchmarks
had missed extreme digit concentration in actual witness commitments.

With split buckets, three paired CPU/unfused/fused rounds completed using the
same loaded production-size Init circuit, keys and witness:

| Core `plonk.Prove` | Median | Range, three proofs |
| --- | ---: | ---: |
| CPU | **53.895 s** | 53.657–54.083 s |
| CUDA unfused | **11.448 s** | 11.374–11.742 s |
| CUDA fused | **11.352 s** | 11.243–11.372 s |

Fused CUDA is **4.75× faster** than the matched CPU median, taking **78.94% less
core proving time**. These timings exclude artifact/witness loading (22.023 s
once), backend setup and verification. Each proof has fresh blinding; each GPU
proof has a fresh native context. All runs use default parallelism on 48 logical
CPUs and GPU 0, with no forced garbage collection. CUDA setup took 0.106–0.402 s.
The first round includes first-use driver/module initialization in that setup
timer; these are not complete fresh-process latency measurements.

Fused callback medians were 0.899 s for all 11 MSMs and 1.169 s for the quotient,
including its internal transforms and host restoration. There were 75 FFTs and
13 CPU tail points per GPU proof. Fused explicit transfers were 15,368,830,016
upload bytes and 9,663,676,416 download bytes, saving 2 GiB in each direction
against unfused. Transfer counts include basis setup. Queue wait (0.529 s median)
overlaps submitted work; it must not be added to callbacks as a separate stage.
The small fused/unfused wall-time difference alone does not identify the
critical path; opt-in stage timing and CPU profiling provide that attribution.

The native accounted/pool-used peak was **18.58 GiB** and pool reservation
**18.59 GiB**. Two-second device polling saw 19,725 MiB; it can miss short peaks.
The entire nine-proof process peaked at **35.80 GiB host RSS**. That shared heap
measurement is not an isolated per-backend RAM comparison.

All nine 584-byte proofs passed independent verification with the frozen
CPU-only helper and the existing verifying key. Wrong-claim and altered-proof
checks passed for both CUDA modes. The first fused CUDA proof also passed all
**47 existing Solidity/Anvil checks** with the same adapted SP1 contract,
including **320,091 total transaction gas** through the ix adapter. Proof
encodings remain 584 bytes native, 624 bytes enveloped and 864 bytes for Solidity.
The native report is `target/bn254-plonk-cuda/init-03-report.json`; the EVM report
is `target/plonk-evm/init-03-cuda-fused/report.json`. Frozen ABI4 executables and
library are under `target/bn254-plonk-cuda/abi4-frozen/`.

### Remaining bottleneck: measured CPU stages and transfers

The final ABI7 build removes the unused normalization/basis-sum interface and
adds transfer accounting. An opt-in gnark observer records monotonic compute,
task and dependency-wait intervals without changing proof scheduling. A
separate diagnostic run produced two independently verified fused proofs:
**11.402 s with CPU sampling**, then **11.500 s without CPU sampling**. Both had
stage observation and DMA event timing enabled. Sampling covered `plonk.Prove`
only; artifact loading, backend setup, verification and profiler start/stop
were excluded. These two diagnostic samples do not replace the three-round
benchmark above.

The second proof's critical path accounts for its complete 11.500 s:

| Stage | Wall time | Interpretation |
| --- | ---: | --- |
| Initialization | 2.991 s | Rebuild FFT domains and fixed circuit trace |
| Constraint solving | 1.650 s | Witness-dependent solver, including BSB22 hint commitment |
| L/R/O commitments | 0.445 s | Enclosing concurrent commitment group, including host work and queueing |
| Permutation grand product | 1.686 s | CPU identity support, row products, prefix products and inversion |
| Z commitment | 0.080 s | CPU/GPU commitment path |
| Fused quotient | 1.200 s | GPU arithmetic, transfers and host restoration |
| H commitments | 0.233 s | Three commitment operations |
| Z opening | 1.031 s | CPU evaluation/division followed by GPU commitment |
| Linearization | 0.976 s | CPU evaluations, canonical conversion and coefficient arithmetic |
| Linearization commitment | 0.080 s | GPU commitment path |
| Batch opening | 1.086 s | CPU evaluation/folding/division followed by GPU commitment |
| Other gaps/bookkeeping | 0.042 s | Includes challenge preparation |

The L/R/O/Qcp evaluations occupy about 0.418 s entirely inside the Z-opening
interval, adding no extra time to the current critical path. Individual L/R/O
commitment spans likewise overlap and must not be added to their enclosing
group. **The quotient is on the critical path**; similar fused/unfused totals
do not establish otherwise.

Transfers during the second proof, after subtracting backend setup, were:

| Measurement | Result |
| --- | ---: |
| Upload | 13,221,346,368 bytes in 25 logical calls |
| Download | 9,663,676,416 bytes in 15 logical calls |
| Actual DMA time, CUDA events | 270.57 ms upload + 189.28 ms download = **459.84 ms** |
| Host staging copies | **778.17 ms**, overlapping DMA/other device work |
| Inclusive upload/download wall time | 458.68 / 713.91 ms |

The bounded transfer rings use pinned staging memory. Download wall time can
include waiting for previously enqueued kernels; it is not pure copy time.
DMA, host-copy and inclusive wall timings overlap, so their sum is invalid.
The first proof similarly measured 463.55 ms DMA and 773.13 ms host staging.
This establishes a CPU-dominated remainder rather than attributing the entire
gap to transfers. Residency remains useful, especially alongside further
arithmetic offload, but copy elimination alone does not explain the remaining
roughly ten seconds.

The CPU profile collected 51.18 CPU-seconds across threads during 11.40 seconds
of wall time. Scalar-field multiplication accounts for 54.14% of flat samples.
Prominent callers include permutation row products, linearization, CPU FFTs
and KZG opening evaluation/folding. These are aggregate CPU samples, not stage
wall-time percentages. The `NewTrace` call alone has 2.78 cumulative sampled
CPU-seconds; the stage timeline separately measures initialization's wall cost.
GC accounts for only 0.02 CPU-seconds (0.04%). Exclusive stack-family analysis
attributes 25.24% to permutation/support, 15.30% to linearization arithmetic,
12.17% to remaining CPU FFTs and 11.25% to polynomial evaluation. Worker stacks
do not retain every parent call, so not every FFT sample can be assigned to
its enclosing wall-clock stage.

The next work should follow this evidence:

1. Cache immutable circuit trace/domain/permutation preparation in a persistent
   worker. The 2.991 s initialization span is an opportunity ceiling, not a
   guaranteed saving. Keep mutable polynomial wrappers/copies separate because
   quotient construction changes representations in place.
2. Reuse fixed permutation identity support and canonical static Qk; schedule
   S1/S2 evaluations beside the existing evaluations, and reuse already-known
   evaluations at the same challenge in batch opening. Remove the two unused
   N-element scratch arrays in quotient construction after validating that
   cleanup separately.
3. Add a permutation scan/inversion operation, then resident linearization and
   opening operations. Horner evaluation, synthetic division and folding still
   execute on the CPU; existing MSM hooks accelerate only their commitments.
   Preserve transcript dependencies and explicit host/device representations.

The diagnostic report is `target/bn254-plonk-cuda/init-04-report.json`, with
CPU profiles and span data under
`/opt/dlami/nvme/ix-bn254-plonk-cuda-52c61479/init-04/` and text profile analyses
under `target/bn254-plonk-cuda/profile-analysis/`. The final proof also passed
all 47 isolated EVM checks (`target/plonk-evm/init-04-cuda-fused/report.json`).
The production helper built and verified that proof with no GPU visible and
without an incidental `LD_LIBRARY_PATH`. Focused ABI7 arithmetic/proof tests,
the backend factory, observer tests, all nine Lake configurations and offline
Nix package evaluation passed. A complete Nix CUDA package build and persistent
worker/service lifecycle tests remain outstanding.

### Structured-witness MSM implementation and replay

The default MSM now partitions oversized buckets into at most 256-point tasks,
then reduces their partial sums in parallel. It retains zero-digit elimination,
the special ±1 path and sppark's existing signed-scalar folding. No affine
normalization or additive masking runs by default. Complete group addition
handles equal, inverse and infinity partials. Supported domain bounds also
bound each reduction lane's work; exact scratch accounting includes invocation
batching. Exception cleanup finishes queued work before freeing scratch.

Four private captures contain the actual Init BSB22/L/R/O Lagrange scalars,
authenticated ranges and CPU results. Replay checked all four results exactly,
including unchanged scalar bytes, with a fresh context per vector and two
invocations per context:

| Captured MSM | CPU reference | Split first / second | Mask first / cached |
| --- | ---: | ---: | ---: |
| BSB22, 16,777,216 points | 361.78 ms | 36.84 / 37.19 ms | 130.34 / 74.37 ms |
| R, 14,689,440 points | 1,503.42 ms | 101.66 / 101.53 ms | 116.75 / 66.39 ms |
| L, 14,689,442 points | 1,702.20 ms | 110.94 / 114.60 ms | 116.97 / 66.42 ms |
| O, 14,689,440 points | 1,147.95 ms | 80.78 / 82.88 ms | 119.47 / 68.06 ms |

These are individual calls with resident bases; scalar upload and callback
overhead are included, while context creation, key loading and capture decoding
are excluded. CPU reference calls use default full parallelism. They are not
whole-proof stage timings. Masking is exact and remains an explicit comparison
mode: its cached calls win on L/R/O, but it loses sparsity, needs correction
precomputation and is slower on BSB22. Split buckets remain the default.

Per-window telemetry confirms buckets as large as **3,672,384 points** in R
and **3,671,509 points** in L. It records maximum bucket occupancy, nonzero/zero
digits, extra chunks, ±1 counts and classification/accumulation/reduction time.
The split scratch at N=2^24 is 41 MiB plus 544 bytes. Boundary and signed-digit
tests, FFT/layout and quotient CPU oracles, 18 small proof variants and the
production backend factory proof test passed.

Reports and resource logs are under `target/bn254-plonk-cuda/`; private captures
and replay reports are under
`/opt/dlami/nvme/ix-bn254-plonk-cuda-52c61479/`. The capture manifest SHA-256 is
`7d34825121e40620f17bd2f27115ea99b6cd1a4463dd2ec74015061fb4bfc0a7`.

## BN254 proof verified by adapted SP1 Solidity on Anvil

On 2026-10-17 the exact 2^24 proof above passed a mined Anvil transaction through
SP1 v6.1.0's PLONK verification algorithm with ix's circuit key. The untouched
SP1 contract rejects the two ix public inputs; padding to five inputs also
fails, and its correctly framed high-level facade rejects with `InvalidProof()`.

The adapted source changes only **23 `VK_*` constants**. Its SRS anchors,
arithmetic, transcript, proof encoding and checks are unchanged. After
normalizing the pragma, it equals the Solidity verifier emitted by our pinned
gnark helper. The existing `IxPlonkVerifier` adapter binds the independently
expected claim digest as two little-endian 128-bit limbs. No proof regeneration
or cryptographic-verifier rewrite was required.

| Call | Execution gas | Total transaction gas | ABI calldata |
| --- | ---: | ---: | ---: |
| Adapted SP1 `Verify` | 279,915 | **316,003** | 1,060 bytes |
| Through ix's claim-digest adapter | 284,435 | **320,103** | 964 bytes |

These are Foundry/Anvil 1.8.5 and solc 0.8.37 measurements, using via-IR,
optimizer 200, Prague bytecode and Osaka execution rules. Total gas includes
transaction intrinsic/calldata gas; deployment is separate. The EVM proof
encoding is **864 bytes**. The 584-byte native proof and 624-byte ix envelope
are rejected as wrong encodings. Valid return values were checked through
`eth_call` and transaction call traces, in addition to successful receipts.

The verifier's runtime is **7,531 bytes** and its deployment cost is
**1,681,283 gas**. The adapter has **913 runtime bytes** and costs **255,356 gas**
to deploy. Ordinary EIP-170/EIP-3860 limits remained enabled. Traces contain
one BN254 two-pair check, 21 scalar multiplications, 21 additions, nine SHA-256
calls and six MODEXP calls; the precompiles consume 257,366 gas in total.

All **47 checks passed**, including positive raw/adapter verification, stock
SP1 rejection, both digest halves, wrong public-input shapes/ranges, malformed
proof lengths, wrong encodings, every proof word mutated independently, and
noncanonical curve/scalar values. The isolated Anvil nodes were shut down
after measurement. No public-chain deployment or production catalog activation
was performed.

The pinned upstream sources, adapted contract, actual Init fixture and
reproducible harness are under `contracts/plonk/bn254/`. See the
[contract documentation](../contracts/plonk/README.md#actual-bn254-init-proof-on-anvil)
for source provenance and the replay command. Full receipts, traces and results
are in `target/plonk-evm/run-final/report.json` and adjacent files.

## Persistent S3 archives

The completed CPU PLONK artifacts were archived on 2026-10-17 in
`s3://argument-kzg-params-063002298335-us-east-1-an/`, account `063002298335`,
region `us-east-1`, grouped by curve. Only the current BN254 2^24 bundle was
uploaded; the obsolete BN254 2^25 bundle was excluded.

| Curve | Domain | Objects including archive manifest | Size |
| --- | ---: | ---: | ---: |
| BLS12-381 / Filecoin | 2^25 | 89 | 9.503 GiB |
| BN254 / Ignition | 2^24 | 87 | 3.367 GiB |

Prefixes relative to the bucket:

```text
bls12-381/plonk/init/2p25/73d8ebbad3df955310fcf7c8b7d35cf04f6ecd5be513f55af25036b7349e5299/
bn254/plonk/init/2p24/4f27f4cb17c22d0e73de231ffbda679314c76a2103f24468af5c700b599ff368/
```

Each contains the compiled circuit, proving/verifying keys, matching frozen
helper and worker, monomial export and receipt, Lagrange cache, input witness,
inner KZG packet/profile, original claim, proof encodings, Solidity verifier,
benchmark records, and a portable candidate verifier catalog. BN254 additionally
includes the pinned Ignition admission and the Anvil verifier sources, fixture,
receipts and traces. Existing ceremony objects are referenced rather than
duplicated. Large KZG witness/fixed checkpoints, compiler caches and unfinished
CUDA experiments at publication time are outside these PLONK archives. The
subsequent completed CUDA benchmark/profile runs (`init-03` and `init-04`),
MSM captures, and CUDA executables also remain local under the paths recorded
above; they have not been uploaded. Their implementation, summarized findings
and artifact locations are committed, while raw logs/profiles and captures
remain in ignored `target/` directories and `/opt/dlami/nvme/`.

Every upload used conditional creation and a server-validated full-object
SHA-256. All 176 objects were checked with S3 checksum-enabled HEAD responses;
both archive manifests were downloaded and hashed independently afterward.
The 118 objects already present in the bucket retained their sizes, ETags and
modification times. Archive `MANIFEST.json` files were published only after all
payload objects had been verified.

Trusted SHA-256 pins for the archive `MANIFEST.json` files:

```text
BLS12-381: 6be357f686599d283acca68e6eb4a9aa9f29c31d0010e7c8190f5767a04daaee
BN254:    18a1ef97033721a578bee16fa0db1f67108f8dc08d8e6e2c7f964f4bf291d286
```

After downloading a complete prefix, run its `verify_bundle.py` with
`--manifest-sha256` set to the corresponding pin above. Restore executable
permissions with `chmod +x bin/*` to use the frozen Linux amd64 tools.
The bundle's `README.txt` describes cache layout and the candidate catalog;
archiving does not authorize that catalog for production. The local publication
receipt is `target/s3-kzg-upload/publication-receipt.json`.

## Original implementation checkpoint

The following records the earlier run on the approximately 47 GiB host,
where parameter preparation was killed by a system OOM before indexing or
proving. Its remaining-work list describes that checkpoint, not the later
benchmark above.

Worktree: `/home/sam/repos/ix.bls-plonk-wrapper`, branch
`sb/bls-plonk-wrapper`, based on ix
`faba9bdd4445295f08dfbcf773ada80afe3f0c35`. The implementation plan is
[bls-plonk-wrapper-plan.md](bls-plonk-wrapper-plan.md). This handoff records the
current implementation and supersedes the earlier October 15 checkpoint.

## Implemented behavior

`ix compress ROOT_PROOF_ADDRESS --plonk --out OUTPUT` selects a terminal
BLS12-381 PLONK stage after the existing compression pipeline. It preserves
the ix claim and produces a new proof envelope. The circuit verifies the final
KZG packet, including both its opening pairing and its deferred pairing.
Its public inputs are the expected BLAKE3 claim digest packed into two
little-endian 128-bit limbs; the trusted circuit fixes the aggregation prefix.

The final ix KZG transcript is BLAKE3. This is separate from gnark's outer
PLONK transcript, which uses matching native/Solidity settings. The wrapper
uses Filecoin universal powers through ix's existing authenticated loader;
there is no circuit-specific trusted ceremony. Development SRS selection is
rejected for the terminal PLONK stage.

Verification requires an independently authorized catalog selected by
`IX_PLONK_VERIFIER_CATALOG`. A generated candidate catalog is never activated
automatically. The envelope identifies a key by SHA-256; verification checks
that key and its Filecoin anchors and derives the expected digest from the
caller's claim. Verification does not require the proving SRS.

| Area | Files and behavior |
| --- | --- |
| BLAKE3 profiles | `crates/proof-compression/src/pipeline/{stages/wrap.rs,wrap/outer.rs,verifier.rs}` and `profiles/aggregate-*-v6.*`. New proving selects version 6/BLAKE3. Historical v5 decoding and direct Solidity fixtures remain. Production v6 profile metadata was regenerated; production v6 proof packets were not. |
| Shared verifier export | `pipeline/wrap/outer/solidity/plonk.rs` and `plonk/ir.rs` reuse the validated graph/opening layout. The scalar program is generated through multi-stark's graph sweep and `logup_constraint_values`, rather than another handwritten scalar verifier. |
| Circuit | `tools/bls-plonk-wrapper/{blake3,profile,circuit}.go`. BLAKE3 block/tree/XOF behavior, canonical point encodings, curve/subgroup checks, native-to-emulated scalar binding, complete MSM arithmetic and two separate pairing checks. Identity maps to `(0,0)`. Trusted fixed-base relations are checked before folding coefficients. |
| Parameters and artifacts | `pipeline/plonk.rs` and Go `{parameters,artifacts,backend}.go`. Rust authenticates Filecoin and exports canonical coordinates with a BLAKE3 receipt. Go derives/caches Lagrange points, prepares keys, proves, verifies and exports Solidity. Cache identities bind the setup, domain, receipt, profile and relevant executable. |
| Native integration | `pipeline/mod.rs`, worker dispatch, `crates/ffi`, `Ix/Cli/{Compression,CompressCmd}.lean`. Adds the `--plonk` flag, proof-envelope dispatch and independently trusted key catalog. Helper output goes to stderr so CLI proof-address output remains usable. |
| Solidity | `contracts/plonk/`. An immutable generated-verifier address and digest-to-limb adapter, with positive, changed-digest, malformed-proof and deployment-size tests. Requires EIP-2537. |
| Build and CI | `lakefile.lean`, `flake.nix`, `.github/workflows/{ci,bench-main,bench-pr}.yml`. Builds/installs the Go helper beside ix and the worker, exposes a standalone Nix package/check, and provisions Go for CI. The new CI job uses the existing Ubuntu 26 RunsOn image. |

Go helper commands are `compile`, `check-witness`, `prepare`, `prove` and
`verify`. Worker PLONK commands are `fixture`, `export`, `srs`,
`profile-blake3` and `wrap`. See the helper and contract READMEs for their
arguments. `check-witness` explicitly reports that it creates no proof; its
diagnostic commitment hint is not used by production `plonk.Prove`.

The Go module pins gnark `v0.16.5-0.20261015185324-262cf453c107`, gnark-crypto
`v0.22.1-0.20261009142911-8911ee45d22b` and Go 1.26.8. The upstream tip was
checked on October 16; v0.16.4 was the latest tagged gnark release then. This
helper uses the native CPU backend. Experimental WebGPU/WASM PLONK support
exists upstream but is not enabled here. The inspected native ICICLE/CUDA
integration is for Groth16. SP1's inspected final PLONK path also runs on CPU,
using an older gnark fork and BN254; the plan has the pinned source comparison.

## Verified results

These results cover the source before the final parameter-memory scheduling
change described below, except where explicitly stated. No tests or builds
were started after the request to stop builds and prepare this handoff.

| Check | Result and boundary |
| --- | --- |
| BLAKE3 differential tests | Passed lengths 0, 1, 63, 64, 65, 1023, 1024, 1025, 2048 and 3073, including 96-byte XOF output and mutations. |
| Compiled one-block BLAKE3 | Valid witness passed and changed input failed; 261,201 constraints including lookup overhead. |
| G1 encoding/subgroups | Identity, generator and negative generator passed; wrong sign, wrong subgroup and a noncanonical `X = p` alias were rejected. |
| Complete verifier witnesses | Two distinct Filecoin conformance statements passed; changed digest and an outer-valid packet with an invalid deferred pairing failed. |
| Full compiled circuit | 20,665,582 constraints, domain `2^25`, two public inputs and one extra commitment. Compilation took 15.23 seconds; serialized constraints occupy 495,020,281 bytes. |
| Compiled witness diagnostic | Valid full witness passed in 2.24 seconds. A subgroup-valid invalid deferred pairing failed in the compiled circuit, bypassing host pre-verification. This is not a PLONK proof. |
| Actual PLONK proofs | Tiny Filecoin-backed `N=8` circuits proved and verified for `m=0` and `m=1`. Native proofs are 664/744 bytes and Solidity encodings are 1,056/1,184 bytes. These circuits do not verify an ix packet. |
| Lagrange and artifact checks | Basis-conversion equality, cache reuse, corruption rejection and backend-identity separation passed on small parameters. Rust parameter export/cache and catalog rejection tests passed. |
| Solidity conformance | Four tests passed on the earlier run. The tiny `m=1` proof used 371,471 gas around the external adapter call, with 1,284 bytes of ABI calldata. This excludes transaction intrinsic/calldata gas and is not a full-wrapper measurement. The October 16 Foundry rerun was not completed because the downloaded binaries need NixOS runtime-loader setup. |
| Rust pipeline tests | The broad filtered run passed 41 tests and found two historical Solidity-version guard failures. Those guards were fixed; the focused five-test Solidity rerun passed. The entire filtered suite was not repeated afterward. |
| Rust Clippy and FFI | Focused Clippy with all targets and `-D warnings` passed. Release `cargo check -p ix-ffi --features parallel` passed. |
| Lean/Lake | `lake -R check-build` and typechecking the two changed CLI modules passed using compatible existing dependency artifacts. A complete `lake build ix` was not run. |
| Nix helper package | Standalone helper build and its checks passed before the final memory change: `/nix/store/n87wh5a7wv2c7y492manm7fvjbpiyr5x-ix-bls-plonk-wrapper-0.1.0`. Full ix packaging was not built. |
| Final memory-change build | `go build -buildvcs=false -trimpath` succeeded. Its new binary has not run parameter preparation or tests. |

The attempted `go vet ./...` session lost its result during the interruption;
it is not counted as a pass. The pre-existing long identity-column proof test
remains ignored. Git whitespace checks pass; no claim is made that the whole
repository test suite or CI has passed.

### Circuit cost breakdown

| Cumulative phase | Constraints | Added constraints |
| --- | ---: | ---: |
| Point validation and public binding | 3,211,317 | 3,211,317 |
| BLAKE3 transcript | 9,496,602 | 6,285,285 |
| Scalar relation | 9,497,043 | 441 |
| Opening MSMs | 17,265,132 | 7,768,089 |
| Outer pairing | 18,965,730 | 1,700,598 |
| Deferred pairing | 20,665,582 | 1,699,852 |

These are compilation differences; shared range checks affect attribution.
Fixed-point folding reduced the initial 23,358,575 constraints to 20,665,582.
The alternative gnark MSM setting increased the count to 25,429,821 and was
reverted. The current implementation retains the default classic GLV path.
Even deleting the entire second pairing for free leaves more than `2^24`
constraints, so pairing batching alone cannot reduce the padded domain.
Randomized pairing batching was not implemented.

## OOM and the final unexercised change

At 10:35:01 America/New_York on October 16, the kernel reported a global OOM
and killed PID 386714, `ix-bls-plonk-wr`, during Lagrange preparation. Its RSS
was approximately 22.1 GiB. Other assistant processes accounted for roughly
22.6 GiB; the VM has about 47 GiB visible RAM and no swap. The existing monitor
only enforced a process RSS threshold, so it did not detect aggregate memory
pressure before the OOM. This does not establish the isolated memory required
by the complete wrapper prover.

The authenticated monomial export completed and survives. No Lagrange cache
was published, `KeysReady` remains false, and neither full indexing nor proving
has completed. There is no full-wrapper proving time, peak-memory result or
total verification transaction-gas result.

The final edit in `tools/bls-plonk-wrapper/backend.go` delays loading the
constraint system until after Lagrange conversion, releases FFT temporary
memory before deserialization, releases setup temporaries before key writing,
and reports the preparation stage. The new helper compiled successfully, but
the memory reduction and runtime behavior have not been tested. No system
available-memory guard or persistent hard-limit runner was implemented.

The last resume check found roughly 36 GiB available and no other large
compute job. The user authorized the full machine and does not want an
artificially small memory cap. At the next authorized run, check actual host
headroom, retain default CPU parallelism, and account for whole-system memory
rather than relying solely on RSS or Go's soft `GOMEMLIMIT`.

## Preserved local artifacts

Everything below is ignored build/research data, not part of the proposed
commit. Paths are relative to this worktree unless absolute.

| Artifact | Location or identity |
| --- | --- |
| Go toolchain | `target/plonk-tools/go/bin/go` (1.26.8). Downloaded from go.dev and checked against official SHA-256 metadata. |
| Go caches | `GOPATH=$PWD/target/plonk-go`, `GOCACHE=$PWD/target/plonk-go-build`. |
| Rust cache and worker | `/home/sam/repos/ix.sb-solidity-verifier/target`; worker under `release/ix-compression-worker`. This cached executable predates some final source edits. |
| Compiled circuit | `target/plonk-artifacts/`; manifest records `KeysReady: false`. |
| Original matching helper | `target/plonk-tools/ix-bls-plonk-wrapper`; SHA-256 `f5fd0c6addfa9792d136be29ee3f2a6cf82ad12c4dd4c099555b5a780ed18c4d`. |
| New helper with deferred circuit loading | `target/plonk-tools/ix-bls-plonk-wrapper-v2`; SHA-256 `eabb30f677f9aa17adb2a9d27611a79e52abb6669c78e8b7913058f77cf4b0e6`. |
| Component measurements | `target/plonk-components.json` and `target/plonk-components-alternative.json`. |
| Filecoin cache used by Rust | `target/plonk-data/filecoin-through-2p26.bin`; sparse file with the authenticated header, required prefix and complete chunk index. Unrequested later powers are holes. |
| Canonical monomial export | `target/plonk-data/wrapper-srs.bin` and `wrapper-srs.json`; 33,554,435 points for `N=2^25`, 3,221,226,040 bytes. |
| Export resource report | `target/plonk-data/export-resources.json`: 53 seconds, peak RSS 9,602,716 KiB, exit 0. |
| Solidity tooling/fixtures | `target/plonk-tools/foundry/` and `contracts/plonk/generated/`. Foundry runtime setup on this NixOS host remains incomplete. |
| Lean typecheck overlay | `target/lean-check/`; compatible prebuilt dependencies came from `/home/sam/repos/ix`. |

The old compiled artifact binds the original helper hash. The new helper must
compile into a new artifact directory; do not edit the manifest to bypass
identity checks. The underlying conformance profile SHA-256 is
`195b35b3f9dc926aa9fe7a01719adc6cb9e6913e0c6443228ae3105d2466830b`, and the
existing compiled circuit SHA-256 is
`e6b895608883f29d03a5db1183e0083d0ceb75bf2fc3bf5c5b38f7f13ca677b4`.

The existing Rust loader authenticated the requested prefix of the sparse
Filecoin cache, not its unpopulated tail. The source was the existing
[prepared Filecoin prefix cache](https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/filecoin-prefix-2p27.bin).
The independently obtained receipts are:

- Filecoin manifest BLAKE3: `1442386005c4e4a2ebc23c109694eb9bb16fe54bc5708f0380658ac99a37f10a`.
- Setup ID: `48b74609da5ec9a9d59efb1d4c9d91d81815a304a8baab8ba35af4fe0145239f`.
- Export BLAKE3: `26d517c2c6c54adfba55635f01d942a3be3394a97f14a4ea22db8d3c13e44c20`.
- Public maximum degree: `268435454` (`2^28 - 2`).

## Remaining work after handoff

1. Exercise the final preparation-order change on a small circuit, including
   prepare/reuse/corruption cases. Add host-memory monitoring before another
   large run. Do not reuse the old RSS-only runner as an OOM safeguard.
2. Complete Lagrange conversion, full indexing and a complete conformance
   wrapper proof, recording time and memory for each stage. The `2^25` domain
   may still exceed the practical prover budget even if conversion succeeds.
3. Give the BLAKE3 conformance fixtures known claim bytes. Their current digest
   words are synthetic `1000+i`-style test values, so they cannot exercise
   `pipeline::verify` against a known claim preimage. Regenerate those witnesses
   with `statement::with_claim`, preserve the fixed aggregation prefix, and
   check profile identity before reusing keys. This change is not implemented.
4. Exercise the complete Rust proof-envelope/catalog path, including wrong
   claim, wrong key and setup anchors, without a proving SRS available to the
   verifier. Expand native intermediate-value differential checks as needed.
5. Generate and prove an actual aggregate v6/BLAKE3 packet. The new production
   profiles are public metadata conversions, not new proof packets; the small
   conformance circuit does not establish production resource requirements.
6. Run real local verification transactions with the full wrapper proof and
   compare the same gas boundary against the optimized direct verifier. The
   acceptance target remains at most 500k total transaction gas and at least
   25% savings; neither has been established for the full wrapper.
7. Complete the deferred integration checks: focused tests of the final Go
   edit, `go vet`, full CLI packaging and CI. Treat catalog authorization and
   production circuit review as separate from generating a key.

## Commit scope

Suggested title: `feat(compression): add experimental BLS12-381 PLONK wrapper`.
The commit description should state that it adds the BLAKE3 relation, Filecoin
parameter adapter, native/CLI integration, independent key authorization,
Solidity adapter and packaging, with small-backend proof coverage. It must
also state that complete wrapper proving stopped at parameter preparation and
that the final memory-ordering change is only build-checked.

The initial commit includes the wrapper implementation, plan, handoff and
[`compression-architecture-options.md`](compression-architecture-options.md).
The architecture-options document is included unchanged for follow-up review;
its alternative pipeline proposals have not been implemented or measured.
The current wrapper measurements are recorded above. Ignored `target/`
artifacts and generated contract fixtures are excluded.

For a split review, the natural groups are: BLAKE3 profiles and shared Rust
export; Go circuit/backend and fixtures; ix CLI/catalog/build integration; and
Solidity plus documentation. Some files cross those boundaries, so splitting
requires hunk staging and independent validation of the resulting commits.
The initial commit does not split those groups.
