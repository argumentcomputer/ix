# Certified compiler performance checkpoint

The target is complete certified Lean-to-Ixon compilation of Init+Std in less
than 10 seconds and Mathlib in less than 60 seconds of wall-clock time.
Neither target is achieved. This checkpoint preserves reviewed integration
work and separate experiments so implementation can continue incrementally.
It is not final CI or merge signoff.

## Measurement contract

Measurements use fresh processes on the development host with 32 physical
cores, 64 logical CPUs and about 495 GB RAM. Lean imports are built beforehand;
the command still loads and elaborates its input. All requested declarations,
proof bodies, ordinary metadata, default sharing limits, production checks,
role finalization, output writing and cleanup are retained. No workload Ixon
output cache or partial-output option is used. Timed runs are exclusive.

The current Init+Std workload has 117,694 input declarations and zero compiler
failures. Its complete 253,772,604-byte artifact has SHA256
`e48adef624e70bcdd3f22e1d96251682ac046a088700ccf5cf512f1b49afcda1`.

## Integrated change

Trace source generation is deferred until the code-generation command requests
it. Previously it ran during unrelated CLI initialization. Strict module/native
checks, exact help output, generated trace freshness, and a small Lean/Rust
artifact comparison passed. A full Init+Std comparison in both orders reduced
mean process wall time from 90.160 to 83.175 seconds (7.75%), with identical
complete artifacts. The pure compiler and its checks are unchanged.

The integration also includes the reviewed implicit Char validation repair,
producer-generated native/trace outputs and focused regression controls. The
generated program and native interpreter/executor comparison pass all 15
assertions. Documentation now describes the actual certified, streamed and Rust
boundaries and partial-output behavior.

## Isolated experiments

| Branch | Status at this checkpoint |
| --- | --- |
| `jcb/ix-certified-v3-ready-scheduler` | Complete checked-report equality and native queue/conflict/refusal/drain controls pass. A full current Init+Std pair reduced main report time from 49.297 to 34.643 seconds and process wall from 82.32 to 68.62 seconds. All 115,942 worker results were reused, with no fallback and identical artifact bytes. The ordinary compiler entry remains unchanged. |
| `jcb/ix-certified-v3-parallel-sharing` | Bounded exact-subset tasks and complete table/stage equality proofs pass with the existing standard axioms. Native direct and corpus controls pass. One sampled Init+Std component selects the parallel route; the Mathlib sample does not. Whole-compiler routing and performance are not established. |
| `jcb/ix-certified-v3-sharing-work` | Scratch reuse passes native controls but gives only 5.1%/2.8% gains on the sampled family stage, so integration is parked. A guarded deferred-materialization draft passes complete result/statistic/key/refusal controls on both sampled corpora; its all-input refinement and compiler routing remain open. |

The scheduler's larger 32,768-entry frontier was correct but slower. A queue
heap-ownership change removed a confirmed alias in generated C and passed
controls, but its full comparison showed no useful wall-time gain. Neither
result is counted as an additional speedup. Coordinator costs are being
measured before further scheduler changes.

The larger sharing opportunity is to retain candidate plans and materialize
only the winning width, as the production Rust route does. The Lean reference
currently constructs and re-expands intermediate and final expressions for all
three widths. The experiment retains the original path when sufficient-budget
and supported-order conditions cannot justify deferring a candidate. It must
preserve lower-width error precedence, every resource refusal, tie rules and
complete compiler output before adoption.

A certificate-path prefetch experiment saved 2.65 seconds in a controller, but
public activation was rejected after a native test showed an escaped child
could keep pipe-reader tasks alive and prevent process exit. Its result is not
part of the integrated performance figure.

## Mathlib characterization

A current-policy run completed all 783,115 inputs with zero failures:

- Full process: 630.020 seconds; main report: 369.915 seconds.
- Output: 2,349,530,307 bytes, SHA256
  `458b779888c8f9627bba58d41a3a2cdf48c38eec32d0a4f36606856782c9374a`.
- Peak RSS: 77,311,912 KiB under a physical 128 GiB limit.

This run incurred 52,714 major faults and substantial input I/O. It is an
initial characterization, not a warm-input acceptance result or a comparable
regression against measurements from an older role configuration.

## Remaining gates

The experimental algorithms are not selected by the production compiler.
They still need complete native call-route and runtime/axiom audits,
appropriate full-workload comparisons and integration checks. The assembled
integration tip still needs the broader three-feature/native/full-test gate,
cross-toolchain aggregation/proving checks, final references and FFT signoff.
Passing focused gates does not imply those outstanding gates passed.

The final performance acceptance requires both complete workloads on the same
gated source/configuration, with repeated fresh-process wall times below
10/60 seconds. Current results remain well above those limits.
