# GPU trainer variants: built, never run

Five changes to `gpu/cuda/step.cu`, kept as a patch series because none of them has been run:
no output of any variant has been compared with the trainer's, and none has been timed. The
trainer in `gpu/cuda` is unchanged and remains the only one with evidence behind it.

Each patch applies on top of the previous one, from the project directory:

```sh
for p in gpu/variants/[1-6]-*.patch; do patch -p1 < "$p"; done
```

| Patch | Change | Expected result |
|---|---|---|
| `1-v1` | `split_kernel` measures the magnitude while it reads the operands (one `atomicMax` per block), so the separate magnitude pass runs only on the first step or after an operand did not fit. `gemm` returns early on an empty dimension. | identical output (a maximum over the same values); 30 to 60 µs off a 1024⁴ step; nothing at the deployed shape |
| `2-v2` | `transpose_kernel` becomes a 32×32 tiled transpose through shared memory. | identical output; transposes several times faster at 1024²; nothing at the deployed shape |
| `3-v3a` | All of a context's work runs on its own stream. A batch of at most 256 KiB goes up as one pinned copy and the status comes back through pinned memory, so a step blocks once instead of four times. Null host buffers are refused explicitly. | identical output; a few to 10 µs off the deployed shape's 66.7 µs |
| `4-v3b` | A staged step whose key matches the previous step's is captured once as a CUDA graph and replayed; the capture is abandoned if the step would wait for magnitudes or grow the limb planes. | identical output; the deployed shape toward its 20 to 30 µs of kernel time if launch gaps dominate. Keep only if it clearly beats `3-v3a` |
| `5-v4` | `limb_gemm` loads the next 64-wide stage into registers before the current stage's multiply-accumulates. | identical output; a small gain at most. Drop unless a per-kernel trace shows the product is load-bound |
| `6-error-test` | Extends `gpu/cuda/error_test.cu`: replayed steps give equal keys, a failing step between replays is reported and the next step reproduces the keys, and shapes with an empty dimension step without error. | needed by `3-v3a` and `4-v3b` |

The expectations are readings of where the time goes, not measurements.

## Baseline, measured 2026-11-19 on the trainer in `gpu/cuda`

| Shape | Wall per step | Device span | |
|---|---|---|---|
| deployed (8×16×11, batch 20) | 66.7 µs | 45.5 µs | 22.8 µs blocked in 4 synchronising calls |
| 1024⁴, default path | 1,504 µs | 419.5 µs | 1,403 µs blocked |
| 1024⁴, CUDA cores | 7,759 µs | 6,689 µs | |

The deployed run of 600 steps takes 40.0 ms, 56.0 ms with the key and model downloads. There is
no per-kernel breakdown: `ncu` needs administrator counters on the machine, and the harness's
CUPTI trace mode has not run.

## What a run must show before a variant replaces the trainer

`harness/run.sh VARIANT`, once per variant and once for the unchanged trainer, in one session:

1. `error_test` passes.
2. The digest of every step of the deployed run equals the trainer's (`cf871b4e7bc716ca`), and
   the shape digests equal the trainer's on every path.
3. The 40-shape sweep agrees across the three paths and across limb-count changes.
4. The Lean trainer's weights for the five triage configurations equal the specification's.
5. Timings at the deployed shape, 1024⁴, 2048⁴ and 256×512×128 with batch 300, and the
   per-kernel trace, beside the trainer's.

Then `harness/final.sh` on the chosen variant: `gpu/test.sh` and `gpu/error-test.sh`.

`harness/` holds the timing and equality harness (`bench2.cu`) and its scripts as they were
written. The scripts name a scratch layout (`/opt/dlami/nvme/ix-ai/review2-gpu`) that holds one
directory of sources per variant and a problem file for the deployed run; set those paths up
again from the patches before running them.
