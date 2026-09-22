# GPU-proven roots through the SP1 terminal to Plonk

**Result (2026-09-18):** the FLT aggregate root proven on four GPUs as a
batch of trace shards (`../flt-lanes4-2026-09-18`, 5.75 MiB) is a 964-byte
Plonk proof, produced on a 64-core CPU box in 37 min 19 s by upstream SP1
v6.6.0 with its stock recursion key map and Succinct's published Plonk
circuit, and re-verified by SP1's pure-Rust verifier against the published
Plonk verifying key; the Mathlib root (`../mathlib-lanes4-metrics-2026-09-17`)
likewise in 38 min 47 s. Nothing custom is trusted: no fork, no key-map
bypass, no locally built circuit. The guest is the batch verifier the sharding design's step 5 left
open (`docs/aiur-trace-sharding.md` §11).

## Plonk

| Root | Store address | Cycles | Core→Plonk wall | Peak RSS | Onchain proof | SDK container |
|---|---|---:|---:|---:|---:|---:|
| FLT, 572 shards | `7d44c48e…dc0` | 690,987,002 | 37 min 19 s | 108 GB | 964 B | 4,293 B |
| Mathlib, 78 shards | `026c8d38…c3d` | 692,240,636 | 38 min 47 s | 106 GB | 964 B | 4,293 B |

## Groth16

| Root | Core→Groth16 wall | Peak RSS | Onchain proof | SDK container |
|---|---:|---:|---:|---:|
| FLT, 572 shards | 35 min 38 s | 108 GB | 356 B | 1,917 B |

Same path with `--mode groth16` and Succinct's published Groth16 circuit
(`proofs/flt-root-7d44c48e.groth16{,.sp1}`, `logs/flt-groth16.log`); the
gnark step is under a minute against 2.4 min for Plonk. Its setup is
circuit-specific (see below), which is why Plonk is the default.

Guest program key hash (what a verifier pins):
`0x001d846fdfa783032fb347ccda1a1e10da908d581d0d1556fd47e93dfba5a187`.
The proofs are in `proofs/`: `<root>.sp1` is the SDK container (proof plus
public values), `<root>.plonk` the raw onchain encoding, `<root>.public` the
224 public-value bytes that must accompany it. `proofs/` files verify with

```console
cargo run --release --manifest-path sp1-compress/Cargo.toml --example verify_terminal -- proofs/flt-root-7d44c48e.sp1
```

which uses `sp1-verifier` and its bundled Plonk or Groth16 key, not the SDK
prover.

### The statement

The Plonk proof's five public inputs are the guest key hash, the SHA-256
digest of the guest's public values, the exit code, SP1's recursion key-map
root and a nonce. The public values are 224 bytes, fixed for every
environment:

```text
"IXROOT01" || blake3(recursion vk) || 5 × u64 FRI parameters || 18 × u64 outer claim
```

For the FLT root: recursion vk `29319a45e19bc36494f05cb5701ae1673357fe76da6b3589e23e8bf001488dc2`,
FRI `(log_final_poly_len 0, max_log_arity 1, num_queries 100, commit_pow 0,
query_pow 20)`, and the claim `[0, 293, d₀…d₇, c₀…c₇]`: the function channel,
the `ix_aggr` function index, the packed Blake3 digest of the allowed-systems
identity blob and the packed Blake3 digest of the serialized closed
`CheckEnv` claim (`Aggr.pubInput`). The batch proof itself is private
witness; the guest commits only after `AiurVerifyingKey::verify` accepts it
for exactly this claim, and the host refuses the SP1 proof unless its public
values equal an independent reconstruction.

## Execute mode

| Guest | Root | Total cycles | decode-vk | decode-proof | verify-root | blake3 syscalls | Wall |
|---|---|---:|---:|---:|---:|---:|---:|
| Fork, Blake3 precompile | FLT | 580,142,190 | 7,631,218 | 89,266,181 | 476,003,531 | 91,299 | 32.8 s |
| Fork, Blake3 precompile | Mathlib | 580,741,457 | 7,631,218 | 89,295,941 | 476,573,038 | 91,838 | 33.4 s |
| Upstream v6.6.0, software Blake3 | FLT | 690,987,002 | 7,631,218 | 89,266,181 | 582,256,995 | 0 | 37.3 s |
| Upstream v6.6.0, software Blake3 | Mathlib | 692,240,636 | 7,631,218 | 89,295,941 | 583,480,869 | 0 | 190 s (box busy proving) |

The two roots are within 0.1% of each other: the root is one `ix_aggr`
proof of fixed shape whatever environment it closes. Software Blake3 costs
about 1,200 cycles per compression, 19% of the total, and buys the stock key
map and circuits. Verification is 82% of the cycles, dominated by Merkle
authentication of opened rows and FRI folding; decoding the 5.75 MiB batch
is 15 cycles per byte.

## What was tried and why it is not the path

- **The Blake3-precompile fork** (`argumentcomputer/sp1` at `7a1cefe5`)
  needs `WITHOUT_VK_VERIFICATION=1`, which substitutes a dummy key tree that
  accepts any key: not sound. Regenerating its key map is a full rebuild,
  not an increment: adding the chip changes every recursion program
  (upstream's builder reproduces 33/33 of its own keys for the first shape
  of each cluster, the fork 0/33), so all 191,670 shapes (33 clusters ×
  5,808 sizes + 6) must be built. Measured 0.93 s per shape at 24 prover
  workers, CPU-bound at ~62 cores, 74 GB peak: about 50 hours on this box.
  Stopped after the first batch.
- **Groth16** works over stock SP1 exactly like Plonk (table above) but
  rests on a circuit-specific setup:
  Succinct's 18-contributor ceremony (Etherealize, Polygon, OP Labs, Alpen
  Labs, Offchain Labs, Coinbase, Across, Succinct; Semaphore tooling), whose
  security depends on every participant discarding their toxic waste, and
  whose docs steer users uncomfortable with that to Plonk. A locally built
  Groth16 circuit has a dummy setup. Plonk's setup is the universal Ignition
  SRS, so the published circuit is trustworthy and a locally built one can
  be too if built against Ignition (gnark picks Ignition iff the container
  path is `/circuit`, not `/circuit_dev`; a 27.6 M-constraint build took
  22.7 min). Succinct's docs do not say whether the v6.1.0 circuit reused
  the ceremony; confirm before relying on Groth16.
- **SP1's Docker gnark backend rejects every Plonk proof it makes**
  (`sp1-docker-plonk-verify-bug.md`): its Plonk verify wrapper forwards
  `proof_nonce` and `vk_root` swapped. The host links gnark natively
  instead (`sp1-sdk/native-gnark`, Go 1.26 + libclang), which also removes
  the Docker dependency.

## Inputs, build and commands

| Item | Value |
|---|---|
| Roots | copied from `../*/proofs/root-<addr>.proof` into `~/.ix/store/<2>/<2>/<2>/<58>`; the file bytes are the store entry (blake3 = address) |
| ix | this branch: `sb/aiur-trace-sharding-gpu` at `13feef0f` + `jcb/sp1-compressor` at `52d5bb2a`, then upstream SP1; multi-stark `59df87a4` everywhere, the 2026-09-03 Mathlib guest at `2892243e` |
| SP1 | upstream `v6.6.0` (circuit artifacts `v6.1.0`, key map `24cd2961…`, wrap key `fce92406…`, unchanged through v6.8.0 and `main`), Succinct toolchain of v6.6.0 (`sp1up --version v6.6.0`; v6.8's fails the guest link on `__atomic_*`) |
| Host | 64 CPUs, 495 GiB, no GPU; `protoc` 3.21, Go 1.26, libclang 21 |
| Build | `IX_SP1=1 lake build ix` with `~/.sp1/bin` on `PATH` |
| Execute | `IX_SP1=1 lake exe ix compress-root <addr> --mode execute` |
| Plonk | `IX_SP1=1 SP1_PROVER=cpu lake exe ix compress-root <addr> --mode plonk --output <addr>.sp1 --onchain-output <addr>.plonk` |

On a GPU box (`IX_SP1_CUDA=1`, `SP1_PROVER=cuda`) the SP1 stages should take
minutes; the gnark Plonk prove is CPU-bound either way (about 2.4 min here).

Files: `logs/*-execute.log` (CLI output with the executor's cycle, opcode
and syscall report), `logs/flt-plonk.log`, `logs/mathlib-plonk.log`,
`logs/flt-groth16.log`, `logs/flt-groth16-stock-circuit.log` (the fork's
proof against the stock Groth16 circuit, unsatisfied constraint), `proofs/`,
`sp1-docker-plonk-verify-bug.md`.
