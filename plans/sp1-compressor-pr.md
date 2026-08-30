<!--
PR description for jcb/sp1-compressor → jcb/aggregate-first
(https://github.com/argumentcomputer/ix/compare/jcb/aggregate-first...jcb/sp1-compressor)

This is a stacked PR. Its base is plans/aggregate-first-pipeline-pr.md; review
this PR as the terminal-compression delta only. Everything between the
BEGIN/END markers is the paste-ready PR body. Author notes after the body are
not intended for the PR.
-->

<!-- BEGIN PR BODY -->

# SP1 terminal compression for aggregate-first roots

## Stack

This PR is stacked on `jcb/aggregate-first` and should target that branch:

```text
main
  └── jcb/aggregate-first
        └── jcb/sp1-compressor  ← this PR
```

The base PR supplies the complete shard-to-root pipeline and persists one
uniform 18-word `ix_aggr` outer claim. This PR adds only the terminal
compression layer: it verifies that one Aiur Multi-STARK root inside SP1 and
uses SP1's stock recursion tail to produce a final Groth16 or Plonk SNARK.

Reviewers do not need to re-review shard planning, structural joins, cache
resume, or the converged `ix_aggr` circuit in this PR. Conversely, this PR
does not re-run the Lean kernel inside SP1 and does not feed individual shard
proofs to SP1.

## Summary

```text
IxVM shard proofs
    |
    |  jcb/aggregate-first
    v
one persisted ix_aggr root
  - Aiur recursion verifying key
  - exact 18-word outer claim
  - compact Multi-STARK proof
    |
    |  native fail-fast verification
    v
SP1 guest verifies the same key / claim / proof
    |
    |  SP1 core → compressed → shrink → wrap
    v
Groth16 or Plonk proof + fixed 224-byte public statement
```

The connector has three deliberately separate responsibilities:

1. The Lean CLI reconstructs the aggregate backend and exact outer claim from
   a persisted `Ixon.Proof`, rejecting anything that is not an eligible
   `CheckEnv` root.
2. The Rust host verifies the Aiur proof before paying SP1 setup/proving cost,
   invokes the requested SP1 stage, verifies the resulting SP1 proof, and
   independently checks its public values.
3. The SP1 guest decodes and verifies the same Aiur proof. This repeated guest
   verification is the check attested by the terminal proof; the host
   preflight is only an early error and cost guard.

## Fixed public statement

The guest commits exactly 224 bytes:

```text
"IXROOT01" || blake3(aiur_recursion_vk) || fri_parameters || outer_claim
```

| Field | Bytes | Meaning |
|---|---:|---|
| Domain | 8 | Literal `IXROOT01` protocol separator |
| Aiur VK digest | 32 | Blake3 of the exact serialized recursion verifying key |
| FRI parameters | 40 | Five little-endian `u64` values |
| Outer claim | 144 | Exactly 18 canonical little-endian Goldilocks words |
| **Total** | **224** | Fixed-width terminal statement |

The compact Multi-STARK proof is private witness data. Proof validity is
existentially attested for the exact verifying key, FRI parameters, and outer
claim bound into the public statement. Omitting the proof bytes from public
values avoids exposing or hashing a large, revision-sensitive encoding while
still pinning the statement it proves.

Both host and guest enforce:

- exactly five FRI words and exactly 18 claim words;
- canonical Goldilocks encodings for every claim element;
- strict Aiur verifying-key and proof decoding;
- equality between the supplied FRI parameters and those encoded by the
  verifying key; and
- native Multi-STARK verification of the proof against that exact claim.

## Integrated command

`ix compress-root ROOT_ADDRESS` reads one persisted aggregate wrapper from
the Ix store, rebuilds the current recursion backend and allowed-system blob,
derives the uniform outer claim from the wrapper's `CheckEnv`, and passes the
result to the SP1 connector.

```console
# Build the CLI with the optional connector.
nix develop .#sp1 --command env IX_SP1=1 lake build ix

# Execute the guest without producing a proof.
nix develop .#sp1 --command env IX_SP1=1 \
  lake exe ix compress-root ROOT_ADDRESS --mode execute

# Produce and retain both the SDK proof container and raw onchain encoding.
nix develop .#sp1 --command env IX_SP1_CUDA=1 \
  WITHOUT_VK_VERIFICATION=1 SP1_PROVER=cuda \
  lake exe ix compress-root ROOT_ADDRESS --mode groth16 \
    --output root.sp1 --onchain-output root.groth16
```

Supported modes are `execute`, `core`, `compressed`, `groth16`, and `plonk`;
the CLI defaults to `groth16`. `--output` saves the verified SP1 SDK proof
container. For Groth16 or Plonk, `--onchain-output` additionally saves the raw
proof bytes expected by an onchain verifier.

Final compression is intentionally a closure boundary:

- proof-producing modes accept only a closed `CheckEnv` root;
- a non-`CheckEnv` wrapper is rejected;
- a root retaining assumptions is rejected; and
- `--allow-open-root` exists only for `--mode execute`, allowing profiling on
  a retained-subtree fixture without permitting a misleading terminal proof.

## Build and dependency isolation

SP1 remains opt-in so ordinary Ix builds do not compile or link the SDK:

- default builds retain a linkable feature-disabled FFI stub;
- `IX_SP1=1` enables the CPU connector;
- `IX_SP1_CUDA=1` enables it with the SDK's CUDA support;
- `sp1-compress` is a separate host workspace using the Succinct toolchain;
  and
- `sp1-compress/guest` is a separate zkVM guest workspace with its own locked
  dependency graph.

The root, host, and guest dependency graphs are synchronized at the protocol
boundary:

- `multi-stark` is pinned to
  `2892243e674f9a0b3aca9004a8d00c79a23beec1` everywhere;
- the SP1 crates are pinned to the Blake3-capable fork at
  `261741a90e6e5e637a4dae7c00a501d63b90349c`; and
- the guest's SP1-aware Blake3 is pinned to
  `d36366f7badbff9be8e2522868dddd14561638f3`.

Aiur proof and verifying-key wire formats are revision-sensitive. These pins,
the host/guest codecs, and all three lockfiles must move together.

## What lands

Guest and protocol boundary:

- An SP1 zkVM guest that reads the serialized Aiur verifying key, five FRI
  parameters, the exact 18-word outer claim, and one compact proof.
- In-guest Aiur proof verification followed by a domain-separated,
  fixed-width public-value commit.
- A standalone public Aiur verifying-key decoder/API usable from both native
  Rust and the zkVM guest.
- Canonical field encoding and exact-length checks at both sides of the guest
  boundary.

Host connector:

- Native proof verification before SP1 setup/proving.
- `execute`, `core`, `compressed`, `groth16`, and `plonk` execution paths.
- Verification of every produced SP1 proof through the SDK.
- Independent reconstruction and byte-for-byte comparison of public values.
- Optional persistence of the SDK artifact and, for final SNARK modes, the
  raw onchain proof encoding.
- A synthetic execute smoke that covers Aiur key/proof serialization, guest
  execution, proof verification, and public-value agreement without needing
  a large production aggregate fixture.

Ix integration:

- `ix compress-root` with persisted-root loading, deterministic backend
  reconstruction, claim derivation, mode selection, and output flags.
- Strict closed-root policy at the command boundary, including tests for all
  open-root and wrong-claim cases.
- Feature-gated Rust FFI wiring and Lake/Nix build controls that leave normal
  builds unchanged.
- Small public helpers in the Aiur synthesis and key-codec layers needed to
  verify a serialized proof outside the original in-process prover path.

## Trust and safety properties

- The native preflight is not trusted for soundness; the SP1 guest repeats the
  full Aiur verification and only then commits public values.
- The host verifies the resulting SP1 proof and independently reconstructs
  the expected 224 bytes, preventing accidental acceptance of a proof for a
  differently encoded statement.
- The verifying-key digest and matching FRI values bind the exact Aiur
  recursion verifier configuration.
- The full 18-word outer claim binds the aggregate protocol identity and
  closed `CheckEnv` statement established by the base PR.
- Domain separation prevents this public-value layout from being confused
  with another SP1 program or future statement format.
- Non-canonical claim words, malformed encodings, mismatched FRI parameters,
  invalid proofs, open roots, and non-`CheckEnv` wrappers fail closed.

## Current limitation

`WITHOUT_VK_VERIFICATION=1` is currently required for proof generation. The
SP1 fork used here adds Blake3 recursion shapes that are not yet represented
in its distributed recursion-verifying-key map. Execute mode does not require
the setting.

This escape hatch affects SP1's artifact-generation key-map check; it does
not bypass Aiur verification in either the native host or the SP1 guest, and
the host still verifies the final SP1 proof and its public values. It should
nonetheless be removed before treating the path as production-ready.

A real persisted production `ix_aggr` root has not yet been executed through
the terminal, and GPU Groth16/Plonk generation has not yet been benchmarked.
The synthetic smoke below validates connector correctness and wire
compatibility only; it is not a cost estimate for the much larger production
recursion key and proof.

## Validation

The rebased stack passes:

- Normal root Rust build:
  `cargo check --release --locked --workspace --all-targets` with the
  production `parallel,net,test-ffi` features.
- Strict root Rust lint:
  `cargo clippy --release --locked --workspace --all-targets` with those same
  features and `-D warnings`.
- Real SP1 host/guest build:
  `cargo check --release --locked --manifest-path sp1-compress/Cargo.toml
  --workspace --all-targets`; this invokes the Succinct guest compiler rather
  than a stub guest.
- Strict SP1 host lint with guest build intentionally skipped under Clippy:
  `SP1_SKIP_PROGRAM_BUILD=1 cargo clippy --release --locked --manifest-path
  sp1-compress/Cargo.toml --workspace --all-targets -- -D warnings`.
- SP1 host unit tests: 3/3 passed, covering the closed mode parser, fixed and
  domain-separated public values, and strict claim shape/canonical encoding.
- Integrated feature build: `IX_SP1=1 lake build ix`.
- Aggregate semantic/closure coverage: `lake exe IxTests ix-aggr`, 99/99
  passed, including six terminal-compression policy cases.
- Full Lean/CLI build: `lake build IxTests ix` (1,093 jobs).
- Generated Aiur artifacts are fresh: `lake exe ix codegen --check`, including
  the 2,061,361-byte / 248-function converged `ix_aggr` executor.
- Root, SP1 host, and SP1 guest `cargo fmt --check` passes.

The end-to-end synthetic guest smoke also passed after rebasing to the current
Multi-STARK revision:

```text
native Aiur proof: 28,327 bytes
native Aiur vk:       707 bytes
SP1 execute: accepted
instructions:     4,272,596
gas:              3,987,232
blake3_compress:         891 syscalls
```

## Review guide

The most useful review order is:

1. `sp1-compress/guest/src/main.rs`: the attested verification and public
   statement.
2. `sp1-compress/host/src/lib.rs`: preflight, SP1 modes, result verification,
   and artifact handling.
3. `crates/aiur/src/vk_codec.rs` and `crates/aiur/src/synthesis.rs`: the
   serialized Aiur verification surface shared with the guest.
4. `Ix/Cli/CompressRootCmd.lean`: aggregate-root reconstruction and closure
   enforcement.
5. `crates/ffi`, `lakefile.lean`, and `flake.nix`: optional feature and build
   isolation.
6. The three Cargo manifests/lockfiles: synchronized protocol revisions.

## Out of scope

- Shard proving and stage-2 aggregate construction; those are in the base PR.
- Re-executing the Lean kernel inside SP1.
- Selecting final production FRI parameters.
- Large-box GPU performance and memory measurements.
- Removing the SP1 recursion-vk-map workaround.
- Solidity verifier generation, deployment, or onchain integration.

<!-- END PR BODY -->

## Author notes

- Open this PR with base branch `jcb/aggregate-first`, not `main`.
- Once the base PR merges, retarget this PR to `main`; GitHub should then show
  only this terminal-compression commit.
- Before production sign-off, run one closed persisted `ix_aggr` root through
  execute mode and a GPU final-SNARK mode, record time/RAM/artifact sizes, and
  resolve the distributed recursion-vk-map limitation.
