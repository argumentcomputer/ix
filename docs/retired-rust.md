# Retired Rust implementations

PR #677 removed three Rust implementations, with their FFI glue and the CLI
paths that used them: the compiler (`crates/compile`), the kernel
(`crates/kernel`) and the port of the sharing construction
(`crates/ixon/src/sharing_exact`). None was certified: no theorem covered
them, and neither the certified compiler (`Ix.Cert.compileReport`) nor the
certified checker (IxC, [kernel](kernel.md)) called them. Lean is now the
only implementation of each.

The code is kept on the branch `jcb/archive-rust-compiler-kernel`, at commit
[`c6dc6d6c38dc`](https://github.com/argumentcomputer/ix/tree/c6dc6d6c38dce2f552a37c1884a25b3855fe3934).
Every link below is pinned to that commit. Comments that still name a Rust
function ("mirrors Rust `compile_mutual`") in `Ix/CompileM.lean`,
`Ix/CompileDriver.lean`, `Ix/Ground.lean`, `Ix/IndFlags.lean`,
`Ix/DecompileM.lean` or `Ix/IxVM/` refer to these crates at that commit.

## Compiler: `crates/compile`

It compiled a Lean environment to Ixon: reference graph, groundedness,
condensation into mutual blocks, inductive-flag validation, then each block
with the canonical sharing construction, on a work-stealing scheduler that
streamed the `.ixe` to disk. The crate also held the Rust decompiler and the
kernel's egress to Lean declarations.

- **Relation to Lean.** A pure-Lean compiler existed first; the Rust compiler
  became the fast production path, and the current Lean driver was then
  ported back from it. At the archive commit, `Ix/CompileDriver.lean` opens
  with "Port of the production scheduler semantics of
  `crates/compile/src/compile/env.rs` … and the per-block dispatch of
  `compile_const`", replacing work-stealing threads with a deterministic fold
  over waves.
- **Trust.** Opt-in (`ix compile --rust`) and outside `CompileCorrect`: it ran
  none of the compile report's checks. It was held to the Lean compiler only
  by byte equality (suites `compile`, `cert-compile-parity-initstd`,
  `initstd-reference` through `compile-lean --rust-check`, and the merge-queue
  `--ignored compile` over the test environment).
- **Performance reference.** It remains the speed to aim at. In the
  historical runs of [BENCHMARKS.md](../BENCHMARKS.md) ("Compilation", an
  older pipeline), it compiled, serialized and wrote Mathlib in 63.6 s, where
  the Lean compile phase took 723.0 s; Init+Std took 4.70 s against 39.9 s.
  At the sharing cutover the Lean compile phase took 556.658 s on Mathlib's
  783,115 declarations ([sharing-minimum §14.4](sharing-minimum.md#144-evidence-and-release-gates)).
- **Code.**
  [`compile.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/compile/src/compile.rs),
  [`compile/env.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/compile/src/compile/env.rs)
  (scheduler), [`graph.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/compile/src/graph.rs),
  [`ground.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/compile/src/ground.rs),
  [`decompile.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/compile/src/decompile.rs),
  the FFI [`crates/ffi/src/compile.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ffi/src/compile.rs).

## Kernel: `crates/kernel`

An out-of-circuit type checker over Ixon (`ix check-rs`), following lean4lean:
inductive validation and recursor generation, WHNF, definitional equality and
inference, plus claim builders, role admission and the shard partitioner (the
partitioner moved to `crates/ixon/src/shard.rs`).

- **Trust.** Uncertified, and never a fallback for the certified entry.
  IxC is a separate design, derived from con-leche's verified checker, not a
  port of this kernel. Its tests compared verdicts: the tutorial and
  check-env suites, and on Init+Std the `initstd-reference` fixture, where it
  passed 99,427 of 99,432 constants (the five others are the
  native-evaluation constants the certified checker declines or blocks).
- **Provenance only.** The IxVM circuit kernel was first written after this
  kernel. Its correctness rests on the certified Lean, not on this kernel.
- **Code.** [`crates/kernel/src`](https://github.com/argumentcomputer/ix/tree/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/kernel/src),
  the FFI [`crates/ffi/src/kernel.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ffi/src/kernel.rs).

## Sharing port: `crates/ixon/src/sharing_exact`

The Rust compiler's copy of the canonical sharing construction
([Ixon, "Sharing System"](Ixon.md#sharing-system)).

- **Relation to Lean.** A port of `Ix.Sharing.Exact`, written after it:
  `tiered.rs` calls itself "a rule-for-rule port of the Lean
  `Ix/Sharing/Exact/Tiered.lean`". Lean is the proved reference; the port was
  unproved.
- **Testing.** The Lean/Rust suite `exact-sharing-ffi` compared bytes on
  fixtures, generated inputs and the compiler route, and over whole `.ixe`
  corpora; Init, Init+Std, Mathlib and the merge-queue environment compiled
  identically ([sharing-minimum §12.10, §14.4](sharing-minimum.md)). Two test
  pieces existed only in Rust: the MSS reference encoding (`mss.rs`) and the
  limit-grammar list `LIMIT_SPEC_PARITY`, which Lean keeps as
  `limitSpecParity`.
- **Speed.** On one captured input the port took 25.50 s where Lean took
  331.00 s, before Lean's area evaluator brought that to 133.245 s
  ([sharing-minimum §14.4](sharing-minimum.md#144-evidence-and-release-gates)).
- **Code.**
  [`sharing_exact.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/sharing_exact.rs),
  [`tiered.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/sharing_exact/tiered.rs)
  (its "Checks" section lists the port's run-time checks),
  [`uniform.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/sharing_exact/uniform.rs),
  [`mss.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/sharing_exact/mss.rs),
  [`tests.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/sharing_exact/tests.rs),
  the parity suite [`Tests/Ix/SharingExactFFI.lean`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/Tests/Ix/SharingExactFFI.lean).

The same PR also removed the Rust resource validator
([`crates/ixon/src/resource.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/resource.rs);
Lean's is `Ix/Resource/Validate.lean`) and the Rust copy of `Ixon.canonUniv`
([`crates/ixon/src/canon_univ.rs`](https://github.com/argumentcomputer/ix/blob/c6dc6d6c38dce2f552a37c1884a25b3855fe3934/crates/ixon/src/canon_univ.rs)).
