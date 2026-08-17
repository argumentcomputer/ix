# Handoff: Lean v4.33.0 bump — remaining integration work

Status (updated 2026-08-17, WIP push): the branch is rebased onto main
`6e10865` and lean4lean is integrated. The pin now points at the fork's dev
tip `3d1390ae` (`argumentcomputer/lean4lean#4`, merged 2026-08-16, stable
toolchain v4.33.0), which unblocked the test suite and lint gate that §2 of
the previous handoff was queued on. Verified locally on this rev:

- `lake build --wfail -v` — green.
- `lake lint -- --wfail -v` — green across all 19 targets, but ONLY with
  `patches/lean4lean-v4.33-lint-clean.patch` applied to the lean4lean
  checkout (blocker 1 below).
- `lake exe ix codegen --check` — green (both codegen'd kernels up to date).
- `diff lean-toolchain Benchmarks/Compile/lean-toolchain` — green.
- `lake exe ix compile Ix.lean --consts Nat.add_comm` — green (47 consts,
  38.4 kB, matching the expected ~40/40 shape).
- `lake test --wfail -- cli` and
  `lake test --wfail -- aiur-cross aiur-prove aiur-hashes rbtree-map
  multi-stark recursive-verifier` — green.
- Rust side: `cargo fmt --check`, `clippy --workspace --all-targets
  --all-features -D warnings`, `cargo check` (same flags), `cargo deny
  check`, `cargo test --release --workspace -- --include-ignored` — all
  green (675 kernel tests among them).
- `nix flake` evaluates and instantiates (4 drvs to build); full
  `nix build` not yet run.

Fixes that rode along with the rebase (already on this branch):

- Main's #558 introduced a `Lean.RBTree`-backed `MemSizes` in
  `Ix/Aiur/Compiler/Layout.lean`; v4.33 deprecates `Lean.Data.RBTree` and
  the CI build runs `--wfail`. Migrated to `Std.TreeSet` (drop-in;
  `foldl` for `fold`).
- Two lints new since v4.29: `linter.defProp` on the deliberately
  prop-valued `wfTwoEqDef` fixture (`Tests/Ix/Compile/LevelSpellings.lean`,
  silenced locally — the def-ness is the point of the fixture) and a dead
  final `popLocals` rebind in `Ix/AuxGen/BRecOn.lean` (effect kept, binding
  dropped).
- clippy 1.92 `cast_sign_loss` in the `Lean.Int` scalar decode
  (`crates/ffi/src/lean_env.rs`); rewritten with `u64::try_from` /
  `unsigned_abs`, squashed into the original FFI commit.

## Blocker 1: lean4lean warnings fail the `--wfail` lint gate

The new pin compiles, but `Lean4Lean/Inductive/Add.lean` emits 6 warnings
under v4.33 (3 unused simp args, 3 `linter.defProp` prop-valued defs), and
ix's lint driver builds that module (via `Lean4Lean.Environment` ←
`Benchmarks.Lean4Lean` ← Tests), so ci.yml's `build` job fails on them.
There is no ix-side workaround: the import chain is load-bearing and Lake
has no per-dependency warning suppression.

The fix is prepared and verified: `patches/lean4lean-v4.33-lint-clean.patch`
(5 line edits; the three prop defs have zero downstream uses, so
`theorem`-ification is safe). With it applied to the `.lake` checkout, the
full lint gate is green locally.

Steps to clear:
1. Apply the patch to `argumentcomputer/lean4lean` on top of dev
   `3d1390ae` (`git apply patches/lean4lean-v4.33-lint-clean.patch`),
   push (dev or a branch — pushing that repo needs human credentials,
   which is why this is a handoff item).
2. Re-pin `lakefile.lean` to the resulting rev; `lake update lean4lean`.
3. Delete `patches/lean4lean-v4.33-lint-clean.patch` and this blocker
   section.

Until then, ci.yml `build` (and everything `needs: build` — lean-test,
sp1-build, zisk-build) is red on the PR. nix.yml is NOT affected (its lake
builds don't use `--wfail`).

## Blocker 2: ixvm kernel-FFT pin suite (`lake test -- --ignored ixvm`)

This suite is PR-gating (ci.yml lean-test) and is the one local run that
did not complete.

- Name fix already applied: v4.29's
  `String.Slice.Pattern.Model.NoPrefixForwardPatternModel.rec` does not
  exist in the v4.33 runtime env (module-system visibility + rename);
  the entry now points at `...Model.NoPrefixPatternModel.rec`. A runtime
  probe (importModules over Tests.Main's import list) confirms all other
  78 pinned names resolve.
- All 79 FFT-cost pins are v4.29 measurements over v4.29 constant bodies.
  Expect a broad re-pin (previous handoff §2: re-baseline, don't debug).
- The first execution was killed after 38 min: single hot thread, RSS
  grew to ~79 GB with no per-case output yet. Unconfirmed suspect: the
  `_private.Init.Data.SInt.Lemmas.0.Int8.toInt64_ne_minValue._proof_1_2`
  entry (pin 15.5B, ~5× any other) whose v4.33 body may have grown
  pathologically; a v4.33-shaped IxVM lazy-defeq pathology (the class
  #560/#562 fixed for v4.29 shapes) is the other candidate.
  Suggested attack: a small driver over the `public def kernelCheck`
  API running entries one-by-one under `ulimit -v` (~30 GB), harvesting
  per-entry costs; drop or replace entries that blow the cap, re-pin the
  rest, and if a mid-size entry blows up, treat it as a kernel bug lead,
  not a pin chore.
- Observed during the partial run (verify when the suite is green):
  the `r6Host` bad fixture (`Tests/Ix/Kernel/TutorialDefs.lean`) is now
  rejected at `compile_aux_block @ preseed(Const)` with
  "missing constant: r6Host.rec_1" instead of via the positivity walk.
  Expected-reject either way, but confirm the case still passes; if the
  suite asserts the rejection PATH, the fixture may need its aux `rec_1`
  stubbed.

## Remaining verification queue

In dependency order once the blockers clear:
1. Full `lake test --wfail` (no args — the primary suites: ffi, ixon,
   compile/decompile roundtrips, tc-unit...). This is what nix.yml's
   devshell job runs; it covers the previous handoff's watch-points
   (`Tests/FFI/Refcount.lean` borrow counts, `CheckEnv.lean` `Std.Time`
   private-name fixtures, `._f` helpers in the decompile roundtrip,
   `Ix/Tc/Primitive.lean` sizeOf address pins).
2. The extended sweep ignored.yml runs on main:
   `lake test -- --ignored
   --exclude=tc-pins,tc-accel-diff,tc-anon-diff,tc-init,tc-tutorial,tc-roundtrip,lean4lean`
   plus `lake exe Apps.ZKVoting.Prover`. Not PR-gating, but reds main
   post-merge if broken. Budget memory (see blocker 2).
3. `nix build` + `nix flake check` + the devshell `lake build && lake
   test` (the flake evaluates and instantiates already; 4 drvs pending).
4. sp1/zisk host builds + guest execution — CI-only here (toolchains not
   installed locally).

## Kernel-semantics divergences vs upstream v4.33 — OPEN

These are places where ix's checkers (Ix/Tc reference kernel, Rust
`crates/kernel`, IxVM model) knowingly differ from the upstream C++ kernel
after this branch. Each needs a decision or work; none is a known
unsoundness.

- **Theorem delta-unfolding (v4.30 #12973).** Upstream made theorem bodies
  kernel-opaque "in almost all ways"; ix still unfolds `.thm` like `.defn`
  (`Ix/Tc/Whnf.lean:404,421`; IxVM `Ix/IxVM/Kernel/DefEq.lean:1002`,
  `Whnf.lean:486,775`). Sound (theorem bodies are well-typed) but strictly
  more permissive: ix can certify proofs Lean's kernel rejects. Do NOT gate
  blindly — the kernel still unfolds theorems in iota-major position (see
  the comment near `Ix/IxVM/Kernel/Whnf.lean:755` citing
  `Rat.instEncodable._proof_1`), so a blanket gate rejects real mathlib.
  The updated lean4lean is the executable spec for exactly where theorem
  unfolding is allowed: replay a corpus (ix's env, then the
  `Benchmarks/Compile` mathlib/FLT environments) through both checkers,
  diff acceptance, then port lean4lean's exact rule into `Ix/Tc/Whnf.lean`,
  the Rust kernel, and IxVM together, with a regression fixture.

- **IxVM still uses the syntactic universe-zero test.** The Lean and Rust
  kernels were fixed on this branch to classify Prop up to normalization
  (`KUniv.isSemanticZero` / `is_semantic_zero`; see commit `fix(tc):
  classify Prop up to universe normalization`, mirroring
  leanprover/lean4#14613/#14615 — `Sort (imax 1 0)` is `Prop`). The IxVM
  model retains the literal-`Zero` test (`Ix/IxVM/Kernel/DefEq.lean:647-669`
  documents the old three-kernel lockstep, now stale). Until ported, IxVM
  diverges from the other two ix kernels AND from upstream: proof
  irrelevance, struct-eta's Prop guard, and Prop-elimination classification
  can disagree on normalizable-zero universes. Port `isSemanticZero` into
  the IxVM model and its fixtures as a dedicated change, and update the
  lockstep comment.

- **Mutual-block universe uniformity (v4.33 #14608) — deliberately not
  enforced.** Upstream's kernel now requires identical `levelParams` across
  a mutual block (only reachable via metaprogramming, only
  `partial`/`unsafe`). ix checks members compositionally (cross-references
  arity-checked at infer; per-member `lvls` in the `muts` form) and its own
  block clustering may legitimately group members Lean never required to be
  uniform — enforcing uniformity could reject valid content. Consequence:
  ix accepts (metaprogrammed, unsafe) blocks upstream rejects. Revisit only
  if lean4lean-parity replays surface a real case; otherwise this stands as
  a documented, justified divergence.

- **Regression-fixture ports.** ix has no fixtures for the v4.32/v4.33
  soundness-bug shapes. Port upstream's repros as Ix/Tc test fixtures:
  `issue14484.lean` (opaque fvar; ix ingress rejects fvars/mvars at
  `Ix/CompileM.lean:777` — the fixture pins that), `issue_14576_min.lean`
  (nested phantom params; see cleared item below), and a
  `Sort (imax 1 0)` Prop-classification case exercising `isSemanticZero`
  end-to-end (the Rust unit tests cover `univ_eq`; an integration-level
  fixture does not exist yet).

## Kernel-semantics divergences — CONSIDERED AND CLEARED

Verified during this branch's audit; recorded so they are not re-derived.

- **Nested-inductive phantom params (#14577/#14607): not vulnerable.**
  Upstream's bug was checking ctor types only *after* nested elimination
  (dropped `Ds` escaped checking). ix fully infers the declared ctor type
  in its original nested form (`Ix/Tc/Check.lean:441`) before the
  positivity walk (`Ix/Tc/Inductive.lean:585-624`), so the params are
  checked as ordinary subterms; ix's aux expansion is ephemeral and
  compile-side. The exploit's `Expr`-hash/approxDepth collision vector does
  not map to Blake3 content addressing.

- **Universe-arity at delta (v4.30 #12817): already defended.** Both
  kernels check const arity at infer (`Ix/Tc/Infer.lean:63`,
  `crates/kernel/src/infer.rs:99`) and error — never default — on
  out-of-range substitution (`substUniv`, `tc.rs` `subst_univ`). The
  egress-side `getD mkAnon` (`Ix/Tc/EgressLean.lean:63`) is display
  metadata; Lean re-checks anything re-added.

- **`_nested` reserved prefix (v4.33 #14616): no collision.** ix's
  `._nested.` auxiliaries (`Ix/AuxGen/Nested.lean`) are ephemeral — never
  persisted, never re-added to a Lean environment; the commit path
  (`Ix/Commit.lean`) adds commitment-address names. Names are erased
  metadata in anon-mode checking, so no checker-side rejection is needed.

- **`isNeverZero` (`Ix/Tc/Inductive.lean:301`): sound as-is.** Its
  true-cases are genuinely never-zero under any assignment; false just
  falls through to the conservative single-ctor analysis, matching the
  large-eliminator semantics.

- **FFI/ABI across v4.29 → v4.33: no layout regression.** All 17 hardcoded
  constructor layouts in `crates/ffi/src/lean.rs` were audited against
  v4.33 declarations — byte-correct for both the `Ix.*` mirror types and
  the real Lean kernel objects `lean_env.rs` decodes. The one real bug
  found (pre-existing): `Lean.Int` decoded as a ctor when it is a
  `Nat`-representation builtin — fixed on this branch (`fix(ffi): decode
  Lean.Int by value`), with the clippy-clean cast rewrite folded in.

## Non-blocking follow-ups

- **FFI pointer-liveness hardening.** `crates/ffi/src/lean_env.rs:594,615`
  key caches by raw `lean_object*` across a decode session; soundness rests
  on callers keeping arguments alive, and v4.30's RC/borrow changes shift
  free/reuse timing. v4.30 added `Runtime.hold` (#13270) for exactly this —
  wrap the Lean-side callers of the env-decoding externs, or take explicit
  refs in Rust. Related audit caveats: the `LeanIx*` layout types' `alloc`
  path must never be pointed at real Lean types (the phantom trailing
  `hash` object slot coincidentally overlays Lean's computed-field scalar,
  which is safe to read one-below but wrong to allocate), and the
  `assert!(i < num_obj)` bound cannot catch an off-by-one into that slot.

- **Benchmark re-baselining.** Pre-v4.30 numbers are not comparable: the
  LCNF backend rewrite landed end-to-end (~15% smaller binaries), LLVM
  19 → 22, DiscrTree fixes (~10% faster `import Mathlib`), `ByteArray`
  equality is now `memcmp`, default 1GB stacks on all threads. Re-baseline
  `bench.json` / CI benchmarks; do not chase cross-version deltas.

- **Thread-pool interaction.** v4.32 #13123 reclaims idle pool workers
  after 5s; reclaimed-and-respawned workers pick up the stack size current
  at spawn. ix sets it via `rs_lean_set_thread_stack_size`
  (`Ix/Tc/ParCheck.lean:57`) — verify it still runs before the parallel
  check phase, and expect lower RSS with possible thread-churn in bursty
  phases.

- **OpenSSL now linked into the Lean runtime** (v4.32 #12030/#13988): a
  plausible duplicate-symbol/version-skew source on the `net`-featured
  `ix` exe, where iroh brings its own TLS stack. No breakage observed;
  watch link errors on that target.

- **`lake setup-file` JSON parsing.** `Ix/Common.lean:266-274` string-splits
  the JSON and v4.33 #14300 enlarged `setup.json`; the code's own TODO asks
  for a real JSON parse.

- **`Benchmarks/CompileFC`** is deliberately frozen at Lean v4.27.0 on
  upstream `lenianiva/lean4-nix` (its overlay API still works there). Do
  not bump it as part of toolchain updates.
