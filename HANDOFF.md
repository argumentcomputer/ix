# Handoff: Lean v4.33.0 bump — remaining integration work

Status of this branch (`update/lean-v4.33.0`): ix is adapted to Lean v4.33.0
and verified as far as is possible without lean4lean. `lake build Ix` is
green, `cargo check --workspace` is clean, the Rust kernel's 674 tests pass,
and every ix-side test target compiles. The one dependency blocker is the
`lean4lean` pin (v4.31-era, does not compile under v4.33); the test suite and
lint gate execute lean4lean-linked binaries and are queued behind it.

This file records everything still open from the v4.29 → v4.33 release-notes
audit: the lean4lean integration steps, kernel-semantics divergences between
ix's checkers and the upstream Lean kernel (open and cleared), and
non-blocking follow-ups. Ingest fully before starting integration.

## 1. lean4lean: why the bump matters

The pinned lean4lean (`5e5bb767`, in `lakefile.lean`) reproduces the kernel
soundness bug fixed upstream in Lean v4.32.1 (leanprover/lean4#14498): its
`addOpaque` (`Lean4Lean/Environment.lean:64-72` at the pinned rev) never
calls `checkNoMVarNoFVar` on the opaque's *value*, so it accepts the
axiom-free `False` construction from leanprover/lean4#14484. Reachable from
ix via `Benchmarks/Lean4Lean.lean:209` (`.opaqueInfo → addDeclAt`).

Upstream `digama0/lean4lean` master has the complete v4.32/v4.33 hardening:
`779c51fde` (the #14498 value check + `Tests/DeclFVar.lean`), `d7e70a5f0`
(nested-inductive phantom params, #14577), `5518bf838` (mutual `levelParams`
uniformity #14608, reserved `_nested` prefix #14616, `checkNoMVarNoFVar` on
inductive/ctor types #14607, + `Tests/KernelHardening.lean`), and the
verified level-normalization algorithm enabled in the typechecker.

The fork update is being done as `argumentcomputer/lean4lean` PR #4
(`jcb/formalization2`) — formalization on top of latest upstream. Do not
integrate an intermediate state; wait for it to land on the fork's dev.

## 2. Integration steps once lean4lean lands

1. **Bump the pin.** In `lakefile.lean`, set the `lean4lean` rev to the new
   dev tip; `lake update lean4lean`. Confirm its `lean-toolchain` is stable
   `leanprover/lean4:v4.33.0` (upstream tracks rc toolchains).

2. **Run the suite**: `lake test`. First actual execution on v4.33.
   Watch-points from the audit:
   - `Tests/FFI/Refcount.lean` — v4.30's borrow-inference overhaul
     (leanprover/lean4#12830, #13136 RC coalescing) may shift caller-side
     inc/dec counts. Diagnose with `trace.Compiler.inferBorrow` before
     adjusting expectations.
   - `Tests/Ix/Kernel/CheckEnv.lean:191-192` pins private `Std.Time` names
     (`Std.Time.PlainTime.format._sparseCasesOn_1`); `Std.Time` was
     refactored in v4.32 and the fixtures may not resolve.
   - Decompile roundtrip — v4.30 #12987 introduced `foo._f` helper
     constants for structural recursion. `classifyAuxGen`
     (`Ix/CallSiteSurgery.lean`) deliberately routes unknown suffixes to the
     plain-definition path and ix's own v4.33 oleans contain no `._f`, but
     dependency environments may carry them; the roundtrip suite confirms.
   - `Ix/Tc/Primitive.lean:221-222` hard-codes canonical addresses for
     `PUnit._sizeOf_1` and `SizeOf.sizeOf`; v4.31 #13320 un-exposed
     auto-generated `sizeOf` definitions, which can invalidate those hashes.
   - Expect broad content-address churn vs v4.29-era artifacts and
     re-baseline rather than debug: derived Prop instances flipped
     `def`→`theorem` (v4.31 #13304), imported `partial` defs regain their
     marking across module boundaries (v4.33 #14609), `Float`/`Float32`
     were redefined around `Float.Model`, derived `BEq`/`Inhabited` bodies
     changed, and several core decls changed exposure/reducibility. All
     `.ixe` fixtures and pinned address tables from v4.29 will differ.

3. **Run the lint gate**: `lake lint -- --wfail -v`. Not yet run on v4.33;
   v4.31 enabled `linter.redundantVisibility` (ix: ~174 files with `public
   section` + explicit `public`, ~800 `private` decls),
   `linter.redundantExpose` (`Ix/Lib.lean:11`), and
   `warning.simp.varHead`/`otherHead` (~257 `@[simp]`s). Escape hatch:
   `leanOptions := #[⟨`linter.redundantVisibility, false⟩]`; prefer fixing
   genuinely redundant modifiers.

4. **Limits, only if they fire.** v4.31 #13030 made heartbeats accumulate
   faster (upstream raised limits 20–50% in places); v4.33 #13956 bounded
   kernel recursion by `maxRecDepth` instead of the physical stack. If
   `IxTcVerify` or deep replays hit deterministic timeouts or
   `(kernel) deep recursion`, raise the seven
   `set_option maxHeartbeats 800000` sites under `Ix/Tc/Verify/` and add
   `maxRecDepth` options before chasing phantom regressions.

## 3. Kernel-semantics divergences vs upstream v4.33 — OPEN

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

## 4. Kernel-semantics divergences — CONSIDERED AND CLEARED

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
  Lean.Int by value`). `lean-ffi` needs no changes (bindings regenerate per
  build; none of the removed/changed `lean.h` symbols are used).

## 5. Non-blocking follow-ups

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
