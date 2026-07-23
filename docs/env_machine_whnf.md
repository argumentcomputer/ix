# Design: environment-machine WHNF for the Rust kernel

Port of the IxVM environment machine (`~/ix-aiur` commits `d0d3375`
Phase A, `b4c4ea3` Phase B; `Ix/IxVM/Kernel/Whnf.lean:209-460`,
`Subst.lean:352-400`) to `crates/kernel/src/whnf.rs`. Status:
IMPLEMENTED — Phase A in `7825e0b` (machine loop in `whnf.rs`,
`Clo`/`MEnv`/`clo_subst` in `subst.rs`), Phase B closure-iota in
`acd0780` (`try_iota_clo`); guest cycle benchmarks pending. One
deviation from §7: machine-native delta (the IxVM Phase C1.5 win)
does not port at this layer — our machine lives inside `whnf_core`,
which must stay delta-free for def-eq's lazy-delta unfold ordering,
whereas the IxVM machine sits in a whnf that includes delta. Spanning
`whnf`'s delta loop with closures is a separate, larger design.

## 1. Problem and evidence

Eager substitution is the dominant residual cost on reduction-heavy
shards. Every beta materializes the substituted body via
`simul_subst` (a full walk + intern of every reachable subterm), and
every iota substitutes a whole recursor rule — including subterms the
reduction then discards (unselected `Decidable`/match branches,
unused minor premises, arguments dropped by projections).

Current guest profiles (`/tmp/prof3-*.log`, cumulative):

- `Vector.extract_append._proof_1` (4.95B steps): `simul_subst` 49%,
  `try_same_head_spine` 71%, `whnf_core` 73%.
- UTF-8 codec proof (1.16B steps): `try_iota_with_flags` **85.6%**,
  `try_same_head_spine` 85.7% — one deep def-eq descent with iota at
  every level, substituting giant match trees whose branches are
  mostly dropped.
- mergesort shard (2.3B steps): `whnf_core` 38%, `simul_subst` 16%.

The same wall was hit independently on the Aiur side ("the
substitution wall is THE remaining structural frontier — needs a
representation-level fix, not another stuck-form"), and the machine
is its proven fix, measured there (FFT cost):

- Phase A: Int16 −33.8%, Vector._proof_2 −17.1%, mergeSortBench
  −6.8%, String.append −7.7%, gcd −5.0%; **synthetic foldAdd_2000
  +14.7%** (see Risks).
- Phase B (closure-iota): a further −3.4% Int16, −2.0% mergeSort;
  headline payoff (dropped-branch laziness on UTF-8-class) not
  represented in that suite.

## 2. Core idea

A Krivine-style abstract machine for the *structural* fragment of
WHNF (beta, zeta, app-spine, bound-variable lookup):

- **Beta and zeta are O(1) environment pushes.** No substitution
  walk, no materialized intermediate body.
- **Substitution happens only at exit points** ("readback"), and only
  for the parts of the term the reduction actually hands to a
  consumer. A beta chain ending in another beta never materializes
  its intermediate bodies; an iota that selects rule 3 never touches
  rules 0–2.
- WHNF never reduces under binders, so environments **never need
  lifting** — no full explicit-substitution calculus required. A
  `Lam`/`All` value reads back with `clo_subst` at binder depth 1.

## 3. Data types (Rust)

```rust
/// Expression closed over a machine environment:
/// `Clo { e, env }` denotes e[Var(i) := env[i]] for i < env.len(),
/// with Var(i) for i >= env.len() shifting DOWN by env.len() into the
/// ambient context. Environments are built only by the machine's
/// beta/zeta pushes.
struct Clo<M: KernelMode> {
  e: KExpr<M>,
  env: MEnv<M>,
}

/// Persistent cons-list environment: O(1) push, structural sharing
/// across the closures captured at each binder. `len` is cached — the
/// IxVM port found recomputing it per suffix cost ~94M rows on the
/// UTF-8 check.
struct MEnvNode<M: KernelMode> { head: Arc<Clo<M>>, tail: MEnv<M> }
type MEnv<M> = Option<Arc<MEnvNode<M>>>;  // + len: u32 carried alongside

/// Machine spine: args nearest-first, each a closure over the env in
/// force where the App layer was peeled. Also a persistent cons list
/// (the machine only pushes at the front and pops from the front).
type CSpine<M> = MEnv-like list of Arc<Clo<M>>;
```

No `CWhnf` enum in Phase A: the Rust machine is a private loop inside
`whnf_core_with_flags_uncached`, and every exit reads back to a plain
`KExpr` that re-enters the *existing* loop (see §5). The symbolic
result type only becomes necessary for Phase C (closure-aware
def-eq), which this design defers.

## 4. The machine loop

A single iterative loop (NOT recursion — machine depth equals
reduction depth and must not consume native stack; every IxVM
transition is tail-call-shaped, so the loop is mechanical). State:
`(head: KExpr, env: MEnv, n: u32, spine: CSpine)`. Fuel: decrements
the same `MAX_WHNF_FUEL` budget as the enclosing `whnf_core` loop —
unlike IxVM we KEEP fuel (adversarial-input posture; see
`docs/kernel_identity.md` for the threat model).

Transitions, mirroring `mwhnf_spine`:

| head | action |
|---|---|
| `App(f, a)` | push `Clo{a, env}` onto spine; `head = f` (O(1) per layer, no `collect_app_spine` Vec) |
| `Lam(_, _, _, body)` | spine non-empty → pop `c`, push onto env, `head = body` (**beta, O(1)**); spine empty → EXIT: read back `Lam` via `clo_subst` (a value) |
| `Let(_, _, val, body)` | push `Clo{val, env}` onto env, `head = body` (**zeta, O(1)**) |
| `Var(i)` with `i < n` | fetch `Clo{e2, env2}` = env[i]; `head, env = e2, env2` (O(1) jump — this is where laziness pays) |
| `Var(i)` with `i >= n` | EXIT stuck: read back spine onto `Var(i - n)`; the *outer* loop's Var arm then does ambient `lookup_let_val` zeta |
| `FVar(_)` | EXIT stuck (readback); outer loop's FVar arm does LDecl zeta |
| `All(..)` | spine empty → EXIT readback; non-empty → ill-typed application, readback stuck (mirror IxVM) |
| `Const(..)` | EXIT: read back spine, rebuild application, hand to the existing dispatch (prim families, iota, projection-definitions, delta in the enclosing loops). Phase B refines the `Recr` case — see §7 |
| `Prj(id, f, val)` | scrutinee = `Clo{val, env}`: whnf it through the machine **respecting `flags.cheap_proj`** (cheap → machine + structural-only exits; full → full `whnf`), then the existing `try_proj_reduce` on the result; spine read back |
| `Sort/Nat/Str` | EXIT readback (stuck application of a non-function — outer loop handles/returns) |

**Exit contract:** every machine exit produces a plain `KExpr` and
*re-enters `whnf_core_with_flags_uncached`'s loop* as the new `cur`
(or returns, where the old code returned). This keeps EVERY existing
behavior — ambient let/LDecl zeta, iota, K-synthesis,
`cleanup_nat_offset_major`, string/nat literal exposure,
proj-definitions, the nat-offset-stuck probe, delta in `whnf` — byte
identical in semantics. The machine replaces only the
App-collect/beta/zeta core.

## 5. Entry gating (the hybrid — load-bearing)

IxVM measured a machine-everywhere variant at **+26% on beta-free
literal-recursor loops** (closure-wrap + readback overhead with no
beta to amortize it). The shipped design enters the machine **only
when a beta actually fires**:

In `whnf_core_with_flags_uncached`'s App arm (whnf.rs:641ff), after
`f = whnf_core(f0)`:

- `f` is `Lam` → wrap the already-collected `args` as empty-env
  closures (`spine_wrap`) and run the machine starting from the beta.
  This REPLACES the current multi-lambda peel + `simul_subst` block.
- otherwise → existing path unchanged (rebuild-if-changed, iota,
  return).

Everything outside the App arm (Const-headed terms, literal recursor
loops, the whole no-delta/delta loop structure) never touches the
machine. This is also why the existing *caches need no changes*: the
machine is invisible between `whnf_core` entry and exit, and cache
keys/values remain plain interned `KExpr`s.

## 6. Readback: `clo_subst`

New functions in `subst.rs`, mirroring IxVM `Subst.lean:352-400`:

```rust
/// e[Var(depth + i) := lift(readback(env[i]), depth)] for i < n,
/// Var(j) for j >= depth + n shifted down by n. lbr-guarded at every
/// node (the no-op-subtree guard measured −68% substitution entries
/// on the IxVM side). Uses a per-call memo scratch keyed (uid, depth)
/// (same pattern as subst_scratch — a NEW scratch map on InternTable;
/// the two must not share entries). Results interned per node, like
/// every other subst.
fn clo_subst(intern, e, env, n, depth) -> KExpr
fn clo_readback(intern, c: &Clo) -> KExpr  // clo_subst(e, env, n, 0)
```

`clo_subst`'s Var arm composes `clo_readback` of the env entry with
the existing `lift` (subst.rs:341) at non-zero depth. Spine readback
maps `clo_readback` over the spine and rebuilds Apps via interning —
exactly what the current post-beta rebuild does, so uid/interning
discipline (see `docs/kernel_identity.md`) is unchanged: readback
goes through the same constructors + intern table as today's
substitution output.

## 7. Phases

**Phase A — machine for beta/zeta (this design's deliverable 1).**
Scope: `whnf.rs` App arm + the machine loop + `subst.rs::clo_subst`.
All Const/Proj exits read back and use existing machinery. Expected
from IxVM Phase A scaled to our profiles: vector double-digit
(its 49% `simul_subst` is the direct target), utf8 and mergesort
mid-single-digit, intRxc small.

**Phase B — closure-iota (`try_iota_c`).** The `Recr` Const-exit no
longer reads its spine back: the major whnfs through its closure
(`clo_whnf`), and on the main ctor-rule hit the rule RHS returns with
params/motives/minors + ctor fields + post-major args as CLOSURES —
the rule's Lam-chain betas push them straight into an env, so
**unselected rules and dropped branches are never substituted and
never read back**. Off-main-path cases (K-flag synthesis, the
nat linear-rec shortcut, struct-eta, quot, `cleanup_nat_offset_major`
interplay) MISS to the existing plain `try_iota_with_flags` on a
readback spine — semantics preserved by construction. This phase is
the UTF-8-class payoff (its 85% iota share is mostly discarded-branch
substitution). `flags.cheap_rec` gates exactly as today (cheap mode
skips the machine-iota entirely and misses to the plain path).

**Phase C (deferred, separate design):** closure-aware def-eq (the
IxVM working tree's `CWhnf` capture route) and env-trimming for the
curried-sharing regression. Do not start until A+B are measured.

## 8. What explicitly does NOT change

- All caches (whnf/whnf_core/cheap variants, infer, def-eq, unfold,
  equiv, failure) — keys, values, clearing. The machine lives strictly
  between one cache miss and its fill.
- The delta loop in `whnf`, prim-family dispatch, nat-offset-stuck
  probes, transient-nat cache exclusion, native/string/decidable
  reducers.
- def-eq tier structure; `whnf_core_for_def_eq` keeps cheap flags,
  which the machine consults only at its Proj exit (A) and Recr exit
  (B).
- Fuel and error semantics (`MaxRecDepth`).
- `simul_subst` itself stays — instantiation sites outside whnf
  (infer's pi-instantiation etc.) still use it.

## 9. Risks and mitigations

1. **Curried-sharing regression (measured +14.7% on IxVM's synthetic
   foldAdd_2000):** eager sequential substitution shared
   constant-prefix substitutions across loop iterations; per-iteration
   env closures do not. Our suite lacks a foldAdd-shaped input —
   **add one before implementing** (e.g. dump `natfoldsucc.ixe` /
   `natreclinear.ixe` from the repo root into the bench suite) so the
   regression class is visible. Mitigation if it bites: env-trimming
   at readback to each subterm's visible slice (IxVM's designed
   fix), or tighten the entry gate (enter only on multi-arg beta).
2. **Native stack:** the machine MUST be an iterative loop;
   `clo_subst` recursion depth is term depth (same exposure as
   today's `subst`).
3. **Memory:** env chains are Arc-shared cons cells; worst case holds
   alive every closure of a deep reduction until exit. Guest RAM is
   512MB; the same terms today materialize MORE memory (full
   substituted bodies), so this should be net-negative pressure, but
   watch the RAM column in `ziskemu -m` on vector/utf8.
4. **Cheap-flag fidelity:** the def-eq false-negative discipline
   (cheap results must not enter full caches) is keyed at the
   `whnf_core_with_flags` wrapper, which is untouched; the machine
   only needs to route its Proj/Recr exits by `flags`. Test: the
   existing 604 suite covers cheap/full splits.
5. **Behavioral drift in exits:** any machine exit that fails to
   re-enter the outer loop (instead of returning) silently loses an
   ambient zeta/iota step. The exit contract in §4 is the review
   checklist: every exit either returns where the old code returned,
   or sets `cur` and continues.

## 10. Test & acceptance plan

Per phase: 604 kernel + 200 ixon tests; native `check_one` on
Vector._proof_1, Int16, UTF-8; full 11-input guest cycle suite +
`natfoldsucc`/`natreclinear` additions; per the acceptance bar, keep
a phase only if the suite nets ≥1% (expected: well above).
Phase A first, committed alone; Phase B on top, committed alone.

## 11. Effort

Phase A: ~350–500 lines (machine loop ~150, clo_subst ~120, App-arm
rewire ~50, spine helpers, tests). Phase B: ~200 more
(try_iota_c + clo_whnf + Recr exit). The IxVM source is the line-by-
line reference for both.
