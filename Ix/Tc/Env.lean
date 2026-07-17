module

public import Ix.Tc.Const
public import Ix.Tc.Error

/-!
Mirror: crates/kernel/src/env.rs

Kernel environment: `KEnv m` maps `KId m` to `KConst m` and owns all shared
kernel state — the intern table and the type-checking caches.

Divergences from Rust (documented, semantics-preserving):
- The `prims: OnceCell<Primitives<M>>` field is not stored here (Rust has an
  env ↔ primitive module cycle Lean can't express); the resolved `Primitives`
  lives on `TcState` instead, which is where the Rust `TypeChecker` copies it
  anyway. `Primitives.fromEnv` performs the resolution (see `Ix.Tc.Primitive`).
- The reserved-marker guard in Rust's `KEnv::insert` (a panic) is enforced at
  ingress time instead (`Ix.Tc.Ingress`), which is the only path that feeds
  untrusted constants into the env.
- `subst_scratch`/`lift_scratch` buffer *reuse* is not ported (allocation
  churn is a Rust concern); per-call memoization itself is (see `Ix.Tc.Subst`).
- Perf counters and the sharding profile sink are not ported.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap HashSet)

/-- Hash-consing intern table for expressions and universes, owned by one
    `KEnv`. Interning returns the first value stored for a key, so equal
    subtrees share representation (RSS only — no cache soundness depends on
    it; all semantic caches key by `Address`). Expression keys are
    `KExpr.internKey`: the metadata-blind semantic address in anon mode,
    the metadata-AWARE `metaAddr` in meta mode — a blind meta key would
    collapse alpha-identical subtrees first-wins and lose per-occurrence
    names/infos/mdata (see `ExprInfo.metaAddr`). Universe interning stays
    semantic in both modes (level display names are positional at
    egress). -/
structure InternTable (m : Mode) where
  univs : HashMap Address (KUniv m) := {}
  exprs : HashMap Address (KExpr m) := {}

namespace InternTable

def empty : InternTable m := {}

instance : Inhabited (InternTable m) := ⟨{}⟩

/-- Read-only fast path: canonical interned universe for `addr`, if present. -/
@[inline] def tryGetUniv (it : InternTable m) (addr : Address) :
    Option (KUniv m) :=
  it.univs[addr]?

/-- Read-only fast path counterpart for expressions (keyed by
    `KExpr.internKey`). -/
@[inline] def tryGetExpr (it : InternTable m) (key : Address) :
    Option (KExpr m) :=
  it.exprs[key]?

/-- Intern a universe: return the existing value for its hash if present,
    otherwise insert and return. -/
def internUniv (it : InternTable m) (u : KUniv m) : KUniv m × InternTable m :=
  match it.univs[u.addr]? with
  | some canon => (canon, it)
  | none => (u, { it with univs := it.univs.insert u.addr u })

/-- Intern an expression: same guarantee as `internUniv`, keyed by
    `KExpr.internKey` (metadata-aware in meta mode). -/
def internExpr (it : InternTable m) (e : KExpr m) : KExpr m × InternTable m :=
  let key := e.internKey
  match it.exprs[key]? with
  | some canon => (canon, it)
  | none => (e, { it with exprs := it.exprs.insert key e })

end InternTable

/-- Generated recursor, cached after inductive validation. -/
structure GeneratedRecursor (m : Mode) where
  indAddr : Address
  ty : KExpr m
  rules : Array (RecRule m)

/-- Which nested-auxiliary order generated-recursor validation should use.
    Lean's original environment emits nested auxiliary recursors in
    source/queue order; Ix's compiled environment canonicalizes the aux
    portion with `sortConsts` partition refinement. -/
inductive RecursorAuxOrder where
  | source
  | canonical
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Snapshot of all `KEnv` cache sizes (diagnostics). -/
structure KEnvCacheSizes where
  consts : Nat := 0
  blocks : Nat := 0
  internExprs : Nat := 0
  internUnivs : Nat := 0
  whnf : Nat := 0
  whnfNoDelta : Nat := 0
  whnfNoDeltaCheap : Nat := 0
  whnfCore : Nat := 0
  whnfCoreCheap : Nat := 0
  infer : Nat := 0
  inferOnly : Nat := 0
  defEq : Nat := 0
  defEqCheap : Nat := 0
  defEqFailure : Nat := 0
  unfold : Nat := 0
  isProp : Nat := 0
  isRec : Nat := 0
  recursor : Nat := 0
  recMajors : Nat := 0
  blockPeerAgreement : Nat := 0
  blockCheckResults : Nat := 0
  deriving Repr, Inhabited

/-- The kernel environment. Single-threaded: one worker owns one environment
    at a time. Contains all kernel state for that worker: constants, intern
    table, and type-checking caches.

    All cache keys are content addresses (`Address`), immune to pointer-reuse
    ABA problems. Cache-soundness notes (from env.rs, load-bearing):

    - `whnfNoDeltaCheapCache` / `whnfCoreCheapCache`: cheap-projection
      (DEF_EQ_CORE) results must NOT be shared with full callers — cheap
      projections leave projection-of-non-ctor terms stuck where FULL would
      unfold. Reads and writes gated to cheap-mode callers only.
    - `inferCache` is populated only by full-mode `infer`; `inferOnlyCache`
      only by infer-only synthesis (and read only while infer-only is
      active). Infer-only lookups may consume full-mode results (strictly
      stronger), never the reverse.
    - `defEqCheapCache`: cheap `false` can be a full-mode false negative;
      cheap `true` may promote to the full cache.
    - `defEqFailure`: negative cache with narrow semantics — only consulted /
      populated around the same-head-spine attempt for equal-rank Regular
      heads inside lazy delta.
    - `natSuccStuck`: memo of stuck succ-chain peels; the succ-collapse loop
      runs its inner WHNF in `NatSuccMode.stuck`, which bypasses WHNF caches. -/
structure KEnv (m : Mode) where
  /-- Loaded constants keyed by `KId`. -/
  consts : HashMap (KId m) (KConst m) := {}
  /-- Block membership: block id → ordered member ids. -/
  blocks : HashMap (KId m) (Array (KId m)) := {}
  intern : InternTable m := {}
  /-- WHNF cache (full, with delta): (expr, ctx)-keyed. -/
  whnfCache : HashMap (Address × Address) (KExpr m) := {}
  /-- WHNF cache (no delta). -/
  whnfNoDeltaCache : HashMap (Address × Address) (KExpr m) := {}
  /-- Cheap-mode WHNF no-delta cache (see structure doc). -/
  whnfNoDeltaCheapCache : HashMap (Address × Address) (KExpr m) := {}
  /-- WHNF core cache: structural-only reduction, FULL flags only. -/
  whnfCoreCache : HashMap (Address × Address) (KExpr m) := {}
  /-- Cheap-mode WHNF core cache (see structure doc). -/
  whnfCoreCheapCache : HashMap (Address × Address) (KExpr m) := {}
  /-- Infer cache (full mode only; see structure doc). -/
  inferCache : HashMap (Address × Address) (KExpr m) := {}
  /-- Infer-only cache (see structure doc). -/
  inferOnlyCache : HashMap (Address × Address) (KExpr m) := {}
  /-- Full def-eq cache: (lo, hi, ctx)-keyed, canonically ordered. -/
  defEqCache : HashMap (Address × Address × Address) Bool := {}
  /-- Cheap def-eq cache (see structure doc). -/
  defEqCheapCache : HashMap (Address × Address × Address) Bool := {}
  /-- Failed def-eq pairs in lazy delta (narrow semantics; see doc). -/
  defEqFailure : HashSet (Address × Address × Address) := {}
  /-- Constant-instantiation cache for delta unfolding, keyed by the head
      `const` expression's address (content-addresses `(id, us)`). -/
  unfoldCache : HashMap Address (KExpr m) := {}
  /-- Stuck `Nat.succ^k(x)` peel outcomes (see structure doc). -/
  natSuccStuck : HashSet (Address × Address) := {}
  /-- "Is this type Prop?" cache, keyed by (type, ctx). -/
  isPropCache : HashMap (Address × Address) Bool := {}
  /-- Computed `isRec` per inductive, keyed by content address. -/
  isRecCache : HashMap Address Bool := {}
  /-- Generated recursors, keyed by inductive Muts block id. -/
  recursorCache : HashMap (KId m) (Array (GeneratedRecursor m)) := {}
  /-- Nested-auxiliary order expected by stored recursors in this env. -/
  recursorAuxOrder : RecursorAuxOrder := .canonical
  /-- Major-inductive set → inductive block id. Keys are arrays sorted by
      `KId.cmp` (the canonical set representation; Rust uses `BTreeSet`). -/
  recMajorsCache : HashMap (Array (KId m)) (KId m) := {}
  /-- Block ids whose peers passed S3/S3b agreement. -/
  blockPeerAgreementCache : HashSet (KId m) := {}
  /-- Whole-block type-check results; failures cached too, so every member
      of a bad block reports the same structured failure. -/
  blockCheckResults : HashMap (KId m) (Except (TcError m) Unit) := {}
  /-- Next free-variable id for checker-local binder openings. Env-level
      (not per-checker) because caches live here and key by expr hash; two
      checkers must never mint the same fvar id. NOT reset per constant. -/
  nextFVarId : UInt64 := 0

namespace KEnv

def new (recursorAuxOrder : RecursorAuxOrder := .canonical) : KEnv m :=
  { recursorAuxOrder }

instance : Inhabited (KEnv m) := ⟨{}⟩

def freshFVarId (env : KEnv m) : FVarId × KEnv m :=
  (⟨env.nextFVarId⟩, { env with nextFVarId := env.nextFVarId + 1 })

@[inline] def get? (env : KEnv m) (id : KId m) : Option (KConst m) :=
  env.consts[id]?

/-- Insert a constant. The Rust reserved-marker panic guard lives at ingress
    (see module doc). -/
def insert (env : KEnv m) (id : KId m) (c : KConst m) : KEnv m :=
  { env with consts := env.consts.insert id c }

def size (env : KEnv m) : Nat := env.consts.size

def isEmpty (env : KEnv m) : Bool := env.consts.isEmpty

def contains (env : KEnv m) (id : KId m) : Bool := env.consts.contains id

@[inline] def getBlock? (env : KEnv m) (id : KId m) : Option (Array (KId m)) :=
  env.blocks[id]?

def insertBlock (env : KEnv m) (id : KId m) (members : Array (KId m)) :
    KEnv m :=
  { env with blocks := env.blocks.insert id members }

/-- Clear all worker-local kernel state (constants, blocks, intern, caches,
    fvar counter). Preserves `recursorAuxOrder`. -/
def clear (env : KEnv m) : KEnv m :=
  { recursorAuxOrder := env.recursorAuxOrder }

/-- Merge two ingress-fresh envs (phase-parallel ingress: chunked local
    envs → one shared env). Constants/blocks union — ingress conversion is
    deterministic, so duplicate KIds (same work item converted twice)
    carry identical entries and last-write-wins is benign. `nextFVarId`
    takes the max. Intern tables and reduction caches are NOT merged:
    interning is RSS-only (no cache soundness depends on it) and
    ingress-fresh envs have empty reduction caches. -/
def union (a b : KEnv m) : KEnv m :=
  { a with
    consts := b.consts.fold (init := a.consts) fun acc id c => acc.insert id c
    blocks := b.blocks.fold (init := a.blocks) fun acc id ms =>
      acc.insert id ms
    nextFVarId := max a.nextFVarId b.nextFVarId }

/-- Clear only the reduction-memo caches (whnf / infer / def-eq / unfold /
    is-prop / nat-succ-stuck). Structural caches (`consts`, `blocks`,
    `intern`, recursor caches, `blockCheckResults`) are preserved. Clearing a
    pure memo never affects correctness — only performance. -/
def clearReductionCaches (env : KEnv m) : KEnv m :=
  { env with
    whnfCache := {}
    whnfNoDeltaCache := {}
    whnfNoDeltaCheapCache := {}
    whnfCoreCache := {}
    whnfCoreCheapCache := {}
    inferCache := {}
    inferOnlyCache := {}
    defEqCache := {}
    defEqCheapCache := {}
    defEqFailure := {}
    unfoldCache := {}
    natSuccStuck := {}
    isPropCache := {} }

/-- Snapshot of all cache sizes (diagnostics). -/
def cacheSizes (env : KEnv m) : KEnvCacheSizes where
  consts := env.consts.size
  blocks := env.blocks.size
  internExprs := env.intern.exprs.size
  internUnivs := env.intern.univs.size
  whnf := env.whnfCache.size
  whnfNoDelta := env.whnfNoDeltaCache.size
  whnfNoDeltaCheap := env.whnfNoDeltaCheapCache.size
  whnfCore := env.whnfCoreCache.size
  whnfCoreCheap := env.whnfCoreCheapCache.size
  infer := env.inferCache.size
  inferOnly := env.inferOnlyCache.size
  defEq := env.defEqCache.size
  defEqCheap := env.defEqCheapCache.size
  defEqFailure := env.defEqFailure.size
  unfold := env.unfoldCache.size
  isProp := env.isPropCache.size
  isRec := env.isRecCache.size
  recursor := env.recursorCache.size
  recMajors := env.recMajorsCache.size
  blockPeerAgreement := env.blockPeerAgreementCache.size
  blockCheckResults := env.blockCheckResults.size

end KEnv

end Ix.Tc

end
end
