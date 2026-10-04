/-
  CompileM: Lean Compiler for Ixon Format (Pure Implementation)

  Architecture:
  - CompileState: global immutable state (Reader)
  - BlockEnv: per-block read-only context (Reader)
  - BlockCache: per-block mutable state (State)
  - Pure sequential compilation

  This implementation is designed for correctness and formalization.
  For performance, use the Rust implementation.
-/

module
import Std.Sync
public import Ix.Ixon
public import Ix.IxonUniv
public import Ix.Environment
public import Ix.SemanticContract
public import Ix.Compile.SourceContract.Transport
public import Ix.Sharing.Exact
public import Ix.Common
public import Ix.PhaseTimers
public import Ix.Store
public import Ix.Mutual
public import Ix.GraphM
public import Ix.CondenseM
public import Ix.SOrder
public import Ix.Compile.Canon.Classes
public import Ix.CallSitePlan
public import Ix.CallSiteSurgery
public import Ix.CanonM
public import Ix.Compile.Pass.Names

namespace Ix.CompileM
public section

-- Need Nonempty for partial function compilation
instance : Nonempty SOrder := ⟨⟨true, .eq⟩⟩

/-- Global compilation environment shared across all blocks. -/
structure CompileEnv where
  /-- Canonicalized Leon environment -/
  env : Ix.Environment
  /-- Map from constant name to Named (address + metadata). This is the
      final NAMED REGISTRY (Rust `stt.env.named`): the aux tail's
      re-registrations override member entries here. It is NOT the
      resolution map — `compileExpr` resolves through `nameToAddr`,
      which keeps the PRIMARY projection addresses (Rust
      `stt.name_to_addr` is never touched by the tail). -/
  nameToNamed : Std.HashMap Name Ixon.Named
  /-- Resolution map from constant name to compiled address (Rust
      `stt.name_to_addr`): primary block/projection registrations plus
      `promote_aux` copies. First hop of `lookupConstAddr`. -/
  nameToAddr : Std.HashMap Name Address := {}
  /-- Compiled constants storage, SERIALIZED. Holding structured
      `Ixon.Constant`s here retained a whole-env-scale object graph for
      the entire compile; the serialized bytes (already computed when a
      block merges) are the compact form — Rust's mathlib compile peaks
      ~20 GiB largely because compiled output lives as bytes. Readers
      needing structure parse on demand (`Ixon.deConstantAt`); assembly
      wraps entries as byte-backed `Ixon.LazyConstant`s. -/
  constants : Std.HashMap Address ByteArray
  /-- Blob storage for literals -/
  blobs : Std.HashMap Address ByteArray
  /-- Total bytes of serialized constants (for profiling) -/
  totalBytes : Nat
  /-- Aux-generated name→address view merged from previously compiled
      blocks (Rust `stt.aux_name_to_addr`; scheduler-visible only after
      the driver merges each block's registrations). -/
  auxNameToAddr : Std.HashMap Name Address := {}
  /-- Per-auxiliary call-site surgery plans, keyed by the original
      auxiliary name (Rust `stt.call_site_plans`). Computed per block by
      `compileMutualAuxTail`; visible to later blocks once the driver
      merges them. -/
  callSitePlans : Std.HashMap Name Ix.AuxGen.CallSitePlan := {}
  /-- Per-`.brecOn` surgery plans (Rust `stt.brec_on_call_site_plans`).
      Shares the motive permutation with `.rec`, but `.brecOn` places
      indices+major before the handler binders. -/
  brecOnCallSitePlans : Std.HashMap Name Ix.AuxGen.BRecOnCallSitePlan := {}
  /-- Per-`.below`-family surgery plans (Rust
      `stt.below_call_site_plans`). A `X.below`/`X.below_N` HEAD has the
      motive-only telescope `params, motives, indices, major`. For
      Prop-level (IndPredBelow) families the map also carries the rest
      of the family's user-visible surface under their own names — the
      `.below` constructors and the `.below.casesOn` wrapper, whose
      telescopes start with the below inductive's parameters (parent
      params, then parent motives) and have NO major-premise floor
      (a field-less below ctor is fully applied at exactly
      params+motives). The apply site discriminates the two shapes via
      `Ix.AuxGen.belowPlanKeyIsHead`. -/
  belowCallSitePlans : Std.HashMap Name Ix.AuxGen.BRecOnCallSitePlan := {}
  /-- Persistent set of names compiled by aux-gen (Rust
      `stt.aux_gen_extra_names`); merged from block tails by the driver
      and consulted by the scheduler's promotion pass. -/
  auxGenExtraNames : Std.HashSet Name := {}
  /-- Constants that couldn't be compiled, name → error description
      (Rust `stt.ungrounded`): pre-compile grounding rejections plus
      per-block compile failures recorded by the scheduler. -/
  ungrounded : Std.HashMap Name String := {}
  /-- Mutual-block canonical class ordering, keyed by every member name
      in the block (Rust `stt.blocks`, compile.rs:4048-4057; the driver
      merges each block's `BlockResult.classNames` here on completion).
      Read by the evaporation claim probe
      (`Ix.AuxGen.positionClaimedBySpecScc`) to rebuild a spec-member
      SCC's canonical expansion — scheduler dependency order guarantees
      the entry exists before any dependent block compiles. -/
  blocks : Std.HashMap Name (Array (Array Name)) := {}
  /-- Name-hash → name over the full INPUT constant set, for
      `nameForAddr`'s reverse lookup when the streaming driver leaves
      `env.consts` unmaterialized (its by-hash scan over `env.consts`
      keys sees nothing there). Materialized-env callers leave this
      empty and keep the scan. -/
  nameByHash : Std.HashMap Address Name := {}
  /-- Resource limits of the canonical sharing construction
      (`buildBlockConstant`, `finishMutualCompilation`): `compilerSharingLimits`
      unless a driver sets the `IX_SHARING_LIMITS` override
      (`compilerSharingLimitsFromEnv`). Limits decide only whether a block
      compiles, never its bytes. -/
  sharingLimits : Ix.Sharing.Exact.Limits := {}
  /-- Pass 3, the faithful rewrite (`IX_PASS3=images`; design document
      §4.5, `Ix.Compile.Pass.Translate`), replaces call-site surgery. Off by
      default: with it off no field below is ever written and the compiler
      is byte-identical to the surgery pipeline. -/
  pass3 : Bool := false
  /-- Pass 3: each image-kind auxiliary name of a changed Lean block (its
      recursors, `casesOn`, `recOn` and the Type-level `below`/`brecOn`
      family) ↦ the block's key (`all₀`). Merged from the block tails. -/
  p3Heads : Std.HashMap Name Name := {}
  /-- Pass 3: changed Lean block key ↦ its `all`. -/
  p3Blocks : Std.HashMap Name (Array Name) := {}
  /-- Pass 3: the canonical recursors (Pass 2's output) of the changed
      blocks under aux-gen's names (`rep.rec`, `all₀.rec_j` by source
      index), the image generator's input. -/
  p3CanonRecs : Std.HashMap Name RecursorVal := {}
  /-- Pass 3, set per block by the driver: the source occurrence of each
      rewritten call site of the block, keyed by the placeholder index the
      rewrite left in the term (`Ix.Compile.Pass.Translate`). Compiled into
      `metaSharing` as the decompile record. -/
  p3Sources : Std.HashMap Nat Expr := {}
  /-- Pass 3: the input's block reference graph (block key ↦ referenced
      names), to rewrite only blocks that reference a changed block's
      auxiliary. -/
  p3BlockRefs : Std.HashMap Name (Ix.Set Name) := {}
  /-- Pass 3: the changed-clique table (`Ix.Compile.Pass.scheduleCliques`):
      every member of an encoded definition clique, and every equation lemma
      carried with it, ↦ (the clique in Lean's order, the carried lemmas,
      the demotion reason: empty unless a dependent unfolds the encoding and
      cannot be carried, in which case the clique compiles as today). -/
  p3Cliques : Std.HashMap Name (Array Name × Array Name × String) := {}

/-- Initialize global state from canonicalization result. -/
def CompileEnv.new (env: Ix.Environment) : CompileEnv :=
  { env, nameToNamed := {}, constants := {}, blobs := {}, totalBytes := 0 }

instance : Inhabited CompileEnv where
  default := { env := { consts := {} }, nameToNamed := {}, constants := {}, blobs := {}, totalBytes := 0 }

/-- Result of compiling a block, including the main constant and any projections. -/
structure BlockResult where
  /-- The main block constant (Muts for mutual blocks, or direct constant) -/
  block : Ixon.Constant
  /-- Pre-computed serialized bytes and address (avoids re-serialization). -/
  blockBytes : ByteArray
  blockAddr : Address
  /-- Metadata for the block constant (for singleton blocks without projections) -/
  blockMeta : Ixon.ConstantMeta := .empty
  /-- Projections: each name maps to its projection constant and metadata.
      Empty for single non-inductive constants (name maps directly to block).
      For inductives/mutual blocks: contains IPrj/DPrj/RPrj/CPrj for each name. -/
  projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
  /-- Canonical class ordering of this block's members (Rust
      `class_ordering`, compile.rs:4049), for the driver to merge into
      `CompileEnv.blocks`. Empty for non-mutual/early-return paths —
      Rust's `stt.blocks` insert sits after the alpha-collapsed
      standalone early return (compile.rs:3872) and is skipped there
      too. -/
  classNames : Array (Array Name) := #[]
  deriving Inhabited

/-- Per-block compilation state and tables. -/
structure BlockState where
  /-- Expression compilation cache (keyed by Expr for O(1) lookup).
      Value is (compiled expression, arena root index). -/
  exprCache : Std.HashMap Expr (Ixon.Expr × UInt64) := {}
  /-- Universe compilation cache (keyed by Level for O(1) lookup) -/
  univCache : Std.HashMap Level Ixon.Univ := {}
  /-- Reference table (ordered unique addresses) -/
  refs : Array Address := #[]
  refsIndex : Std.HashMap Address UInt64 := {}
  /-- Universe table (ordered unique universes). Canonicity §10.6: every
      entry is `canonUniv`-fixed — `compileAndInternUnivCanon` interns
      only canonical forms and preseeding canonicalizes before sorting. -/
  univs : Array Ixon.Univ := #[]
  univsIndex : Std.HashMap Ixon.Univ UInt64 := {}
  /-- Set once preseeding finalizes the primary `univs` table. From then
      on any on-the-fly intern of a canonical form must HIT a preseeded
      entry — a miss would silently shift the `univPatches` virtual
      indices (`univs.size + slot`), so `compileAndInternUnivCanon`
      errors instead (canonicity §10.6 V3). -/
  univsFinal : Bool := false
  /-- `Ixon.canonUniv` memo (positional trees — context-free, so the
      cache is sound across constants and univ contexts). -/
  canonUnivCache : Std.HashMap Ixon.Univ Ixon.Univ := {}
  /-- Extension univs of the CURRENT constant: original (non-canonical)
      spellings referenced by `univPatches`, in first-use order.
      Canonicity §10.6 — resets with the arena. -/
  metaUnivs : Array Ixon.Univ := #[]
  metaUnivsIndex : Std.HashMap Ixon.Univ UInt64 := {}
  /-- Level-spelling patches of the CURRENT constant, keyed by the arena
      root of each affected `sort`/`const` occurrence — resets with the
      arena. -/
  univPatches : Array Ixon.UnivPatch := #[]
  /-- Blob storage collected during block compilation -/
  blockBlobs : Std.HashMap Address ByteArray := {}
  /-- Name components collected during block compilation -/
  blockNames : Std.HashMap Address Ix.Name := {}
  /-- Reducibility hints per definition name compiled in this block.
      Hints are not part of `ConstantMeta`; the driver resolves this
      map into `Ixon.Env.anonHints` once addresses are final. -/
  defHints : Std.HashMap Name Lean.ReducibilityHints := {}
  /-- Arena-based expression metadata for the current constant -/
  arena : Ixon.ExprMetaArena := {}
  /-- Primary name→address registrations of the CURRENT block (member
      projection addresses), inserted after the primary block compiles
      and BEFORE the aux tail runs — Rust's `compile_mutual` writes them
      into the global `stt.name_to_addr` at exactly that point
      (compile.rs:3926/3946/3966), so the tail's aux compilation
      resolves sibling members through them. The driver merges these
      into `CompileEnv.nameToAddr` on block completion. -/
  blockNameToAddr : Std.HashMap Name Address := {}
  /-- Aux-generation outputs of the CURRENT block (Rust mutates
      `stt.aux_name_to_addr` / `stt.env` globally; the pure model collects
      per block and the driver merges). Within-block phases resolve
      earlier phases' constants through `auxNameToAddr` via
      `lookupConstAddr`'s fallback chain. -/
  auxNameToAddr : Std.HashMap Name Address := {}
  /-- `stt.env.store_const` calls (blocks + projections), in order. -/
  auxConsts : Array (Address × Ixon.Constant) := #[]
  /-- `stt.env.register_name` calls (incl. synthetic `Muts` entries), in
      order; later entries for a name override earlier (DashMap insert). -/
  auxNamed : Array (Name × Ixon.Named) := #[]
  /-- `stt.aux_gen_extra_names` membership (Rust mutual.rs). -/
  auxGenExtraNames : Std.HashSet Name := {}
  /-- Compiled Ixon expressions for collapsed call-site args, accumulated
      by surgered `compileExpr` calls within the current constant and
      drained into `ConstantMeta.metaSharing` when the constant's
      metadata is built (Rust `BlockCache.surgery_sharing`). -/
  surgerySharing : Array Ixon.Expr := #[]
  /-- Pass 3: compiling a decompile record (the source occurrence of a
      rewritten call site) into `metaSharing`. References and universes
      outside the primary tables go to the per-constant extension tables
      (`p3MetaRefs`, `metaUnivs`) instead, so the record never changes the
      constant's bytes. -/
  p3MetaMode : Bool := false
  /-- Pass 3: the current constant's extension refs (`ConstantMeta.metaRefs`;
      virtual index `refs.size + slot`). -/
  p3MetaRefs : Array Address := #[]
  p3MetaRefsIndex : Std.HashMap Address UInt64 := {}
  /-- Pass 3: placeholder index ↦ (`metaSharing` index, arena root) of the
      current constant's compiled decompile records. -/
  p3Records : Std.HashMap Nat (Nat × UInt64) := {}
  /-- Pass 3, filled by the aux tail of a changed block for the driver:
      the canonical recursors aux-gen generated (Pass 2), the image-kind
      heads (name ↦ Lean block key) and the Lean blocks (key ↦ `all`). -/
  p3AuxRecs : Array (Name × RecursorVal) := #[]
  p3Heads : Array (Name × Name) := #[]
  p3Blocks : Array (Name × Array Name) := #[]
  /-- Pass 3: the canonical recursors of the block's Prop `IndPredBelow`
      family (`compileBelowRecursors`), read by the A3V-IPB hook
      (`Ix.Compile.Pass.editPermutedBelowFamily`); never merged by itself. -/
  p3BelowRecs : Array (Name × RecursorVal) := #[]
  deriving Inhabited

/-- Get or insert a reference into the refs table, returning its index. -/
def BlockState.internRef (cache : BlockState) (addr : Address) : BlockState × UInt64 :=
  match cache.refsIndex.get? addr with
  | some idx => (cache, idx)
  | none =>
    let idx := cache.refs.size.toUInt64
    ({ cache with
      refs := cache.refs.push addr
      refsIndex := cache.refsIndex.insert addr idx
    }, idx)

/-- Get or insert a universe into the univs table, returning its index. -/
def BlockState.internUniv (cache : BlockState) (u : Ixon.Univ) : BlockState × UInt64 :=
  match cache.univsIndex.get? u with
  | some idx => (cache, idx)
  | none =>
    let idx := cache.univs.size.toUInt64
    ({ cache with
      univs := cache.univs.push u
      univsIndex := cache.univsIndex.insert u idx
    }, idx)

/-- Memoize the compiled positional form of a named universe level. -/
def BlockState.cacheUniv (cache : BlockState) (level : Level)
    (u : Ixon.Univ) : BlockState :=
  { cache with univCache := cache.univCache.insert level u }

/-- Per-block compilation environment. -/
structure BlockEnv where
  /-- All constants in current mutual block -/
  all : Set Name
  /-- Current constant being compiled -/
  current : Name
  /-- Mutual recursion context: name → index within block -/
  mutCtx : MutCtx
  /-- Universe parameter context (de Bruijn indices) -/
  univCtx : List Name
  /-- Set while compiling the original Lean form of a regenerated auxiliary
      (`compileConstNoAuxPure`; Rust `BlockCache::provenance_only`): the
      result is provenance only (`Named.original`, never a stored
      constant) and its call sites keep every dropped argument in
      `collapsed` metadata, so the collapse-drop checks (A0) do not apply. -/
  provenanceOnly : Bool := false

/-! ## Compilation Error -/

/-- Compilation error type. Variant order matches Rust CompileError (tags 0–7). -/
inductive CompileError where
  | missingConstant (name : String)
  | missingAddress (addr : Address)
  | invalidMutualBlock (reason : String)
  | unsupportedExpr (desc : String)
  | unknownUnivParam (curr param : String)
  | serializeError (err : Ixon.SerializeError)
  | resourceLimit (reason : String)
  /-- The sharing construction failed (other than by resource exhaustion, which is
      `resourceLimit`). -/
  | sharingConstruction (reason : String)
  deriving Repr, BEq

instance : ToString CompileError where
  toString
  | .missingConstant name => s!"missingConstant: {name}"
  | .missingAddress addr => s!"missingAddress: {addr}"
  | .invalidMutualBlock reason => s!"invalidMutualBlock: {reason}"
  | .unsupportedExpr desc => s!"unsupportedExpr: {desc}"
  | .unknownUnivParam curr param => s!"unknownUnivParam: compiling {curr}, param {param}"
  | .serializeError err => s!"serializeError: {err}"
  | .resourceLimit reason => s!"resourceLimit: {reason}"
  | .sharingConstruction reason => s!"sharingConstruction: {reason}"

abbrev CompileM := ReaderT (CompileEnv × BlockEnv) (ExceptT CompileError (StateT BlockState Id))

/-- Run a CompileM computation purely. -/
def CompileM.run (compileEnv : CompileEnv) (blockEnv : BlockEnv) (blockState : BlockState)
    (m : CompileM α) : Except CompileError (α × BlockState) :=
  match StateT.run (ExceptT.run (ReaderT.run m (compileEnv, blockEnv))) blockState with
  | (Except.ok a, state') => Except.ok (a, state')
  | (Except.error e, _) => Except.error e

/-- Run `act` inside worker phase `ph` (`Ix.PhaseTimers`, off unless
    `IX_PHASE_TIMERS` is set). The phase opens on the block state `act`
    receives and closes on the block state it returns, on success and on
    error alike; the result is `act`'s, unchanged. -/
@[inline] def timedC (ph : Ix.PhaseTimers.Phase) (act : CompileM α) : CompileM α :=
  fun r => ExceptT.mk fun s =>
    if Ix.PhaseTimers.enabled () then
      Ix.PhaseTimers.exitV ((ExceptT.run (act r)).run (Ix.PhaseTimers.enterV ph s))
    else (ExceptT.run (act r)).run s

/-- Get the global compile environment. -/
def getCompileEnv : CompileM CompileEnv := do
  pure (← read).1

/-- Get the block environment. -/
def getBlockEnv : CompileM BlockEnv := do
  pure (← read).2

/-- Get the block state. -/
def getBlockState : CompileM BlockState := do
  get

/-- A7 (D8): the named error of an out-of-range access in the compiler. It
    names the block (`BlockEnv.current`) and the site; the drivers record it
    for every member of the block, like any other block failure. -/
def internalIndexError (what : String) (i size : Nat) : CompileM α := do
  throw (.invalidMutualBlock s!"internal error in block '{(← getBlockEnv).current.pretty}': \
{what}: index {i} out of range (size {size})")

/-- A7 (D8): total array access for the compiler's monads (`CompileM` and
    the stacks over it, by lifting). Replaces `a[i]!`, which on an
    out-of-range index printed `PANIC` and continued with `default`, so a
    construction bug could reach the output as a well-formed but wrong
    constant; now it is `internalIndexError`. On every index that was in
    range the value is the same. -/
@[inline] def arrIdx (a : Array α) (i : Nat) (what : String) : CompileM α :=
  match a[i]? with
  | some x => pure x
  | none => internalIndexError what i a.size

/-- Modify the block state. -/
def modifyBlockState (f : BlockState → BlockState) : CompileM Unit := do
  modify f

/-- Modify the block state and return a value. -/
def modifyGetBlockState (f : BlockState → α × BlockState) : CompileM α := do
  modifyGet fun state =>
    let (a, state') := f state
    (a, state')

/-- Modify the block environment locally. -/
def withBlockEnv (f : BlockEnv → BlockEnv) (m : CompileM α) : CompileM α :=
  withReader (fun (env, blockEnv) => (env, f blockEnv)) m

/-- Set the universe-parameter context, dropping the universe cache.

    `compileUniv` keys `univCache` by the `Level` alone, but a
    `Level.param` compiles to `Univ.var i` where `i` is the parameter's
    POSITION in `univCtx` — so the result depends on this context. The
    cache lives for a whole block while each member compiles under its
    own `levelParams`, so without this a member whose context orders the
    same parameter name differently would inherit the earlier member's
    index: a silently wrong constant under a correct-looking name, with
    no error. The expression cache is cleared per constant for the same
    reason (`clearExprCache`); the Rust mirror instead widens the key to
    `(level, univ_params_key)`. -/
def withUnivCtx (univCtx : List Name) : CompileM α → CompileM α := fun act => do
  modifyBlockState fun c => { c with univCache := {} }
  withBlockEnv (fun env => { env with univCtx }) act

/-- Set mutual context. -/
def withMutCtx (mutCtx : MutCtx) : CompileM α → CompileM α :=
  withBlockEnv fun env => { env with mutCtx }

/-- Get the mutual context as an array of name hashes, ordered by index then name. -/
def getMutCtxAddrs : CompileM (Array Address) := do
  let ctx := (← getBlockEnv).mutCtx
  pure <| ctx.toList.toArray.qsort (fun a b =>
    if a.2 != b.2 then a.2 < b.2 else (compare a.1 b.1).isLT) |>.map (·.1.getHash)

/-- Set current constant. -/
def withCurrent (name : Name) : CompileM α → CompileM α :=
  withBlockEnv fun env => { env with current := name }

/-- Set all constants in block. -/
def withAll (all : Set Name) : CompileM α → CompileM α :=
  withBlockEnv fun env => { env with all }

/-! ## Metadata Management (Arena-Based) -/

/-- Allocate a new node in the arena, returning its index. -/
def allocArenaNode (node : Ixon.ExprMetaData) : CompileM UInt64 :=
  modifyGetBlockState fun c =>
    let idx := c.arena.nodes.size.toUInt64
    (idx, { c with arena := { nodes := c.arena.nodes.push node } })

/-- Take the current arena and reset for next constant. -/
def takeArena : CompileM Ixon.ExprMetaArena :=
  modifyGetBlockState fun c => (c.arena, { c with arena := {} })

/-- Reset the arena for a new constant. -/
def resetArena : CompileM Unit :=
  modifyBlockState fun c =>
    { c with arena := {}, metaUnivs := #[], metaUnivsIndex := {},
             univPatches := #[], p3MetaRefs := #[], p3MetaRefsIndex := {},
             p3Records := {} }

/-- Clear the expression cache (between constants to avoid cross-constant arena references). -/
def clearExprCache : CompileM Unit :=
  modifyBlockState fun c => { c with exprCache := {} }

/-- Take the accumulated collapsed call-site expressions for the current
    constant, clearing the accumulator (Rust
    `std::mem::take(&mut cache.surgery_sharing)`, compile.rs:2230). The
    result becomes the constant's `ConstantMeta.metaSharing`. -/
def takeSurgerySharing : CompileM (Array Ixon.Expr) :=
  modifyGetBlockState fun c => (c.surgerySharing, { c with surgerySharing := #[] })

/-- Take the current constant's Pass 3 extension refs (`ConstantMeta.metaRefs`;
    empty unless a decompile record referenced an address outside the
    primary table). -/
def takeMetaRefs : CompileM (Array Address) :=
  modifyGetBlockState fun c =>
    (c.p3MetaRefs, { c with p3MetaRefs := #[], p3MetaRefsIndex := {} })

/-! ## Universe Compilation -/

/-- Compile an Ix.Level to Ixon.Univ type. -/
def compileUniv (lvl : Level) : CompileM Ixon.Univ := do
  -- Check cache first (O(1) lookup via embedded hash)
  let state ← getBlockState
  if let some u := state.univCache.get? lvl then
    return u

  let u ← match lvl with
  | .zero _ => pure .zero
  | .succ l _ => pure (.succ (← compileUniv l))
  | .max l r _ => pure (.max (← compileUniv l) (← compileUniv r))
  | .imax l r _ => pure (.imax (← compileUniv l) (← compileUniv r))
  | .param name _ => do
    let ctx := (← getBlockEnv).univCtx
    match ctx.idxOf? name with
    | some i => pure (.var i.toUInt64)
    | none => throw (.unknownUnivParam s!"{(← getBlockEnv).current}" s!"{name}")
  | .mvar _ _ => throw (.unsupportedExpr "level metavariable")

  -- Cache result
  modifyBlockState fun c => c.cacheUniv lvl u
  pure u
termination_by lvl

/-- Intern a universe into the block's univs table, returning its index. -/
def internUniv (u : Ixon.Univ) : CompileM UInt64 :=
  modifyGetBlockState fun state =>
    let (state', idx) := state.internUniv u
    (idx, state')

/-- `Ixon.canonUniv` through the block memo. -/
def canonUnivCached (u : Ixon.Univ) : CompileM Ixon.Univ := do
  if let some c := (← getBlockState).canonUnivCache.get? u then
    return c
  let c := Ixon.canonUniv u
  modifyBlockState fun st =>
    { st with canonUnivCache := st.canonUnivCache.insert u c }
  return c

/-- Intern an original (non-canonical) spelling into the current
    constant's `metaUnivs` extension, returning its VIRTUAL index
    (`univs.size + slot` — the primary table is preseed-final by the
    time expressions compile, so the offset is stable). -/
def BlockState.internMetaUniv (state : BlockState)
    (raw : Ixon.Univ) : BlockState × UInt64 :=
  match state.metaUnivsIndex.get? raw with
  | some k => (state, state.univs.size.toUInt64 + k)
  | none =>
    let k := state.metaUnivs.size.toUInt64
    ({ state with metaUnivs := state.metaUnivs.push raw
                  metaUnivsIndex := state.metaUnivsIndex.insert raw k },
      state.univs.size.toUInt64 + k)

def internMetaUniv (raw : Ixon.Univ) : CompileM UInt64 :=
  modifyGetBlockState fun st =>
    let (st', idx) := st.internMetaUniv raw
    (idx, st')

/-- Compile a level and intern its CANONICAL form into the primary
    table (canonicity §10.6). Returns the canonical index plus, when
    the source spelling differs, the virtual index of the original
    spelling in the `metaUnivs` extension (the patch payload). -/
def compileAndInternUnivCanon (lvl : Level) : CompileM (UInt64 × Option UInt64) := do
  let raw ← compileUniv lvl
  let canon ← canonUnivCached raw
  -- Pass 3 decompile record: a universe outside the primary table goes to
  -- the extension (virtual index), never into the primary table.
  if (← getBlockState).p3MetaMode then
    if !(← getBlockState).univsIndex.contains canon then
      let cidx ← internMetaUniv canon
      if canon == raw then return (cidx, none)
      return (cidx, some (← internMetaUniv raw))
  let sizeBefore := (← getBlockState).univs.size
  let cidx ← internUniv canon
  -- V3 tripwire (canonicity §10.6): the primary table must not grow
  -- after preseeding — a miss here would shift every virtual patch
  -- index minted so far. Mirrors the Rust `debug_assert` in
  -- `compile_univ_idx`.
  if (← getBlockState).univsFinal && (← getBlockState).univs.size != sizeBefore then
    throw (.invalidMutualBlock
      s!"preseed missed canonical form {repr canon} — primary univ table \
        grew after preseeding, shifting univPatches virtual indices \
        (canonicity 10.6 V3)")
  if canon == raw then
    return (cidx, none)
  let vidx ← internMetaUniv raw
  return (cidx, some vidx)

/-- Record a level-spelling patch for the occurrence at `arenaIdx`. -/
def pushUnivPatch (arenaIdx : UInt64) (univIdxs : Array UInt64) : CompileM Unit :=
  modifyBlockState fun st =>
    { st with univPatches := st.univPatches.push { arenaIdx, univIdxs } }

/-- Take (and clear) the current constant's level-spelling channels:
    the `metaUnivs` extension and the arena-keyed patches. -/
def takeUnivPatches : CompileM (Array Ixon.Univ × Array Ixon.UnivPatch) :=
  modifyGetBlockState fun st =>
    ((st.metaUnivs, st.univPatches),
     { st with metaUnivs := #[], metaUnivsIndex := {}, univPatches := #[] })

/-! ## Reference Handling -/

/-- Pass 3 decompile-record interning (see `internRef`). -/
def internRefMeta (addr : Address) : CompileM UInt64 := do
    let st ← getBlockState
    if let some idx := st.refsIndex.get? addr then return idx
    -- Pass 3 decompile record: an address outside the primary table goes
    -- to the constant's extension (`metaRefs`, virtual `refs.size + j`).
    -- The primary table is preseed-final here (preseeding walks the
    -- rewritten terms, which are all that the constant's bytes contain).
    match st.p3MetaRefsIndex.get? addr with
    | some j => return st.refs.size.toUInt64 + j
    | none =>
      let j := st.p3MetaRefs.size.toUInt64
      modifyBlockState fun c => { c with
        p3MetaRefs := c.p3MetaRefs.push addr
        p3MetaRefsIndex := c.p3MetaRefsIndex.insert addr j }
      return st.refs.size.toUInt64 + j

/-- Intern an address into the block's refs table, returning its index.
    (The state is read only for the mode flag, so the update below stays in
    place: no reference to the old state is alive.) -/
def internRef (addr : Address) : CompileM UInt64 := do
  if (← getBlockState).p3MetaMode then return ← internRefMeta addr
  modifyGetBlockState fun state =>
    let (state', idx) := state.internRef addr
    (idx, state')

/-- Look up a constant's address: compiled names first, then the current
    block's aux registrations, then previously merged aux names. Mirrors
    Rust `stt.resolve_addr` (compile.rs:261-274 — `name_to_addr` with
    `aux_name_to_addr` fallback; the block-local layer stands in for
    Rust's global DashMap being visible mid-block). -/
def lookupConstAddr (name : Name) : CompileM Address := do
  let env ← getCompileEnv
  let bstate ← getBlockState
  -- Rust `stt.resolve_addr` (compile.rs:261-274): `name_to_addr` first
  -- (the Lean model splits it into the current block's primary
  -- registrations plus the driver-merged map), then `aux_name_to_addr`
  -- (current block's aux registrations, then driver-merged).
  match bstate.blockNameToAddr.get? name with
  | some addr => pure addr
  | none =>
  match env.nameToAddr.get? name with
  | some addr => pure addr
  | none =>
    match bstate.auxNameToAddr.get? name with
    | some addr => pure addr
    | none =>
      match env.auxNameToAddr.get? name with
      | some addr => pure addr
      | none => throw (.missingConstant s!"{name}")

/-- Find a constant in the Ix environment (through the streaming
    fallback when the driver runs canon-on-demand). -/
def findConst (name : Name) : CompileM ConstantInfo := do
  let env ← getCompileEnv
  match env.env.get? name with
  | some const => pure const
  | none => throw (.missingConstant s!"{name}")

/-- Get the Expr for a constant's type. -/
def getConstType (name : Name) : CompileM Expr := do
  let const ← findConst name
  pure const.getCnst.type

/-- Get the Expr for a definition/theorem/opaque value. -/
def getConstValue (name : Name) : CompileM Expr := do
  let const ← findConst name
  match const with
  | .defnInfo v => pure v.value
  | .thmInfo v => pure v.value
  | .opaqueInfo v => pure v.value
  | _ => throw (.invalidMutualBlock s!"Constant {name} has no value")

/-! ## DataValue and KVMap Compilation -/

/-- Serialize an Ix.Int to bytes. -/
def serializeIxInt (i : Ix.Int) : ByteArray :=
  match i with
  | .ofNat n =>
    let natBytes := ByteArray.mk (Nat.toBytesLE n)
    ByteArray.mk #[0] ++ natBytes
  | .negSucc n =>
    let natBytes := ByteArray.mk (Nat.toBytesLE n)
    ByteArray.mk #[1] ++ natBytes

/-- Store a string as a blob and return its 32-byte address. -/
def storeString (s : String) : CompileM Address := do
  let bytes := s.toUTF8
  let addr := Address.blake3 bytes
  modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
  pure addr

/-- Record a definition's reducibility hints (see `BlockState.defHints`). -/
def recordDefHints (name : Name) (hints : Lean.ReducibilityHints) : CompileM Unit :=
  modifyBlockState fun c => { c with defHints := c.defHints.insert name hints }

/-- Pure state transition underlying `compileName`. -/
def BlockState.compileName : BlockState → Ix.Name → BlockState
  | state, name =>
    let addr := name.getHash
    if state.blockNames.contains addr then
      state
    else
      match name with
      | .anonymous _ =>
        { state with blockNames := state.blockNames.insert addr name }
      | .str parent s _ =>
        let state :=
          { state with blockNames := state.blockNames.insert addr name }
        let bytes := s.toUTF8
        let stringAddr := Address.blake3 bytes
        let state :=
          { state with blockBlobs := state.blockBlobs.insert stringAddr bytes }
        state.compileName parent
      | .num parent _ _ =>
        let state :=
          { state with blockNames := state.blockNames.insert addr name }
        state.compileName parent
termination_by _ name => name

/-- Compile a name: store all string components as blobs and track
    name components in blockNames for deduplication.
    This matches Rust's compile_name behavior. -/
def compileName (name : Ix.Name) : CompileM Unit :=
  modifyBlockState fun state => state.compileName name

/-- Record an array of names through the same left-to-right pure transition
used by repeated `compileName` calls. -/
def BlockState.compileNames (state : BlockState)
    (names : Array Ix.Name) : BlockState :=
  names.foldl (fun current name => current.compileName name) state

def compileNames (names : Array Ix.Name) : CompileM Unit :=
  modifyBlockState fun state => state.compileNames names

/-- A Nat as a TagN (`f = 0`) integer (`Ixon.putTagN 0 0`). -/
def tagN0Bytes (n : Nat) : ByteArray :=
  Ixon.runPut (Ixon.putTagN 0 0 n.toUInt64)

/-- Serialize an Ix.Substring to bytes, storing strings as blobs. -/
def serializeIxSubstring (ss : Ix.Substring) : CompileM ByteArray := do
  let strAddr ← storeString ss.str
  pure (strAddr.hash ++ tagN0Bytes ss.startPos ++ tagN0Bytes ss.stopPos)

/-- Serialize an Ix.SourceInfo to bytes, storing strings as blobs. -/
def serializeIxSourceInfo (si : Ix.SourceInfo) : CompileM ByteArray := do
  match si with
  | .original leading leadingPos trailing trailingPos =>
    let leadingBytes ← serializeIxSubstring leading
    let trailingBytes ← serializeIxSubstring trailing
    pure (ByteArray.mk #[0] ++ leadingBytes ++ tagN0Bytes leadingPos ++
      trailingBytes ++ tagN0Bytes trailingPos)
  | .synthetic start stop canonical =>
    pure (ByteArray.mk #[1] ++ tagN0Bytes start ++ tagN0Bytes stop ++
      ByteArray.mk #[if canonical then 1 else 0])
  | .none => pure (ByteArray.mk #[2])

/-- Serialize an Ix.SyntaxPreresolved to bytes, storing strings as blobs. -/
def serializeIxSyntaxPreresolved (sp : Ix.SyntaxPreresolved) : CompileM ByteArray := do
  match sp with
  | .namespace name =>
    compileName name
    pure (ByteArray.mk #[0] ++ name.getHash.hash)
  | .decl name aliases =>
    compileName name
    let header := ByteArray.mk #[1] ++ name.getHash.hash ++ tagN0Bytes aliases.size
    let aliasAddrs ← aliases.mapM storeString
    let aliasesBytes := aliasAddrs.foldl (fun bytes addr => bytes ++ addr.hash)
      ByteArray.empty
    pure (header ++ aliasesBytes)

/-- Serialize an `Ix.Syntax` to bytes, storing strings as blobs. Traversing
`args.attach` exposes the structural membership proof needed to keep this
production serializer kernel-visible and total without changing array order. -/
def serializeIxSyntax (syn : Ix.Syntax) : CompileM ByteArray := do
  match syn with
  | .missing => pure (ByteArray.mk #[0])
  | .node info kind args =>
    compileName kind
    let header := ByteArray.mk #[1]
    let infoBytes ← serializeIxSourceInfo info
    let kindBytes := kind.getHash.hash
    let lenBytes := tagN0Bytes args.size
    let serializedArgs ← args.attach.mapM fun arg => serializeIxSyntax arg.1
    let argsBytes := serializedArgs.foldl (fun bytes arg => bytes ++ arg)
      ByteArray.empty
    pure (header ++ infoBytes ++ kindBytes ++ lenBytes ++ argsBytes)
  | .atom info val =>
    let infoBytes ← serializeIxSourceInfo info
    let valAddr ← storeString val
    pure (ByteArray.mk #[2] ++ infoBytes ++ valAddr.hash)
  | .ident info rawVal val preresolved =>
    compileName val
    let header := ByteArray.mk #[3]
    let infoBytes ← serializeIxSourceInfo info
    let rawBytes ← serializeIxSubstring rawVal
    let valBytes := val.getHash.hash
    let lenBytes := tagN0Bytes preresolved.size
    let serializedPres ← preresolved.mapM serializeIxSyntaxPreresolved
    let presBytes := serializedPres.foldl (fun bytes pr => bytes ++ pr)
      ByteArray.empty
    pure (header ++ infoBytes ++ rawBytes ++ valBytes ++ lenBytes ++ presBytes)
termination_by sizeOf syn
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem arg.property) (by omega)

/-- Compile a DataValue to Ixon.DataValue, storing blobs as needed. -/
def compileDataValue (dv : Ix.DataValue) : CompileM Ixon.DataValue := do
  match dv with
  | .ofString s =>
    let bytes := s.toUTF8
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    pure (.ofString addr)
  | .ofBool b => pure (.ofBool b)
  | .ofName n =>
    compileName n
    pure (.ofName n.getHash)
  | .ofNat n =>
    let bytes := ByteArray.mk (Nat.toBytesLE n)
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    pure (.ofNat addr)
  | .ofInt i =>
    let bytes := serializeIxInt i
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    pure (.ofInt addr)
  | .ofSyntax syn =>
    let bytes ← serializeIxSyntax syn
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    pure (.ofSyntax addr)

/-- Compile a KVMap (array of name-value pairs).

    Pass 3: the placeholder `[(_ix.inline, n)]` that the faithful rewrite
    leaves around a rewritten call site (`Ix.Compile.Pass.Names.inlineKey`)
    becomes the decompile record `[(_ix.inline, s), (_ix.inline_meta, m)]`:
    the `metaSharing` index and the arena root of the compiled source
    occurrence (`compileExpr` compiles it before the term). -/
def compileKVMap (kvs : Array (Ix.Name × Ix.DataValue)) : CompileM Ixon.KVMap := do
  if let #[(k, .ofNat n)] := kvs then
    if k == Ix.Compile.Pass.inlineKey && (← getCompileEnv).pass3 then
      let some (s, m) := (← getBlockState).p3Records.get? n
        | throw (.invalidMutualBlock s!"Pass 3: call-site record {n} was not compiled")
      return ← #[(Ix.Compile.Pass.inlineKey, Ix.DataValue.ofNat s),
          (Ix.Compile.Pass.inlineMetaKey, Ix.DataValue.ofNat m.toNat)].mapM fun (k, v) => do
        compileName k
        let vData ← compileDataValue v
        pure (k.getHash, vData)
  kvs.mapM fun (k, v) => do
    compileName k
    let vData ← compileDataValue v
    pure (k.getHash, vData)

/-! ## Expression Compilation -/

/-- Stable insertion sort of `(canonical position, arg)` pairs by
    position. Rust sorts surgered spines with `sort_by_key` (stable,
    compile.rs:1136); canonical positions are structurally unique per
    telescope, but stability is preserved anyway so the port stays exact
    (`Array.qsort` is unstable). Spines are small — O(n²) is fine. -/
def sortByCanonIdx (xs : Array (Nat × Expr)) : Array (Nat × Expr) := Id.run do
  let mut out : Array (Nat × Expr) := #[]
  for x in xs do
    let pos := (out.findIdx? (fun y => x.1 < y.1)).getD out.size
    out := ((out.extract 0 pos).push x) ++ out.extract pos out.size
  return out

/-- Whether expression compilation can take the kernel-visible ordinary
    path.  A nonempty plan map selects the existing surgery implementation,
    even when every plan happens to be the identity; this keeps the dispatch
    criterion independent of the expression being compiled. -/
def CompileEnv.surgeryFree (env : CompileEnv) : Bool :=
  env.callSitePlans.isEmpty && env.brecOnCallSitePlans.isEmpty &&
    env.belowCallSitePlans.isEmpty

/-- Memoised runtime implementation of `exprCompileDepth`: the same height,
computed once per distinct node (`Ix.Expr` keys compare by their embedded
hash). The structural definition below is a tree walk, exponential on the
DAG-shaped proof terms of a library. -/
private partial def exprCompileDepthMemo (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some d := (← get).get? e then return d
  let d ← match e with
    | .app fn arg _ => do pure (max (← exprCompileDepthMemo fn) (← exprCompileDepthMemo arg) + 1)
    | .lam _ ty body _ _ | .forallE _ ty body _ _ => do
      pure (max (← exprCompileDepthMemo ty) (← exprCompileDepthMemo body) + 1)
    | .letE _ ty val body _ _ => do
      pure (max (← exprCompileDepthMemo ty) (max (← exprCompileDepthMemo val)
        (← exprCompileDepthMemo body)) + 1)
    | .mdata _ inner _ | .proj _ _ inner _ => do pure ((← exprCompileDepthMemo inner) + 1)
    | _ => pure 1
  modify (·.insert e d)
  return d

private def exprCompileDepthImpl (e : Expr) : Nat := (exprCompileDepthMemo e).run' {}

/-- Structural height used to fuel ordinary expression compilation. -/
@[implemented_by exprCompileDepthImpl]
def exprCompileDepth : Expr → Nat

  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1
  | .app fn arg _ => max (exprCompileDepth fn) (exprCompileDepth arg) + 1
  | .lam _ ty body _ _ | .forallE _ ty body _ _ =>
    max (exprCompileDepth ty) (exprCompileDepth body) + 1
  | .letE _ ty val body _ _ =>
    max (exprCompileDepth ty) (max (exprCompileDepth val)
      (exprCompileDepth body)) + 1
  | .mdata _ inner _ | .proj _ _ inner _ => exprCompileDepth inner + 1

/-- Compile one flattened App spine using `compile` only for the head and
    arguments.  Recursive partial-spine App nodes never pass through
    `compile`, hence never gain expression-cache entries. -/
def compileAppNoSurgery
    (compile : Expr → CompileM (Ixon.Expr × UInt64)) :
    Expr → CompileM (Ixon.Expr × UInt64)
  | .app fn arg _ => do
    let (f, fRoot) ← compileAppNoSurgery compile fn
    let (a, aRoot) ← compile arg
    let root ← allocArenaNode (.app fRoot aRoot)
    pure (.app f a, root)
  | head => compile head

/-- One cache-miss step of ordinary expression compilation, parameterized by
    the recursive compiler.  Factoring the constructor transition from cache
    lookup/insertion keeps the executable behavior unchanged while exposing a
    small kernel-visible proof boundary. -/
def compileExprNoSurgeryStep
    (compile : Expr → CompileM (Ixon.Expr × UInt64))
    (e : Expr) : CompileM (Ixon.Expr × UInt64) :=
  match e with
    | .bvar idx _ => do
      let root ← allocArenaNode .leaf
      pure (.var idx.toUInt64, root)

    | .sort lvl _ => do
      let (idx, orig?) ← compileAndInternUnivCanon lvl
      let root ← allocArenaNode .leaf
      if let some vidx := orig? then
        pushUnivPatch root #[vidx]
      pure (.sort idx, root)

    | .const name lvls _ => do
      let mutCtx := (← getBlockEnv).mutCtx
      let compiled ← lvls.mapM compileAndInternUnivCanon
      let univIndices := compiled.map (·.1)
      compileName name
      let nameAddr := name.getHash
      let recordPatch (root : UInt64) : CompileM Unit := do
        if compiled.any (·.2.isSome) then
          pushUnivPatch root (compiled.map fun (cidx, orig?) => orig?.getD cidx)
      match mutCtx.get? name with
      | some recIdx =>
        let root ← allocArenaNode (.ref nameAddr)
        recordPatch root
        pure (.recur recIdx.toUInt64 univIndices, root)
      | none => do
        let addr ← lookupConstAddr name
        let refIdx ← internRef addr
        let root ← allocArenaNode (.ref nameAddr)
        recordPatch root
        pure (.ref refIdx univIndices, root)

    | .app .. => compileAppNoSurgery compile e

    | .lam name ty body bi _ => do
      compileName name
      let nameAddr := name.getHash
      let (t, tyRoot) ← compile ty
      let (b, bodyRoot) ← compile body
      let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
      pure (.leanLam t b, root)

    | .forallE name ty body bi _ => do
      compileName name
      let nameAddr := name.getHash
      let (t, tyRoot) ← compile ty
      let (b, bodyRoot) ← compile body
      let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
      pure (.leanAll t b, root)

    | .letE name ty val body nonDep _ => do
      compileName name
      let nameAddr := name.getHash
      let (t, tyRoot) ← compile ty
      let (v, valRoot) ← compile val
      let (b, bodyRoot) ← compile body
      let root ← allocArenaNode (.letBinder nameAddr tyRoot valRoot bodyRoot)
      pure (.leanLet nonDep t v b, root)

    | .lit (.natVal n) _ => do
      let bytes := ByteArray.mk (Nat.toBytesLE n)
      let addr := Address.blake3 bytes
      modifyBlockState fun c =>
        { c with blockBlobs := c.blockBlobs.insert addr bytes }
      let idx ← internRef addr
      let root ← allocArenaNode .leaf
      pure (.nat idx, root)

    | .lit (.strVal s) _ => do
      let bytes := s.toUTF8
      let addr := Address.blake3 bytes
      modifyBlockState fun c =>
        { c with blockBlobs := c.blockBlobs.insert addr bytes }
      let idx ← internRef addr
      let root ← allocArenaNode .leaf
      pure (.str idx, root)

    | .proj typeName fieldIdx struct _ => do
      compileName typeName
      let typeAddr ← lookupConstAddr typeName
      let typeRefIdx ← internRef typeAddr
      let structNameAddr := typeName.getHash
      let (s, sRoot) ← compile struct
      let root ← allocArenaNode (.prj structNameAddr sRoot)
      pure (.prj typeRefIdx fieldIdx.toUInt64 s, root)

    | .mdata kvData inner _ => do
      if SemanticContract.hasMetadata kvData then
        let contract ← match SemanticContract.read kvData with
          | .ok contract => pure contract
          | .error error => throw (.unsupportedExpr error)
        let (value, root) ← compile inner
        match contract.lower inner value with
        | .ok value => return (value, root)
        | .error error => throw (.unsupportedExpr error)
      let kvmap ← compileKVMap kvData
      let (innerResult, innerRoot) ← compile inner
      let root ← allocArenaNode (.mdata #[kvmap] innerRoot)
      pure (innerResult, root)

    | .fvar _ _ => throw (.unsupportedExpr "free variable")
    | .mvar _ _ => throw (.unsupportedExpr "metavariable")

/-- Fuel-total implementation of the ordinary (no call-site surgery)
    expression compiler.  The App arm deliberately flattens the complete
    telescope before recurring, so inner partial-spine nodes are allocated
    but not expression-cached, exactly as in the Rust compiler and the
    surgery implementation's normal path.

    Recursive calls consume one unit of fuel.  The public entry point uses
    `exprCompileDepth e`; every recursively compiled head, argument, or
    constructor child is a strict source subterm, so the exhaustion branch is
    unreachable for that entry point. -/
def compileExprNoSurgeryFuel : Nat → Expr → CompileM (Ixon.Expr × UInt64)
  | 0, _ => throw (.invalidMutualBlock
      "internal error: ordinary expression compiler exhausted structural fuel")
  | fuel + 1, e => do
    let state ← getBlockState
    if let some cached := state.exprCache.get? e then
      return cached

    let (result, root) ← compileExprNoSurgeryStep
      (compileExprNoSurgeryFuel fuel) e

    modifyBlockState fun c =>
      { c with exprCache := c.exprCache.insert e (result, root) }
    pure (result, root)

/-- Kernel-visible ordinary expression compiler. -/
def compileExprNoSurgery (e : Expr) : CompileM (Ixon.Expr × UInt64) :=
  compileExprNoSurgeryFuel (exprCompileDepth e) e

/-- Arity information for a source-visible head carrying non-identity
    call-site surgery. -/
structure PlanHeadArity where
  floor : Nat
  expected : Nat
  headRewrite : Bool
  /-- The plan drops arguments of collapsed members: a Tier-B eta wrapper
      would drop bound variables, which no kept argument equals. -/
  dropsCollapsed : Bool

/-- Shared Tier-A/Tier-B arity classification. Mirrors Rust
    `plan_head_arity`. -/
def planHeadArity? (cenv : CompileEnv) (name : Name) : Option PlanHeadArity :=
  match cenv.callSitePlans.get? name with
  | some plan =>
    if !plan.isIdentity then
      some { floor := plan.minimalFullPrefix
             expected := plan.nParams + plan.nSourceMotives
               + plan.nSourceMinors + plan.nIndices + 1
             headRewrite := plan.headRewrite.isSome
             dropsCollapsed := plan.dropsCollapsed }
    else none
  | none =>
    match cenv.belowCallSitePlans.get? name with
    | some plan =>
      if !plan.isIdentity then
        let floor := plan.belowMinimalFullPrefix
        some { floor
               expected := if Ix.AuxGen.belowPlanKeyIsHead name then
                 floor + plan.nIndices + 1 else floor
               headRewrite := false
               dropsCollapsed := plan.dropsCollapsed }
      else none
    | none =>
      match cenv.brecOnCallSitePlans.get? name with
      | some plan =>
        if !plan.isIdentity then
          let expected := plan.brecOnMinimalFullPrefix
          some { floor := expected, expected, headRewrite := false
                 dropsCollapsed := plan.dropsCollapsed }
        else none
      | none => none

/-- Read-only walk over one ORIGINAL expression. Ordinary partial/bare plan
    references are handled by Tier B. The audit rejects the deliberately
    unsupported cases before they can silently become a kernel type error:
    partial evaporated-aux head rewrites, and a short plan spine split by a
    `mdata`/`let` wrapper in the function part of an outer application.
    Mirrors Rust `audit_plan_head_arities`. -/
def auditPlanHeadArities (owner : Name) (top : Expr) : CompileM Unit := do
  let cenv ← getCompileEnv
  if cenv.callSitePlans.isEmpty && cenv.belowCallSitePlans.isEmpty &&
      cenv.brecOnCallSitePlans.isEmpty then
    return
  let annotated ← match Ix.SemanticContract.inspect top with
    | .ok annotated => pure annotated
    | .error error => throw (.unsupportedExpr error)
  -- Lean expressions are DAGs. Large tactic proofs may reach one shared
  -- subexpression through exponentially many tree paths, while the ordinary
  -- compiler memoizes it. Keep the audit linear in unique nodes as well.
  -- `obscured` belongs in the key: a node that is safe as an argument can be
  -- invalid when reused in a wrapped function position.
  let mut seen : Std.HashSet (Expr × Bool) := {}
  let mut stack : Array (Expr × Bool) := #[(top, false)]
  while !stack.isEmpty do
    let (e, obscured) := stack.back!
    stack := stack.pop
    if seen.contains (e, obscured) then continue
    seen := seen.insert (e, obscured)
    match e with
    | .app .. =>
      let (head, args) := Ix.AuxGen.collectLeanTelescope e
      match head with
      | .const name _ _ =>
        if let some arity := planHeadArity? cenv name then
          if annotated then
            throw (.unsupportedExpr s!"resource contracts across non-identity call-site surgery: {owner.pretty} calls {name.pretty}")
          let need := if arity.headRewrite then arity.expected else arity.floor
          if args.size < need && (obscured || arity.headRewrite) then
            let suffix := if obscured then
              " (application spine obscured by mdata/let)" else ""
            throw (.invalidMutualBlock s!"plan-head arity audit while \
compiling '{owner.pretty}': head '{name.pretty}' has {args.size} args, \
expected at least {need}{suffix}")
      | .lam .. => stack := stack.push (head, false)
      | _ => stack := stack.push (head, true)
      for arg in args do
        stack := stack.push (arg, false)
    | .const name _ _ =>
      if let some arity := planHeadArity? cenv name then
        if annotated then
          throw (.unsupportedExpr s!"resource contracts across non-identity call-site surgery: {owner.pretty} calls {name.pretty}")
        if obscured || arity.headRewrite then
          let need := if arity.headRewrite then arity.expected else arity.floor
          let suffix := if obscured then
            " (application spine obscured by mdata/let)" else ""
          throw (.invalidMutualBlock s!"plan-head arity audit while \
compiling '{owner.pretty}': head '{name.pretty}' has 0 args, expected at \
least {need}{suffix}")
    | .lam _ ty body _ _ | .forallE _ ty body _ _ =>
      stack := stack.push (body, obscured) |>.push (ty, false)
    | .letE _ ty val body _ _ =>
      stack := stack.push (body, obscured) |>.push (val, false) |>.push (ty, false)
    | .mdata _ inner _ => stack := stack.push (inner, obscured)
    | .proj _ _ s _ => stack := stack.push (s, false)
    | _ => pure ()

/-- Audit every original recursor-rule expression in source order. -/
def auditRecursorRulePlanHeads (owner : Name) :
    List RecursorRule → CompileM Unit
  | [] => pure ()
  | rule :: rest => do
    auditPlanHeadArities owner rule.rhs
    auditRecursorRulePlanHeads owner rest

/-- Audit every original expression belonging to a singleton declaration. -/
def auditConstantInfoPlanHeads (ci : ConstantInfo) : CompileM Unit := do
  let owner := ci.getCnst.name
  auditPlanHeadArities owner ci.getCnst.type
  match ci with
  | .defnInfo d => auditPlanHeadArities owner d.value
  | .thmInfo d => auditPlanHeadArities owner d.value
  | .opaqueInfo d => auditPlanHeadArities owner d.value
  | .recInfo r => auditRecursorRulePlanHeads owner r.rules.toList
  | _ => pure ()

/-- Audit constructor types belonging to one original mutual inductive. -/
def auditMutualConstructorPlanHeads : List ConstructorVal → CompileM Unit
  | [] => pure ()
  | ctor :: rest => do
    auditPlanHeadArities ctor.cnst.name ctor.cnst.type
    auditMutualConstructorPlanHeads rest

/-- Audit every expression embedded in one original mutual member. -/
def auditMutConstPlanHeads (c : MutConst) : CompileM Unit := do
  match c with
  | .defn d =>
    auditPlanHeadArities d.name d.type
    auditPlanHeadArities d.name d.value
  | .indc i =>
    auditPlanHeadArities i.name i.type
    auditMutualConstructorPlanHeads i.ctors.toList
  | .recr r =>
    auditPlanHeadArities r.cnst.name r.cnst.type
    auditRecursorRulePlanHeads r.cnst.name r.rules.toList

/-- Whether the current body is one of our regenerated canonical
    auxiliaries. Such bodies already use canonical argument order. -/
def compilingIsAuxRegen : CompileM Bool := do
  let compiling := (← getBlockEnv).current
  if !Ix.AuxGen.isAuxGenSuffix compiling then return false
  let cenv ← getCompileEnv
  let bstate ← getBlockState
  if bstate.auxNameToAddr.contains compiling then return true
  if cenv.auxNameToAddr.contains compiling then return true
  return match cenv.nameToNamed.get? compiling with
    | some named => named.original.isSome
    | none => false

/-- Does this short source application need the Tier-B eta adapter? -/
def etaAdapterNeeded (name : Name) (nArgs : Nat) : CompileM Bool := do
  if ← compilingIsAuxRegen then return false
  return match planHeadArity? (← getCompileEnv) name with
    | some arity => !arity.headRewrite && nArgs < arity.floor
    | none => false

/-- Refuse the Tier-B eta adapter for a head whose plan drops arguments of
    collapsed members (A0, WB-B4): the wrapper binds the missing source
    arguments as variables, so a dropped motive or minor is a bound variable
    that no kept argument equals, and the drop cannot be justified (both
    kernels reject such users anyway). Mirrors Rust `refuse_collapsed_eta`. -/
def refuseCollapsedEta (name : Name) (nArgs : Nat) : CompileM Unit := do
  if (← getBlockEnv).provenanceOnly then return
  if let some arity := planHeadArity? (← getCompileEnv) name then
    if arity.dropsCollapsed then
      throw (.invalidMutualBlock s!"{Ix.AuxGen.collapseEtaError}: compiling \
'{(← getBlockEnv).current.pretty}', call-site head '{name.pretty}' applied to \
{nArgs} argument(s) would be eta-wrapped, dropping bound arguments of \
collapsed members")

/-- The collapse checks of a surgered call site's bands (A0, WB-B4). A drop
    with no kept partner is refused here; a drop whose compiled form differs
    from its partner's is refused in `buildCallSite`. Each band is `(what,
    keep, sourceToCanon, inBlock, slots)`. -/
def callSiteCollapseChecks (head : Name)
    (bands : Array (String × Array Bool × Array Nat × Array Bool
      × Array Ix.AuxGen.ArgSlot)) : CompileM (Array Ix.AuxGen.CollapseCheck) := do
  let compiling := (← getBlockEnv).current.pretty
  let mut out : Array Ix.AuxGen.CollapseCheck := #[]
  for (what, keep, sourceToCanon, inBlock, slots) in bands do
    match Ix.AuxGen.collapseChecks what keep sourceToCanon inBlock slots
        compiling head.pretty with
    | .ok cs => out := out ++ cs
    | .error msg => throw (.invalidMutualBlock msg)
  return out

/-- Derive a partial call's residual source Pi telescope and build the
    source-interface eta wrapper. Mirrors Rust `synthesize_eta_call_site`. -/
def synthesizeEtaCallSite (name : Name) (lvls : Array Level)
    (applied : Array Expr) : CompileM (Expr × Nat) := do
  refuseCollapsedEta name applied.size
  let ci ← findConst name
  let cnst := ci.getCnst
  let instantiatedType := Ix.AuxGen.substLevels cnst.type cnst.levelParams lvls
  let residual := Ix.AuxGen.instantiatePiParams instantiatedType applied.size applied
  let mut binders : Array (Name × Expr × Lean.BinderInfo) := #[]
  let mut cur := residual
  repeat
    match cur with
    | .forallE binderName ty body info _ =>
      binders := binders.push (binderName, ty, info)
      cur := body
    | _ => break
  if binders.isEmpty then
    throw (.invalidMutualBlock s!"eta call-site adapter for '{name.pretty}' \
found no residual Pi binders after {applied.size} args")
  let nSynth := binders.size
  let mut fullArgs := applied.map fun arg => Ix.AuxGen.shiftVars arg nSynth 0
  for i in [0:nSynth] do
    fullArgs := fullArgs.push (Expr.mkBVar (nSynth - 1 - i))
  let mut body := Expr.mkConst name lvls
  for arg in fullArgs do body := Expr.mkApp body arg
  for (binderName, ty, info) in binders.reverse do
    body := Expr.mkLam binderName ty body info
  pure (body, nSynth)

/-- Compile a Const as the raw canonical call-site head. This bypasses bare
    reference eta detection and intentionally does not use the expression
    cache; source bare occurrences check for an adapter before consulting
    that cache. Mirrors Rust `compile_const_expr_raw`. -/
def compileConstExprRaw (name : Name) (lvls : Array Level) :
    CompileM (Ixon.Expr × UInt64) := do
  let mutCtx := (← getBlockEnv).mutCtx
  let compiled ← lvls.mapM compileAndInternUnivCanon
  let univIndices := compiled.map (·.1)
  compileName name
  let nameAddr := name.getHash
  let recordPatch (root : UInt64) : CompileM Unit := do
    if compiled.any (·.2.isSome) then
      pushUnivPatch root (compiled.map fun (cidx, orig?) => orig?.getD cidx)
  match mutCtx.get? name with
  | some recIdx =>
    let root ← allocArenaNode (.ref nameAddr)
    recordPatch root
    pure (.recur recIdx.toUInt64 univIndices, root)
  | none =>
    let addr ← lookupConstAddr name
    let refIdx ← internRef addr
    let root ← allocArenaNode (.ref nameAddr)
    recordPatch root
    pure (.ref refIdx univIndices, root)

/-- Overlay the decompile-facing eta marker on an already-compiled ordinary
    synthesized Binder/CallSite metadata tree. -/
def finishEtaCallSite (wrapperIxon : Ixon.Expr) (wrapperRoot : UInt64)
    (nSynth nApplied : Nat) : CompileM (Ixon.Expr × UInt64) := do
  let arena := (← getBlockState).arena
  let mut bodyRoot := wrapperRoot
  for _ in [0:nSynth] do
    match arena.nodes[bodyRoot.toNat]? with
    | some (.binder _ _ _ bodyChild) => bodyRoot := bodyChild
    | other => throw (.invalidMutualBlock s!"eta adapter metadata expected \
{nSynth} Binder nodes, found {reprStr other}")
  let (name, entries, canonMeta, origHead) ←
    match arena.nodes[bodyRoot.toNat]? with
    | some (.callSite name entries canonMeta origHead) =>
      pure (name, entries, canonMeta, origHead)
    | other => throw (.invalidMutualBlock s!"eta adapter body did not \
compile to CallSite metadata: {reprStr other}")
  if origHead.isSome || entries.size != nApplied + nSynth then
    throw (.invalidMutualBlock s!"eta adapter body metadata mismatch: \
{entries.size} source entries for {nApplied} applied + {nSynth} synthesized \
args (origHead={origHead.isSome})")
  let etaRoot ← allocArenaNode (.etaCallSite nSynth.toUInt64 name
    (entries.extract 0 nApplied) canonMeta wrapperRoot)
  if let some bodyPatch :=
      (← getBlockState).univPatches.find? (·.arenaIdx == bodyRoot) then
    pushUnivPatch etaRoot bodyPatch.univIdxs
  pure (wrapperIxon, etaRoot)

mutual

/-- Compile a canonical Ix.Expr to Ixon.Expr with arena-based metadata.
    Returns (compiled expression, arena root index).
    Uses Ix.Expr as cache key for O(1) lookup via embedded hash.

    Mirrors Rust `compile_expr` (compile.rs:650). Rust is stack-based
    (`Frame::Compile`/`Frame::Cache`); this recursion has identical
    cache and arena semantics: an expression is cache-checked and cached
    exactly when Rust pushes a `Frame::Compile` for it — App telescopes
    are flattened in `compileAppSpine`, so inner partial-spine nodes are
    neither checked nor cached. -/
partial def compileExprSurgical (e : Expr) : CompileM (Ixon.Expr × UInt64) := do
  -- Bare plan references must decide on eta expansion before consulting the
  -- ordinary expression cache: canonical call-site heads deliberately cache
  -- their raw Const form under the same source expression.
  let isEta ← match e with
    | .const name _ _ => etaAdapterNeeded name 0
    | _ => pure false
  -- Check cache (O(1) lookup via embedded hash)
  let state ← getBlockState
  if !isEta then
    if let some cached := state.exprCache.get? e then
      return cached

  let (result, root) ← match e with
  | .bvar idx _ => do
    let root ← allocArenaNode .leaf
    pure (.var idx.toUInt64, root)

  | .sort lvl _ => do
    let (idx, orig?) ← compileAndInternUnivCanon lvl
    let root ← allocArenaNode .leaf
    -- Canonicity §10.6: a spelling the canonicalization changed is
    -- restorable from the patch keyed by this occurrence's arena root.
    if let some vidx := orig? then
      pushUnivPatch root #[vidx]
    pure (.sort idx, root)

  | .const name lvls _ => do
    if isEta then
      let (wrapper, nSynth) ← synthesizeEtaCallSite name lvls #[]
      let (wrapperIxon, wrapperRoot) ← compileExprSurgical wrapper
      finishEtaCallSite wrapperIxon wrapperRoot nSynth 0
    else
      compileConstExprRaw name lvls

  | .app .. => compileAppSpine e

  | .lam name ty body bi _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExprSurgical ty
    let (b, bodyRoot) ← compileExprSurgical body
    let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
    pure (.leanLam t b, root)

  | .forallE name ty body bi _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExprSurgical ty
    let (b, bodyRoot) ← compileExprSurgical body
    let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
    pure (.leanAll t b, root)

  | .letE name ty val body nonDep _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExprSurgical ty
    let (v, valRoot) ← compileExprSurgical val
    let (b, bodyRoot) ← compileExprSurgical body
    let root ← allocArenaNode (.letBinder nameAddr tyRoot valRoot bodyRoot)
    pure (.leanLet nonDep t v b, root)

  | .lit (.natVal n) _ => do
    let bytes := ByteArray.mk (Nat.toBytesLE n)
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    let idx ← internRef addr
    let root ← allocArenaNode .leaf
    pure (.nat idx, root)

  | .lit (.strVal s) _ => do
    let bytes := s.toUTF8
    let addr := Address.blake3 bytes
    modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
    let idx ← internRef addr
    let root ← allocArenaNode .leaf
    pure (.str idx, root)

  | .proj typeName fieldIdx struct _ => do
    compileName typeName
    let typeAddr ← lookupConstAddr typeName
    let typeRefIdx ← internRef typeAddr
    let structNameAddr := typeName.getHash
    let (s, sRoot) ← compileExprSurgical struct
    let root ← allocArenaNode (.prj structNameAddr sRoot)
    pure (.prj typeRefIdx fieldIdx.toUInt64 s, root)

  | .mdata kvData inner _ => do
    if SemanticContract.hasMetadata kvData then
      let contract ← match SemanticContract.read kvData with
        | .ok contract => pure contract
        | .error error => throw (.unsupportedExpr error)
      let (value, root) ← compileExprSurgical inner
      match contract.lower inner value with
      | .ok value => return (value, root)
      | .error error => throw (.unsupportedExpr error)
    let kvmap ← compileKVMap kvData
    let (innerResult, innerRoot) ← compileExprSurgical inner
    let root ← allocArenaNode (.mdata #[kvmap] innerRoot)
    pure (innerResult, root)

  | .fvar _ _ => throw (.unsupportedExpr "free variable")
  | .mvar _ _ => throw (.unsupportedExpr "metavariable")

  -- Store in block-local cache
  modifyBlockState fun c => { c with exprCache := c.exprCache.insert e (result, root) }

  pure (result, root)

/-- Compile an App telescope (Rust compile.rs:751-1407).

    Mirrors Rust's flattened-telescope semantics EXACTLY: the whole spine
    is collected in one pass, call-site surgery is checked on a bare-Const
    head, and the normal path compiles `head, arg₁, app-node, arg₂,
    app-node, …` WITHOUT cache-checking or caching the inner partial-spine
    App nodes — only the outermost App (our caller `compileExpr`) is
    cached, matching Rust's `Frame::Compile`/`Frame::Cache` granularity.
    Inner-spine caching would diverge from Rust's arena layout: a later
    occurrence of a partial spine as a maximal subterm would reuse a
    cached arena root instead of re-allocating metadata nodes. -/
partial def compileAppSpine (e : Expr) : CompileM (Ixon.Expr × UInt64) := do
  let (headExpr, args) := Ix.AuxGen.collectLeanTelescope e
  if let .const name lvls _ := headExpr then
    let cenv ← getCompileEnv
    -- Call-site surgery guard (compile.rs:800-838). Surgery applies iff:
    --  (1) the compiling constant is *not* an AuxRegen name — one of the
    --      Lean auto-generated auxiliaries we ourselves regenerate. The
    --      regenerator emits those bodies in canonical order by
    --      construction, so surgery would permute already-canonical args
    --      into the wrong positions. The guard is name-based (not a
    --      cache flag) because AuxRegen names compile twice: as Lean
    --      originals via `compileMutualBlock` and as regenerated
    --      canonicals via `compileAuxBlock`. The suffix alone is NOT
    --      sufficient: an EVAPORATED aux has no regenerated canonical —
    --      its surgered original IS its canonical form. "Has a
    --      regen/alias" is membership in the aux name→addr maps (fresh
    --      compiles) or `Named.original.isSome` (deserialized states,
    --      set by promote). Evaporated names enter neither.
    --  (2) the head has a non-identity surgery plan.
    let compiling := (← getBlockEnv).current
    let compilingIsAuxRegen ← do
      if Ix.AuxGen.isAuxGenSuffix compiling then
        let bstate ← getBlockState
        if bstate.auxNameToAddr.contains compiling then
          pure true
        else if cenv.auxNameToAddr.contains compiling then
          pure true
        else
          pure (match cenv.nameToNamed.get? compiling with
            | some named => named.original.isSome
            | none => false)
      else
        pure false
    if !compilingIsAuxRegen then
      if let some plan := cenv.callSitePlans.get? name then
        if !plan.isIdentity then
          if let some hr := plan.headRewrite then
            return ← compileHeadRewriteCallSite name lvls plan hr headExpr args
          else
            if args.size >= plan.minimalFullPrefix then
              return ← compileRecCallSite name lvls plan headExpr args
      if let some plan := cenv.belowCallSitePlans.get? name then
        if !plan.isIdentity then
          -- `.below`/`.below_N` HEADS need the indices+major floor; a
          -- Prop-below FAMILY member (ctor / `.below.casesOn`) has no
          -- floor — a field-less below ctor is fully applied at exactly
          -- params+motives (compile.rs below-family branch).
          if args.size >= plan.belowMinimalFullPrefix then
            return ← compileBelowCallSite name plan headExpr args
      if let some plan := cenv.brecOnCallSitePlans.get? name then
        if !plan.isIdentity then
          let expectedTotal := plan.brecOnMinimalFullPrefix
          if args.size >= expectedTotal then
            return ← compileBRecOnCallSite name plan headExpr args
      if ← etaAdapterNeeded name args.size then
        let (wrapper, nSynth) ← synthesizeEtaCallSite name lvls args
        let (wrapperIxon, wrapperRoot) ← compileExprSurgical wrapper
        return ← finishEtaCallSite wrapperIxon wrapperRoot nSynth args.size
  -- Normal telescope path (compile.rs:1399-1407): head, then one App
  -- node per arg. Same result as one-App-at-a-time recursion, but the
  -- inner spine nodes never touch the expression cache.
  let (h, hRoot) ← compileExprSurgical headExpr
  let mut acc := h
  let mut accRoot := hRoot
  for arg in args do
    let (a, aRoot) ← compileExprSurgical arg
    let root ← allocArenaNode (.app accRoot aRoot)
    acc := .app acc a
    accRoot := root
  pure (acc, accRoot)

/-- Shared call-site build tail (Rust `Frame::BuildCallSite`,
    compile.rs:1586-1668): compile the canonical head, the canonical args
    (in canonical order), and the collapsed args (in source-collapse
    order); append the collapsed Ixon expressions to the constant's
    surgery-sharing accumulator; fill each entry's metadata root
    (Kept → canonical root at its `canonIdx`, Collapsed → sequential
    collapsed root + absolute sharing index); allocate the `callSite`
    arena node; and fold the canonical Ixon App spine.

    When `origHeadCollapsed`, the LAST collapsed slot is the original
    (pre-rewrite) head expression — it has no source-order entry, so the
    sequential fill never reaches it; it is referenced by the node's
    `origHead` field instead. The head's own arena root is intentionally
    dropped (subsumed by `CallSite.name`, compile.rs:1633) — which is
    why any level-spelling patch keyed by it is CLONED onto the
    `callSite` root below (canonicity §10.6): replay consumers (the
    decompiler's head rebuild, the kernel's meta-ingress head arms) have
    only the callSite root in hand. -/
partial def buildCallSite (nameAddr : Address) (headForCanon : Expr)
    (sortedCanon : Array Expr) (collapsedArgs : Array Expr)
    (entries : Array Ixon.CallSiteEntry) (origHeadCollapsed : Bool)
    (checks : Array Ix.AuxGen.CollapseCheck) (headName : Name) :
    CompileM (Ixon.Expr × UInt64) := do
  let (headIxon, headRoot) ← match headForCanon with
    | .const name lvls _ => compileConstExprRaw name lvls
    | _ => throw (.invalidMutualBlock "call-site canonical head is not a Const")
  let mut canonicalExprs : Array Ixon.Expr := #[]
  let mut canonicalRoots : Array UInt64 := #[]
  for arg in sortedCanon do
    let (a, aRoot) ← compileExprSurgical arg
    canonicalExprs := canonicalExprs.push a
    canonicalRoots := canonicalRoots.push aRoot
  let mut collapsedIxon : Array Ixon.Expr := #[]
  let mut collapsedRoots : Array UInt64 := #[]
  for arg in collapsedArgs do
    let (a, aRoot) ← compileExprSurgical arg
    collapsedIxon := collapsedIxon.push a
    collapsedRoots := collapsedRoots.push aRoot
  -- A collapse drop is sound only when the dropped argument compiles to the
  -- same Ixon as the kept argument at its canonical slot (the two members
  -- share one projection address, so motives written over `A` and `B`
  -- agree here). Otherwise the rebuilt spine would run the kept member's
  -- code at the dropped member's nodes (A0, WB-B4; Rust `BuildCallSite`).
  let checks := if (← getBlockEnv).provenanceOnly then #[] else checks
  for check in checks do
    let slotExpr : Ix.AuxGen.ArgSlot → Option Ixon.Expr
      | .canon i => canonicalExprs[i]?
      | .collapsed i => collapsedIxon[i]?
    match slotExpr check.dropped, slotExpr check.kept with
    | some dropped, some kept =>
      if dropped != kept then
        throw (.invalidMutualBlock s!"{Ix.AuxGen.collapseDropError}: compiling \
'{(← getBlockEnv).current.pretty}', call-site head '{headName.pretty}': dropped \
{check.what} #{check.src} differs from the kept {check.what} #{check.keptSrc}")
    | _, _ =>
      throw (.invalidMutualBlock s!"{Ix.AuxGen.collapseDropError}: compiling \
'{(← getBlockEnv).current.pretty}', call-site head '{headName.pretty}': \
{check.what} #{check.src} has no compiled argument")
  -- Store collapsed arg expressions in surgery sharing (compile.rs:1637).
  let sharingBase := (← getBlockState).surgerySharing.size
  modifyBlockState fun c =>
    { c with surgerySharing := c.surgerySharing ++ collapsedIxon }
  -- Fill `meta` fields and absolute sharing indices (compile.rs:1640-1665).
  -- Kept entries index `canonicalRoots` by `canonIdx` — their canonical
  -- position — NOT by source-sequential order (the two coincide only
  -- under identity plans, which surgery short-circuits).
  let mut filled : Array Ixon.CallSiteEntry := #[]
  let mut collapsedIdx : Nat := 0
  for entry in entries do
    match entry with
    | .kept canonIdx _ =>
      filled := filled.push (.kept canonIdx canonicalRoots[canonIdx.toNat]!)
    | .collapsed _ _ =>
      filled := filled.push (.collapsed (sharingBase + collapsedIdx).toUInt64
        collapsedRoots[collapsedIdx]!)
      collapsedIdx := collapsedIdx + 1
  let origHead : Option (UInt64 × UInt64) :=
    if origHeadCollapsed && collapsedArgs.size > 0 then
      some ((sharingBase + collapsedArgs.size - 1).toUInt64,
        collapsedRoots[collapsedArgs.size - 1]!)
    else
      none
  let root ← allocArenaNode (.callSite nameAddr filled canonicalRoots origHead)
  -- Canonicity §10.6: clone the head's level-spelling patch (if any)
  -- onto the callSite root (see the docstring). Clone, not move — the
  -- head root may be a shared expr-cache root serving other occurrences.
  if let some headPatch :=
      (← getBlockState).univPatches.find? (·.arenaIdx == headRoot) then
    pushUnivPatch root headPatch.univIdxs
  let mut ixon := headIxon
  for a in canonicalExprs do
    ixon := .app ixon a
  pure (ixon, root)

/-- Normal (non-head-rewrite) `.rec` call-site surgery
    (compile.rs:1017-1160): separate source args into kept/collapsed per
    plan, reorder kept args to canonical positions, adapt kept minors
    whose fields target out-of-block SCCs, compile everything through
    `buildCallSite`. -/
partial def compileRecCallSite (name : Name) (lvls : Array Level)
    (plan : Ix.AuxGen.CallSitePlan) (headExpr : Expr) (args : Array Expr) :
    CompileM (Ixon.Expr × UInt64) := do
  compileName name
  let nameAddr := name.getHash
  let params := args.extract 0 plan.nParams
  let motives := args.extract plan.nParams (plan.nParams + plan.nSourceMotives)
  let minors := args.extract (plan.nParams + plan.nSourceMotives)
    (plan.nParams + plan.nSourceMotives + plan.nSourceMinors)
  let tail := args.extract
    (plan.nParams + plan.nSourceMotives + plan.nSourceMinors) args.size

  let nCanonMotives := plan.nCanonicalMotives
  let nCanonMinors := plan.nCanonicalMinors
  let mut canonicalArgs : Array (Nat × Expr) := #[]
  let mut collapsedArgs : Array Expr := #[]
  let mut entries : Array Ixon.CallSiteEntry := #[]
  let mut motiveSlots : Array Ix.AuxGen.ArgSlot := #[]
  let mut minorSlots : Array Ix.AuxGen.ArgSlot := #[]

  -- Params: always kept, identity mapping.
  for (p, i) in params.zipIdx do
    canonicalArgs := canonicalArgs.push (i, p)
    entries := entries.push (.kept i.toUInt64 0)

  -- Motives: kept or collapsed per plan.
  let canonBase := plan.nParams
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := canonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, motive)
      motiveSlots := motiveSlots.push (.canon canonPos)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      motiveSlots := motiveSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push motive

  -- Minors: kept (possibly split-adapted) or collapsed per plan. An
  -- adapted minor compiles at the canonical position while the ORIGINAL
  -- minor is preserved as a Collapsed sharing entry for decompile.
  let minorCanonBase := plan.nParams + nCanonMotives
  let env := (← getCompileEnv).env
  for (minor, srcI) in minors.zipIdx do
    if plan.minorKeep[srcI]! then
      let canonPos := minorCanonBase + plan.sourceToCanonMinor[srcI]!
      let adaptedMinor := Ix.AuxGen.adaptSplitMinor name lvls plan srcI minor
        params motives minors env
      let minorArg := adaptedMinor.getD minor
      canonicalArgs := canonicalArgs.push (canonPos, minorArg)
      if adaptedMinor.isSome then
        minorSlots := minorSlots.push (.collapsed collapsedArgs.size)
        entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
        collapsedArgs := collapsedArgs.push minor
      else
        minorSlots := minorSlots.push (.canon canonPos)
        entries := entries.push (.kept canonPos.toUInt64 0)
    else
      minorSlots := minorSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push minor

  -- Tail (indices + major): always kept, identity.
  let tailCanonBase := plan.nParams + nCanonMotives + nCanonMinors
  for (t, i) in tail.zipIdx do
    canonicalArgs := canonicalArgs.push (tailCanonBase + i, t)
    entries := entries.push (.kept (tailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  let checks ← callSiteCollapseChecks name #[
    ("motive", plan.motiveKeep, plan.sourceToCanonMotive, plan.sourceInBlock,
      motiveSlots),
    ("minor", plan.minorKeep, plan.sourceToCanonMinor, plan.minorInBlock,
      minorSlots)]
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false checks
    name

/-- Evaporated-aux head-rewrite call-site surgery (compile.rs:844-1015):
    the callee's claim is aliased to the external inductive's recursor,
    so the over-merged spine is rebuilt onto that telescope —
    `specs… motive minors′… indices… major` — with the level list
    extended to the target's arity. Dropped args are preserved as
    Collapsed entries; the head keeps its SOURCE name (the alias resolves
    it to the external recursor's address) but carries the target's level
    list, and the ORIGINAL head lands as the last sharing entry
    (`origHead`). -/
partial def compileHeadRewriteCallSite (name : Name) (lvls : Array Level)
    (plan : Ix.AuxGen.CallSitePlan) (hr : Ix.AuxGen.AuxHeadRewrite)
    (headExpr : Expr) (args : Array Expr) : CompileM (Ixon.Expr × UInt64) := do
  let expectedTotal := plan.nParams + plan.nSourceMotives
    + plan.nSourceMinors + plan.nIndices + 1 -- major
  if args.size < expectedTotal then
    throw (.invalidMutualBlock s!"head-rewrite call site for \
'{name.pretty}' is under-applied: {args.size} args, telescope needs \
{expectedTotal}")
  let env := (← getCompileEnv).env
  compileName name
  let nameAddr := name.getHash
  let params := args.extract 0 plan.nParams
  let motives := args.extract plan.nParams (plan.nParams + plan.nSourceMotives)
  let minors := args.extract (plan.nParams + plan.nSourceMotives)
    (plan.nParams + plan.nSourceMotives + plan.nSourceMinors)
  let tail := args.extract
    (plan.nParams + plan.nSourceMotives + plan.nSourceMinors) args.size
  let (targetLevels, specs) ←
    match Ix.AuxGen.deriveHeadRewriteApp name lvls hr params motives env with
    | .ok v => pure v
    | .error msg =>
      throw (.invalidMutualBlock s!"head-rewrite for '{name.pretty}': {msg}")

  let mut canonicalArgs : Array Expr := #[]
  let mut collapsedArgs : Array Expr := #[]
  let mut entries : Array Ixon.CallSiteEntry := #[]
  let mut motiveSlots : Array Ix.AuxGen.ArgSlot := #[]
  let mut minorSlots : Array Ix.AuxGen.ArgSlot := #[]

  -- Source params don't appear in the target spine (the specs subsume
  -- them) — collapse for reconstruction.
  for p in params do
    entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
    collapsedArgs := collapsedArgs.push p
  let nSpecs := specs.size
  canonicalArgs := canonicalArgs ++ specs
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      motiveSlots := motiveSlots.push (.canon canonicalArgs.size)
      canonicalArgs := canonicalArgs.push motive
      entries := entries.push (.kept nSpecs.toUInt64 0)
    else
      motiveSlots := motiveSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push motive
  for (minor, srcI) in minors.zipIdx do
    if plan.minorKeep[srcI]! then
      let canonPos := canonicalArgs.size
      let adaptedMinor := Ix.AuxGen.adaptSplitMinor name lvls plan srcI minor
        params motives minors env
      let minorArg := adaptedMinor.getD minor
      canonicalArgs := canonicalArgs.push minorArg
      if adaptedMinor.isSome then
        minorSlots := minorSlots.push (.collapsed collapsedArgs.size)
        entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
        collapsedArgs := collapsedArgs.push minor
      else
        minorSlots := minorSlots.push (.canon canonPos)
        entries := entries.push (.kept canonPos.toUInt64 0)
    else
      minorSlots := minorSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push minor
  for t in tail do
    let canonPos := canonicalArgs.size
    canonicalArgs := canonicalArgs.push t
    entries := entries.push (.kept canonPos.toUInt64 0)

  -- Preserve the ORIGINAL head (source name + source level args) as the
  -- LAST sharing entry so decompile can restore it (compile.rs:983).
  collapsedArgs := collapsedArgs.push headExpr
  let headForCanon := Expr.mkConst name targetLevels
  let checks ← callSiteCollapseChecks name #[
    ("motive", plan.motiveKeep, plan.sourceToCanonMotive, plan.sourceInBlock,
      motiveSlots),
    ("minor", plan.minorKeep, plan.sourceToCanonMinor, plan.minorInBlock,
      minorSlots)]
  buildCallSite nameAddr headForCanon canonicalArgs collapsedArgs entries true
    checks name

/-- `.below`-family call-site surgery (compile.rs below-family branch).
    HEAD telescope is `params, motives, indices, major`; a Prop-below
    FAMILY member (ctor / `.below.casesOn`) starts with the below params
    (parent params, then parent motives). In both shapes everything
    after the motive segment is kept identically, so one identity tail
    covers indices+major, ctor fields, and casesOn
    target-motive+indices+major+minors alike — the caller enforces the
    per-shape application floor. -/
partial def compileBelowCallSite (name : Name)
    (plan : Ix.AuxGen.BRecOnCallSitePlan) (headExpr : Expr)
    (args : Array Expr) : CompileM (Ixon.Expr × UInt64) := do
  compileName name
  let nameAddr := name.getHash
  let params := args.extract 0 plan.nParams
  let motives := args.extract plan.nParams (plan.nParams + plan.nSourceMotives)
  let tail := args.extract (plan.nParams + plan.nSourceMotives) args.size

  let nCanonMotives := plan.nCanonicalMotives
  let mut canonicalArgs : Array (Nat × Expr) := #[]
  let mut collapsedArgs : Array Expr := #[]
  let mut entries : Array Ixon.CallSiteEntry := #[]
  let mut motiveSlots : Array Ix.AuxGen.ArgSlot := #[]

  for (p, i) in params.zipIdx do
    canonicalArgs := canonicalArgs.push (i, p)
    entries := entries.push (.kept i.toUInt64 0)

  let motiveCanonBase := plan.nParams
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := motiveCanonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, motive)
      motiveSlots := motiveSlots.push (.canon canonPos)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      motiveSlots := motiveSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push motive

  let tailCanonBase := plan.nParams + nCanonMotives
  for (t, i) in tail.zipIdx do
    canonicalArgs := canonicalArgs.push (tailCanonBase + i, t)
    entries := entries.push (.kept (tailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  let checks ← callSiteCollapseChecks name #[
    ("motive", plan.motiveKeep, plan.sourceToCanonMotive, plan.sourceInBlock,
      motiveSlots)]
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false checks
    name

/-- `.brecOn` call-site surgery (compile.rs:1265-1396): telescope is
    `params, motives, indices, major, handlers` — one handler per motive,
    keyed by the SAME motive keep/permutation as the motives band. -/
partial def compileBRecOnCallSite (name : Name)
    (plan : Ix.AuxGen.BRecOnCallSitePlan) (headExpr : Expr)
    (args : Array Expr) : CompileM (Ixon.Expr × UInt64) := do
  let fixedTailLen := plan.nIndices + 1 -- indices + major
  let expectedTotal := plan.nParams + plan.nSourceMotives + fixedTailLen
    + plan.nSourceMotives
  compileName name
  let nameAddr := name.getHash
  let params := args.extract 0 plan.nParams
  let motives := args.extract plan.nParams (plan.nParams + plan.nSourceMotives)
  let fixedTail := args.extract (plan.nParams + plan.nSourceMotives)
    (plan.nParams + plan.nSourceMotives + fixedTailLen)
  let handlers := args.extract
    (plan.nParams + plan.nSourceMotives + fixedTailLen) expectedTotal
  let extraTail := args.extract expectedTotal args.size

  let nCanonMotives := plan.nCanonicalMotives
  let mut canonicalArgs : Array (Nat × Expr) := #[]
  let mut collapsedArgs : Array Expr := #[]
  let mut entries : Array Ixon.CallSiteEntry := #[]
  let mut motiveSlots : Array Ix.AuxGen.ArgSlot := #[]
  let mut handlerSlots : Array Ix.AuxGen.ArgSlot := #[]

  for (p, i) in params.zipIdx do
    canonicalArgs := canonicalArgs.push (i, p)
    entries := entries.push (.kept i.toUInt64 0)

  let motiveCanonBase := plan.nParams
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := motiveCanonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, motive)
      motiveSlots := motiveSlots.push (.canon canonPos)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      motiveSlots := motiveSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push motive

  let fixedTailCanonBase := plan.nParams + nCanonMotives
  for (t, i) in fixedTail.zipIdx do
    canonicalArgs := canonicalArgs.push (fixedTailCanonBase + i, t)
    entries := entries.push (.kept (fixedTailCanonBase + i).toUInt64 0)

  let handlerCanonBase := fixedTailCanonBase + fixedTailLen
  for (handler, srcI) in handlers.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := handlerCanonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, handler)
      handlerSlots := handlerSlots.push (.canon canonPos)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      handlerSlots := handlerSlots.push (.collapsed collapsedArgs.size)
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push handler

  let extraTailCanonBase := handlerCanonBase + nCanonMotives
  for (t, i) in extraTail.zipIdx do
    canonicalArgs := canonicalArgs.push (extraTailCanonBase + i, t)
    entries := entries.push (.kept (extraTailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  let checks ← callSiteCollapseChecks name #[
    ("motive", plan.motiveKeep, plan.sourceToCanonMotive, plan.sourceInBlock,
      motiveSlots),
    ("handler", plan.motiveKeep, plan.sourceToCanonMotive, plan.sourceInBlock,
      handlerSlots)]
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false checks
    name

end

/-- Pass 3: the placeholder indices of the rewritten call sites in `e`
    (`[(_ix.inline, n)]` mdata nodes), in first-occurrence order, each once.
    The walk visits every distinct node once. -/
def pass3Placeholders (e : Expr) : Array Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut out : Array Nat := #[]
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .mdata kvs inner _ =>
      if let #[(k, .ofNat n)] := kvs then
        if k == Ix.Compile.Pass.inlineKey && !out.contains n then out := out.push n
      stack := stack.push inner
    | .app f a _ => stack := stack.push a |>.push f
    | .lam _ t b _ _ | .forallE _ t b _ _ => stack := stack.push b |>.push t
    | .letE _ t v b _ _ => stack := stack.push b |>.push v |>.push t
    | .proj _ _ s _ => stack := stack.push s
    | _ => pure ()
  return out

/-- Pass 3: compile the decompile record of every rewritten call site of
    `e` that the current constant has not compiled yet: its source
    occurrence (`CompileEnv.p3Sources`), into `metaSharing`, with
    references and universes outside the primary tables in the extension
    tables (`p3MetaMode`). The expression cache is saved and restored
    around it, so no metadata-only form is ever reused by the term. -/
def pass3CompileRecords (e : Expr) : CompileM Unit := do
  let cenv ← getCompileEnv
  for n in pass3Placeholders e do
    if (← getBlockState).p3Records.contains n then continue
    let some src := cenv.p3Sources.get? n
      | throw (.invalidMutualBlock s!"Pass 3: no source occurrence for call-site record {n}")
    let savedCache := (← getBlockState).exprCache
    modifyBlockState fun c => { c with p3MetaMode := true }
    let (ix, root) ← compileExprSurgical src
    modifyBlockState fun c => { c with
      p3MetaMode := false
      exprCache := savedCache
      p3Records := c.p3Records.insert n (c.surgerySharing.size, root)
      surgerySharing := c.surgerySharing.push ix }

/-- Production expression compiler.  Environments without any call-site
    plans use the total ordinary implementation, while plan-bearing
    environments retain the existing surgery state machine.  The split gives
    the ordinary refinement proof kernel-visible equations without changing
    surgery behavior.

    Under Pass 3 the block's terms were rewritten before compilation
    (`Ix.Compile.Pass.Translate`): no plan is ever registered, so the
    ordinary implementation runs, after the decompile records of the
    rewritten call sites in `e` are compiled (`pass3CompileRecords`). -/
def compileExpr (e : Expr) : CompileM (Ixon.Expr × UInt64) := do
  let cenv ← getCompileEnv
  if cenv.pass3 && !cenv.p3Sources.isEmpty then
    pass3CompileRecords e
  -- Under Pass 3 no plan exists, so `surgeryFree` holds everywhere, but the
  -- ordinary implementation sizes its fuel with `exprCompileDepth`, a tree
  -- walk that is exponential on the DAG-shaped proofs of a library (a
  -- Mathlib theorem never finishes). The plan-bearing implementation, with an
  -- empty plan map, takes its ordinary path on every node and gives the same
  -- bytes (it is what every library compile with a changed block runs today).
  if cenv.surgeryFree && !cenv.pass3 then
    compileExprNoSurgery e
  else
    compileExprSurgical e

/-! ## Table Preseeding

Mirrors Rust `preseed_expr_tables` (crates/compile/src/compile.rs:576):
before compiling a block, walk every expression the block will compile,
collect all external refs (consts, nat/str literal blobs, proj type
addresses) and all universes, then intern them into the block tables in
CANONICAL SORTED order — refs by address bytes, univs by their serialized
encoding (`univ_sort_key`, compile.rs:476). Table indices thereby become
traversal-order-independent; the on-the-fly interning during actual
compilation then always finds the preseeded entries. Without this pass,
ref/univ indices depend on compile traversal order and every nontrivial
constant's serialized form (hence address) diverges from Rust's. -/

/-- Blake3 key over a univ-param context: hash of the concatenated
    32-byte name hashes. Mirrors Rust `univ_params_key` (compile.rs:482). -/
def univParamsKey (univParams : List Name) : Address := Id.run do
  let mut buf := ByteArray.empty
  for n in univParams do
    buf := buf ++ n.getHash.hash
  return Address.blake3 buf

/-- Sort key for preseeded universes: the serialized encoding. Mirrors
    Rust `univ_sort_key` (compile.rs:476). -/
def univSortKey (u : Ixon.Univ) : ByteArray :=
  Ixon.runPut (Ixon.putUniv u)

/-- Byte-loop lexicographic ByteArray comparison (same convention as
    `Address.cmpBytes`; Rust `Vec<u8>` `Ord`). -/
def byteArrayCmp (x y : ByteArray) : Ordering := Id.run do
  let n := min x.size y.size
  for i in [0:n] do
    let xi := x[i]!
    let yi := y[i]!
    if xi < yi then return .lt
    if xi > yi then return .gt
  return compare x.size y.size

/-- Accumulator shared by the proof-visible and iterative preseed walks. -/
abbrev ExprTableCollection :=
  Array Address × Array Ixon.Univ ×
    Std.HashMap (Address × Address) Unit

/-- Compile one source level list and append its positional universes in
    source order. This is the proof-visible counterpart of the tight array
    loop used by the runtime collector. -/
def collectExprTableUnivs : List Level → Array Ixon.Univ →
    CompileM (Array Ixon.Univ)
  | [], univs => pure univs
  | lvl :: lvls, univs => do
    let u ← compileUniv lvl
    collectExprTableUnivs lvls (univs.push u)

/-- Structurally recursive semantics of the expression-table collection
    walk. Children are visited in the same preorder as the production stack
    machine: function before argument, binder type before body, and let type,
    value, then body. The seen set preserves the Rust digest/context dedup. -/
def collectExprTablesStructural (ctxKey : Address) (mutCtx : MutCtx) :
    (e : Expr) → ExprTableCollection → CompileM ExprTableCollection
  | e, (refs, univs, seen) => do
    let key := (e.getHash, ctxKey)
    if seen.contains key then
      return (refs, univs, seen)
    let seen := seen.insert key ()
    match e with
    | .bvar .. => pure (refs, univs, seen)
    | .sort lvl _ =>
      pure (refs, univs.push (← compileUniv lvl), seen)
    | .const name lvls _ =>
      let univs ← collectExprTableUnivs lvls.toList univs
      if (mutCtx.get? name).isNone then
        pure (refs.push (← lookupConstAddr name), univs, seen)
      else
        pure (refs, univs, seen)
    | .app func arg _ =>
      let acc ← collectExprTablesStructural ctxKey mutCtx func
        (refs, univs, seen)
      collectExprTablesStructural ctxKey mutCtx arg acc
    | .lam _ ty body _ _ =>
      let acc ← collectExprTablesStructural ctxKey mutCtx ty
        (refs, univs, seen)
      collectExprTablesStructural ctxKey mutCtx body acc
    | .forallE _ ty body _ _ =>
      let acc ← collectExprTablesStructural ctxKey mutCtx ty
        (refs, univs, seen)
      collectExprTablesStructural ctxKey mutCtx body acc
    | .letE _ ty val body _ _ =>
      let acc ← collectExprTablesStructural ctxKey mutCtx ty
        (refs, univs, seen)
      let acc ← collectExprTablesStructural ctxKey mutCtx val acc
      collectExprTablesStructural ctxKey mutCtx body acc
    | .lit (.natVal n) _ =>
      let bytes := ByteArray.mk (Nat.toBytesLE n)
      let addr := Address.blake3 bytes
      modifyBlockState fun c =>
        { c with blockBlobs := c.blockBlobs.insert addr bytes }
      pure (refs.push addr, univs, seen)
    | .lit (.strVal s) _ =>
      let bytes := s.toUTF8
      let addr := Address.blake3 bytes
      modifyBlockState fun c =>
        { c with blockBlobs := c.blockBlobs.insert addr bytes }
      pure (refs.push addr, univs, seen)
    | .proj typeName _ struct _ =>
      let refs := refs.push (← lookupConstAddr typeName)
      collectExprTablesStructural ctxKey mutCtx struct
        (refs, univs, seen)
    | .mdata _ inner _ =>
      collectExprTablesStructural ctxKey mutCtx inner
        (refs, univs, seen)
    | .fvar .. => throw (.unsupportedExpr "free variable")
    | .mvar .. => throw (.unsupportedExpr "metavariable")
termination_by e _ => e

/-- Stack-safe runtime implementation of `collectExprTables`. Its stack push
    order implements exactly the preorder of `collectExprTablesStructural`. -/
private unsafe def collectExprTablesImpl (top : Expr) (ctxKey : Address)
    (acc : ExprTableCollection) : CompileM ExprTableCollection := do
  let mutCtx := (← getBlockEnv).mutCtx
  let mut (refs, univs, seen) := acc
  let mut stack : Array Expr := #[top]
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    let key := (e.getHash, ctxKey)
    if seen.contains key then continue
    seen := seen.insert key ()
    match e with
    | .bvar .. => pure ()
    | .sort lvl _ =>
      univs := univs.push (← compileUniv lvl)
    | .const name lvls _ =>
      for lvl in lvls do
        univs := univs.push (← compileUniv lvl)
      if (mutCtx.get? name).isNone then
        refs := refs.push (← lookupConstAddr name)
    | .app func arg _ =>
      stack := stack.push arg |>.push func
    | .lam _ ty body _ _ =>
      stack := stack.push body |>.push ty
    | .forallE _ ty body _ _ =>
      stack := stack.push body |>.push ty
    | .letE _ ty val body _ _ =>
      stack := stack.push body |>.push val |>.push ty
    | .lit (.natVal n) _ =>
      let bytes := ByteArray.mk (Nat.toBytesLE n)
      let addr := Address.blake3 bytes
      modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
      refs := refs.push addr
    | .lit (.strVal s) _ =>
      let bytes := s.toUTF8
      let addr := Address.blake3 bytes
      modifyBlockState fun c => { c with blockBlobs := c.blockBlobs.insert addr bytes }
      refs := refs.push addr
    | .proj typeName _ struct _ =>
      refs := refs.push (← lookupConstAddr typeName)
      stack := stack.push struct
    | .mdata _ inner _ =>
      stack := stack.push inner
    | .fvar .. => throw (.unsupportedExpr "free variable")
    | .mvar .. => throw (.unsupportedExpr "metavariable")
  pure (refs, univs, seen)

/-- Walk one expression collecting refs and univs for preseeding.
    Mirrors Rust `collect_expr_tables` (compile.rs:490), deduped by
    `(expr hash, univ-param-context key)`; nat/str literal blobs are stored as
    a side effect (their addresses join the refs), and universes are compiled
    through the shared `univCache`. The kernel sees the structurally recursive
    semantics, while generated code uses the equivalent iterative stack walk.
    Must run under the expression's own `univCtx` (Rust passes `univ_params`
    explicitly). -/
@[implemented_by collectExprTablesImpl]
def collectExprTables (top : Expr) (ctxKey : Address)
    (acc : ExprTableCollection) : CompileM ExprTableCollection := do
  let mutCtx := (← getBlockEnv).mutCtx
  collectExprTablesStructural ctxKey mutCtx top acc

/-- Collect a list of roots, resetting the context-sensitive universe cache
    before each root exactly as production `withUnivCtx` requires. -/
def collectPreseedExprs : List (Expr × List Name) → ExprTableCollection →
    CompileM ExprTableCollection
  | [], acc => pure acc
  | (e, params) :: rest, acc => do
    let acc ← withUnivCtx params
      (collectExprTables e (univParamsKey params) acc)
    collectPreseedExprs rest acc

/-- Intern adjacent-unique references from the canonically sorted list. -/
def internPreseedRefs : List Address → Option Address → CompileM Unit
  | [], _ => pure ()
  | addr :: rest, previous => do
    if previous != some addr then
      discard <| internRef addr
    internPreseedRefs rest (some addr)

/-- Canonicalize every collected positional universe in source order. -/
def canonPreseedUnivs : List Ixon.Univ → Array Ixon.Univ →
    CompileM (Array Ixon.Univ)
  | [], result => pure result
  | u :: rest, result => do
    let canon ← canonUnivCached u
    canonPreseedUnivs rest (result.push canon)

/-- Intern adjacent-unique universes from their canonically sorted serialized
    keys. `putUniv` is injective, so skipping an equal key skips the same
    universe value. -/
def internPreseedUnivs : List (ByteArray × Ixon.Univ) →
    Option ByteArray → CompileM Unit
  | [], _ => pure ()
  | (key, u) :: rest, previous => do
    if previous != some key then
      discard <| internUniv u
    internPreseedUnivs rest (some key)

/-- Preseed the block's ref/univ intern tables from the given
    `(expr, levelParams)` list, in canonical sorted order. Mirrors Rust
    `preseed_expr_tables` (compile.rs:576). Call sites mirror Rust's:
    every singleton path in `compileConstantInfo` and the mutual path in
    `compileMutualBlock`.

    The public body composes total recursive phases for refinement proofs;
    generated code uses the equivalent loop-based implementation below. -/
private unsafe def preseedExprTablesImpl
    (exprs : Array (Expr × List Name)) : CompileM Unit := do
  let mut refs : Array Address := #[]
  let mut univs : Array Ixon.Univ := #[]
  let mut seen : Std.HashMap (Address × Address) Unit := {}
  for (e, params) in exprs do
    let (r, u, s) ←
      withUnivCtx params (collectExprTables e (univParamsKey params) (refs, univs, seen))
    refs := r
    univs := u
    seen := s
  -- Refs: sort by address bytes, dedup, intern in order.
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  let mut prevRef : Option Address := none
  for a in sortedRefs do
    if prevRef != some a then
      discard <| internRef a
      prevRef := some a
  -- Univs: canonicalize (§10.6 — the primary table holds only
  -- `canonUniv`-fixed forms; the on-the-fly `compileAndInternUnivCanon`
  -- then always finds the preseeded canonical entry), sort by
  -- serialized key, dedup by key, intern in order (`put_univ` is
  -- injective, so key equality is univ equality).
  let mut canonUnivs : Array Ixon.Univ := Array.mkEmpty univs.size
  for u in univs do
    canonUnivs := canonUnivs.push (← canonUnivCached u)
  let keyed := canonUnivs.map fun u => (univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) => byteArrayCmp ka kb == .lt
  let mut prevKey : Option ByteArray := none
  for (k, u) in sortedUnivs do
    if prevKey != some k then
      discard <| internUniv u
      prevKey := some k
  modifyBlockState fun st => { st with univsFinal := true }

@[implemented_by preseedExprTablesImpl]
def preseedExprTables (exprs : Array (Expr × List Name)) : CompileM Unit := do
  let (refs, univs, _) ←
    collectPreseedExprs exprs.toList (#[], #[], {})
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  internPreseedRefs sortedRefs.toList none
  let canonUnivs ←
    canonPreseedUnivs univs.toList (Array.mkEmpty univs.size)
  let keyed := canonUnivs.map fun u => (univSortKey u, u)
  let sortedUnivs :=
    keyed.qsort fun (ka, _) (kb, _) => byteArrayCmp ka kb == .lt
  internPreseedUnivs sortedUnivs.toList none
  modifyBlockState fun st => { st with univsFinal := true }

/-- Source expressions of a recursor in production compilation order. -/
def recursorSourceExprs (recursorVal : RecursorVal) : List Expr :=
  recursorVal.cnst.type :: recursorVal.rules.toList.map (·.rhs)

def recursorPreseedExprs (recursorVal : RecursorVal) :
    Array (Expr × List Name) :=
  (recursorSourceExprs recursorVal).map
    (fun source => (source, recursorVal.cnst.levelParams.toList)) |>.toArray

/-- Source expressions of a standalone inductive family in production order. -/
def inductiveSourceExprs (inductiveVal : InductiveVal)
    (ctorVals : Array ConstructorVal) : List Expr :=
  inductiveVal.cnst.type :: ctorVals.toList.map (·.cnst.type)

/-- Exact standalone-inductive preseed inputs. Constructors retain their own
recorded universe-parameter contexts, matching mutual-block preseeding. -/
def inductivePreseedExprs (inductiveVal : InductiveVal)
    (ctorVals : Array ConstructorVal) : Array (Expr × List Name) :=
  #[(inductiveVal.cnst.type, inductiveVal.cnst.levelParams.toList)] ++
    ctorVals.map fun ctorVal =>
      (ctorVal.cnst.type, ctorVal.cnst.levelParams.toList)

/-- The `(expr, levelParams)` list a `MutConst` contributes to preseeding.
Mirrors Rust `collect_mut_const_exprs` (compile.rs:618). -/
def mutConstPreseedInputs (c : MutConst) : List (Expr × List Name) :=
  match c with
  | .defn d =>
    [(d.type, d.levelParams.toList), (d.value, d.levelParams.toList)]
  | .indc i =>
    (i.type, i.levelParams.toList) :: i.ctors.toList.map fun ctor =>
      (ctor.cnst.type, ctor.cnst.levelParams.toList)
  | .recr r =>
    (recursorSourceExprs r).map fun source =>
      (source, r.cnst.levelParams.toList)

def mutConstPreseedExprs (c : MutConst) : Array (Expr × List Name) :=
  (mutConstPreseedInputs c).toArray

/-! ## Classes and canonical order (Pass 1, `Ix.Compile.Canon`)

Step 1 of a block's compilation, the classes (collapse) and their canonical
order, is `Ix.Compile.Canon.sortClasses` under `Rules.compiler`: today's
rules (name-hash seed and least-name-hash representative, syntactic levels,
external references by address at the first difference, today's structural
nested order) with the two Lean-port comparator fixes on (mixed kinds by
kind tag; the comparison cache normalised to the key's orientation, design
document §3.4, C1 and C2). Neither fix is reachable on Lean input, so the
output is today's. The pure functions are the definition; what follows only
converts between them and `CompileM`. -/

/-- The compiled address of a constant as `lookupConstAddr` resolves it
(current block's primary registrations, the merged name map, the current
block's auxiliary registrations, the merged auxiliary map), as a pure
function of the current state. Sorting writes none of these maps, so a
snapshot taken before a sort answers every lookup the sort makes. -/
def constAddrLookup : CompileM (Name → Option Address) := do
  let env ← getCompileEnv
  let bstate ← getBlockState
  pure fun name =>
    match bstate.blockNameToAddr.get? name with
    | some addr => some addr
    | none =>
    match env.nameToAddr.get? name with
    | some addr => some addr
    | none =>
    match bstate.auxNameToAddr.get? name with
    | some addr => some addr
    | none => env.auxNameToAddr.get? name

/-- Resolve one inductive member's constructors for SCC collection. -/
def collectMutConstConstructors :
    List Name → Array ConstructorVal → CompileM (Array ConstructorVal)
  | [], acc => pure acc
  | name :: rest, acc => do
    match ← findConst name with
    | .ctorInfo ctor =>
      collectMutConstConstructors rest (acc.push ctor)
    | _ => throw (.invalidMutualBlock s!"Expected constructor: {name}")

/-- Create a MutConst.indc from an InductiveVal by fetching constructors. -/
def MutConst.mkIndc (i : InductiveVal) : CompileM MutConst := do
  let ctors ← collectMutConstConstructors i.ctors.toList #[]
  pure (.indc ⟨i.cnst.name, i.cnst.levelParams, i.cnst.type, i.numParams,
    i.numIndices, i.all, ctors, i.numNested, i.isRec, i.isReflexive,
    i.isUnsafe⟩)

/-- The classes of a block's members in canonical order, each class's
representative first: `Ix.Compile.Canon.sortClasses Rules.compiler`, with
external addresses from `constAddrLookup`. Pure: the comparison cache lives
inside the call, so nothing leaks into the block state. -/
def sortConstsCore (sources : List MutConst) : CompileM (List (List MutConst)) := do
  let addr? ← constAddrLookup
  match Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addr? sources with
  | .ok (classes, _) => pure classes
  | .error e => throw (.invalidMutualBlock s!"sortConsts: {e}")

/-- The declared flat position of a recursor in its family: `X.rec` of the
`i`-th member of `RecursorVal.all` is at `i`, and the nested auxiliary
recursor `all[0].rec_N` at `all.size + N - 1` (`u64::MAX` otherwise).
Mirrors Rust `recursor_family_position`. -/
def recursorFamilyPosition (r : RecursorVal) : UInt64 :=
  match r.cnst.name with
  | .str parent "rec" _ =>
    match r.all.findIdx? (· == parent) with
    | some i => UInt64.ofNat i
    | none => 0xFFFFFFFFFFFFFFFF
  | .str parent s _ =>
    match (s.dropPrefix? "rec_").bind (·.toString.toNat?) with
    | some k =>
      if k ≥ 1 && r.all[0]? == some parent then UInt64.ofNat (r.all.size + k - 1)
      else 0xFFFFFFFFFFFFFFFF
    | none => 0xFFFFFFFFFFFFFFFF
  | _ => 0xFFFFFFFFFFFFFFFF

/-- A block of recursors is laid out in its family's flat order (the
order the kernel pairs with the inductive block's flat members), not in
`sortConsts` order; other blocks are returned unchanged. The regenerated
families get this from `compileAuxBlockWithRename`'s class-order key; this
applies the same rule to a recursor block compiled from Lean's own
declarations (`Named.original`, decompile's verification recompile), so
that on a block canonicalisation leaves unchanged Lean's form and the Ix
form of each recursor have one address (D6). Stable. Mirrors Rust
`order_recursor_family`. -/
def orderRecursorFamily (classes : List (List MutConst)) : List (List MutConst) :=
  if classes.isEmpty || !classes.all (·.all fun c => c matches .recr _) then classes
  else
    let key (cls : List MutConst) : UInt64 := cls.foldl (init := 0xFFFFFFFFFFFFFFFF)
      fun acc c => match c with
        | .recr r => min acc (recursorFamilyPosition r)
        | _ => acc
    let decorated := classes.toArray.zipIdx.map fun (cls, i) => (key cls, i, cls)
    let sorted := decorated.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
    (sorted.map (·.2.2)).toList

/-- `sortConstsCore`, timed as the classes phase (`Ix.PhaseTimers`). -/
def sortConsts (sources : List MutConst) : CompileM (List (List MutConst)) :=
  timedC .classes (sortConstsCore sources)

/-! ## Constant Building -/

/-- Expressions rewritten by production sharing for one mutual member, in
the cursor order `withRootExprs` writes them back. -/
def mutConstRootExprs : Ixon.MutConst → List Ixon.Expr
  | .defn definition => [definition.typ, definition.value]
  | .indc indInfo =>
    indInfo.typ :: indInfo.ctors.toList.map (·.typ)
  | .recr recursor =>
    recursor.typ :: recursor.rules.toList.map (·.rhs)

/-- Canonical production sharing roots for a `ConstantInfo`.  Projection
payloads contain no expressions, while mutual members are flattened in member
order. This is the order of `Ix.Sharing.Exact.constantInfoRoots`, which
`withRootExprs` consumes. -/
def constantInfoRootExprs : Ixon.ConstantInfo → Array Ixon.Expr
  | .defn definition =>
    (mutConstRootExprs (.defn definition)).toArray
  | .recr recursor =>
    (mutConstRootExprs (.recr recursor)).toArray
  | .axio axiomInfo => #[axiomInfo.typ]
  | .quot quotient => #[quotient.typ]
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => #[]
  | .muts members =>
    (members.toList.flatMap mutConstRootExprs).toArray

/-! ## Canonical sharing

The compiler builds every block Constant with the canonical sharing
construction `Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust
`canonical_sharing_tiered`), under the limits of `CompileEnv.sharingLimits`.
There is no fallback: every construction failure is a compile error. -/

/-- Resource limits of the compiler's canonical sharing construction: the
    library defaults (`Ix.Sharing.Exact.Limits`), a safety net far above every
    corpus maximum. `CompileEnv.sharingLimits` carries the limits a compile
    runs under. Mirrors Rust `compiler_sharing_limits`. -/
def compilerSharingLimits : Ix.Sharing.Exact.Limits := {}

/-- Environment variable carrying a sharing-limit override in the format of
    `Ix.Sharing.Exact.Limits.withOverrides` (for example `states=2^44,depth=2^22`
    or `unbounded`). `ix compile --sharing-limits` and `ix compile-lean
    --sharing-limits` set it. `compilerSharingLimitsFromEnv` reads it, once per
    run, in the Lean drivers `compileEnvParallelAux` and
    `Ix.DecompileM.decompileEnvFullParallel`; Rust's `compiler_sharing_limits`
    reads it once per compile or decompile entry point. -/
def sharingLimitsEnvVar : String := "IX_SHARING_LIMITS"

/-- `compilerSharingLimits` with the `IX_SHARING_LIMITS` override applied, or
    the parse error. -/
def compilerSharingLimitsFromEnv : IO (Except String Ix.Sharing.Exact.Limits) := do
  match ← IO.getEnv sharingLimitsEnvVar with
  | none => pure (.ok compilerSharingLimits)
  | some spec =>
    pure ((compilerSharingLimits.withOverrides spec).mapError (s!"{sharingLimitsEnvVar}: " ++ ·))

/-- A sharing-construction failure as a compile error: resource exhaustion is
    `resourceLimit` (naming the limit and its override), every other kind
    `sharingConstruction`. Mirrors Rust `sharing_compile_error`. -/
def sharingCompileError : Ix.Sharing.Exact.SharingError → CompileError
  | .resourceExhausted r limit =>
    .resourceLimit s!"canonical sharing: resource exhausted: {r.key} (limit {limit}); \
      raise it with --sharing-limits {r.key}=N ({sharingLimitsEnvVar})"
  | e => .sharingConstruction s!"canonical sharing: {e}"

/-- Write `rewrittenExprs` back into the root slots of `info`, in
    `constantInfoRootExprs` order: `Ix.Sharing.Exact.withRoots`, which fails
    unless there is exactly one expression per root, so no slot keeps its old
    value. -/
def withRootExprs (info : Ixon.ConstantInfo) (rewrittenExprs : Array Ixon.Expr) :
    Except CompileError Ixon.ConstantInfo :=
  (Ix.Sharing.Exact.withRoots info rewrittenExprs).mapError sharingCompileError

/-- Build a block Constant with the canonical sharing of its payload: the
    roots are `constantInfoRootExprs info`, shared by
    `Ix.Sharing.Exact.canonicalSharingTiered .tagN` under `limits`, and written
    back by `withRootExprs` (the construction must return one root per input
    root). There is no fallback: every failure is a compile error. -/
def buildConstantWithSharing (limits : Ix.Sharing.Exact.Limits)
    (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ) :
    Except CompileError Ixon.Constant := do
  let roots := constantInfoRootExprs info
  let r ← (Ix.Sharing.Exact.canonicalSharingTiered .tagN roots limits).mapError
    sharingCompileError
  unless r.result.roots.size == roots.size do
    throw (.sharingConstruction
      s!"canonical sharing: {r.result.roots.size} roots returned for {roots.size}")
  let info ← withRootExprs info r.result.roots
  pure { info, sharing := r.result.sharing, refs, univs }

/-- Lift a sharing result into `CompileM`. -/
def liftSharing (r : Except CompileError Ixon.Constant) : CompileM Ixon.Constant :=
  match r with
  | .ok c => pure c
  | .error e => throw e

/-- Build a block Constant with the compiler's canonical sharing under
    `CompileEnv.sharingLimits`. Every block the compiler emits goes through
    here. -/
def buildBlockConstant (info : Ixon.ConstantInfo) (refs : Array Address)
    (univs : Array Ixon.Univ) : CompileM Ixon.Constant := do
  liftSharing (buildConstantWithSharing (← read).1.sharingLimits info refs univs)

/-! ## Individual Constant Compilation -/

/-- Convert Lean DefinitionSafety to Ixon DefinitionSafety -/
def convertSafety : Lean.DefinitionSafety → DefinitionSafety
  | .unsafe => .unsaf
  | .safe => .safe
  | .partial => .part

def definitionValData (d : DefinitionVal) : Def :=
  { name := d.cnst.name
    levelParams := d.cnst.levelParams
    type := d.cnst.type
    kind := .defn
    value := d.value
    hints := d.hints
    safety := convertSafety d.safety
    all := d.all }

def theoremValData (d : TheoremVal) : Def :=
  { name := d.cnst.name
    levelParams := d.cnst.levelParams
    type := d.cnst.type
    kind := .thm
    value := d.value
    hints := .opaque
    safety := .safe
    all := d.all }

def opaqueValData (d : OpaqueVal) : Def :=
  { name := d.cnst.name
    levelParams := d.cnst.levelParams
    type := d.cnst.type
    kind := .opaq
    value := d.value
    hints := .opaque
    safety := if d.isUnsafe then .unsaf else .safe
    all := d.all }

/-- Finish already compiled definition-like type and value expressions: drain
per-constant metadata, record source and mutual-context names, assemble the
Ixon payload, and retain the appropriate reducibility hint. -/
def finishDefinitionDataCompilation (d : Def)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache

  -- Store name string components as blobs for deduplication
  compileName d.name
  compileNames d.levelParams
  compileNames d.all
  let mutNames := (← getBlockEnv).mutCtx.toList.toArray.map (·.1)
  compileNames mutNames

  let nameAddr := d.name.getHash
  let lvlAddrs := d.levelParams.map (·.getHash)
  let allAddrs := d.all.map (·.getHash)
  let ctxAddrs ← getMutCtxAddrs

  let defn : Ixon.Definition := {
    kind := d.kind
    safety := d.safety
    lvls := d.levelParams.size.toUInt64
    typ := typeExpr
    value := valueExpr
  }
  let hints := match d.kind with
    | .defn => d.hints
    | .thm | .opaq => .opaque
  recordDefHints d.name hints
  let constMeta := { Ixon.ConstantMeta.new
    (.defn nameAddr lvlAddrs allAddrs ctxAddrs arena typeRoot valueRoot) with
    metaSharing := surgerySharing, metaRefs, metaUnivs, univPatches }
  pure (defn, constMeta, typeExpr, valueExpr)

/-- Definition specialization of the common definition-like finalizer. -/
def finishDefinitionCompilation (d : DefinitionVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  finishDefinitionDataCompilation (definitionValData d)
    typeExpr typeRoot valueExpr valueRoot

/-- Theorem specialization of the common definition-like finalizer. -/
def finishTheoremCompilation (d : TheoremVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  finishDefinitionDataCompilation (theoremValData d)
    typeExpr typeRoot valueExpr valueRoot

/-- Opaque specialization of the common definition-like finalizer. -/
def finishOpaqueCompilation (d : OpaqueVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  finishDefinitionDataCompilation (opaqueValData d)
    typeExpr typeRoot valueExpr valueRoot

/-- Compile a definition to Ixon.Definition with metadata. -/
def compileDefinition (d : DefinitionVal) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  withCurrent d.cnst.name do
    withUnivCtx d.cnst.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr d.cnst.type
      let (valueExpr, valueRoot) ← compileExpr d.value
      finishDefinitionCompilation d typeExpr typeRoot valueExpr valueRoot

/-- Compile a theorem to Ixon.Definition with metadata. -/
def compileTheorem (d : TheoremVal) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  withCurrent d.cnst.name do
    withUnivCtx d.cnst.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr d.cnst.type
      let (valueExpr, valueRoot) ← compileExpr d.value
      finishTheoremCompilation d typeExpr typeRoot valueExpr valueRoot

/-- Compile an opaque to Ixon.Definition with metadata. -/
def compileOpaque (d : OpaqueVal) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  withCurrent d.cnst.name do
    withUnivCtx d.cnst.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr d.cnst.type
      let (valueExpr, valueRoot) ← compileExpr d.value
      finishOpaqueCompilation d typeExpr typeRoot valueExpr valueRoot

/-- Finish an already compiled axiom type: drain per-constant metadata,
record its source names, and assemble the Ixon payload and metadata. -/
def finishAxiomCompilation (a : AxiomVal) (typeExpr : Ixon.Expr)
    (typeRoot : UInt64) :
    CompileM (Ixon.Axiom × Ixon.ConstantMeta × Ixon.Expr) := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache

  -- Store name string components for deduplication
  compileName a.cnst.name
  compileNames a.cnst.levelParams

  let nameAddr := a.cnst.name.getHash
  let lvlAddrs := a.cnst.levelParams.map (·.getHash)

  let axio : Ixon.Axiom := {
    isUnsafe := a.isUnsafe
    lvls := a.cnst.levelParams.size.toUInt64
    typ := typeExpr
  }
  let constMeta := { Ixon.ConstantMeta.new
    (.axio nameAddr lvlAddrs arena typeRoot) with
    metaSharing := surgerySharing, metaRefs, metaUnivs, univPatches }
  pure (axio, constMeta, typeExpr)

/-- Compile an axiom to Ixon.Axiom with metadata. -/
def compileAxiom (a : AxiomVal) :
    CompileM (Ixon.Axiom × Ixon.ConstantMeta × Ixon.Expr) :=
  withCurrent a.cnst.name do
    withUnivCtx a.cnst.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr a.cnst.type
      finishAxiomCompilation a typeExpr typeRoot

/-- Convert Lean's quotient-declaration discriminator to its Ixon form. -/
def convertQuotKind : Lean.QuotKind → Ix.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- Finish an already compiled quotient type while preserving the primary
expression tables. -/
def finishQuotientCompilation (q : QuotVal) (typeExpr : Ixon.Expr)
    (typeRoot : UInt64) :
    CompileM (Ixon.Quotient × Ixon.ConstantMeta × Ixon.Expr) := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache

  compileName q.cnst.name
  compileNames q.cnst.levelParams

  let quot : Ixon.Quotient := {
    kind := convertQuotKind q.kind
    lvls := q.cnst.levelParams.size.toUInt64
    typ := typeExpr
  }
  let constMeta := { Ixon.ConstantMeta.new
    (.quot q.cnst.name.getHash
      (q.cnst.levelParams.map (·.getHash)) arena typeRoot) with
    metaSharing := surgerySharing, metaRefs, metaUnivs, univPatches }
  pure (quot, constMeta, typeExpr)

/-- Compile a quotient to Ixon.Quotient with metadata. -/
def compileQuotient (q : QuotVal) :
    CompileM (Ixon.Quotient × Ixon.ConstantMeta × Ixon.Expr) :=
  withCurrent q.cnst.name do
    withUnivCtx q.cnst.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr q.cnst.type
      finishQuotientCompilation q typeExpr typeRoot

/-- Compile a recursor rule to Ixon, returning the ctor address and rhs expression. -/
def compileRecursorRule (rule : RecursorRule) : CompileM (Ixon.RecursorRule × Address × UInt64) := do
  let (rhs, ruleRoot) ← compileExpr rule.rhs
  let ctorAddr := rule.ctor.getHash
  pure ({ fields := rule.nfields.toUInt64, rhs }, ctorAddr, ruleRoot)

/-- Accumulated rule payloads and metadata roots during recursor compilation. -/
structure RecursorRuleCompileState where
  rules : Array Ixon.RecursorRule := #[]
  ruleAddrs : Array Address := #[]
  ruleRoots : Array UInt64 := #[]

/-- Compile recursor rules in source order.  This proof-visible list fold is
extensionally the mutable array loop used by the original implementation. -/
def compileRecursorRules :
    List RecursorRule → RecursorRuleCompileState →
      CompileM RecursorRuleCompileState
  | [], acc => pure acc
  | rule :: rest, acc => do
    let (ixonRule, ctorAddr, ruleRoot) ← compileRecursorRule rule
    compileRecursorRules rest {
      rules := acc.rules.push ixonRule
      ruleAddrs := acc.ruleAddrs.push ctorAddr
      ruleRoots := acc.ruleRoots.push ruleRoot
    }

/-- Finish an already compiled recursor type and rule array while preserving
the primary expression tables. -/
def finishRecursorCompilation (r : RecursorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (compiledRules : RecursorRuleCompileState) :
    CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache

  -- Store name string components as blobs for deduplication
  compileName r.cnst.name
  compileNames r.cnst.levelParams
  compileNames r.all
  let mutNames := (← getBlockEnv).mutCtx.toList.toArray.map (·.1)
  compileNames mutNames
  compileNames (r.rules.map (·.ctor))

  let nameAddr := r.cnst.name.getHash
  let lvlAddrs := r.cnst.levelParams.map (·.getHash)
  let allAddrs := r.all.map (·.getHash)
  let ctxAddrs ← getMutCtxAddrs

  let recursor : Ixon.Recursor := {
    k := r.k
    isUnsafe := r.isUnsafe
    lvls := r.cnst.levelParams.size.toUInt64
    params := r.numParams.toUInt64
    indices := r.numIndices.toUInt64
    motives := r.numMotives.toUInt64
    minors := r.numMinors.toUInt64
    typ := typeExpr
    rules := compiledRules.rules
  }
  let constMeta := { Ixon.ConstantMeta.new
    (.recr nameAddr lvlAddrs compiledRules.ruleAddrs allAddrs ctxAddrs
      arena typeRoot compiledRules.ruleRoots) with
    metaSharing := surgerySharing, metaRefs, metaUnivs, univPatches }
  pure (recursor, constMeta, typeExpr)

/-- Compile a recursor to Ixon.Recursor with metadata. -/
def compileRecursor (r : RecursorVal) : CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) := withCurrent r.cnst.name do
  withUnivCtx r.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr r.cnst.type
    let compiledRules ← compileRecursorRules r.rules.toList {}
    finishRecursorCompilation r typeExpr typeRoot compiledRules

/-- Finish an already compiled constructor type while preserving the primary
expression tables. -/
def finishConstructorCompilation (c : ConstructorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    CompileM (Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr) := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache

  -- Store name string components as blobs for deduplication
  compileName c.cnst.name
  compileNames c.cnst.levelParams

  let nameAddr := c.cnst.name.getHash
  let lvlAddrs := c.cnst.levelParams.map (·.getHash)

  let ctor : Ixon.Constructor := {
    isUnsafe := c.isUnsafe
    lvls := c.cnst.levelParams.size.toUInt64
    cidx := c.cidx.toUInt64
    params := c.numParams.toUInt64
    fields := c.numFields.toUInt64
    typ := typeExpr
  }
  let ctorMeta := { Ixon.ConstantMeta.new
    (.ctor nameAddr lvlAddrs c.induct.getHash arena typeRoot) with
    metaSharing := surgerySharing, metaRefs, metaUnivs, univPatches }
  pure (ctor, ctorMeta, typeExpr)

/-- Compile a constructor to Ixon.Constructor with metadata (ConstantMeta.ctor). -/
def compileConstructor (c : ConstructorVal) :
    CompileM (Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr) :=
  withCurrent c.cnst.name do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr c.cnst.type
    finishConstructorCompilation c typeExpr typeRoot

/-- Accumulated constructor payloads, metadata, and sharing roots. -/
structure InductiveConstructorCompileState where
  ctors : Array Ixon.Constructor := #[]
  ctorMetaPairs : Array (Name × Ixon.ConstantMeta) := #[]
  ctorNameAddrs : Array Address := #[]
  ctorExprs : Array Ixon.Expr := #[]

/-- Metadata drained from the inductive type before constructor compilation
starts. Each constructor subsequently owns an independent arena. -/
structure InductiveTypeCompileMeta where
  arena : Ixon.ExprMetaArena
  surgerySharing : Array Ixon.Expr
  metaRefs : Array Address := #[]
  metaUnivs : Array Ixon.Univ
  univPatches : Array Ixon.UnivPatch

def takeInductiveTypeCompileMeta : CompileM InductiveTypeCompileMeta := do
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  let metaRefs ← takeMetaRefs
  let (metaUnivs, univPatches) ← takeUnivPatches
  clearExprCache
  pure { arena, surgerySharing, metaRefs, metaUnivs, univPatches }

/-- Compile constructors in source order. -/
def compileInductiveConstructors :
    List ConstructorVal → InductiveConstructorCompileState →
      CompileM InductiveConstructorCompileState
  | [], acc => pure acc
  | ctorVal :: rest, acc => do
    let (ctor, ctorMeta, ctorExpr) ← compileConstructor ctorVal
    compileInductiveConstructors rest {
      ctors := acc.ctors.push ctor
      ctorMetaPairs := acc.ctorMetaPairs.push (ctorVal.cnst.name, ctorMeta)
      ctorNameAddrs := acc.ctorNameAddrs.push ctorVal.cnst.name.getHash
      ctorExprs := acc.ctorExprs.push ctorExpr
    }

/-- Assemble an inductive after its type metadata has been drained and all
constructors have been compiled. -/
def finishInductiveCompilation (i : InductiveVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeMeta : InductiveTypeCompileMeta)
    (compiledCtors : InductiveConstructorCompileState) :
    CompileM (Ixon.Inductive × Ixon.ConstantMeta ×
      Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := do
  -- Store name string components as blobs for deduplication
  compileName i.cnst.name
  compileNames i.cnst.levelParams
  compileNames i.all
  let mutNames := (← getBlockEnv).mutCtx.toList.toArray.map (·.1)
  compileNames mutNames

  let nameAddr := i.cnst.name.getHash
  let lvlAddrs := i.cnst.levelParams.map (·.getHash)
  let allAddrs := i.all.map (·.getHash)
  let ctxAddrs ← getMutCtxAddrs

  let ind : Ixon.Inductive := {
    isUnsafe := i.isUnsafe
    lvls := i.cnst.levelParams.size.toUInt64
    params := i.numParams.toUInt64
    indices := i.numIndices.toUInt64
    typ := typeExpr
    ctors := compiledCtors.ctors
  }
  let constMeta := { Ixon.ConstantMeta.new
    (.indc nameAddr lvlAddrs compiledCtors.ctorNameAddrs allAddrs ctxAddrs
      typeMeta.arena typeRoot) with
    metaSharing := typeMeta.surgerySharing
    metaRefs := typeMeta.metaRefs
    metaUnivs := typeMeta.metaUnivs
    univPatches := typeMeta.univPatches }
  pure (ind, constMeta, compiledCtors.ctorMetaPairs,
    compiledCtors.ctorExprs)

/-- Compile an inductive to Ixon.Inductive with metadata.
    Takes the inductive and its constructors (looked up from Ix.Environment).
    Returns (inductive, indc meta, ctor metas with names, all exprs). -/
def compileInductive (i : InductiveVal) (ctorVals : Array ConstructorVal)
    : CompileM (Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := withCurrent i.cnst.name do
  withUnivCtx i.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr i.cnst.type
    let typeMeta ← takeInductiveTypeCompileMeta

    let compiledCtors ← compileInductiveConstructors ctorVals.toList {
      ctorExprs := #[typeExpr] }
    finishInductiveCompilation i typeExpr typeRoot typeMeta compiledCtors

/-! ## Internal compilation helpers for mutual blocks -/

/-- Compile definition data for a `Def` structure (from `Mutual.lean`). -/
def compileDefinitionData (d : Def) :
    CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) :=
  withCurrent d.name do
    withUnivCtx d.levelParams.toList do
      resetArena
      let (typeExpr, typeRoot) ← compileExpr d.type
      let (valueExpr, valueRoot) ← compileExpr d.value
      finishDefinitionDataCompilation d typeExpr typeRoot valueExpr valueRoot

/-- Compile inductive data for an Ind structure (from Mutual.lean).
    Returns (inductive, indc meta, ctor metas with names, all exprs). -/
def finishInductiveDataCompilation (i : Ind)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64)
    (typeMeta : InductiveTypeCompileMeta)
    (compiledCtors : InductiveConstructorCompileState) :
    CompileM (Ixon.Inductive × Ixon.ConstantMeta ×
      Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := do
  -- Store name components for deduplication
  compileName i.name
  compileNames i.levelParams
  compileNames i.all
  let mutNames := (← getBlockEnv).mutCtx.toList.toArray.map (·.1)
  compileNames mutNames

  let nameAddr := i.name.getHash
  let lvlAddrs := i.levelParams.map (·.getHash)
  let allAddrs := i.all.map (·.getHash)
  let ctxAddrs ← getMutCtxAddrs

  let ind : Ixon.Inductive := {
    isUnsafe := i.isUnsafe
    lvls := i.levelParams.size.toUInt64
    params := i.numParams.toUInt64
    indices := i.numIndices.toUInt64
    typ := typeExpr
    ctors := compiledCtors.ctors
  }
  let constMeta := { Ixon.ConstantMeta.new
    (.indc nameAddr lvlAddrs compiledCtors.ctorNameAddrs allAddrs ctxAddrs
      typeMeta.arena typeRoot) with
    metaSharing := typeMeta.surgerySharing
    metaRefs := typeMeta.metaRefs
    metaUnivs := typeMeta.metaUnivs
    univPatches := typeMeta.univPatches }
  pure (ind, constMeta, compiledCtors.ctorMetaPairs,
    compiledCtors.ctorExprs)

/-- Compile inductive data for an Ind structure (from Mutual.lean).
    Returns (inductive, indc meta, ctor metas with names, all exprs). -/
def compileInductiveData (i : Ind)
    : CompileM (Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := withCurrent i.name do
  withUnivCtx i.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr i.type
    let typeMeta ← takeInductiveTypeCompileMeta
    let compiledCtors ← compileInductiveConstructors i.ctors.toList {
      ctorExprs := #[typeExpr] }
    finishInductiveDataCompilation i typeExpr typeRoot typeMeta compiledCtors

/-- Compile recursor data for a RecursorVal. -/
def compileRecursorData (r : RecursorVal) :
    CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) :=
  compileRecursor r

/-! ## Mutual Block Compilation -/

/-- The complete result of compiling one source mutual member.  Every member
is compiled for metadata; the class fold decides whether its payload and
sharing roots are retained as the class representative. -/
structure CompiledMutConstMember where
  payload : Ixon.MutConst
  roots : Array Ixon.Expr
  metas : Array (Name × Ixon.ConstantMeta)

/-- Compile one mutual member independently of representative selection. -/
def compileMutConstMember : MutConst → CompileM CompiledMutConstMember
  | .indc i => do
    let (ind, constMeta, ctorMetaPairs, exprs) ←
      withCurrent i.name (compileInductiveData i)
    pure {
      payload := .indc ind
      roots := exprs
      metas := #[(i.name, constMeta)] ++ ctorMetaPairs }
  | .defn d => do
    let (defn, constMeta, typeExpr, valueExpr) ←
      withCurrent d.name (compileDefinitionData d)
    pure {
      payload := .defn defn
      roots := #[typeExpr, valueExpr]
      metas := #[(d.name, constMeta)] }
  | .recr r => do
    let (recursor, constMeta, typeExpr) ←
      withCurrent r.cnst.name (compileRecursorData r)
    pure {
      payload := .recr recursor
      roots := #[typeExpr] ++ recursor.rules.map (·.rhs)
      metas := #[(r.cnst.name, constMeta)] }

/-- Accumulator for the mutual member and equivalence-class folds. -/
structure MutConstCompileState where
  payloads : Array Ixon.MutConst := #[]
  roots : Array Ixon.Expr := #[]
  metas : Array (Name × Ixon.ConstantMeta) := #[]

def MutConstCompileState.addRepresentative
    (state : MutConstCompileState) (member : CompiledMutConstMember) :
    MutConstCompileState :=
  { payloads := state.payloads.push member.payload
    roots := state.roots ++ member.roots
    metas := state.metas ++ member.metas }

def MutConstCompileState.addEquivalent
    (state : MutConstCompileState) (member : CompiledMutConstMember) :
    MutConstCompileState :=
  { state with metas := state.metas ++ member.metas }

/-- Compile the non-representative tail of one equivalence class. -/
def compileEquivalentMutConsts :
    List MutConst → MutConstCompileState → CompileM MutConstCompileState
  | [], state => pure state
  | source :: rest, state => do
    let member ← compileMutConstMember source
    compileEquivalentMutConsts rest (state.addEquivalent member)

/-- Compile one equivalence class, retaining the first member as its payload
representative while still retaining metadata from every later member. -/
def compileMutConstClass :
    List MutConst → MutConstCompileState → CompileM MutConstCompileState
  | [], state => pure state
  | representative :: equivalents, state => do
    let member ← compileMutConstMember representative
    compileEquivalentMutConsts equivalents (state.addRepresentative member)

/-- Compile equivalence classes in their sorted source order. -/
def compileMutConstClasses :
    List (List MutConst) → MutConstCompileState →
      CompileM MutConstCompileState
  | [], state => pure state
  | constClass :: rest, state => do
    let state ← compileMutConstClass constClass state
    compileMutConstClasses rest state

/-- Compile sorted equivalence classes of mutual constants.
    Returns compiled constants, all root expressions, and metadata for each constant.
    No caller uses the roots (`buildBlockConstant` derives them from the payload
    with `constantInfoRootExprs`). -/
def compileMutConsts (classes : List (List MutConst))
    : CompileM (Array Ixon.MutConst × Array Ixon.Expr × Array (Name × Ixon.ConstantMeta)) := do
  let state ← compileMutConstClasses classes {}
  pure (state.payloads, state.roots, state.metas)

/-- Preseed roots for one equivalence class in member order. -/
def mutConstClassPreseedInputs :
    List MutConst → List (Expr × List Name)
  | [] => []
  | source :: rest =>
    mutConstPreseedInputs source ++ mutConstClassPreseedInputs rest

def mutConstClassPreseedExprs (sources : List MutConst) :
    Array (Expr × List Name) :=
  (mutConstClassPreseedInputs sources).toArray

/-- Exact heterogeneous preseed input used by a mutual block. -/
def mutualPreseedInputs :
    List (List MutConst) → List (Expr × List Name)
  | [] => []
  | constClass :: rest =>
    mutConstClassPreseedInputs constClass ++ mutualPreseedInputs rest

def mutualPreseedExprs (classes : List (List MutConst)) :
    Array (Expr × List Name) :=
  (mutualPreseedInputs classes).toArray

/-- Audit one equivalence class in source order. -/
def auditMutConstClassPlanHeads : List MutConst → CompileM Unit
  | [] => pure ()
  | source :: rest => do
    auditMutConstPlanHeads source
    auditMutConstClassPlanHeads rest

/-- Audit all equivalence classes in source order. -/
def auditMutConstClassesPlanHeads : List (List MutConst) → CompileM Unit
  | [] => pure ()
  | constClass :: rest => do
    auditMutConstClassPlanHeads constClass
    auditMutConstClassesPlanHeads rest

/-- Standalone collapse used for a single definition or recursor
representative. Inductives retain the mutual wrapper for their projection
scheme. -/
def standaloneMutConstInfo? (payloads : Array Ixon.MutConst) :
    Option Ixon.ConstantInfo :=
  if payloads.size == 1 then
    match payloads[0]! with
    | .defn definition => some (.defn definition)
    | .recr recursor => some (.recr recursor)
    | .indc _ => none
  else
    none

/-- Build a BlockResult from a block constant, serializing once. -/
def BlockResult.mk' (block : Ixon.Constant)
    (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array
      (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]) : BlockResult :=
  let blockBytes := Ixon.ser block
  let blockAddr := Address.blake3 blockBytes
  ⟨block, blockBytes, blockAddr, blockMeta, projections, #[]⟩

/-- Name-to-block registrations for a collapsed standalone representative. -/
def buildStandaloneMutualProjections (classes : List (List MutConst))
    (block : Ixon.Constant)
    (metas : Array (Name × Ixon.ConstantMeta)) :
    Array (Name × Ixon.Constant × Ixon.ConstantMeta) := Id.run do
  let metaMap : Std.HashMap Name Ixon.ConstantMeta :=
    metas.foldl (init := {}) fun map (name, constMeta) =>
      map.insert name constMeta
  let mut projections :
      Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
  for constClass in classes do
    for source in constClass do
      let name := source.name
      projections := projections.push
        (name, block, metaMap.get? name |>.getD .empty)
  return projections

/-- Definition, inductive/constructor, and recursor projections for a mutual
wrapper. -/
def buildMutualProjections (classes : List (List MutConst))
    (blockAddr : Address)
    (metas : Array (Name × Ixon.ConstantMeta)) :
    Array (Name × Ixon.Constant × Ixon.ConstantMeta) := Id.run do
  let metaMap : Std.HashMap Name Ixon.ConstantMeta :=
    metas.foldl (init := {}) fun map (name, constMeta) =>
      map.insert name constMeta
  let mut projections :
      Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
  let mut idx : UInt64 := 0
  for constClass in classes do
    for source in constClass do
      let projInfo : Ixon.ConstantInfo := match source with
        | .defn _ => .dPrj ⟨idx, blockAddr⟩
        | .indc _ => .iPrj ⟨idx, blockAddr⟩
        | .recr _ => .rPrj ⟨idx, blockAddr⟩
      let proj : Ixon.Constant := ⟨projInfo, #[], #[], #[]⟩
      let sourceMeta := metaMap.get? source.name |>.getD .empty
      projections := projections.push (source.name, proj, sourceMeta)
      if let .indc inductiveData := source then
        let mut cidx : UInt64 := 0
        for ctor in inductiveData.ctors do
          let ctorProjInfo : Ixon.ConstantInfo :=
            .cPrj ⟨idx, cidx, blockAddr⟩
          let ctorProj : Ixon.Constant := ⟨ctorProjInfo, #[], #[], #[]⟩
          let ctorMeta := metaMap.get? ctor.cnst.name |>.getD .empty
          projections := projections.push
            (ctor.cnst.name, ctorProj, ctorMeta)
          cidx := cidx + 1
    idx := idx + 1
  return projections

/-- Assembly of an already compiled mutual payload with the canonical sharing
under `limits`; fails exactly when the construction does. Projection arrays do
not affect the serialized main-block codec but remain part of the exact
production result. -/
def buildCompiledMutualBlock (limits : Ix.Sharing.Exact.Limits)
    (classes : List (List MutConst)) (payloads : Array Ixon.MutConst)
    (metas : Array (Name × Ixon.ConstantMeta))
    (cache : BlockState) : Except CompileError BlockResult := do
  if let some info := standaloneMutConstInfo? payloads then
    let block ← buildConstantWithSharing limits info cache.refs cache.univs
    pure (BlockResult.mk' block .empty
      (buildStandaloneMutualProjections classes block metas))
  else
    let block ← buildConstantWithSharing limits (.muts payloads) cache.refs cache.univs
    pure (BlockResult.mk' block .empty
      (buildMutualProjections classes (Address.blake3 (Ixon.ser block)) metas))

/-- Read the finished table state and assemble a compiled mutual payload with
the compiler's canonical sharing (`CompileEnv.sharingLimits`). -/
def finishMutualCompilation (classes : List (List MutConst))
    (payloads : Array Ixon.MutConst)
    (metas : Array (Name × Ixon.ConstantMeta)) : CompileM BlockResult := do
  let cache ← getBlockState
  let limits := (← read).1.sharingLimits
  -- Timed at the call (`Ix.PhaseTimers`): the builders themselves carry proofs.
  match Ix.PhaseTimers.withPhase .sharing payloads
      (buildCompiledMutualBlock limits classes · metas cache) with
  | .ok result => pure result
  | .error e => throw e

/-- Compile all mutual members and assemble their retained representatives. -/
def compileMutualPayload (classes : List (List MutConst)) :
    CompileM BlockResult := do
  let (payloads, _, metas) ← compileMutConsts classes
  finishMutualCompilation classes payloads metas

/-- Compile a mutual block and create projections for each constant.
    Returns the Muts block constant and projections for each name with metadata. -/
def compileMutualBlock (classes : List (List MutConst))
    : CompileM BlockResult := do
  auditMutConstClassesPlanHeads classes
  let mutCtx := MutConst.ctx classes
  withMutCtx mutCtx do
    -- Preseed mirrors Rust compile_mutual (compile.rs:3763): collect over
    -- every member (Rust iterates source order, we iterate sorted classes —
    -- equivalent, since the tables are canonically re-sorted afterwards).
    preseedExprTables (mutualPreseedExprs classes)
    compileMutualPayload classes

/-! ## Main Compilation Entry Points -/

/-- Build mutCtx for an inductive: includes the inductive and all its constructors. -/
def buildInductiveMutCtx (i : InductiveVal) (ctorVals : Array ConstructorVal) : Ix.MutCtx := Id.run do
  let mut ctx : Ix.MutCtx := Std.TreeMap.empty
  -- Inductive at index 0
  ctx := ctx.insert i.cnst.name 0
  -- Constructors at indices 1, 2, ...
  for (ctor, idx) in ctorVals.zipIdx do
    ctx := ctx.insert ctor.cnst.name (idx + 1)
  return ctx

/-- Resolve and audit an inductive's constructors in declaration order. -/
def collectInductiveConstructors :
    List Name → Array ConstructorVal → CompileM (Array ConstructorVal)
  | [], acc => pure acc
  | ctorName :: rest, acc => do
    match ← findConst ctorName with
    | .ctorInfo ctorVal =>
      auditPlanHeadArities ctorVal.cnst.name ctorVal.cnst.type
      collectInductiveConstructors rest (acc.push ctorVal)
    | _ =>
      throw (.invalidMutualBlock s!"Expected constructor for {ctorName}")

def lookupInductiveConstructors (i : InductiveVal) :
    CompileM (Array ConstructorVal) :=
  collectInductiveConstructors i.ctors.toList #[]

/-- Projection constants for a standalone one-member inductive block. -/
def buildInductiveProjections (i : InductiveVal)
    (indMeta : Ixon.ConstantMeta)
    (ctorMetaPairs : Array (Name × Ixon.ConstantMeta))
    (blockAddr : Address) :
    Array (Name × Ixon.Constant × Ixon.ConstantMeta) :=
  let indProjInfo : Ixon.ConstantInfo := .iPrj ⟨0, blockAddr⟩
  let indProj : Ixon.Constant := ⟨indProjInfo, #[], #[], #[]⟩
  #[(i.cnst.name, indProj, indMeta)] ++
    ctorMetaPairs.mapIdx fun cidx (ctorName, ctorMeta) =>
      let ctorProjInfo : Ixon.ConstantInfo :=
        .cPrj ⟨0, cidx.toUInt64, blockAddr⟩
      let ctorProj : Ixon.Constant := ⟨ctorProjInfo, #[], #[], #[]⟩
      (ctorName, ctorProj, ctorMeta)

/-- Finish the main block and projections of a compiled standalone inductive
family. -/
def finishInductiveFamilyBlock (i : InductiveVal)
    (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (ctorMetaPairs : Array (Name × Ixon.ConstantMeta)) : CompileM BlockResult := do
  let cache ← getBlockState
  let block ← timedC .sharing (buildBlockConstant
    (.muts #[.indc ind]) cache.refs cache.univs)
  let blockBytes := Ixon.ser block
  let blockAddr := Address.blake3 blockBytes
  let projections :=
    buildInductiveProjections i indMeta ctorMetaPairs blockAddr
  pure (BlockResult.mk' block .empty projections)

/-- Finish a compiled singleton payload using the current block tables, the
compiler's canonical sharing (`buildBlockConstant`, roots derived from the
payload), and the canonical `BlockResult` serializer. -/
def finishConstantWithSharing (info : Ixon.ConstantInfo)
    (blockMeta : Ixon.ConstantMeta := .empty) : CompileM BlockResult := do
  let cache ← getBlockState
  let block ← buildBlockConstant info cache.refs cache.univs
  pure (BlockResult.mk' block blockMeta)

/-- Finish a singleton declaration (`finishConstantWithSharing`; the sharing
roots are the payload's). -/
def finishConstantInfoWithSharing (info : Ixon.ConstantInfo)
    (blockMeta : Ixon.ConstantMeta := .empty) : CompileM BlockResult :=
  finishConstantWithSharing info blockMeta

/-- Compile and finalize the payload of a singleton definition declaration.
The outer singleton driver remains responsible for auditing and preseeding. -/
def compileDefinitionBlock (definitionVal : DefinitionVal) :
    CompileM BlockResult := do
  let (defn, constMeta, _typeExpr, _valueExpr) ←
    compileDefinition definitionVal
  timedC .sharing (finishConstantInfoWithSharing (.defn defn) constMeta)

/-- Preseed and compile a singleton definition after the common declaration
audit and singleton mutual-context setup performed by `compileConstantInfo`. -/
def compileDefinitionInfo (definitionVal : DefinitionVal) :
    CompileM BlockResult := do
  preseedExprTables
    #[(definitionVal.cnst.type, definitionVal.cnst.levelParams.toList),
      (definitionVal.value, definitionVal.cnst.levelParams.toList)]
  compileDefinitionBlock definitionVal

/-- Compile and finalize a common definition-like payload. -/
def compileDefinitionDataBlock (definitionData : Def) : CompileM BlockResult := do
  let (defn, constMeta, _typeExpr, _valueExpr) ←
    compileDefinitionData definitionData
  timedC .sharing (finishConstantInfoWithSharing (.defn defn) constMeta)

/-- Preseed and compile a common two-expression definition-like payload. -/
def compileDefinitionDataInfo (definitionData : Def) : CompileM BlockResult := do
  preseedExprTables
    #[(definitionData.type, definitionData.levelParams.toList),
      (definitionData.value, definitionData.levelParams.toList)]
  compileDefinitionDataBlock definitionData

def compileTheoremInfo (theoremVal : TheoremVal) : CompileM BlockResult :=
  compileDefinitionDataInfo (theoremValData theoremVal)

def compileOpaqueInfo (opaqueVal : OpaqueVal) : CompileM BlockResult :=
  compileDefinitionDataInfo (opaqueValData opaqueVal)

/-- Compile and finalize the payload of a singleton axiom declaration.  The
outer singleton driver remains responsible for auditing and preseeding. -/
def compileAxiomBlock (axiomVal : AxiomVal) : CompileM BlockResult := do
  let (axiomInfo, constMeta, _typeExpr) ← compileAxiom axiomVal
  timedC .sharing (finishConstantInfoWithSharing (.axio axiomInfo) constMeta)

/-- Preseed and compile a singleton axiom after the common declaration audit
and singleton mutual-context setup performed by `compileConstantInfo`. -/
def compileAxiomInfo (axiomVal : AxiomVal) : CompileM BlockResult := do
  preseedExprTables
    #[(axiomVal.cnst.type, axiomVal.cnst.levelParams.toList)]
  compileAxiomBlock axiomVal

/-- Compile and finalize a singleton quotient payload. -/
def compileQuotientBlock (quotientVal : QuotVal) : CompileM BlockResult := do
  let (quotientInfo, constMeta, _typeExpr) ← compileQuotient quotientVal
  timedC .sharing (finishConstantInfoWithSharing (.quot quotientInfo) constMeta)

/-- Preseed and compile a singleton quotient after its driver setup. -/
def compileQuotientInfo (quotientVal : QuotVal) : CompileM BlockResult := do
  preseedExprTables
    #[(quotientVal.cnst.type, quotientVal.cnst.levelParams.toList)]
  compileQuotientBlock quotientVal

/-- Compile and finalize a singleton recursor payload. -/
def compileRecursorBlock (recursorVal : RecursorVal) : CompileM BlockResult := do
  let (recursor, constMeta, _typeExpr) ← compileRecursor recursorVal
  timedC .sharing (finishConstantInfoWithSharing (.recr recursor) constMeta)

/-- Preseed and compile a singleton recursor after its driver setup. -/
def compileRecursorInfo (recursorVal : RecursorVal) : CompileM BlockResult := do
  preseedExprTables (recursorPreseedExprs recursorVal)
  compileRecursorBlock recursorVal

/-- Compile and finalize a standalone inductive family after its family mutual
context and preseed have been installed. -/
def compileInductiveFamilyBlock (inductiveVal : InductiveVal)
    (ctorVals : Array ConstructorVal) : CompileM BlockResult := do
  let (ind, indMeta, ctorMetaPairs, _) ←
    compileInductive inductiveVal ctorVals
  finishInductiveFamilyBlock inductiveVal ind indMeta ctorMetaPairs

def compileInductiveFamilyInfo (inductiveVal : InductiveVal)
    (ctorVals : Array ConstructorVal) : CompileM BlockResult := do
  preseedExprTables (inductivePreseedExprs inductiveVal ctorVals)
  compileInductiveFamilyBlock inductiveVal ctorVals

/-- Reconstruct, audit, and compile a standalone inductive family. -/
def compileInductiveInfo (inductiveVal : InductiveVal) : CompileM BlockResult := do
  let ctorVals ← lookupInductiveConstructors inductiveVal
  let indMutCtx := buildInductiveMutCtx inductiveVal ctorVals
  withMutCtx indMutCtx
    (compileInductiveFamilyInfo inductiveVal ctorVals)

/-- A constructor singleton is represented by recompiling its parent family. -/
def compileConstructorInfo (constructorVal : ConstructorVal) :
    CompileM BlockResult := do
  match ← findConst constructorVal.induct with
  | .inductInfo inductiveVal => compileInductiveInfo inductiveVal
  | _ => throw (.invalidMutualBlock "Constructor has non-inductive parent")

/-- Audit, establish the singleton mutual context, and compile a definition.
Kept separate so the definition dispatch equation reduces without unfolding the
other `ConstantInfo` branches. -/
def compileDefinitionConstantInfo (definitionVal : DefinitionVal) : CompileM BlockResult := do
  auditConstantInfoPlanHeads (.defnInfo definitionVal)
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert definitionVal.cnst.name 0
  withMutCtx mutCtx (compileDefinitionInfo definitionVal)

def compileTheoremConstantInfo (theoremVal : TheoremVal) : CompileM BlockResult := do
  auditConstantInfoPlanHeads (.thmInfo theoremVal)
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert theoremVal.cnst.name 0
  withMutCtx mutCtx (compileTheoremInfo theoremVal)

def compileOpaqueConstantInfo (opaqueVal : OpaqueVal) : CompileM BlockResult := do
  auditConstantInfoPlanHeads (.opaqueInfo opaqueVal)
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert opaqueVal.cnst.name 0
  withMutCtx mutCtx (compileOpaqueInfo opaqueVal)

def compileQuotientConstantInfo (quotientVal : QuotVal) : CompileM BlockResult := do
  auditConstantInfoPlanHeads (.quotInfo quotientVal)
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert quotientVal.cnst.name 0
  withMutCtx mutCtx (compileQuotientInfo quotientVal)

def compileRecursorConstantInfo (recursorVal : RecursorVal) : CompileM BlockResult := do
  auditConstantInfoPlanHeads (.recInfo recursorVal)
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert recursorVal.cnst.name 0
  withMutCtx mutCtx (compileRecursorInfo recursorVal)

def compileInductiveConstantInfo (inductiveVal : InductiveVal) :
    CompileM BlockResult := do
  auditConstantInfoPlanHeads (.inductInfo inductiveVal)
  let mutCtx : Ix.MutCtx :=
    Std.TreeMap.empty.insert inductiveVal.cnst.name 0
  withMutCtx mutCtx (compileInductiveInfo inductiveVal)

def compileConstructorConstantInfo (constructorVal : ConstructorVal) :
    CompileM BlockResult := do
  auditConstantInfoPlanHeads (.ctorInfo constructorVal)
  let mutCtx : Ix.MutCtx :=
    Std.TreeMap.empty.insert constructorVal.cnst.name 0
  withMutCtx mutCtx (compileConstructorInfo constructorVal)

/-- Shared implementation of the remaining singleton `ConstantInfo` branches. -/
def compileConstantInfoCore (const : ConstantInfo) : CompileM BlockResult := do
  auditConstantInfoPlanHeads const
  let name := const.getCnst.name
  let mutCtx : Ix.MutCtx := Std.TreeMap.empty.insert name 0
  withMutCtx mutCtx do
    match const with
    | .defnInfo d =>
      -- Preseed mirrors Rust compile_single_def (compile.rs:3492).
      compileDefinitionInfo d

    | .thmInfo d =>
      compileTheoremInfo d

    | .opaqueInfo d =>
      compileOpaqueInfo d

    | .axiomInfo a =>
      -- Preseed mirrors Rust compile_const_inner Axiom arm (compile.rs:3584).
      compileAxiomInfo a

    | .quotInfo q =>
      compileQuotientInfo q

    | .recInfo r =>
      -- Preseed mirrors Rust compile_const_inner RecInfo arm (compile.rs:3656).
      compileRecursorInfo r

    | .inductInfo i =>
      compileInductiveInfo i

    | .ctorInfo c =>
      compileConstructorInfo c

/-- Compile a single Ix.ConstantInfo directly (singleton, non-mutual).
    Returns BlockResult with the constant and any projections needed. -/
def compileConstantInfo : ConstantInfo → CompileM BlockResult
  | .defnInfo definitionVal => compileDefinitionConstantInfo definitionVal
  | .thmInfo theoremVal => compileTheoremConstantInfo theoremVal
  | .opaqueInfo opaqueVal => compileOpaqueConstantInfo opaqueVal
  | .quotInfo quotientVal => compileQuotientConstantInfo quotientVal
  | .recInfo recursorVal => compileRecursorConstantInfo recursorVal
  | .inductInfo inductiveVal => compileInductiveConstantInfo inductiveVal
  | .ctorInfo constructorVal => compileConstructorConstantInfo constructorVal
  | const => compileConstantInfoCore const

/-- Convert one environment declaration into the mutual compiler's source
grammar. Declarations that are not mutual payload members are skipped exactly
as in the original block loop; inductives resolve their constructor payloads
before being retained. -/
def collectMutConst? : ConstantInfo → CompileM (Option MutConst)
  | .inductInfo val => return some (← MutConst.mkIndc val)
  | .defnInfo val => pure (some (MutConst.fromDefinitionVal val))
  | .opaqueInfo val => pure (some (MutConst.fromOpaqueVal val))
  | .thmInfo val => pure (some (MutConst.fromTheoremVal val))
  | .recInfo val => pure (some (.recr val))
  | _ => pure none

def resolveMutConst? (name : Name) : CompileM (Option MutConst) := do
  collectMutConst? (← findConst name)

/-- Resolve the SCC's names into mutual source members in hash-set iteration
order. This recursive form exposes the collection boundary to refinement
proofs while preserving the former filtering behavior. -/
def collectMutConsts : List Name → Array MutConst →
    CompileM (Array MutConst)
  | [], acc => pure acc
  | name :: rest, acc => do
    let source? ← resolveMutConst? name
    let acc := match source? with
      | some source => acc.push source
      | none => acc
    collectMutConsts rest acc

/-- Resolve, canonically classify, and compile a non-singleton SCC. -/
def compileMutualConstants (all : Set Name) : CompileM BlockResult := do
  let consts ← collectMutConsts all.toList #[]
  let mutConsts := orderRecursorFamily (← sortConsts consts.toList)
  compileMutualBlock mutConsts

/-- Compile a constant by name (looks it up in the environment).
    Uses the block's `all` set from BlockEnv (populated from SCC analysis). -/
def compileConstant (name : Name) : CompileM BlockResult := do
  let const ← findConst name
  let blockEnv ← getBlockEnv
  -- Use the block's all set from SCC analysis
  let all := blockEnv.all

  -- Handle singleton non-mutual constants
  if all.size == 1 then
    compileConstantInfo const
  else
    compileMutualConstants all

/-! ## Block Compilation Entry Point -/

/-- Compile a single block purely, returning the block result and state. -/
def compileBlockPure (compileEnv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError (BlockResult × BlockState) :=
  let blockEnv : BlockEnv := {
    all := all
    current := lo
    mutCtx := default
    univCtx := []
  }
  CompileM.run compileEnv blockEnv {} (compileConstant lo)

/-! ## Main Compilation Entry Point -/

/-- Compile an Ix.Environment purely (sequential, no IO).
    Returns the compiled Ixon.Env and total serialized bytes.
    Pass `dbg := true` to enable progress tracing via dbg_trace. -/
def compileEnv (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (dbg : Bool := false)
    : Except String (Ixon.Env × Nat) := Id.run do
  -- Initialize compilation state
  let mut compileEnv := CompileEnv.new env
  let mut blockNames : Std.HashMap Address Ix.Name := {}
  let mut defHints : Std.HashMap Name Lean.ReducibilityHints := {}

  -- Build work queue data structures
  let totalBlocks := blocks.blocks.size

  -- blockInfo: lo → (all names in block, remaining dep count)
  let mut blockInfo : Std.HashMap Name (Set Name × Nat) := {}
  -- reverseDeps: constant name → list of block lowlinks that depend on it
  let mut reverseDeps : Std.HashMap Name (Array Name) := {}

  for (lo, all) in blocks.blocks do
    let deps := blocks.blockRefs.get! lo
    blockInfo := blockInfo.insert lo (all, deps.size)
    -- Register reverse dependencies
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]

  -- Initialize ready queue with blocks that have no dependencies
  let mut readyQueue : Array (Name × Set Name) := #[]
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.push (lo, all)

  -- Compile blocks in dependency order
  let mut blocksCompiled : Nat := 0
  let mut lastPct : Nat := 0

  while !readyQueue.isEmpty do
    -- Pop from ready queue
    let (lo, all) := readyQueue.back!
    readyQueue := readyQueue.pop

    match compileBlockPure compileEnv all lo with
    | Except.ok (result, cache) =>
      -- Use pre-computed serialized bytes and address
      let blockBytes := result.blockBytes
      let blockAddr := result.blockAddr
      compileEnv := { compileEnv with
        totalBytes := compileEnv.totalBytes + blockBytes.size
        constants := compileEnv.constants.insert blockAddr blockBytes
        blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) compileEnv.blobs
      }
      blockNames := cache.blockNames.fold (fun m k v => m.insert k v) blockNames
      defHints := cache.defHints.fold (fun m k v => m.insert k v) defHints

      -- If there are projections, store them and map names to projection addresses
      if result.projections.isEmpty then
        -- No projections: map lowlink name directly to block
        compileEnv := { compileEnv with
          nameToNamed := compileEnv.nameToNamed.insert lo { addr := blockAddr, constMeta := result.blockMeta }
          nameToAddr := compileEnv.nameToAddr.insert lo blockAddr }
      else
        -- Store each projection and map name to projection address
        for (name, proj, constMeta) in result.projections do
          let projBytes := Ixon.ser proj
          let projAddr := Address.blake3 projBytes
          compileEnv := { compileEnv with
            totalBytes := compileEnv.totalBytes + projBytes.size
            constants := compileEnv.constants.insert projAddr projBytes
            nameToNamed := compileEnv.nameToNamed.insert name { addr := projAddr, constMeta }
            nameToAddr := compileEnv.nameToAddr.insert name projAddr
          }

      -- Decrement dep counts for blocks that depend on constants in this block
      for name in all do
        if let some dependents := reverseDeps.get? name then
          for dependentLo in dependents do
            if let some (depAll, depCount) := blockInfo.get? dependentLo then
              let newCount := depCount - 1
              blockInfo := blockInfo.insert dependentLo (depAll, newCount)
              -- If dep count reaches 0, add to ready queue
              if newCount == 0 then
                readyQueue := readyQueue.push (dependentLo, depAll)

      blocksCompiled := blocksCompiled + 1
      if dbg then
        let pct := (blocksCompiled * 100) / totalBlocks
        if pct >= lastPct + 10 then
          dbg_trace s!"  [Compile] {pct}% ({blocksCompiled}/{totalBlocks})"
          lastPct := pct
    | Except.error e =>
      if dbg then
        dbg_trace s!"  [Compile ERROR] {lo}: {e}"
        dbg_trace s!"  [Compile] nameToNamed has {compileEnv.nameToNamed.size} entries"
      return .error s!"Compilation error in {lo}: {e}"

  -- Check that all blocks were compiled
  if blocksCompiled != totalBlocks then
    return .error s!"Only compiled {blocksCompiled}/{totalBlocks} blocks - circular dependency?"

  -- Build reverse index and names map, storing name string components as blobs
  -- Seed with blockNames collected during compilation (binder names, level params, etc.)
  let (addrToNameMap, namesMap, nameBlobs) :=
    compileEnv.nameToNamed.fold (init := ({}, blockNames, {})) fun (addrMap, namesMap, blobs) name named =>
      let addrMap := addrMap.insert named.addr name
      let (namesMap, blobs) := Ixon.RawEnv.addNameComponentsWithBlobs namesMap blobs name
      (addrMap, namesMap, blobs)

  -- Merge name string blobs into the main blobs map
  let allBlobs := nameBlobs.fold (fun m k v => m.insert k v) compileEnv.blobs

  -- Resolve per-name hints into both channels (matching Rust
  -- `CompileState::finalize_hints`): the EXACT value onto each Named
  -- entry (decompile fidelity — alpha-identical definitions under
  -- different names keep their own hints), and the per-address
  -- `anonHints` advisory map keyed by each name's registered constant
  -- address (the projection address for mutual-block members — exactly
  -- the address the kernel looks hints up under), where alias
  -- collisions merge order-independently.
  let namedWithHints := compileEnv.nameToNamed.fold (init := {})
    fun m name named => m.insert name { named with hints := defHints.get? name }
  let anonHints := compileEnv.nameToNamed.fold (init := {}) fun m name named =>
    match defHints.get? name with
    | some h => m.alter named.addr fun
      | some h₀ => some (Ixon.mergeHints h₀ h)
      | none => some h
    | none => m

  let ixonEnv : Ixon.Env := {
    consts := compileEnv.constants.fold (init := {})
      fun m a bytes => m.insert a { buf := bytes, len := bytes.size }
    named := namedWithHints
    blobs := allBlobs
    names := namesMap
    comms := {}
    addrToName := addrToNameMap
    anonHints
  }

  return .ok (ixonEnv, compileEnv.totalBytes)

/-! ## Parallel Compilation with Work-Stealing -/

/-- Reference to Rust compilation results for incremental comparison. -/
structure RustRef where
  /-- Map from constant name to compiled address -/
  nameToAddr : Std.HashMap Name Address

/-- A single constant's mismatch info -/
structure ConstMismatch where
  name : Name
  leanAddr : Address
  rustAddr : Address
  leanBytes : ByteArray
  leanConst : Ixon.Constant
  deriving Inhabited

/-- Mismatch error with all info needed for debugging -/
structure MismatchError where
  /-- The block's lowlink name -/
  blockName : Name
  /-- The main block constant (mutual definitions) -/
  mainBlock : Ixon.Constant
  /-- Serialized bytes of the main block -/
  mainBlockBytes : ByteArray
  /-- Address of the main block -/
  mainBlockAddr : Address
  /-- All projection constants in the block with their info -/
  projections : Array ConstMismatch
  /-- The specific constant that triggered the mismatch -/
  failedConst : ConstMismatch
  /-- Optional system error message (for non-mismatch errors) -/
  systemError : Option String := none

/-- Create a system error (not a mismatch) -/
def MismatchError.system (msg : String) : MismatchError :=
  { blockName := default, mainBlock := default, mainBlockBytes := default, mainBlockAddr := default,
    projections := #[], failedConst := ⟨default, default, default, default, default⟩, systemError := some msg }

/-- Result of compiling a single block. -/
structure BlockCompileResult where
  /-- Lowlink name of the block -/
  lo : Name
  /-- All names in the block -/
  all : Set Name
  /-- The compiled block constant -/
  block : Ixon.Constant
  /-- Block address -/
  blockAddr : Address
  /-- Projections: name → (projection constant, projection address, metadata) -/
  projections : Array (Name × Ixon.Constant × Address × Ixon.ConstantMeta)
  /-- Blobs collected during compilation -/
  blobs : Std.HashMap Address ByteArray
  /-- Total serialized bytes -/
  totalBytes : Nat

/-- Shared state for parallel compilation. Protected by mutex. -/
structure ParallelState where
  /-- Map from constant name to Named (address + metadata) -/
  nameToNamed : Std.HashMap Name Ixon.Named
  /-- Compiled constants storage, SERIALIZED (see `CompileEnv.constants`). -/
  constants : Std.HashMap Address ByteArray
  /-- Blob storage -/
  blobs : Std.HashMap Address ByteArray
  /-- Total bytes compiled -/
  totalBytes : Nat
  /-- Block dependency counts (remaining deps) -/
  blockDepCounts : Std.HashMap Name Nat
  /-- Blocks compiled so far -/
  blocksCompiled : Nat
  /-- First error encountered (if any) -/
  firstError : Option String
  /-- Mismatches found during incremental comparison -/
  mismatches : Array (Name × Address × Address)  -- (name, lean addr, rust addr)
  /-- Last printed percentage (for progress tracking) -/
  lastPrintedPct : Nat

/-- Result of compiling a single block in a wave. -/
structure WaveBlockResult where
  lo : Name
  all : Set Name
  block : Ixon.Constant
  blockAddr : Address
  projections : Array (Name × Ixon.Constant × Address × Ixon.ConstantMeta)
  blobs : Std.HashMap Address ByteArray
  names : Std.HashMap Address Ix.Name
  defHints : Std.HashMap Name Lean.ReducibilityHints
  totalBytes : Nat

/-- Work item for a worker thread -/
structure WorkItem where
  lo : Name
  all : Set Name
  compileEnv : CompileEnv
  rustRef : Option RustRef

instance : Inhabited WorkItem where
  default := { lo := default, all := {}, compileEnv := default, rustRef := none }

instance : Inhabited (Except MismatchError WaveBlockResult) where
  default := .error { blockName := default, mainBlock := default, mainBlockBytes := default,
                      mainBlockAddr := default, projections := #[],
                      failedConst := ⟨default, default, default, default, default⟩ }

/-- Compile an Ix.Environment in parallel using dedicated workers.
    Workers are created once and reused across waves.
    Each wave compiles all blocks whose dependencies are satisfied.
    Optionally compares results against Rust incrementally - fails fast on first mismatch.
    Returns the compiled Ixon.Env and total bytes, or a MismatchError on first discrepancy. -/
def compileEnvParallel (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (rustRef : Option RustRef := none) (numWorkers : Nat := 32) (dbg : Bool := false)
    : IO (Except MismatchError (Ixon.Env × Nat)) := do
  let totalBlocks := blocks.blocks.size

  -- Create channels for work distribution (using Sync for blocking operations)
  let workChan ← Std.CloseableChannel.Sync.new (α := WorkItem)
  let resultChan ← Std.CloseableChannel.Sync.new (α := Except MismatchError WaveBlockResult)

  -- Worker function: receive work, compile, send result
  let worker (_workerId : Nat) : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break  -- Channel closed, exit
      | some item =>
        let result : Except MismatchError WaveBlockResult := Id.run do
          match compileBlockPure item.compileEnv item.all item.lo with
          | Except.error e =>
            return .error <| .system s!"Compilation error in {item.lo}: {e}"
          | Except.ok (blockResult, cache) =>
            -- Use pre-computed serialized bytes and address
            let blockBytes := blockResult.blockBytes
            let blockAddr := blockResult.blockAddr
            let mut projections : Array (Name × Ixon.Constant × Address × ByteArray × Ixon.ConstantMeta) := #[]
            let mut projBytes := blockBytes.size

            if blockResult.projections.isEmpty then
              projections := #[(item.lo, blockResult.block, blockAddr, blockBytes, blockResult.blockMeta)]
            else
              for (name, proj, constMeta) in blockResult.projections do
                let pBytes := Ixon.ser proj
                let pAddr := Address.blake3 pBytes
                projections := projections.push (name, proj, pAddr, pBytes, constMeta)
                projBytes := projBytes + pBytes.size

            -- Check against Rust reference - fail fast on first mismatch
            if let some rust := item.rustRef then
              -- Build full block info for all projection constants
              let projMismatches : Array ConstMismatch := projections.map fun (name, const, leanAddr, bytes, _) =>
                let rustAddr := rust.nameToAddr.get? name |>.getD default
                ⟨name, leanAddr, rustAddr, bytes, const⟩

              -- Check for any mismatch
              for cm in projMismatches do
                if let some rustAddr := rust.nameToAddr.get? cm.name then
                  if cm.leanAddr != rustAddr then
                    return .error {
                      blockName := item.lo
                      mainBlock := blockResult.block
                      mainBlockBytes := blockBytes
                      mainBlockAddr := blockAddr
                      projections := projMismatches
                      failedConst := { cm with rustAddr }
                    }

            -- Convert projections to the format without bytes for the result
            let projsNoBytes := projections.map fun (n, c, a, _, m) => (n, c, a, m)

            return .ok {
              lo := item.lo
              all := item.all
              block := blockResult.block
              blockAddr
              projections := projsNoBytes
              blobs := cache.blockBlobs
              names := cache.blockNames
              defHints := cache.defHints
              totalBytes := projBytes
            }
        discard <| resultChan.send result

  -- Spawn dedicated worker threads
  let mut workerTasks : Array (Task (Except IO.Error Unit)) := #[]
  for i in [:numWorkers] do
    let task ← IO.asTask (prio := .dedicated) (worker i)
    workerTasks := workerTasks.push task

  -- Track compiled constants and remaining blocks
  let mut nameToNamed : Std.HashMap Name Ixon.Named := {}
  let mut nameToAddr : Std.HashMap Name Address := {}
  let mut constants : Std.HashMap Address Ixon.Constant := {}
  let mut blobs : Std.HashMap Address ByteArray := {}
  let mut blockNames : Std.HashMap Address Ix.Name := {}
  let mut defHints : Std.HashMap Name Lean.ReducibilityHints := {}
  let mut totalBytes : Nat := 0

  let mut remaining : Set Name := {}
  for (lo, _) in blocks.blocks do
    remaining := remaining.insert lo

  let baseCompileEnv := CompileEnv.new env

  if dbg then
    IO.println s!"  [Lean Compile] {totalBlocks} blocks, {numWorkers} workers"

  let mut waveNum := 0
  let mut compiled := 0

  while !remaining.isEmpty do
    waveNum := waveNum + 1

    -- Find all blocks ready to compile (all deps satisfied)
    let mut ready : Array (Name × Set Name) := #[]
    for lo in remaining do
      let all := blocks.blocks.get! lo
      let deps := blocks.blockRefs.get! lo
      if deps.all (nameToNamed.contains ·) then
        ready := ready.push (lo, all)

    if ready.isEmpty then
      discard <| workChan.close
      return .error <| .system s!"Circular dependency detected: {remaining.size} blocks remaining but none ready"

    if dbg then
      let pct := (compiled * 100) / totalBlocks
      IO.println s!"  [Lean Compile] Wave {waveNum}: {ready.size} blocks ready, {pct}% ({compiled}/{totalBlocks})"

    -- Create compileEnv for this wave (with current nameToNamed +
    -- resolution map)
    let compileEnv := { baseCompileEnv with nameToNamed, nameToAddr }

    -- Send all ready blocks to workers
    for (lo, all) in ready do
      discard <| workChan.send { lo, all, compileEnv, rustRef }

    -- Collect results for this wave
    for _ in [:ready.size] do
      match ← resultChan.recv with
      | none =>
        discard <| workChan.close
        return .error <| .system "Result channel closed unexpectedly"
      | some (.error e) =>
        discard <| workChan.close
        return .error e
      | some (.ok result) =>
        -- Store block constant
        constants := constants.insert result.blockAddr result.block
        -- Store projections and update nameToNamed
        for (name, proj, addr, constMeta) in result.projections do
          constants := constants.insert addr proj
          nameToNamed := nameToNamed.insert name { addr, constMeta }
          nameToAddr := nameToAddr.insert name addr
        -- Store blobs, names, and hints
        blobs := result.blobs.fold (fun m k v => m.insert k v) blobs
        blockNames := result.names.fold (fun m k v => m.insert k v) blockNames
        defHints := result.defHints.fold (fun m k v => m.insert k v) defHints
        totalBytes := totalBytes + result.totalBytes
        compiled := compiled + 1

    -- Remove completed blocks from remaining
    for (lo, _) in ready do
      remaining := remaining.erase lo

  -- Close work channel to signal workers to exit
  discard <| workChan.close

  if dbg then
    IO.println s!"  [Lean Compile] All {waveNum} waves finished, {compiled} blocks compiled"

  -- Check all blocks compiled
  if compiled != totalBlocks then
    return .error <| .system s!"Only compiled {compiled}/{totalBlocks} blocks - circular dependency?"

  -- Build reverse index and names map, storing name string components as blobs
  -- Seed with blockNames collected during compilation (binder names, level params, etc.)
  let (addrToNameMap, namesMap, nameBlobs) :=
    nameToNamed.fold (init := ({}, blockNames, {})) fun (addrMap, namesMap, nameBlobs) name named =>
      let addrMap := addrMap.insert named.addr name
      let (namesMap, nameBlobs) := Ixon.RawEnv.addNameComponentsWithBlobs namesMap nameBlobs name
      (addrMap, namesMap, nameBlobs)

  -- Merge name string blobs into the main blobs map
  let blockBlobCount := blobs.size
  let nameBlobCount := nameBlobs.size
  let allBlobs := nameBlobs.fold (fun m k v => m.insert k v) blobs
  let finalBlobCount := allBlobs.size
  let overlapCount := blockBlobCount + nameBlobCount - finalBlobCount

  if dbg then
    IO.println s!"  [Lean Compile] Blobs: {blockBlobCount} from blocks, {nameBlobCount} from names, {overlapCount} overlap, {finalBlobCount} final"

  -- Resolve per-name hints into both channels (see the serial driver /
  -- Rust `CompileState::finalize_hints`): exact per-Named + merged
  -- per-address.
  let namedWithHints := nameToNamed.fold (init := {})
    fun m name named => m.insert name { named with hints := defHints.get? name }
  let anonHints := nameToNamed.fold (init := {}) fun m name named =>
    match defHints.get? name with
    | some h => m.alter named.addr fun
      | some h₀ => some (Ixon.mergeHints h₀ h)
      | none => some h
    | none => m

  let ixonEnv : Ixon.Env := {
    consts := constants.fold (init := {})
      fun m a c => m.insert a (Ixon.LazyConstant.ofConstant c)
    named := namedWithHints
    blobs := allBlobs
    names := namesMap
    comms := {}
    addrToName := addrToNameMap
    anonHints
  }

  return .ok (ixonEnv, totalBytes)

/-! ## Rust Compilation FFI -/

/-- Structured result of `rs_compile_env`. Field kinds/order must match
    the `LeanIxCompileEnvStatus` FFI layout in `crates/ffi/src/lean.rs`:
    boxed fields first (`root`, `ungrounded`), then the UInt64 scalars
    (`bytes`, `named`, `uniqueAnon`) in declaration order. -/
structure CompileEnvStatus where
  /-- 64-hex canonical consts merkle root. Equals the `.ixe` header root
      when a file was written; still computed on a fail-closed abort. -/
  root : String
  /-- `(pretty name, reason)` for every requested constant whose block
      failed to compile, sorted by name. Empty ⇔ complete environment. -/
  ungrounded : Array (String × String)
  /-- Bytes written to `outPath` (0 when nothing was written). -/
  bytes : UInt64
  /-- Named constants in the compiled env. -/
  named : UInt64
  /-- Unique anonymous constants (content-deduplicated). -/
  uniqueAnon : UInt64
  deriving Repr, Inhabited

/-- FFI: Compile a Lean environment and write the serialized Ixon.Env
    bytes straight to `outPath` from Rust (streamed; no env-sized
    ByteArray crosses the FFI). Writes to `<outPath>.tmp` then renames,
    so a crash cannot leave a truncated file.

    Fail-closed semantics live behind the FFI: with
    `allowPartial := false`, an env with any ungrounded requested
    constant writes NOTHING (the final path is never created) and the
    returned status carries the full ungrounded list; with
    `allowPartial := true`, the grounded subset is serialized and the
    status discloses what was omitted. -/
@[extern "rs_compile_env"]
opaque rsCompileEnvBytesFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → @& String → Bool
  → IO CompileEnvStatus

/-- `rsCompileEnvBytesFFI` with strict-anon output (`ix compile
    --anon`): §4 names, §5 metadata, and §6 commitments are cleared —
    strictly after `finalize_hints`, which derives §3 from `env.named`
    — so the piece carries the anon layer only (§1–§3). The env root
    is identical either way (it covers §2 keys only); the status
    reports `named = 0`. -/
@[extern "rs_compile_env_anon"]
opaque rsCompileEnvBytesAnonFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → @& String → Bool
  → IO CompileEnvStatus

/-- FFI: 8-phase validation of the aux_gen compile pipeline (compile +
    decompile + roundtrip + alpha-equivalence + nested-detect checks).
    Returns total failure count across all phases. The second argument
    is a report path: non-empty ⇒ the Rust side writes the
    machine-readable phase-table JSON there (on completion and on
    abort paths alike); empty ⇒ no report.

    Shared between the `ix validate` CLI subcommand (`Ix.Cli.ValidateCmd`)
    and the `validate-aux` test runner (`Tests.Ix.Compile.ValidateAux`).
    The underlying Rust function is `rs_compile_validate_aux` in
    `src/ffi/lean_env.rs`. -/
@[extern "rs_compile_validate_aux"]
opaque rsCompileValidateAuxFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → @& String → USize

/-- Compile a Lean environment and write the serialized Ixon.Env bytes
    to `outPath` using the Rust compiler. Fail-closed by default: any
    ungrounded constant throws (and nothing is written) unless
    `allowPartial := true`. Returns the structured compile status. -/
def rsCompileEnvBytes (leanEnv : Lean.Environment) (outPath : String)
    (allowPartial : Bool := false) : IO CompileEnvStatus := do
  let constList ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants leanEnv leanEnv.constants.toList
  let status ← rsCompileEnvBytesFFI constList outPath allowPartial
  if !allowPartial && !status.ungrounded.isEmpty then
    throw <| IO.userError <|
      s!"rsCompileEnvBytes: {status.ungrounded.size} requested constant(s) " ++
      s!"failed to compile; nothing written to {outPath}. First failure: " ++
      match status.ungrounded[0]? with
      | some (n, r) => s!"{n}: {r}"
      | none => "<empty>"
  return status

-- Re-export RawEnv types from Ixon for backwards compatibility
export Ixon (RawConst RawNamed RawBlob RawComm RawEnv)

/-- FFI: Compile a Lean environment to RawEnv (structured Lean objects) using Rust. -/
@[extern "rs_compile_env_to_ixon"]
opaque rsCompileEnvFFI : @& List (Lean.Name × Lean.ConstantInfo) → IO Ixon.RawEnv

/-- FFI: Compute the LEON content hash of every constant in a Lean
    environment. Returns `(Ix.Name, Ix.Address)` pairs where the address
    is the 32-byte Blake3 digest produced by `ConstantInfo::get_hash()`
    in `src/ix/env.rs`. This is the addressing scheme under which
    `orig_kenv` stores KIds in the kernel — two constants with the same
    Lean name but different content get distinct addresses. Used by
    `Tests.Ix.Kernel.BuildPrimOrigs` to regenerate `PrimAddrs::new_orig`
    in the Rust kernel. -/
@[extern "rs_leon_hashes"]
opaque rsLeonHashesFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → IO (Array (Ix.Name × Address))

/-! ## Combined Compile Phases FFI -/

/-- Raw FFI type returned from Rust's rs_compile_phases.
    Contains all compilation phases in array-based format for FFI compatibility. -/
structure RustCompilePhases where
  rawEnv : Ix.RawEnvironment        -- Array-based canonicalized constants
  condensed : RustCondensedBlocks   -- Array-based SCC data
  compileEnv : RawEnv               -- Ixon raw type (RawConst, RawNamed, etc.)
  deriving Inhabited, Repr

/-- Nice Lean type with proper data structures.
    Converted from RustCompilePhases for ergonomic use in Lean. -/
structure CompilePhases where
  rawEnv : Ix.Environment           -- HashMap-based canonicalized constants
  condensed : CondensedBlocks       -- Map/Set-based SCC data
  compileEnv : Ixon.Env             -- HashMap-based Ixon environment

/-- FFI: Run all compilation phases in Rust and return structured data. -/
@[extern "rs_compile_phases"]
opaque rsCompilePhasesFFI : @& List (Lean.Name × Lean.ConstantInfo) → IO RustCompilePhases

/-- Run all compilation phases in Rust over an explicit constant list
    and convert to Lean-friendly types. Use this for closure-scoped
    compiles (e.g. `#ixeval` compiles only a term's reference closure);
    `rsCompilePhases` covers the whole-environment case. -/
def rsCompilePhasesOf (constList : List (Lean.Name × Lean.ConstantInfo)) :
    IO CompilePhases := do
  let constList ← IO.ofExcept <| Ix.Compile.prepareSourceConstants constList
  let raw ← rsCompilePhasesFFI constList

  -- Convert RawEnvironment to Environment
  let rawEnv := raw.rawEnv.toEnvironment

  -- Convert RustCondensedBlocks to CondensedBlocks
  let condensed := raw.condensed.toCondensedBlocks

  -- Convert RawEnv to Ixon.Env
  let compileEnv := raw.compileEnv.toEnv

  pure { rawEnv, condensed, compileEnv }

/-- Run all compilation phases using Rust and convert to Lean-friendly types.
    This is the main entry point for getting Rust compilation results. -/
def rsCompilePhases (leanEnv : Lean.Environment) : IO CompilePhases := do
  let constants ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants leanEnv leanEnv.constants.toList
  let raw ← rsCompilePhasesFFI constants
  return { rawEnv := raw.rawEnv.toEnvironment
           condensed := raw.condensed.toCondensedBlocks
           compileEnv := raw.compileEnv.toEnv }

/-- Compile an explicit constant list to Ixon.Env using the Rust
    compiler. Use for compiles over constructed environments (e.g. the
    catalog `--audit` per-library comparison). -/
def rsCompileEnvOf (constList : List (Lean.Name × Lean.ConstantInfo)) :
    IO Ixon.Env := do
  let constList ← IO.ofExcept <| Ix.Compile.prepareSourceConstants constList
  let rawEnv ← rsCompileEnvFFI constList
  pure rawEnv.toEnv

/-- Compile a Lean environment to Ixon.Env using the Rust compiler.
    Uses the direct FFI that returns structured Lean objects. -/
def rsCompileEnv (leanEnv : Lean.Environment) : IO Ixon.Env := do
  let constants ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants leanEnv leanEnv.constants.toList
  let raw ← rsCompileEnvFFI constants
  return raw.toEnv

end
end Ix.CompileM


