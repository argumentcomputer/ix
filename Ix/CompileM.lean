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
public import Ix.Environment
public import Ix.Sharing
public import Ix.Common
public import Ix.Store
public import Ix.Mutual
public import Ix.GraphM
public import Ix.CondenseM
public import Ix.SOrder
public import Ix.CallSitePlan
public import Ix.CallSiteSurgery
public import Ix.CanonM

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
  /-- Compiled constants storage -/
  constants : Std.HashMap Address Ixon.Constant
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
  /-- Per-`.below` surgery plans (Rust `stt.below_call_site_plans`).
      `.below` has the motive-only telescope `params, motives, indices,
      major`. -/
  belowCallSitePlans : Std.HashMap Name Ix.AuxGen.BRecOnCallSitePlan := {}
  /-- Persistent set of names compiled by aux-gen (Rust
      `stt.aux_gen_extra_names`); merged from block tails by the driver
      and consulted by the scheduler's promotion pass. -/
  auxGenExtraNames : Std.HashSet Name := {}
  /-- Constants that couldn't be compiled, name → error description
      (Rust `stt.ungrounded`): pre-compile grounding rejections plus
      per-block compile failures recorded by the scheduler. -/
  ungrounded : Std.HashMap Name String := {}

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
  deriving Inhabited

/-- Per-block compilation state and tables. -/
structure BlockState where
  /-- Expression compilation cache (keyed by Expr for O(1) lookup).
      Value is (compiled expression, arena root index). -/
  exprCache : Std.HashMap Expr (Ixon.Expr × UInt64) := {}
  /-- Universe compilation cache (keyed by Level for O(1) lookup) -/
  univCache : Std.HashMap Level Ixon.Univ := {}
  /-- Constant comparison cache (by name pairs) -/
  cmpCache : Std.HashMap (Name × Name) Ordering := {}
  /-- Reference table (ordered unique addresses) -/
  refs : Array Address := #[]
  refsIndex : Std.HashMap Address UInt64 := {}
  /-- Universe table (ordered unique universes) -/
  univs : Array Ixon.Univ := #[]
  univsIndex : Std.HashMap Ixon.Univ UInt64 := {}
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

/-! ## Compilation Error -/

/-- Compilation error type. Variant order matches Rust CompileError (tags 0–5). -/
inductive CompileError where
  | missingConstant (name : String)
  | missingAddress (addr : Address)
  | invalidMutualBlock (reason : String)
  | unsupportedExpr (desc : String)
  | unknownUnivParam (curr param : String)
  | serializeError (err : Ixon.SerializeError)
  deriving Repr, BEq

instance : ToString CompileError where
  toString
  | .missingConstant name => s!"missingConstant: {name}"
  | .missingAddress addr => s!"missingAddress: {addr}"
  | .invalidMutualBlock reason => s!"invalidMutualBlock: {reason}"
  | .unsupportedExpr desc => s!"unsupportedExpr: {desc}"
  | .unknownUnivParam curr param => s!"unknownUnivParam: compiling {curr}, param {param}"
  | .serializeError err => s!"serializeError: {err}"

abbrev CompileM := ReaderT (CompileEnv × BlockEnv) (ExceptT CompileError (StateT BlockState Id))

/-- Run a CompileM computation purely. -/
def CompileM.run (compileEnv : CompileEnv) (blockEnv : BlockEnv) (blockState : BlockState)
    (m : CompileM α) : Except CompileError (α × BlockState) :=
  match StateT.run (ExceptT.run (ReaderT.run m (compileEnv, blockEnv))) blockState with
  | (Except.ok a, state') => Except.ok (a, state')
  | (Except.error e, _) => Except.error e

/-- Get the global compile environment. -/
def getCompileEnv : CompileM CompileEnv := do
  pure (← read).1

/-- Get the block environment. -/
def getBlockEnv : CompileM BlockEnv := do
  pure (← read).2

/-- Get the block state. -/
def getBlockState : CompileM BlockState := do
  get

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

/-- Set universe context. -/
def withUnivCtx (univCtx : List Name) : CompileM α → CompileM α :=
  withBlockEnv fun env => { env with univCtx }

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
  modifyBlockState fun c => { c with arena := {} }

/-- Clear the expression cache (between constants to avoid cross-constant arena references). -/
def clearExprCache : CompileM Unit :=
  modifyBlockState fun c => { c with exprCache := {} }

/-- Take the accumulated collapsed call-site expressions for the current
    constant, clearing the accumulator (Rust
    `std::mem::take(&mut cache.surgery_sharing)`, compile.rs:2230). The
    result becomes the constant's `ConstantMeta.metaSharing`. -/
def takeSurgerySharing : CompileM (Array Ixon.Expr) :=
  modifyGetBlockState fun c => (c.surgerySharing, { c with surgerySharing := #[] })

/-! ## Universe Compilation -/

/-- Compile an Ix.Level to Ixon.Univ type. -/
partial def compileUniv (lvl : Level) : CompileM Ixon.Univ := do
  -- Check cache first (O(1) lookup via embedded hash)
  let state ← getBlockState
  if let some u := state.univCache.get? lvl then
    return u

  let u ← match lvl with
  | .zero _ => pure .zero
  | .succ l _ => .succ <$> compileUniv l
  | .max l r _ => .max <$> compileUniv l <*> compileUniv r
  | .imax l r _ => .imax <$> compileUniv l <*> compileUniv r
  | .param name _ => do
    let ctx := (← getBlockEnv).univCtx
    match ctx.idxOf? name with
    | some i => pure (.var i.toUInt64)
    | none => throw (.unknownUnivParam s!"{(← getBlockEnv).current}" s!"{name}")
  | .mvar _ _ => throw (.unsupportedExpr "level metavariable")

  -- Cache result
  modifyBlockState fun c => { c with univCache := c.univCache.insert lvl u }
  pure u

/-- Intern a universe into the block's univs table, returning its index. -/
def internUniv (u : Ixon.Univ) : CompileM UInt64 :=
  modifyGetBlockState fun state =>
    let (state', idx) := state.internUniv u
    (idx, state')

/-- Compile and intern an Ix.Level, returning its univs table index. -/
def compileAndInternUniv (lvl : Level) : CompileM UInt64 := do
  let u ← compileUniv lvl
  internUniv u

/-! ## Reference Handling -/

/-- Intern an address into the block's refs table, returning its index. -/
def internRef (addr : Address) : CompileM UInt64 :=
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

/-- Find a constant in the Ix environment. -/
def findConst (name : Name) : CompileM ConstantInfo := do
  let env ← getCompileEnv
  match env.env.consts.get? name with
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

/-- Compile a name: store all string components as blobs and track
    name components in blockNames for deduplication.
    This matches Rust's compile_name behavior. -/
partial def compileName (name : Ix.Name) : CompileM Unit := do
  let addr := name.getHash
  let state ← getBlockState
  if state.blockNames.contains addr then return ()
  match name with
  | .anonymous _ =>
    modifyBlockState fun c =>
      { c with blockNames := c.blockNames.insert addr name }
  | .str parent s _ =>
    modifyBlockState fun c =>
      { c with blockNames := c.blockNames.insert addr name }
    discard <| storeString s
    compileName parent
  | .num parent _ _ =>
    modifyBlockState fun c =>
      { c with blockNames := c.blockNames.insert addr name }
    compileName parent

/-- Serialize a u64 in trimmed little-endian format (only necessary bytes).
    Uses Ixon.u64ByteCount for the byte count calculation. -/
def putU64TrimmedLE (x : UInt64) : ByteArray := Id.run do
  let count := Ixon.u64ByteCount x
  let mut bytes := ByteArray.empty
  let mut v := x
  for _ in [:count.toNat] do
    bytes := bytes.push (v &&& 0xFF).toUInt8
    v := v >>> 8
  bytes

/-- Serialize a Nat using Tag0 encoding (variable length, compact for small values).
    Uses Ixon.u64ByteCount for the byte count calculation. -/
def putTag0 (n : Nat) : ByteArray :=
  let x := n.toUInt64
  if x < 128 then
    ByteArray.mk #[x.toUInt8]
  else
    let byteCount := Ixon.u64ByteCount x
    ByteArray.mk #[0x80 ||| (byteCount - 1)] ++ putU64TrimmedLE x

/-- Serialize an Ix.Substring to bytes, storing strings as blobs. -/
def serializeIxSubstring (ss : Ix.Substring) : CompileM ByteArray := do
  let strAddr ← storeString ss.str
  pure (strAddr.hash ++ putTag0 ss.startPos ++ putTag0 ss.stopPos)

/-- Serialize an Ix.SourceInfo to bytes, storing strings as blobs. -/
def serializeIxSourceInfo (si : Ix.SourceInfo) : CompileM ByteArray := do
  match si with
  | .original leading leadingPos trailing trailingPos =>
    let leadingBytes ← serializeIxSubstring leading
    let trailingBytes ← serializeIxSubstring trailing
    pure (ByteArray.mk #[0] ++ leadingBytes ++ putTag0 leadingPos ++
      trailingBytes ++ putTag0 trailingPos)
  | .synthetic start stop canonical =>
    pure (ByteArray.mk #[1] ++ putTag0 start ++ putTag0 stop ++
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
    let header := ByteArray.mk #[1] ++ name.getHash.hash ++ putTag0 aliases.size
    let mut aliasesBytes := ByteArray.empty
    for a in aliases do
      let addr ← storeString a
      aliasesBytes := aliasesBytes ++ addr.hash
    pure (header ++ aliasesBytes)

/-- Serialize an Ix.Syntax to bytes, storing strings as blobs. -/
partial def serializeIxSyntax (syn : Ix.Syntax) : CompileM ByteArray := do
  match syn with
  | .missing => pure (ByteArray.mk #[0])
  | .node info kind args =>
    compileName kind
    let header := ByteArray.mk #[1]
    let infoBytes ← serializeIxSourceInfo info
    let kindBytes := kind.getHash.hash
    let lenBytes := putTag0 args.size
    let mut argsBytes := ByteArray.empty
    for arg in args do
      argsBytes := argsBytes ++ (← serializeIxSyntax arg)
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
    let lenBytes := putTag0 preresolved.size
    let mut presBytes := ByteArray.empty
    for pr in preresolved do
      presBytes := presBytes ++ (← serializeIxSyntaxPreresolved pr)
    pure (header ++ infoBytes ++ rawBytes ++ valBytes ++ lenBytes ++ presBytes)

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

/-- Compile a KVMap (array of name-value pairs). -/
def compileKVMap (kvs : Array (Ix.Name × Ix.DataValue)) : CompileM Ixon.KVMap := do
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
partial def compileExpr (e : Expr) : CompileM (Ixon.Expr × UInt64) := do
  -- Check cache (O(1) lookup via embedded hash)
  let state ← getBlockState
  if let some cached := state.exprCache.get? e then
    return cached

  let (result, root) ← match e with
  | .bvar idx _ => do
    let root ← allocArenaNode .leaf
    pure (.var idx.toUInt64, root)

  | .sort lvl _ => do
    let idx ← compileAndInternUniv lvl
    let root ← allocArenaNode .leaf
    pure (.sort idx, root)

  | .const name lvls _ => do
    let mutCtx := (← getBlockEnv).mutCtx
    let univIndices ← lvls.mapM compileAndInternUniv
    compileName name
    let nameAddr := name.getHash
    match mutCtx.find? name with
    | some recIdx =>
      let root ← allocArenaNode (.ref nameAddr)
      pure (.recur recIdx.toUInt64 univIndices, root)
    | none => do
      let addr ← lookupConstAddr name
      let refIdx ← internRef addr
      let root ← allocArenaNode (.ref nameAddr)
      pure (.ref refIdx univIndices, root)

  | .app .. => compileAppSpine e

  | .lam name ty body bi _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExpr ty
    let (b, bodyRoot) ← compileExpr body
    let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
    pure (.lam t b, root)

  | .forallE name ty body bi _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExpr ty
    let (b, bodyRoot) ← compileExpr body
    let root ← allocArenaNode (.binder nameAddr bi tyRoot bodyRoot)
    pure (.all t b, root)

  | .letE name ty val body nonDep _ => do
    compileName name
    let nameAddr := name.getHash
    let (t, tyRoot) ← compileExpr ty
    let (v, valRoot) ← compileExpr val
    let (b, bodyRoot) ← compileExpr body
    let root ← allocArenaNode (.letBinder nameAddr tyRoot valRoot bodyRoot)
    pure (.letE nonDep t v b, root)

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
    let (s, sRoot) ← compileExpr struct
    let root ← allocArenaNode (.prj structNameAddr sRoot)
    pure (.prj typeRefIdx fieldIdx.toUInt64 s, root)

  | .mdata kvData inner _ => do
    let kvmap ← compileKVMap kvData
    let (innerResult, innerRoot) ← compileExpr inner
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
            let expectedTotal := plan.nParams + plan.nSourceMotives
              + plan.nSourceMinors + plan.nIndices + 1 -- major
            if args.size >= expectedTotal then
              return ← compileRecCallSite name lvls plan headExpr args
      if let some plan := cenv.belowCallSitePlans.get? name then
        if !plan.isIdentity then
          let fixedTailLen := plan.nIndices + 1 -- indices + major
          let expectedTotal :=
            plan.nParams + plan.nSourceMotives + fixedTailLen
          if args.size >= expectedTotal then
            return ← compileBelowCallSite name plan headExpr args
      if let some plan := cenv.brecOnCallSitePlans.get? name then
        if !plan.isIdentity then
          let fixedTailLen := plan.nIndices + 1 -- indices + major
          let expectedTotal := plan.nParams + plan.nSourceMotives
            + fixedTailLen + plan.nSourceMotives
          if args.size >= expectedTotal then
            return ← compileBRecOnCallSite name plan headExpr args
  -- Normal telescope path (compile.rs:1399-1407): head, then one App
  -- node per arg. Same result as one-App-at-a-time recursion, but the
  -- inner spine nodes never touch the expression cache.
  let (h, hRoot) ← compileExpr headExpr
  let mut acc := h
  let mut accRoot := hRoot
  for arg in args do
    let (a, aRoot) ← compileExpr arg
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
    dropped (subsumed by `CallSite.name`, compile.rs:1633). -/
partial def buildCallSite (nameAddr : Address) (headForCanon : Expr)
    (sortedCanon : Array Expr) (collapsedArgs : Array Expr)
    (entries : Array Ixon.CallSiteEntry) (origHeadCollapsed : Bool) :
    CompileM (Ixon.Expr × UInt64) := do
  let (headIxon, _headRoot) ← compileExpr headForCanon
  let mut canonicalExprs : Array Ixon.Expr := #[]
  let mut canonicalRoots : Array UInt64 := #[]
  for arg in sortedCanon do
    let (a, aRoot) ← compileExpr arg
    canonicalExprs := canonicalExprs.push a
    canonicalRoots := canonicalRoots.push aRoot
  let mut collapsedIxon : Array Ixon.Expr := #[]
  let mut collapsedRoots : Array UInt64 := #[]
  for arg in collapsedArgs do
    let (a, aRoot) ← compileExpr arg
    collapsedIxon := collapsedIxon.push a
    collapsedRoots := collapsedRoots.push aRoot
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
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
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
        entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
        collapsedArgs := collapsedArgs.push minor
      else
        entries := entries.push (.kept canonPos.toUInt64 0)
    else
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push minor

  -- Tail (indices + major): always kept, identity.
  let tailCanonBase := plan.nParams + nCanonMotives + nCanonMinors
  for (t, i) in tail.zipIdx do
    canonicalArgs := canonicalArgs.push (tailCanonBase + i, t)
    entries := entries.push (.kept (tailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false

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

  -- Source params don't appear in the target spine (the specs subsume
  -- them) — collapse for reconstruction.
  for p in params do
    entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
    collapsedArgs := collapsedArgs.push p
  let nSpecs := specs.size
  canonicalArgs := canonicalArgs ++ specs
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      canonicalArgs := canonicalArgs.push motive
      entries := entries.push (.kept nSpecs.toUInt64 0)
    else
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
        entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
        collapsedArgs := collapsedArgs.push minor
      else
        entries := entries.push (.kept canonPos.toUInt64 0)
    else
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
  buildCallSite nameAddr headForCanon canonicalArgs collapsedArgs entries true

/-- `.below` call-site surgery (compile.rs:1163-1263): telescope is
    `params, motives, indices, major` — motive keep/reorder mirrors the
    recursor plan; everything after the motives is kept identically. -/
partial def compileBelowCallSite (name : Name)
    (plan : Ix.AuxGen.BRecOnCallSitePlan) (headExpr : Expr)
    (args : Array Expr) : CompileM (Ixon.Expr × UInt64) := do
  let fixedTailLen := plan.nIndices + 1 -- indices + major
  let expectedTotal := plan.nParams + plan.nSourceMotives + fixedTailLen
  compileName name
  let nameAddr := name.getHash
  let params := args.extract 0 plan.nParams
  let motives := args.extract plan.nParams (plan.nParams + plan.nSourceMotives)
  let fixedTail := args.extract (plan.nParams + plan.nSourceMotives) expectedTotal
  let extraTail := args.extract expectedTotal args.size

  let nCanonMotives := plan.nCanonicalMotives
  let mut canonicalArgs : Array (Nat × Expr) := #[]
  let mut collapsedArgs : Array Expr := #[]
  let mut entries : Array Ixon.CallSiteEntry := #[]

  for (p, i) in params.zipIdx do
    canonicalArgs := canonicalArgs.push (i, p)
    entries := entries.push (.kept i.toUInt64 0)

  let motiveCanonBase := plan.nParams
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := motiveCanonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, motive)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push motive

  let fixedTailCanonBase := plan.nParams + nCanonMotives
  for (t, i) in fixedTail.zipIdx do
    canonicalArgs := canonicalArgs.push (fixedTailCanonBase + i, t)
    entries := entries.push (.kept (fixedTailCanonBase + i).toUInt64 0)

  let extraTailCanonBase := fixedTailCanonBase + fixedTailLen
  for (t, i) in extraTail.zipIdx do
    canonicalArgs := canonicalArgs.push (extraTailCanonBase + i, t)
    entries := entries.push (.kept (extraTailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false

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

  for (p, i) in params.zipIdx do
    canonicalArgs := canonicalArgs.push (i, p)
    entries := entries.push (.kept i.toUInt64 0)

  let motiveCanonBase := plan.nParams
  for (motive, srcI) in motives.zipIdx do
    if plan.motiveKeep[srcI]! then
      let canonPos := motiveCanonBase + plan.sourceToCanonMotive[srcI]!
      canonicalArgs := canonicalArgs.push (canonPos, motive)
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
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
      entries := entries.push (.kept canonPos.toUInt64 0)
    else
      entries := entries.push (.collapsed collapsedArgs.size.toUInt64 0)
      collapsedArgs := collapsedArgs.push handler

  let extraTailCanonBase := handlerCanonBase + nCanonMotives
  for (t, i) in extraTail.zipIdx do
    canonicalArgs := canonicalArgs.push (extraTailCanonBase + i, t)
    entries := entries.push (.kept (extraTailCanonBase + i).toUInt64 0)

  let sortedCanon := (sortByCanonIdx canonicalArgs).map (·.2)
  buildCallSite nameAddr headExpr sortedCanon collapsedArgs entries false

end

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

/-- Walk one expression collecting refs and univs for preseeding.
    Mirrors Rust `collect_expr_tables` (compile.rs:490): iterative stack
    walk, deduped by `(expr hash, univ-param-context key)`; nat/str
    literal blobs are stored as a side effect (their addresses join the
    refs), universes are compiled through the shared `univCache`. Must
    run under the expression's own `univCtx` (Rust passes `univ_params`
    explicitly). -/
def collectExprTables (top : Expr) (ctxKey : Address)
    (acc : Array Address × Array Ixon.Univ × Std.HashMap (Address × Address) Unit)
    : CompileM (Array Address × Array Ixon.Univ × Std.HashMap (Address × Address) Unit) := do
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
      if (mutCtx.find? name).isNone then
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

/-- Preseed the block's ref/univ intern tables from the given
    `(expr, levelParams)` list, in canonical sorted order. Mirrors Rust
    `preseed_expr_tables` (compile.rs:576). Call sites mirror Rust's:
    every singleton path in `compileConstantInfo` and the mutual path in
    `compileMutualBlock`. -/
def preseedExprTables (exprs : Array (Expr × List Name)) : CompileM Unit := do
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
  -- Univs: sort by serialized key, dedup by key, intern in order
  -- (`put_univ` is injective, so key equality is univ equality).
  let keyed := univs.map fun u => (univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) => byteArrayCmp ka kb == .lt
  let mut prevKey : Option ByteArray := none
  for (k, u) in sortedUnivs do
    if prevKey != some k then
      discard <| internUniv u
      prevKey := some k

/-- The `(expr, levelParams)` list a MutConst contributes to preseeding.
    Mirrors Rust `collect_mut_const_exprs` (compile.rs:618). -/
def mutConstPreseedExprs (c : MutConst) : Array (Expr × List Name) :=
  match c with
  | .defn d =>
    #[(d.type, d.levelParams.toList), (d.value, d.levelParams.toList)]
  | .indc i => Id.run do
    let mut exprs := #[(i.type, i.levelParams.toList)]
    for ctor in i.ctors do
      exprs := exprs.push (ctor.cnst.type, ctor.cnst.levelParams.toList)
    return exprs
  | .recr r => Id.run do
    let mut exprs := #[(r.cnst.type, r.cnst.levelParams.toList)]
    for rule in r.rules do
      exprs := exprs.push (rule.rhs, r.cnst.levelParams.toList)
    return exprs

/-! ## Level Comparison -/

/-- Compare two Ix levels for ordering. -/
def compareLevel (xctx yctx : List Name)
    : Level → Level → CompileM SOrder
  | .mvar .., _ => throw (.unsupportedExpr "level metavariable")
  | _, .mvar .. => throw (.unsupportedExpr "level metavariable")
  | .zero _, .zero _ => pure ⟨true, .eq⟩
  | .zero _, _ => pure ⟨true, .lt⟩
  | _, .zero _ => pure ⟨true, .gt⟩
  | .succ x _, .succ y _ => compareLevel xctx yctx x y
  | .succ .., _ => pure ⟨true, .lt⟩
  | _, .succ .. => pure ⟨true, .gt⟩
  | .max xl xr _, .max yl yr _ => SOrder.cmpM
    (compareLevel xctx yctx xl yl) (compareLevel xctx yctx xr yr)
  | .max .., _ => pure ⟨true, .lt⟩
  | _, .max .. => pure ⟨true, .gt⟩
  | .imax xl xr _, .imax yl yr _ => SOrder.cmpM
      (compareLevel xctx yctx xl yl) (compareLevel xctx yctx xr yr)
  | .imax .., _ => pure ⟨true, .lt⟩
  | _, .imax .. => pure ⟨true, .gt⟩
  | .param x _, .param y _ => do
    match (xctx.idxOf? x), (yctx.idxOf? y) with
    | some xi, some yi => pure ⟨true, compare xi yi⟩
    | none, _ => throw (.unknownUnivParam s!"{(← getBlockEnv).current}" s!"{x}")
    | _, none => throw (.unknownUnivParam s!"{(← getBlockEnv).current}" s!"{y}")

/-! ## Expression Comparison -/

/-- Name-irrelevant ordering of Ix expressions.
    Matches Rust's compare_expr - no caching, handles mdata inline. -/
partial def compareExpr (ctx : Ix.MutCtx) (xlvls ylvls : List Name)
    (x y : Expr) : CompileM SOrder := do
  match x, y with
  | .mvar .., _ => throw (.unsupportedExpr "metavariable in comparison")
  | _, .mvar .. => throw (.unsupportedExpr "metavariable in comparison")
  | .fvar .., _ => throw (.unsupportedExpr "fvar in comparison")
  | _, .fvar .. => throw (.unsupportedExpr "fvar in comparison")
  | .mdata _ x _, .mdata _ y _ => compareExpr ctx xlvls ylvls x y
  | .mdata _ x _, y => compareExpr ctx xlvls ylvls x y
  | x, .mdata _ y _ => compareExpr ctx xlvls ylvls x y
  | .bvar x _, .bvar y _ => pure ⟨true, compare x y⟩
  | .bvar .., _ => pure ⟨true, .lt⟩
  | _, .bvar .. => pure ⟨true, .gt⟩
  | .sort x _, .sort y _ => compareLevel xlvls ylvls x y
  | .sort .., _ => pure ⟨true, .lt⟩
  | _, .sort .. => pure ⟨true, .gt⟩
  | .const x xls _, .const y yls _ => do
    let univs ← SOrder.zipM (compareLevel xlvls ylvls) xls.toList yls.toList
    if univs.ord != .eq then pure univs
    else if x == y then pure ⟨true, .eq⟩
    else match ctx.find? x, ctx.find? y with
    | some nx, some ny => pure ⟨false, compare nx ny⟩
    | some _, none => pure ⟨true, .lt⟩
    | none, some _ => pure ⟨true, .gt⟩
    | none, none => do
      let x' ← lookupConstAddr x
      let y' ← lookupConstAddr y
      pure ⟨true, compare x' y'⟩
  | .const .., _ => pure ⟨true, .lt⟩
  | _, .const .. => pure ⟨true, .gt⟩
  | .app xf xa _, .app yf ya _ =>
    SOrder.cmpM
      (compareExpr ctx xlvls ylvls xf yf)
      (compareExpr ctx xlvls ylvls xa ya)
  | .app .., _ => pure ⟨true, .lt⟩
  | _, .app .. => pure ⟨true, .gt⟩
  | .lam _ xt xb _ _, .lam _ yt yb _ _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
  | .lam .., _ => pure ⟨true, .lt⟩
  | _, .lam .. => pure ⟨true, .gt⟩
  | .forallE _ xt xb _ _, .forallE _ yt yb _ _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) (compareExpr ctx xlvls ylvls xb yb)
  | .forallE .., _ => pure ⟨true, .lt⟩
  | _, .forallE .. => pure ⟨true, .gt⟩
  | .letE _ xt xv xb _ _, .letE _ yt yv yb _ _ =>
    SOrder.cmpM (compareExpr ctx xlvls ylvls xt yt) <|
    SOrder.cmpM (compareExpr ctx xlvls ylvls xv yv)
      (compareExpr ctx xlvls ylvls xb yb)
  | .letE .., _ => pure ⟨true, .lt⟩
  | _, .letE .. => pure ⟨true, .gt⟩
  | .lit x _, .lit y _ => pure ⟨true, compare x y⟩
  | .lit .., _ => pure ⟨true, .lt⟩
  | _, .lit .. => pure ⟨true, .gt⟩
  | .proj tnx ix tx _, .proj tny iy ty _ => do
    let tn ← match ctx.find? tnx, ctx.find? tny with
      | some nx, some ny => pure ⟨false, compare nx ny⟩
      | none, some _ => pure ⟨true, .gt⟩
      | some _, none => pure ⟨true, .lt⟩
      | none, none =>
        if tnx == tny then pure ⟨true, .eq⟩
        else do
          let x' ← lookupConstAddr tnx
          let y' ← lookupConstAddr tny
          pure ⟨true, compare x' y'⟩
    SOrder.cmpM (pure tn) <|
    SOrder.cmpM (pure ⟨true, compare ix iy⟩)
      (compareExpr ctx xlvls ylvls tx ty)

/-! ## Constant Comparison -/

/-- Compare two mutual constants for ordering. -/
def compareConst (ctx : Ix.MutCtx) (x y : MutConst) : CompileM Ordering := do
  let key := match compare x.name y.name with
    | .lt => (x.name, y.name)
    | _ => (y.name, x.name)
  -- Check cache
  let cache ← getBlockState
  if let some o := cache.cmpCache.get? key then
    return o

  let sorder : SOrder ← match x, y with
  | .defn x, .defn y => compareDef ctx x y
  | .defn _, _ => pure ⟨true, .lt⟩
  | .indc x, .indc y => compareInd ctx x y
  | .indc _, _ => pure ⟨true, .lt⟩
  | .recr x, .recr y => compareRecr ctx x y
  | .recr _, _ => pure ⟨true, .lt⟩

  -- Cache if strong ordering
  if sorder.strong then
    modifyBlockState fun c => { c with cmpCache := c.cmpCache.insert key sorder.ord }
  pure sorder.ord
where
  compareDef (ctx : Ix.MutCtx) (x y : Def) : CompileM SOrder := do
    SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.levelParams.size y.levelParams.size⟩) <|
    SOrder.cmpM (compareExpr ctx x.levelParams.toList y.levelParams.toList x.type y.type)
      (compareExpr ctx x.levelParams.toList y.levelParams.toList x.value y.value)
  compareInd (ctx : Ix.MutCtx) (x y : Ind) : CompileM SOrder := do
    SOrder.cmpM (pure ⟨true, compare x.levelParams.size y.levelParams.size⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.ctors.size y.ctors.size⟩) <|
    SOrder.cmpM (compareExpr ctx x.levelParams.toList y.levelParams.toList x.type y.type)
      (SOrder.zipM (compareCtor ctx x.levelParams.toList y.levelParams.toList) x.ctors.toList y.ctors.toList)
  compareCtor (ctx : Ix.MutCtx) (xlvls ylvls : List Name)
      (x y : ConstructorVal) : CompileM SOrder := do
    -- Cache key: normalize to (smaller, larger) pair
    let key := match compare x.cnst.name y.cnst.name with
      | .lt => (x.cnst.name, y.cnst.name)
      | _ => (y.cnst.name, x.cnst.name)
    -- Check cache first
    let cache ← getBlockState
    if let some o := cache.cmpCache.get? key then
      return ⟨true, o⟩
    -- Compute comparison
    let sorder ←
      SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
      SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩)
        (compareExpr ctx xlvls ylvls x.cnst.type y.cnst.type)
    -- Cache if strong ordering
    if sorder.strong then
      modifyBlockState fun c => { c with cmpCache := c.cmpCache.insert key sorder.ord }
    return sorder
  compareRecr (ctx : Ix.MutCtx) (x y : RecursorVal) : CompileM SOrder := do
    SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numMotives y.numMotives⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numMinors y.numMinors⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.k y.k⟩) <|
    SOrder.cmpM (compareExpr ctx x.cnst.levelParams.toList y.cnst.levelParams.toList x.cnst.type y.cnst.type)
      (SOrder.zipM (compareRule ctx x.cnst.levelParams.toList y.cnst.levelParams.toList) x.rules.toList y.rules.toList)
  compareRule (ctx : Ix.MutCtx) (xlvls ylvls : List Name)
      (x y : RecursorRule) : CompileM SOrder := do
    SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩)
      (compareExpr ctx xlvls ylvls x.rhs y.rhs)

/-- Check if two mutual constants are equal (for grouping). -/
def eqConst (ctx : Ix.MutCtx) (x y : MutConst) : CompileM Bool :=
  (· == .eq) <$> compareConst ctx x y

/-! ## sortConsts Fixed-Point Algorithm -/

/-- Create a MutConst.indc from an InductiveVal by fetching constructors. -/
def MutConst.mkIndc (i : InductiveVal) : CompileM MutConst := do
  let mut ctors : Array ConstructorVal := #[]
  for ctorName in i.ctors do
    let c ← getCtor ctorName
    ctors := ctors.push c
  pure (.indc ⟨i.cnst.name, i.cnst.levelParams, i.cnst.type, i.numParams, i.numIndices, i.all,
    ctors, i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩)
where
  getCtor (name : Name) : CompileM ConstructorVal := do
    match ← findConst name with
    | .ctorInfo c => pure c
    | _ => throw (.invalidMutualBlock s!"Expected constructor: {name}")

/-- Sort mutual constants into ordered equivalence classes.
    Uses partition refinement - starts assuming all equal,
    recursively improves until fixed-point. -/
partial def sortConsts (classes : List MutConst) : CompileM (List (List MutConst)) :=
  go [List.sortBy (compare ·.name ·.name) classes]
where
  go (cs : List (List MutConst)) : CompileM (List (List MutConst)) := do
    let ctx := MutConst.ctx cs
    let cs' ← cs.mapM fun ds =>
      match ds with
      | [] => throw (.invalidMutualBlock "empty class in sortConsts")
      | [d] => pure [[d]]
      | ds => ds.sortByM (compareConst ctx) >>= List.groupByM (eqConst ctx)
    let cs' := cs'.flatten.map (List.sortBy (compare ·.name ·.name))
    if cs == cs' then pure cs' else go cs'

/-! ## Constant Building -/

/-- Count Share references in an expression (for debugging). -/
partial def countShareRefs : Ixon.Expr → Nat
  | .share _ => 1
  | .prj _ _ val => countShareRefs val
  | .app f a => countShareRefs f + countShareRefs a
  | .lam ty body => countShareRefs ty + countShareRefs body
  | .all ty body => countShareRefs ty + countShareRefs body
  | .letE _ ty val body => countShareRefs ty + countShareRefs val + countShareRefs body
  | _ => 0

/-- Update recursor rules with rewritten expressions starting at given index.
    Returns updated rules and next index. -/
def updateRecursorRules (rules : Array Ixon.RecursorRule) (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat)
    : Array Ixon.RecursorRule × Nat := Id.run do
  let mut result := rules
  let mut idx := startIdx
  for i in [:rules.size] do
    if let some rhs := rewrittenExprs[idx]? then
      result := result.set! i { result[i]! with rhs }
    idx := idx + 1
  (result, idx)

/-- Update inductive constructor types with rewritten expressions starting at given index.
    Returns updated constructors and next index. -/
def updateConstructorTypes (ctors : Array Ixon.Constructor) (rewrittenExprs : Array Ixon.Expr) (startIdx : Nat)
    : Array Ixon.Constructor × Nat := Id.run do
  let mut result := ctors
  let mut idx := startIdx
  for i in [:ctors.size] do
    if let some ctorTyp := rewrittenExprs[idx]? then
      result := result.set! i { result[i]! with typ := ctorTyp }
    idx := idx + 1
  (result, idx)

/-- Update Ixon MutConsts with rewritten expressions. -/
def updateMutConsts (ms : Array Ixon.MutConst) (rewrittenExprs : Array Ixon.Expr)
    : Array Ixon.MutConst := Id.run do
  let mut idx := 0
  let mut result := ms
  for i in [:ms.size] do
    match ms[i]! with
    | .indc ind =>
      let typ := rewrittenExprs[idx]?.getD ind.typ
      idx := idx + 1
      let (ctors, nextIdx) := updateConstructorTypes ind.ctors rewrittenExprs idx
      idx := nextIdx
      result := result.set! i (.indc { ind with typ, ctors })
    | .defn d =>
      let typ := rewrittenExprs[idx]?.getD d.typ
      let value := rewrittenExprs[idx + 1]?.getD d.value
      idx := idx + 2
      result := result.set! i (.defn { d with typ, value })
    | .recr r =>
      let typ := rewrittenExprs[idx]?.getD r.typ
      idx := idx + 1
      let (rules, nextIdx) := updateRecursorRules r.rules rewrittenExprs idx
      idx := nextIdx
      result := result.set! i (.recr { r with typ, rules })
  result

/-- Apply sharing analysis to expressions and build a Constant. -/
def buildConstantWithSharing (info : Ixon.ConstantInfo) (rootExprs : Array Ixon.Expr)
    (refs : Array Address) (univs : Array Ixon.Univ) (dbg : Bool := false) : Ixon.Constant := Id.run do
  let (rewrittenExprs, sharingVec) := Sharing.applySharing rootExprs dbg
  -- Debug: count Share refs in rewritten expressions
  if dbg && sharingVec.size > 0 then
    let totalShareRefs := rewrittenExprs.foldl (fun acc e => acc + countShareRefs e) 0
    dbg_trace s!"[buildConstant] sharingVec.size={sharingVec.size}, totalShareRefs in rewritten={totalShareRefs}"
  -- Update expressions in info with rewritten versions
  let info' := match info with
  | .defn d =>
    let typ := rewrittenExprs[0]?.getD d.typ
    let value := rewrittenExprs[1]?.getD d.value
    Ixon.ConstantInfo.defn { d with typ, value }
  | .axio a =>
    let typ := rewrittenExprs[0]?.getD a.typ
    Ixon.ConstantInfo.axio { a with typ }
  | .quot q =>
    let typ := rewrittenExprs[0]?.getD q.typ
    Ixon.ConstantInfo.quot { q with typ }
  | .recr r =>
    let typ := rewrittenExprs[0]?.getD r.typ
    let (rules, _) := updateRecursorRules r.rules rewrittenExprs 1
    Ixon.ConstantInfo.recr { r with typ, rules }
  | .muts ms =>
    Ixon.ConstantInfo.muts (updateMutConsts ms rewrittenExprs)
  | other => other
  return { info := info', sharing := sharingVec, refs, univs }

/-! ## Individual Constant Compilation -/

/-- Convert Lean DefinitionSafety to Ixon DefinitionSafety -/
def convertSafety : Lean.DefinitionSafety → DefinitionSafety
  | .unsafe => .unsaf
  | .safe => .safe
  | .partial => .part

/-- Compile a definition to Ixon.Definition with metadata. -/
def compileDefinition (d : DefinitionVal) : CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := withCurrent d.cnst.name do
  withUnivCtx d.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr d.cnst.type
    let (valueExpr, valueRoot) ← compileExpr d.value
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName d.cnst.name
    for lvl in d.cnst.levelParams do compileName lvl
    for n in d.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

    let nameAddr := d.cnst.name.getHash
    let lvlAddrs := d.cnst.levelParams.map (·.getHash)
    let allAddrs := d.all.map (·.getHash)
    let ctxAddrs ← getMutCtxAddrs

    let defn : Ixon.Definition := {
      kind := .defn
      safety := convertSafety d.safety
      lvls := d.cnst.levelParams.size.toUInt64
      typ := typeExpr
      value := valueExpr
    }
    recordDefHints d.cnst.name d.hints
    let constMeta := { Ixon.ConstantMeta.new
      (.defn nameAddr lvlAddrs allAddrs ctxAddrs arena typeRoot valueRoot) with
      metaSharing := surgerySharing }
    pure (defn, constMeta, typeExpr, valueExpr)

/-- Compile a theorem to Ixon.Definition with metadata. -/
def compileTheorem (d : TheoremVal) : CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := withCurrent d.cnst.name do
  withUnivCtx d.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr d.cnst.type
    let (valueExpr, valueRoot) ← compileExpr d.value
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName d.cnst.name
    for lvl in d.cnst.levelParams do compileName lvl
    for n in d.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

    let nameAddr := d.cnst.name.getHash
    let lvlAddrs := d.cnst.levelParams.map (·.getHash)
    let allAddrs := d.all.map (·.getHash)
    let ctxAddrs ← getMutCtxAddrs

    let defn : Ixon.Definition := {
      kind := .thm
      safety := .safe
      lvls := d.cnst.levelParams.size.toUInt64
      typ := typeExpr
      value := valueExpr
    }
    recordDefHints d.cnst.name .opaque
    let constMeta := { Ixon.ConstantMeta.new
      (.defn nameAddr lvlAddrs allAddrs ctxAddrs arena typeRoot valueRoot) with
      metaSharing := surgerySharing }
    pure (defn, constMeta, typeExpr, valueExpr)

/-- Compile an opaque to Ixon.Definition with metadata. -/
def compileOpaque (d : OpaqueVal) : CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := withCurrent d.cnst.name do
  withUnivCtx d.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr d.cnst.type
    let (valueExpr, valueRoot) ← compileExpr d.value
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName d.cnst.name
    for lvl in d.cnst.levelParams do compileName lvl
    for n in d.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

    let nameAddr := d.cnst.name.getHash
    let lvlAddrs := d.cnst.levelParams.map (·.getHash)
    let allAddrs := d.all.map (·.getHash)
    let ctxAddrs ← getMutCtxAddrs

    let defn : Ixon.Definition := {
      kind := .opaq
      safety := if d.isUnsafe then .unsaf else .safe
      lvls := d.cnst.levelParams.size.toUInt64
      typ := typeExpr
      value := valueExpr
    }
    recordDefHints d.cnst.name .opaque
    let constMeta := { Ixon.ConstantMeta.new
      (.defn nameAddr lvlAddrs allAddrs ctxAddrs arena typeRoot valueRoot) with
      metaSharing := surgerySharing }
    pure (defn, constMeta, typeExpr, valueExpr)

/-- Compile an axiom to Ixon.Axiom with metadata. -/
def compileAxiom (a : AxiomVal) : CompileM (Ixon.Axiom × Ixon.ConstantMeta × Ixon.Expr) := withCurrent a.cnst.name do
  withUnivCtx a.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr a.cnst.type
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName a.cnst.name
    for lvl in a.cnst.levelParams do compileName lvl

    let nameAddr := a.cnst.name.getHash
    let lvlAddrs := a.cnst.levelParams.map (·.getHash)

    let axio : Ixon.Axiom := {
      isUnsafe := a.isUnsafe
      lvls := a.cnst.levelParams.size.toUInt64
      typ := typeExpr
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.axio nameAddr lvlAddrs arena typeRoot) with
      metaSharing := surgerySharing }
    pure (axio, constMeta, typeExpr)

/-- Compile a quotient to Ixon.Quotient with metadata. -/
def compileQuotient (q : QuotVal) : CompileM (Ixon.Quotient × Ixon.ConstantMeta × Ixon.Expr) := withCurrent q.cnst.name do
  withUnivCtx q.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr q.cnst.type
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName q.cnst.name
    for lvl in q.cnst.levelParams do compileName lvl

    let nameAddr := q.cnst.name.getHash
    let lvlAddrs := q.cnst.levelParams.map (·.getHash)

    let kind : QuotKind := match q.kind with
      | .type => .type
      | .ctor => .ctor
      | .lift => .lift
      | .ind => .ind
    let quot : Ixon.Quotient := {
      kind
      lvls := q.cnst.levelParams.size.toUInt64
      typ := typeExpr
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.quot nameAddr lvlAddrs arena typeRoot) with
      metaSharing := surgerySharing }
    pure (quot, constMeta, typeExpr)

/-- Compile a recursor rule to Ixon, returning the ctor address and rhs expression. -/
def compileRecursorRule (rule : RecursorRule) : CompileM (Ixon.RecursorRule × Address × UInt64) := do
  let (rhs, ruleRoot) ← compileExpr rule.rhs
  let ctorAddr := rule.ctor.getHash
  pure ({ fields := rule.nfields.toUInt64, rhs }, ctorAddr, ruleRoot)

/-- Compile a recursor to Ixon.Recursor with metadata. -/
def compileRecursor (r : RecursorVal) : CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) := withCurrent r.cnst.name do
  withUnivCtx r.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr r.cnst.type

    let mut rules : Array Ixon.RecursorRule := #[]
    let mut ruleAddrs : Array Address := #[]
    let mut ruleRoots : Array UInt64 := #[]
    for rule in r.rules do
      let (ixonRule, ctorAddr, ruleRoot) ← compileRecursorRule rule
      rules := rules.push ixonRule
      ruleAddrs := ruleAddrs.push ctorAddr
      ruleRoots := ruleRoots.push ruleRoot

    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName r.cnst.name
    for lvl in r.cnst.levelParams do compileName lvl
    for n in r.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n
    for rule in r.rules do compileName rule.ctor

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
      rules := rules
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.recr nameAddr lvlAddrs ruleAddrs allAddrs ctxAddrs arena typeRoot ruleRoots) with
      metaSharing := surgerySharing }
    pure (recursor, constMeta, typeExpr)

/-- Compile a constructor to Ixon.Constructor with metadata (ConstantMeta.ctor). -/
def compileConstructor (c : ConstructorVal) : CompileM (Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr) := withCurrent c.cnst.name do
  resetArena
  let (typeExpr, typeRoot) ← compileExpr c.cnst.type
  let arena ← takeArena
  let surgerySharing ← takeSurgerySharing
  clearExprCache

  -- Store name string components as blobs for deduplication
  compileName c.cnst.name
  for lvl in c.cnst.levelParams do compileName lvl

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
    metaSharing := surgerySharing }
  pure (ctor, ctorMeta, typeExpr)

/-- Compile an inductive to Ixon.Inductive with metadata.
    Takes the inductive and its constructors (looked up from Ix.Environment).
    Returns (inductive, indc meta, ctor metas with names, all exprs). -/
def compileInductive (i : InductiveVal) (ctorVals : Array ConstructorVal)
    : CompileM (Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := withCurrent i.cnst.name do
  withUnivCtx i.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr i.cnst.type
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    let mut ctors : Array Ixon.Constructor := #[]
    let mut ctorMetaPairs : Array (Name × Ixon.ConstantMeta) := #[]
    let mut ctorNameAddrs : Array Address := #[]
    let mut ctorExprs : Array Ixon.Expr := #[typeExpr]
    for ctorVal in ctorVals do
      let (c, cm, e) ← compileConstructor ctorVal
      ctors := ctors.push c
      ctorMetaPairs := ctorMetaPairs.push (ctorVal.cnst.name, cm)
      ctorNameAddrs := ctorNameAddrs.push ctorVal.cnst.name.getHash
      ctorExprs := ctorExprs.push e

    -- Store name string components as blobs for deduplication
    compileName i.cnst.name
    for lvl in i.cnst.levelParams do compileName lvl
    for n in i.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

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
      ctors := ctors
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.indc nameAddr lvlAddrs ctorNameAddrs allAddrs ctxAddrs arena typeRoot) with
      metaSharing := surgerySharing }
    pure (ind, constMeta, ctorMetaPairs, ctorExprs)

/-! ## Internal compilation helpers for mutual blocks -/

/-- Compile definition data for a Def structure (from Mutual.lean). -/
def compileDefinitionData (d : Def) : CompileM (Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr) := withCurrent d.name do
  withUnivCtx d.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr d.type
    let (valueExpr, valueRoot) ← compileExpr d.value
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name components for deduplication
    compileName d.name
    for lvl in d.levelParams do compileName lvl
    for n in d.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

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
      | .thm => .opaque
      | .opaq => .opaque
    recordDefHints d.name hints
    let constMeta := { Ixon.ConstantMeta.new
      (.defn nameAddr lvlAddrs allAddrs ctxAddrs arena typeRoot valueRoot) with
      metaSharing := surgerySharing }
    pure (defn, constMeta, typeExpr, valueExpr)

/-- Compile inductive data for an Ind structure (from Mutual.lean).
    Returns (inductive, indc meta, ctor metas with names, all exprs). -/
def compileInductiveData (i : Ind)
    : CompileM (Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := withCurrent i.name do
  withUnivCtx i.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr i.type
    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    let mut ctors : Array Ixon.Constructor := #[]
    let mut ctorMetaPairs : Array (Name × Ixon.ConstantMeta) := #[]
    let mut ctorNameAddrs : Array Address := #[]
    let mut ctorExprs : Array Ixon.Expr := #[typeExpr]
    for ctorVal in i.ctors do
      let (c, cm, e) ← compileConstructor ctorVal
      ctors := ctors.push c
      ctorMetaPairs := ctorMetaPairs.push (ctorVal.cnst.name, cm)
      ctorNameAddrs := ctorNameAddrs.push ctorVal.cnst.name.getHash
      ctorExprs := ctorExprs.push e

    -- Store name components for deduplication
    compileName i.name
    for lvl in i.levelParams do compileName lvl
    for n in i.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n

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
      ctors := ctors
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.indc nameAddr lvlAddrs ctorNameAddrs allAddrs ctxAddrs arena typeRoot) with
      metaSharing := surgerySharing }
    pure (ind, constMeta, ctorMetaPairs, ctorExprs)

/-- Compile recursor data for a RecursorVal. -/
def compileRecursorData (r : RecursorVal) : CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) := withCurrent r.cnst.name do
  withUnivCtx r.cnst.levelParams.toList do
    resetArena
    let (typeExpr, typeRoot) ← compileExpr r.cnst.type

    let mut rules : Array Ixon.RecursorRule := #[]
    let mut ruleAddrs : Array Address := #[]
    let mut ruleRoots : Array UInt64 := #[]
    for rule in r.rules do
      let (ixonRule, ctorAddr, ruleRoot) ← compileRecursorRule rule
      rules := rules.push ixonRule
      ruleAddrs := ruleAddrs.push ctorAddr
      ruleRoots := ruleRoots.push ruleRoot

    let arena ← takeArena
    let surgerySharing ← takeSurgerySharing
    clearExprCache

    -- Store name string components as blobs for deduplication
    compileName r.cnst.name
    for lvl in r.cnst.levelParams do compileName lvl
    for n in r.all do compileName n
    for (n, _) in (← getBlockEnv).mutCtx.toList do compileName n
    for rule in r.rules do compileName rule.ctor

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
      rules := rules
    }
    let constMeta := { Ixon.ConstantMeta.new
      (.recr nameAddr lvlAddrs ruleAddrs allAddrs ctxAddrs arena typeRoot ruleRoots) with
      metaSharing := surgerySharing }
    pure (recursor, constMeta, typeExpr)

/-! ## Mutual Block Compilation -/

/-- Compile sorted equivalence classes of mutual constants.
    Returns compiled constants, all root expressions, and metadata for each constant. -/
def compileMutConsts (classes : List (List MutConst))
    : CompileM (Array Ixon.MutConst × Array Ixon.Expr × Array (Name × Ixon.ConstantMeta)) := do
  let mut dat : Array Ixon.MutConst := #[]
  let mut allExprs : Array Ixon.Expr := #[]
  let mut allMetas : Array (Name × Ixon.ConstantMeta) := #[]

  -- Only push one representative per equivalence class into dat,
  -- since alpha-equivalent constants compile to identical data and share
  -- the same class index in MutConst.ctx.
  for constClass in classes do
    let mut representativePushed := false
    for const in constClass do
      match const with
      | .indc i => do
        let (ind, constMeta, ctorMetaPairs, exprs) ← withCurrent i.name (compileInductiveData i)
        if !representativePushed then
          dat := dat.push (Ixon.MutConst.indc ind)
          for e in exprs do
            allExprs := allExprs.push e
          representativePushed := true
        allMetas := allMetas.push (i.name, constMeta)
        for (ctorName, ctorMeta) in ctorMetaPairs do
          allMetas := allMetas.push (ctorName, ctorMeta)
      | .defn d => do
        let (defn, constMeta, tExpr, vExpr) ← withCurrent d.name (compileDefinitionData d)
        if !representativePushed then
          dat := dat.push (Ixon.MutConst.defn defn)
          allExprs := allExprs.push tExpr
          allExprs := allExprs.push vExpr
          representativePushed := true
        allMetas := allMetas.push (d.name, constMeta)
      | .recr r => do
        let (recursor, constMeta, tExpr) ← withCurrent r.cnst.name (compileRecursorData r)
        if !representativePushed then
          dat := dat.push (Ixon.MutConst.recr recursor)
          allExprs := allExprs.push tExpr
          for rule in recursor.rules do
            allExprs := allExprs.push rule.rhs
          representativePushed := true
        allMetas := allMetas.push (r.cnst.name, constMeta)

  pure (dat, allExprs, allMetas)

/-- Compile a mutual block and create projections for each constant.
    Returns the Muts block constant and projections for each name with metadata. -/
def compileMutualBlock (classes : List (List MutConst))
    : CompileM BlockResult := do
  let mutCtx := MutConst.ctx classes
  withMutCtx mutCtx do
    -- Preseed mirrors Rust compile_mutual (compile.rs:3763): collect over
    -- every member (Rust iterates source order, we iterate sorted classes —
    -- equivalent, since the tables are canonically re-sorted afterwards).
    let mut preseedExprs : Array (Expr × List Name) := #[]
    for cls in classes do
      for c in cls do
        preseedExprs := preseedExprs ++ mutConstPreseedExprs c
    preseedExprTables preseedExprs
    let (mutConsts, allExprs, allMetas) ← compileMutConsts classes
    let cache ← getBlockState

    -- Singleton non-inductive representative: emit as a standalone
    -- `Defn`/`Recr` Constant instead of wrapping in `Muts [one]`
    -- (compile.rs:3815-3873). Covers both true singletons routed here
    -- and multi-member blocks whose members all alpha-collapse into ONE
    -- class (e.g. symmetric `partial def` `_unsafe_rec` witnesses).
    -- Self-reference inside the body still uses `Expr.recur 0`, which
    -- the kernel resolves the same way for a single-member block. Every
    -- member of every class registers to the standalone address (via
    -- the projections array — the driver stores the constant once,
    -- content-addressed, and maps each name to it). No synthetic Muts
    -- entry and no aux tail run for these blocks (Rust returns before
    -- both).
    let standaloneInfo? : Option Ixon.ConstantInfo :=
      if mutConsts.size == 1 then
        match mutConsts[0]! with
        | .defn d => some (.defn d)
        | .recr r => some (.recr r)
        | .indc _ => none -- inductive projection scheme requires the block
      else
        none
    if let some info := standaloneInfo? then
      let block := buildConstantWithSharing info allExprs cache.refs cache.univs
      let blockBytes := Ixon.ser block
      let blockAddr := Address.blake3 blockBytes
      let metaMap : Std.HashMap Name Ixon.ConstantMeta :=
        allMetas.foldl (init := {}) fun m (n, cm) => m.insert n cm
      let mut projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
      for constClass in classes do
        for const in constClass do
          let n := const.name
          projections := projections.push (n, block, metaMap.get? n |>.getD .empty)
      return ⟨block, blockBytes, blockAddr, .empty, projections⟩

    let block := buildConstantWithSharing (.muts mutConsts) allExprs cache.refs cache.univs

    -- Serialize once and compute block address
    let blockBytes := Ixon.ser block
    let blockAddr := Address.blake3 blockBytes

    -- Build a lookup map from name to metadata
    let metaMap : Std.HashMap Name Ixon.ConstantMeta := allMetas.foldl (init := {}) fun m (n, constMeta) => m.insert n constMeta

    -- Create projections for each constant
    let mut projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
    let mut idx : UInt64 := 0
    for constClass in classes do
      for const in constClass do
        let projInfo : Ixon.ConstantInfo := match const with
          | .defn _ => .dPrj ⟨idx, blockAddr⟩
          | .indc _ => .iPrj ⟨idx, blockAddr⟩
          | .recr _ => .rPrj ⟨idx, blockAddr⟩
        let proj : Ixon.Constant := ⟨projInfo, #[], #[], #[]⟩
        let constMeta := metaMap.get? const.name |>.getD .empty
        projections := projections.push (const.name, proj, constMeta)

        -- For inductives, also create constructor projections
        if let .indc i := const then
          let mut cidx : UInt64 := 0
          for ctor in i.ctors do
            let ctorProjInfo : Ixon.ConstantInfo := .cPrj ⟨idx, cidx, blockAddr⟩
            let ctorProj : Ixon.Constant := ⟨ctorProjInfo, #[], #[], #[]⟩
            let ctorMeta := metaMap.get? ctor.cnst.name |>.getD .empty
            projections := projections.push (ctor.cnst.name, ctorProj, ctorMeta)
            cidx := cidx + 1
      idx := idx + 1

    pure ⟨block, blockBytes, blockAddr, .empty, projections⟩

/-! ## Main Compilation Entry Points -/

/-- Build mutCtx for an inductive: includes the inductive and all its constructors. -/
def buildInductiveMutCtx (i : InductiveVal) (ctorVals : Array ConstructorVal) : Ix.MutCtx := Id.run do
  let mut ctx : Ix.MutCtx := Batteries.RBMap.empty
  -- Inductive at index 0
  ctx := ctx.insert i.cnst.name 0
  -- Constructors at indices 1, 2, ...
  for (ctor, idx) in ctorVals.zipIdx do
    ctx := ctx.insert ctor.cnst.name (idx + 1)
  return ctx

/-- Build a BlockResult from a block constant, serializing once. -/
def BlockResult.mk' (block : Ixon.Constant) (blockMeta : Ixon.ConstantMeta := .empty)
    (projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]) : BlockResult :=
  let blockBytes := Ixon.ser block
  let blockAddr := Address.blake3 blockBytes
  ⟨block, blockBytes, blockAddr, blockMeta, projections⟩

/-- Compile a single Ix.ConstantInfo directly (singleton, non-mutual).
    Returns BlockResult with the constant and any projections needed. -/
def compileConstantInfo (const : ConstantInfo) : CompileM BlockResult := do
  let name := const.getCnst.name
  let mutCtx : Ix.MutCtx := Batteries.RBMap.empty.insert name 0
  withMutCtx mutCtx do
    match const with
    | .defnInfo d =>
      -- Preseed mirrors Rust compile_single_def (compile.rs:3492).
      preseedExprTables
        #[(d.cnst.type, d.cnst.levelParams.toList), (d.value, d.cnst.levelParams.toList)]
      let (defn, constMeta, tExpr, vExpr) ← compileDefinition d
      let cache ← getBlockState
      let block := buildConstantWithSharing (.defn defn) #[tExpr, vExpr] cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .thmInfo d =>
      preseedExprTables
        #[(d.cnst.type, d.cnst.levelParams.toList), (d.value, d.cnst.levelParams.toList)]
      let (defn, constMeta, tExpr, vExpr) ← compileTheorem d
      let cache ← getBlockState
      let block := buildConstantWithSharing (.defn defn) #[tExpr, vExpr] cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .opaqueInfo d =>
      preseedExprTables
        #[(d.cnst.type, d.cnst.levelParams.toList), (d.value, d.cnst.levelParams.toList)]
      let (defn, constMeta, tExpr, vExpr) ← compileOpaque d
      let cache ← getBlockState
      let block := buildConstantWithSharing (.defn defn) #[tExpr, vExpr] cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .axiomInfo a =>
      -- Preseed mirrors Rust compile_const_inner Axiom arm (compile.rs:3584).
      preseedExprTables #[(a.cnst.type, a.cnst.levelParams.toList)]
      let (axio, constMeta, typeExpr) ← compileAxiom a
      let cache ← getBlockState
      let block := buildConstantWithSharing (.axio axio) #[typeExpr] cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .quotInfo q =>
      preseedExprTables #[(q.cnst.type, q.cnst.levelParams.toList)]
      let (quot, constMeta, typeExpr) ← compileQuotient q
      let cache ← getBlockState
      let block := buildConstantWithSharing (.quot quot) #[typeExpr] cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .recInfo r =>
      -- Preseed mirrors Rust compile_const_inner RecInfo arm (compile.rs:3656).
      preseedExprTables (mutConstPreseedExprs (.recr r))
      let (recursor, constMeta, tExpr) ← compileRecursor r
      let mut allExprs : Array Ixon.Expr := #[tExpr]
      for rule in recursor.rules do
        allExprs := allExprs.push rule.rhs
      let cache ← getBlockState
      let block := buildConstantWithSharing (.recr recursor) allExprs cache.refs cache.univs
      pure (BlockResult.mk' block constMeta)

    | .inductInfo i =>
      -- Look up constructor values from environment
      let mut ctorVals : Array ConstructorVal := #[]
      for ctorName in i.ctors do
        let ctorConst ← findConst ctorName
        match ctorConst with
        | .ctorInfo c => ctorVals := ctorVals.push c
        | _ => throw (.invalidMutualBlock s!"Expected constructor for {ctorName}")
      -- Build mutCtx with all names in the inductive family
      let indMutCtx := buildInductiveMutCtx i ctorVals
      withMutCtx indMutCtx do
        -- Preseed mirrors Rust: singleton inductives route through
        -- compile_mutual (compile.rs:3645), whose preseed collects the
        -- inductive's type plus every constructor type (compile.rs:3763).
        preseedExprTables (mutConstPreseedExprs (MutConst.fromInductiveVal i ctorVals))
        let (ind, indMeta, ctorMetaPairs, ctorExprs) ← compileInductive i ctorVals
        let cache ← getBlockState
        -- Wrap single inductive in muts for consistency
        let block := buildConstantWithSharing (.muts #[.indc ind]) ctorExprs cache.refs cache.univs
        -- Compute block address for projections
        let blockBytes := Ixon.ser block
        let blockAddr := Address.blake3 blockBytes
        -- Create projections for inductive and constructors
        let mut projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
        -- Inductive projection (index 0)
        let indProjInfo : Ixon.ConstantInfo := .iPrj ⟨0, blockAddr⟩
        let indProj : Ixon.Constant := ⟨indProjInfo, #[], #[], #[]⟩
        projections := projections.push (i.cnst.name, indProj, indMeta)
        -- Constructor projections from ctorMetaPairs
        for ((ctorName, ctorMeta), cidx) in ctorMetaPairs.zipIdx do
          let ctorProjInfo : Ixon.ConstantInfo := .cPrj ⟨0, cidx.toUInt64, blockAddr⟩
          let ctorProj : Ixon.Constant := ⟨ctorProjInfo, #[], #[], #[]⟩
          projections := projections.push (ctorName, ctorProj, ctorMeta)
        pure ⟨block, blockBytes, blockAddr, .empty, projections⟩

    | .ctorInfo c =>
      -- Constructors are compiled by compiling their parent inductive
      let parentConst ← findConst c.induct
      match parentConst with
      | .inductInfo i =>
        let mut ctorVals : Array ConstructorVal := #[]
        for ctorName in i.ctors do
          let ctorConst ← findConst ctorName
          match ctorConst with
          | .ctorInfo cv => ctorVals := ctorVals.push cv
          | _ => throw (.invalidMutualBlock s!"Expected constructor")
        -- Build mutCtx with all names in the inductive family
        let indMutCtx := buildInductiveMutCtx i ctorVals
        withMutCtx indMutCtx do
          preseedExprTables (mutConstPreseedExprs (MutConst.fromInductiveVal i ctorVals))
          let (ind, indMeta, ctorMetaPairs, ctorExprs) ← compileInductive i ctorVals
          let cache ← getBlockState
          let block := buildConstantWithSharing (.muts #[.indc ind]) ctorExprs cache.refs cache.univs
          let blockBytes := Ixon.ser block
          let blockAddr := Address.blake3 blockBytes
          let mut projections : Array (Name × Ixon.Constant × Ixon.ConstantMeta) := #[]
          let indProjInfo : Ixon.ConstantInfo := .iPrj ⟨0, blockAddr⟩
          let indProj : Ixon.Constant := ⟨indProjInfo, #[], #[], #[]⟩
          projections := projections.push (i.cnst.name, indProj, indMeta)
          for ((ctorName, ctorMeta), cidx) in ctorMetaPairs.zipIdx do
            let ctorProjInfo : Ixon.ConstantInfo := .cPrj ⟨0, cidx.toUInt64, blockAddr⟩
            let ctorProj : Ixon.Constant := ⟨ctorProjInfo, #[], #[], #[]⟩
            projections := projections.push (ctorName, ctorProj, ctorMeta)
          pure ⟨block, blockBytes, blockAddr, .empty, projections⟩
      | _ => throw (.invalidMutualBlock s!"Constructor has non-inductive parent")

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
    -- Multi-constant mutual block
    let mut consts : Array MutConst := #[]
    for n in all do
      match ← findConst n with
      | .inductInfo val => consts := consts.push (← MutConst.mkIndc val)
      | .defnInfo val => consts := consts.push (MutConst.fromDefinitionVal val)
      | .opaqueInfo val => consts := consts.push (MutConst.fromOpaqueVal val)
      | .thmInfo val => consts := consts.push (MutConst.fromTheoremVal val)
      | .recInfo val => consts := consts.push (.recr val)
      | _ => continue

    let mutConsts ← sortConsts consts.toList
    compileMutualBlock mutConsts

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
        constants := compileEnv.constants.insert blockAddr result.block
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
            constants := compileEnv.constants.insert projAddr proj
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
      fun m a c => m.insert a (Ixon.LazyConstant.ofConstant c)
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
  /-- Compiled constants storage -/
  constants : Std.HashMap Address Ixon.Constant
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

/-- FFI: Compile a Lean environment and write the serialized Ixon.Env
    bytes straight to `outPath` from Rust (streamed; no env-sized
    ByteArray crosses the FFI). Writes to `<outPath>.tmp` then renames,
    so a crash cannot leave a truncated file. Returns the byte count
    written. -/
@[extern "rs_compile_env"]
opaque rsCompileEnvBytesFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → @& String → IO Nat

/-- FFI: 8-phase validation of the aux_gen compile pipeline (compile +
    decompile + roundtrip + alpha-equivalence + nested-detect checks).
    Returns total failure count across all phases.

    Shared between the `ix validate` CLI subcommand (`Ix.Cli.ValidateCmd`)
    and the `validate-aux` test runner (`Tests.Ix.Compile.ValidateAux`).
    The underlying Rust function is `rs_compile_validate_aux` in
    `src/ffi/lean_env.rs`. -/
@[extern "rs_compile_validate_aux"]
opaque rsCompileValidateAuxFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → USize

/-- Compile a Lean environment and write the serialized Ixon.Env bytes
    to `outPath` using the Rust compiler. Returns the byte count. -/
def rsCompileEnvBytes (leanEnv : Lean.Environment) (outPath : String)
    : IO Nat := do
  let constList := leanEnv.constants.toList
  rsCompileEnvBytesFFI constList outPath

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
    `Tests.Ix.Kernel.BuildPrimOrigs` to regenerate `PrimOrigAddrs` in
    the Rust kernel. -/
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

/-- Run all compilation phases using Rust and convert to Lean-friendly types.
    This is the main entry point for getting Rust compilation results. -/
def rsCompilePhases (leanEnv : Lean.Environment) : IO CompilePhases := do
  let constList := leanEnv.constants.toList
  let raw ← rsCompilePhasesFFI constList

  -- Convert RawEnvironment to Environment
  let rawEnv := raw.rawEnv.toEnvironment

  -- Convert RustCondensedBlocks to CondensedBlocks
  let condensed := raw.condensed.toCondensedBlocks

  -- Convert RawEnv to Ixon.Env
  let compileEnv := raw.compileEnv.toEnv

  pure { rawEnv, condensed, compileEnv }

/-- Compile a Lean environment to Ixon.Env using the Rust compiler.
    Uses the direct FFI that returns structured Lean objects. -/
def rsCompileEnv (leanEnv : Lean.Environment) : IO Ixon.Env := do
  let constList := leanEnv.constants.toList
  let rawEnv ← rsCompileEnvFFI constList
  pure rawEnv.toEnv

end
end Ix.CompileM
