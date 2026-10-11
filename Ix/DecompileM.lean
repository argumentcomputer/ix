module
/-
  DecompileM: Decompilation from the Ixon format to Ix types.

  This module decompiles the Ixon format (with indirection tables, sharing,
  and per-expression metadata arenas) back to Ix expressions and constants.
  It is the inverse of the compilation pipeline.

  The output is Ix.Expr / Ix.ConstantInfo (with content hashes), NOT Lean.Expr.
  Conversion from Ix.Expr → Lean.Expr (decanonicalization) is a separate trivial step.
  This design enables cheap hash-based comparison of decompiled results.
-/

public import Ix.Ixon
public import Ix.SemanticContract
public import Ix.Address
public import Ix.Environment
public import Ix.Common
public import Ix.AuxGen.ExprUtils
public import Ix.Compile.Pass.Names

public section

namespace Ix.DecompileM

open Ixon

/-! ## Name Helpers -/

/-- Convert Ix.Name to Lean.Name by stripping embedded hashes. -/
def ixNameToLean : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str parent s _ => .str (ixNameToLean parent) s
  | .num parent n _ => .num (ixNameToLean parent) n

/-- Resolve an address to Ix.Name from the names table. -/
def resolveIxName (names : Std.HashMap Address Ix.Name) (addr : Address) : Option Ix.Name :=
  names.get? addr

/-! ## Error Type -/

/-- Decompilation error type. Variant order matches Rust DecompileError (tags 0–11). -/
inductive DecompileError where
  | invalidRefIndex (idx : UInt64) (refsLen : Nat) (constant : String)
  | invalidUnivIndex (idx : UInt64) (univsLen : Nat) (constant : String)
  | invalidShareIndex (idx : UInt64) (max : Nat) (constant : String)
  | invalidRecIndex (idx : UInt64) (ctxSize : Nat) (constant : String)
  | invalidUnivVarIndex (idx : UInt64) (max : Nat) (constant : String)
  | missingAddress (addr : Address)
  | missingMetadata (addr : Address)
  | blobNotFound (addr : Address)
  | badBlobFormat (addr : Address) (expected : String)
  | badConstantFormat (msg : String)
  | serializeError (err : Ixon.SerializeError)
  /-- `share idx` occurring in `metaSharing[entry]` outside that entry's
      index space (`ConstantMeta.metaSharing`): with `primaryLen` primary
      and `metaLen` metadata entries, the valid indices are
      `idx < primaryLen + entry`. `idx ≥ primaryLen + metaLen` is out of
      range; any other rejected index is a forward or self reference. -/
  | invalidMetaShareIndex (idx : UInt64) (entry : UInt64) (primaryLen : Nat)
      (metaLen : Nat) (constant : String)
  deriving Repr, BEq

def DecompileError.toString : DecompileError → String
  | .invalidRefIndex idx len c => s!"Invalid ref index {idx} in '{c}': refs table has {len} entries"
  | .invalidUnivIndex idx len c => s!"Invalid univ index {idx} in '{c}': univs table has {len} entries"
  | .invalidShareIndex idx max c => s!"Invalid share index {idx} in '{c}': sharing vector has {max} entries"
  | .invalidRecIndex idx sz c => s!"Invalid rec index {idx} in '{c}': mutual context has {sz} entries"
  | .invalidUnivVarIndex idx max c => s!"Invalid univ var index {idx} in '{c}': only {max} level params"
  | .missingAddress addr => s!"Missing address: {addr}"
  | .missingMetadata addr => s!"Missing metadata for: {addr}"
  | .blobNotFound addr => s!"Blob not found at: {addr}"
  | .badBlobFormat addr expected => s!"Bad blob format at {addr}, expected {expected}"
  | .badConstantFormat msg => s!"Bad constant format: {msg}"
  | .serializeError err => s!"Serialization error: {err}"
  | .invalidMetaShareIndex idx entry p q c =>
    if idx.toNat ≥ p + q then
      s!"Invalid metadata share index {idx} in metaSharing[{entry}] of '{c}': \
        out of range ({p} primary + {q} metadata entries)"
    else
      s!"Invalid metadata share index {idx} in metaSharing[{entry}] of '{c}': \
        forward or self reference (this entry may reference only indices below \
        {p + entry.toNat})"

instance : ToString DecompileError := ⟨DecompileError.toString⟩

/-! ## Context and State Structures -/

/-- Global decompilation environment (reader, immutable). -/
structure DecompileEnv where
  ixonEnv : Ixon.Env
  /-- Read the compiled term under a Pass 3 decompile record (`_ix.inline`)
      instead of replaying the recorded source occurrence. Off everywhere
      but `ix validate-lean`'s clique value phase, which evaluates the
      compiled (transported) value of a clique member against Lean's. -/
  compiledTerms : Bool := false
  deriving Inhabited

/-- Per-block context for decompiling a single constant (reader, immutable per-block). -/
structure BlockCtx where
  refs : Array Address
  univs : Array Ixon.Univ
  sharing : Array Ixon.Expr
  mutCtx : Array Ix.Name       -- mutual context: index = Rec index
  univParams : Array Ix.Name   -- universe parameter names
  arena : ExprMetaArena
  /-- `ConstantMeta.metaSharing` of the constant being decompiled: the
      source occurrences of its Pass 3 decompile records (`_ix.inline`),
      or, in a file the legacy call-site surgery wrote (deleted at M6R
      slice 6; read, never written), its collapsed call-site arguments and
      rewritten original heads, indexed by
      `CallSiteEntry.collapsed.sharingIdx` / `origHead` —
      distinct from the block's primary `sharing` table. A `share` inside
      one of these expressions is read in the extended index space
      (`ShareScope.metaEntry`). -/
  metaSharing : Array Ixon.Expr := #[]
  /-- Level-spelling patches of the constant being decompiled, keyed by
      metadata-arena index (canonicity §10.6): a patched `sort`/`ref`/
      `recur` occurrence (or surgered call-site head) resolves the
      patch's univ indices — written in the VIRTUAL space
      `univs ++ metaUnivs`, i.e. this ctx's already-extended `univs` —
      instead of the node's own canonical indices. Absent patch → the
      canonical spelling (the D4 foreign-artifact semantics). -/
  univPatches : Std.HashMap UInt64 (Array UInt64) := {}
  deriving Inhabited

/-- The index space a `share i` node is read in: the extended index space
    of `ConstantMeta.metaSharing`. With `p` primary entries
    (`BlockCtx.sharing`) and `q` metadata entries (`BlockCtx.metaSharing`):

    * `primary`: a primary expression (a root or a primary table entry).
      `share i` denotes `sharing[i]`; `i ≥ p` is `invalidShareIndex`.
      Metadata never changes how a primary expression decodes.
    * `metaEntry j`: an expression of `metaSharing[j]`. `share i` denotes
      primary entry `i` when `i < p` (read in `primary`: shares nested in a
      primary entry stay primary) and `metaSharing[i - p]` when
      `p ≤ i < p + j` (read in `metaEntry (i - p)`). Any other index is
      `invalidMetaShareIndex`: `i ≥ p + q` is out of range,
      `p + j ≤ i < p + q` a forward or self reference. The entry index
      strictly decreases along metadata-to-metadata resolution, so
      expansion is well founded.

    Call-site references (`CallSiteEntry.collapsed sharingIdx`,
    `origHead = some (sharingIdx, _)`) index `metaSharing` directly (no
    offset by `p`) and read the entry in scope `metaEntry sharingIdx`.
    Mirrors Rust `decompile::ShareScope`. -/
inductive ShareScope where
  | primary
  | metaEntry (entry : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Per-block mutable state (caches). The expression cache is keyed by the
    share scope too: the same Ixon expression may be valid in a metadata
    scope and invalid in the primary scope. -/
structure BlockState where
  exprCache : Std.HashMap (Ixon.Expr × UInt64 × ShareScope) Ix.Expr := {}
  univCache : Std.HashMap UInt64 Ix.Level := {}
  deriving Inhabited

/-! ## DecompileM Monad -/

abbrev DecompileM := ReaderT (DecompileEnv × BlockCtx) (ExceptT DecompileError (StateT BlockState Id))

def DecompileM.run (env : DecompileEnv) (ctx : BlockCtx) (stt : BlockState)
    (m : DecompileM α) : Except DecompileError (α × BlockState) :=
  match StateT.run (ExceptT.run (ReaderT.run m (env, ctx))) stt with
  | (Except.ok a, stt') => Except.ok (a, stt')
  | (Except.error e, _) => Except.error e

def getEnv : DecompileM DecompileEnv := (·.1) <$> read
def getCtx : DecompileM BlockCtx := (·.2) <$> read

def withBlockCtx (ctx : BlockCtx) (m : DecompileM α) : DecompileM α :=
  fun (env, _) => m (env, ctx)

/-! ## Lookup Helpers -/

/-- Resolve Address → Ix.Name via names table, or throw. -/
def lookupNameAddr (addr : Address) : DecompileM Ix.Name := do
  match (← getEnv).ixonEnv.names.get? addr with
  | some n => pure n
  | none => throw (.missingAddress addr)

/-- Resolve Address → Ix.Name via names table, or anonymous. -/
def lookupNameAddrOrAnon (addr : Address) : DecompileM Ix.Name := do
  match (← getEnv).ixonEnv.names.get? addr with
  | some n => pure n
  | none => pure Ix.Name.mkAnon

/-- Resolve constant Address → Ix.Name via addrToName. -/
def lookupConstName (addr : Address) : DecompileM Ix.Name := do
  match (← getEnv).ixonEnv.addrToName.get? addr with
  | some n => pure n
  | none => throw (.missingAddress addr)

def lookupBlob (addr : Address) : DecompileM ByteArray := do
  match (← getEnv).ixonEnv.blobs.get? addr with
  | some blob => pure blob
  | none => throw (.blobNotFound addr)

def getRef (idx : UInt64) : DecompileM Address := do
  let ctx ← getCtx
  match ctx.refs[idx.toNat]? with
  | some addr => pure addr
  | none => throw (.invalidRefIndex idx ctx.refs.size "")

def getMutName (idx : UInt64) : DecompileM Ix.Name := do
  let ctx ← getCtx
  match ctx.mutCtx[idx.toNat]? with
  | some name => pure name
  | none => throw (.invalidRecIndex idx ctx.mutCtx.size "")

def readNatBlob (blob : ByteArray) : Nat := Nat.fromBytesLE blob.data

def readStringBlob (blob : ByteArray) : DecompileM String :=
  match String.fromUTF8? blob with
  | some s => pure s
  -- TODO: pass actual blob address instead of empty for better error diagnostics
  | none => throw (.badBlobFormat ⟨ByteArray.empty⟩ "UTF-8 string")

/-! ## Universe Decompilation → Ix.Level -/

partial def decompileUniv (u : Ixon.Univ) : DecompileM Ix.Level := do
  let ctx ← getCtx
  match u with
  | .zero => pure Ix.Level.mkZero
  | .succ inner => Ix.Level.mkSucc <$> decompileUniv inner
  | .max a b => Ix.Level.mkMax <$> decompileUniv a <*> decompileUniv b
  | .imax a b => Ix.Level.mkIMax <$> decompileUniv a <*> decompileUniv b
  | .var idx =>
    match ctx.univParams[idx.toNat]? with
    | some name => pure (Ix.Level.mkParam name)
    | none => throw (.invalidUnivVarIndex idx ctx.univParams.size "")

def getUniv (idx : UInt64) : DecompileM Ix.Level := do
  let stt ← get
  if let some cached := stt.univCache.get? idx then return cached
  let ctx ← getCtx
  match ctx.univs[idx.toNat]? with
  | some u =>
    let lvl ← decompileUniv u
    modify fun s => { s with univCache := s.univCache.insert idx lvl }
    pure lvl
  | none => throw (.invalidUnivIndex idx ctx.univs.size "")

def decompileUnivIndices (indices : Array UInt64) : DecompileM (Array Ix.Level) :=
  indices.mapM getUniv

/-! ## DataValue and KVMap Decompilation → Ix types -/

def deserializeInt (bytes : ByteArray) : DecompileM Ix.Int :=
  if bytes.size == 0 then throw (.badConstantFormat "deserialize_int: empty")
  else
    let tag := bytes.get! 0
    let rest := bytes.extract 1 bytes.size
    let n := Nat.fromBytesLE rest.data
    if tag == 0 then pure (.ofNat n)
    else if tag == 1 then pure (.negSucc n)
    else throw (.badConstantFormat "deserialize_int: invalid tag")

/-! ### Blob cursor helpers -/

structure BlobCursor where
  bytes : ByteArray
  pos : Nat
  deriving Inhabited

def BlobCursor.readByte (c : BlobCursor) : DecompileM (UInt8 × BlobCursor) :=
  if c.pos < c.bytes.size then
    pure (c.bytes.get! c.pos, { c with pos := c.pos + 1 })
  else throw (.badConstantFormat "BlobCursor: unexpected EOF")

/-- A TagN (`f = 0`) integer, read by `Ixon.getTagN 0`. -/
def BlobCursor.readTagN0 (c : BlobCursor) : DecompileM (UInt64 × BlobCursor) :=
  match (Ixon.getTagN 0).run { idx := c.pos, bytes := c.bytes } with
  | .ok t s => pure (t.value, { c with pos := s.idx })
  | .error e _ => throw (.badConstantFormat s!"BlobCursor.readTagN0: {e}")

def BlobCursor.readAddr (c : BlobCursor) : DecompileM (Address × BlobCursor) :=
  if c.pos + 32 ≤ c.bytes.size then
    pure (⟨c.bytes.extract c.pos (c.pos + 32)⟩, { c with pos := c.pos + 32 })
  else throw (.badConstantFormat "BlobCursor.readAddr: need 32 bytes")

def resolveNameFromBlob (addr : Address) : DecompileM Ix.Name :=
  lookupNameAddrOrAnon addr

def resolveStringFromBlob (addr : Address) : DecompileM String := do
  lookupBlob addr >>= readStringBlob

/-! ### Syntax deserialization → Ix.Syntax -/

def deserializeSubstring (c : BlobCursor) : DecompileM (Ix.Substring × BlobCursor) := do
  let (strAddr, c) ← c.readAddr
  let s ← resolveStringFromBlob strAddr
  let (startPos, c) ← c.readTagN0
  let (stopPos, c) ← c.readTagN0
  pure (⟨s, startPos.toNat, stopPos.toNat⟩, c)

def deserializeSourceInfo (c : BlobCursor) : DecompileM (Ix.SourceInfo × BlobCursor) := do
  let (tag, c) ← c.readByte
  match tag with
  | 0 =>
    let (leading, c) ← deserializeSubstring c
    let (leadingPos, c) ← c.readTagN0
    let (trailing, c) ← deserializeSubstring c
    let (trailingPos, c) ← c.readTagN0
    pure (.original leading leadingPos.toNat trailing trailingPos.toNat, c)
  | 1 =>
    let (start, c) ← c.readTagN0
    let (stop, c) ← c.readTagN0
    let (canonical, c) ← c.readByte
    pure (.synthetic start.toNat stop.toNat (canonical != 0), c)
  | 2 => pure (.none, c)
  | _ => throw (.badConstantFormat s!"deserializeSourceInfo: invalid tag {tag}")

def deserializePreresolved (c : BlobCursor) : DecompileM (Ix.SyntaxPreresolved × BlobCursor) := do
  let (tag, c) ← c.readByte
  match tag with
  | 0 =>
    let (nameAddr, c) ← c.readAddr
    let name ← resolveNameFromBlob nameAddr
    pure (.namespace name, c)
  | 1 =>
    let (nameAddr, c) ← c.readAddr
    let name ← resolveNameFromBlob nameAddr
    let (count, c) ← c.readTagN0
    let mut fields : Array String := #[]
    let mut cur := c
    for _ in [:count.toNat] do
      let (fieldAddr, c') ← cur.readAddr
      let field ← resolveStringFromBlob fieldAddr
      fields := fields.push field
      cur := c'
    pure (.decl name fields, cur)
  | _ => throw (.badConstantFormat s!"deserializePreresolved: invalid tag {tag}")

partial def deserializeSyntax (c : BlobCursor) : DecompileM (Ix.Syntax × BlobCursor) := do
  let (tag, c) ← c.readByte
  match tag with
  | 0 => pure (.missing, c)
  | 1 =>
    let (info, c) ← deserializeSourceInfo c
    let (kindAddr, c) ← c.readAddr
    let kind ← resolveNameFromBlob kindAddr
    let (argCount, c) ← c.readTagN0
    let mut args : Array Ix.Syntax := #[]
    let mut cur := c
    for _ in [:argCount.toNat] do
      let (arg, c') ← deserializeSyntax cur
      args := args.push arg
      cur := c'
    pure (.node info kind args, cur)
  | 2 =>
    let (info, c) ← deserializeSourceInfo c
    let (valAddr, c) ← c.readAddr
    let val ← resolveStringFromBlob valAddr
    pure (.atom info val, c)
  | 3 =>
    let (info, c) ← deserializeSourceInfo c
    let (rawVal, c) ← deserializeSubstring c
    let (valAddr, c) ← c.readAddr
    let val ← resolveNameFromBlob valAddr
    let (prCount, c) ← c.readTagN0
    let mut preresolved : Array Ix.SyntaxPreresolved := #[]
    let mut cur := c
    for _ in [:prCount.toNat] do
      let (pr, c') ← deserializePreresolved cur
      preresolved := preresolved.push pr
      cur := c'
    pure (.ident info rawVal val preresolved, cur)
  | _ => throw (.badConstantFormat s!"deserializeSyntax: invalid tag {tag}")

def deserializeSyntaxBlob (blob : ByteArray) : DecompileM Ix.Syntax := do
  let (syn, _) ← deserializeSyntax ⟨blob, 0⟩
  pure syn

/-- Decompile an Ixon DataValue to an Ix DataValue. -/
def decompileDataValue (dv : Ixon.DataValue) : DecompileM Ix.DataValue :=
  match dv with
  | .ofString addr => do pure (.ofString (← lookupBlob addr >>= readStringBlob))
  | .ofBool b => pure (.ofBool b)
  | .ofName addr => do pure (.ofName (← lookupNameAddr addr))
  | .ofNat addr => do pure (.ofNat (readNatBlob (← lookupBlob addr)))
  | .ofInt addr => do pure (.ofInt (← lookupBlob addr >>= deserializeInt))
  | .ofSyntax addr => do pure (.ofSyntax (← lookupBlob addr >>= deserializeSyntaxBlob))

/-- Decompile an Ixon KVMap to Ix mdata format. -/
def decompileKVMap (kvm : Ixon.KVMap) : DecompileM (Array (Ix.Name × Ix.DataValue)) := do
  let mut result : Array (Ix.Name × Ix.DataValue) := #[]
  for (keyAddr, dataVal) in kvm do
    let keyName ← lookupNameAddr keyAddr
    let val ← decompileDataValue dataVal
    result := result.push (keyName, val)
  pure result

/-! ## Mdata Application -/

/-- Apply collected mdata layers to an Ix.Expr (outermost-first). -/
def applyMdata (expr : Ix.Expr) (layers : Array (Array (Ix.Name × Ix.DataValue))) : Ix.Expr :=
  layers.foldr (init := expr) fun mdata e => Ix.Expr.mkMData mdata e

/-! ## Expression Decompilation → Ix.Expr -/

def getArenaNode (idx : UInt64) : DecompileM ExprMetaData := do
  pure ((← getCtx).arena.nodes[idx.toNat]?.getD .leaf)

/-! ## Share Resolution (extended index space of `metaSharing`) -/

/-- Resolve `share idx` read in `scope` (see `ShareScope`): the target
    expression and the scope its own `share` nodes are read in. `label`
    names the reading site in errors. Mirrors Rust
    `BlockCache::resolve_share`. -/
def resolveShareIn (ctx : BlockCtx) (scope : ShareScope) (idx : UInt64)
    (label : String := "") : Except DecompileError (Ixon.Expr × ShareScope) :=
  let p := ctx.sharing.size
  let i := idx.toNat
  match scope with
  | .primary =>
    match ctx.sharing[i]? with
    | some e => .ok (e, .primary)
    | none => .error (.invalidShareIndex idx p label)
  | .metaEntry entry =>
    if h : i < p then .ok (ctx.sharing[i], .primary)
    else
      let target := if i - p < entry then ctx.metaSharing[i - p]? else none
      match target with
      | some e => .ok (e, .metaEntry (i - p))
      | none => .error (.invalidMetaShareIndex idx entry.toUInt64 p
          ctx.metaSharing.size label)

/-- `resolveShareIn` against the current block context. -/
def resolveShare (scope : ShareScope) (idx : UInt64) (label : String := "") :
    DecompileM (Ixon.Expr × ShareScope) := do
  match resolveShareIn (← getCtx) scope idx label with
  | .ok r => pure r
  | .error e => throw e

/-- Pointer identity of an expression object (a visited-set key: equal
    pointers are the same subterm). -/
private def exprAddr (e : Ixon.Expr) : USize := unsafe ptrAddrUnsafe e

/-- Well-foundedness of a `metaSharing` table against `p` primary entries:
    every `share i` occurring in `metaSharing[j]` has `i < p + j` (a primary
    entry, or a metadata entry BEFORE `j`). Checked when a block context is
    built (`withFreshBlock`), so a malformed table is rejected even where
    decompilation never reads it. The first violation in entry order, then
    in left-to-right pre-order, is reported as `invalidMetaShareIndex`
    (Rust `validate_meta_sharing` walks in the same order). Iterative; the
    walk does not expand `share` nodes. Each shared node (by pointer) is
    visited once across the table, so the walk is linear in the DAG size of
    an in-memory table: a node seen before passed under a bound no larger
    than the current one, so the first violation is unchanged. -/
def validateMetaSharing (p : Nat) (metaSharing : Array Ixon.Expr)
    (label : String := "metaSharing") : Except DecompileError Unit := do
  let mut seen : Std.HashSet USize := {}
  for h : j in [:metaSharing.size] do
    let mut stack : Array Ixon.Expr := #[metaSharing[j]]
    while !stack.isEmpty do
      let e := stack.back!
      stack := stack.pop
      let ptr := exprAddr e
      if seen.contains ptr then continue
      seen := seen.insert ptr
      match e with
      | .share i =>
        if i.toNat ≥ p + j then
          throw (.invalidMetaShareIndex i j.toUInt64 p metaSharing.size label)
      | .app f a => stack := stack.push a |>.push f
      | .lam _ t b | .all _ _ t b => stack := stack.push b |>.push t
      | .letE _ t v b => stack := stack.push b |>.push v |>.push t
      | .prj _ _ v => stack := stack.push v
      | .sort _ | .var _ | .ref .. | .recur .. | .str _ | .nat _ => pure ()

/-- Collect an Ixon App telescope for call-site replay, transparently
    expanding `.share` nodes along the SPINE (Rust
    `collect_ixon_telescope_expanding_shares`). `scope` is the share scope
    of `e`. Arguments are returned in application order, each with the
    scope it is read in (a spine `share` can lead from a metadata
    expression into a primary entry), and are NOT share-expanded — each is
    decompiled individually, where `.share` handling applies as usual. -/
def collectIxonTelescopeExpandingShares (scope : ShareScope) (e : Ixon.Expr)
    : DecompileM (Ixon.Expr × Array (Ixon.Expr × ShareScope)) := do
  let mut args : Array (Ixon.Expr × ShareScope) := #[]
  let mut cur := e
  let mut curScope := scope
  repeat
    match cur with
    | .share idx =>
      let (s, sScope) ← resolveShare curScope idx "callSite telescope"
      cur := s
      curScope := sScope
    | .app f a =>
      args := args.push (a, curScope)
      cur := f
    | _ => break
  return (cur, args.reverse)

/-- Decompile an expression read in share scope `scope` to Ix.Expr with
    arena-based metadata. -/
partial def decompileExprIn (scope : ShareScope) (e : Ixon.Expr) (arenaIdx : UInt64) :
    DecompileM Ix.Expr := do
  -- 1. Expand Share transparently (same arena index, target's scope)
  match e with
  | .share idx =>
    let (sharedExpr, sharedScope) ← resolveShare scope idx
    decompileExprIn sharedScope sharedExpr arenaIdx
  | _ =>

  -- Check cache
  let cacheKey := (e, arenaIdx, scope)
  if let some cached := (← get).exprCache.get? cacheKey then return cached

  -- 2. Follow mdata chain
  let mut currentIdx := arenaIdx
  let mut mdataLayers : Array (Array (Ix.Name × Ix.DataValue)) := #[]
  -- Pass 3 decompile record of a rewritten call site (`_ix.inline`,
  -- `_ix.inline_meta`): the source occurrence in `metaSharing`.
  let mut inlineRecord : Option (Nat × Nat) := none
  let mut done := false
  while !done do
    match ← getArenaNode currentIdx with
    | .mdata kvmaps child =>
      for kvm in kvmaps do
        let data ← decompileKVMap kvm
        if Ix.SemanticContract.hasMetadata data then
          throw (.badConstantFormat "semantic contracts cannot come from optional metadata")
        match data with
        | #[(k1, .ofNat s), (k2, .ofNat m)] =>
          if k1 == Ix.Compile.Pass.inlineKey && k2 == Ix.Compile.Pass.inlineMetaKey then
            if inlineRecord.isNone then inlineRecord := some (s, m)
          else mdataLayers := mdataLayers.push data
        | _ => mdataLayers := mdataLayers.push data
      currentIdx := child
    | _ => done := true

  -- Pass 3 replay: the decompiled term is the recorded source occurrence;
  -- the compiled (rewritten) term is not read (unless `compiledTerms`).
  if (← getEnv).compiledTerms then inlineRecord := none
  if let some (s, m) := inlineRecord then
    let ctx ← getCtx
    let some shared := ctx.metaSharing[s]?
      | throw (.invalidShareIndex s.toUInt64 ctx.metaSharing.size "Pass 3 inline record")
    let src ← decompileExprIn (.metaEntry s) shared m.toUInt64
    let result := applyMdata src mdataLayers
    modify fun st => { st with exprCache := st.exprCache.insert cacheKey result }
    return result

  let node ← getArenaNode currentIdx

  match node with
  | .callSite .. | .etaCallSite .. =>
    let ctx ← getCtx
    let annotated ← match Ix.SemanticContract.containsIxon
        (fun s idx => resolveShareIn ctx s idx "semantic scan") scope e with
      | .ok annotated => pure annotated
      | .error error => throw error
    if annotated then
      throw (.badConstantFormat "optional call-site replay would rewrite a semantic contract")
  | _ => pure ()
  if let some contract := Ix.SemanticContract.ofIxon? e then
    mdataLayers := mdataLayers.push contract.ixMetadata

  -- 3. Match (arenaNode, ixonExpr) → Ix.Expr
  let result ← match node, e with
  -- Eta adapter replay (legacy metadata: written only by the call-site
  -- surgery deleted at M6R slice 6; read so older files decompile): strip
  -- the synthesized lambda telescope, read the
  -- canonical body spine, and rebuild only the source prefix that was
  -- originally present. Existing source arguments were lifted under the
  -- wrapper, so lower their loose BVars after decompilation.
  | .etaCallSite nSynth nameAddr entries canonMeta _wrapperMeta, _ => do
    let ctx ← getCtx
    let mut body := e
    let mut bodyScope := scope
    for _ in [0:nSynth.toNat] do
      repeat
        match body with
        | .share idx =>
          let (shared, sharedScope) ← resolveShare bodyScope idx
            "etaCallSite wrapper"
          body := shared
          bodyScope := sharedScope
        | _ => break
      match body with
      | .lam _ _ b => body := b
      | _ => throw (.badConstantFormat s!"EtaCallSite: expected \
{nSynth} synthesized lambdas")
    let (headIxon, canonicalArgs) ←
      collectIxonTelescopeExpandingShares bodyScope body
    if canonMeta.size != canonicalArgs.size then
      throw (.badConstantFormat s!"EtaCallSite: {canonMeta.size} canonical \
metadata entries but body telescope has {canonicalArgs.size} args")
    let headName ← lookupNameAddr nameAddr
    let headPatch := ctx.univPatches.get? currentIdx
    let levels ← match headPatch, headIxon with
      | some idxs, .ref .. => decompileUnivIndices idxs
      | some idxs, .recur .. => decompileUnivIndices idxs
      | none, .ref _ univIndices => decompileUnivIndices univIndices
      | none, .recur _ univIndices => decompileUnivIndices univIndices
      | _, _ => pure #[]
    let mut spine := Ix.Expr.mkConst headName levels
    for entry in entries do
      let arg ← match entry with
        | .kept canonIdx metaIdx =>
          match canonicalArgs[canonIdx.toNat]? with
          | some (argIxon, argScope) => decompileExprIn argScope argIxon metaIdx
          | none => throw (.badConstantFormat s!"EtaCallSite: Kept \
canonIdx {canonIdx} out of bounds (body telescope has \
{canonicalArgs.size} args)")
        | .collapsed sharingIdx metaIdx =>
          -- Direct `metaSharing` index (no offset by the primary length);
          -- the entry's own shares are read in its metadata scope.
          match ctx.metaSharing[sharingIdx.toNat]? with
          | some shared => decompileExprIn (.metaEntry sharingIdx.toNat) shared metaIdx
          | none => throw (.invalidShareIndex sharingIdx ctx.metaSharing.size
              "etaCallSite collapsed")
      spine := Ix.Expr.mkApp spine
        (Ix.AuxGen.lowerVars arg nSynth.toNat 0)
    pure (applyMdata spine mdataLayers)

  -- Call-site surgery replay (legacy metadata: written only by the surgery
  -- deleted at M6R slice 6; read so older files decompile): reconstruct the
  -- SOURCE-order application
  -- spine from the canonical Ixon spine plus the metadata extension
  -- tables (Rust `decompile_expr`, CallSite arm). Entries walk in source
  -- order: Kept entries index the canonical telescope by `canonIdx`;
  -- Collapsed entries index `ConstantMeta.metaSharing` directly (NOT the
  -- block's primary sharing table, no offset by its length) and are read
  -- in that entry's metadata scope. `origHead` restores the pre-rewrite
  -- head of evaporated-aux sites; otherwise the head is rebuilt from the
  -- CallSite name plus the canonical head's level args. Mdata wraps the
  -- WHOLE reassembled spine, matching how the compiler produced the
  -- node.
  | .callSite nameAddr entries _canonMeta origHead, _ => do
    let ctx ← getCtx
    let (headIxon, canonicalArgs) ← collectIxonTelescopeExpandingShares scope e
    -- Most CallSites have one Kept entry per canonical arg; split-SCC
    -- minor adaptation stores a synthesized wrapper canonically with the
    -- source arg Collapsed, so canonical args may OUTNUMBER Kept
    -- entries — but every Kept entry must point at an existing slot.
    let keptCount := entries.foldl (init := 0) fun n entry =>
      match entry with
      | .kept .. => n + 1
      | _ => n
    if keptCount > canonicalArgs.size then
      throw (.badConstantFormat s!"CallSite: {keptCount} Kept entries \
but canonical telescope has only {canonicalArgs.size} args")
    let head ← match origHead with
      | some (sharingIdx, headMetaIdx) =>
        -- Head-rewritten site: the ORIGINAL head expression (source
        -- name + source level args) lives in metaSharing.
        match ctx.metaSharing[sharingIdx.toNat]? with
        | some shared => decompileExprIn (.metaEntry sharingIdx.toNat) shared headMetaIdx
        | none =>
          throw (.invalidShareIndex sharingIdx ctx.metaSharing.size
            "callSite origHead")
      | none =>
        let headName ← lookupNameAddr nameAddr
        -- Level-spelling patch replay (canonicity §10.6): the compiler
        -- clones the head's patch onto the callSite root (the head's
        -- own arena root is unreachable from here), so look it up by
        -- the CURRENT arena index.
        let headPatch := ctx.univPatches.get? currentIdx
        let levels ← match headPatch, headIxon with
          | some idxs, .ref .. => decompileUnivIndices idxs
          | some idxs, .recur .. => decompileUnivIndices idxs
          | none, .ref _ univIndices => decompileUnivIndices univIndices
          | none, .recur _ univIndices => decompileUnivIndices univIndices
          | _, _ => pure #[]
        pure (Ix.Expr.mkConst headName levels)
    let mut spine := head
    for entry in entries do
      match entry with
      | .kept canonIdx metaIdx =>
        match canonicalArgs[canonIdx.toNat]? with
        | some (argIxon, argScope) =>
          spine := Ix.Expr.mkApp spine (← decompileExprIn argScope argIxon metaIdx)
        | none =>
          throw (.badConstantFormat s!"CallSite: Kept canonIdx \
{canonIdx} out of bounds (canonical telescope has \
{canonicalArgs.size} args)")
      | .collapsed sharingIdx metaIdx =>
        match ctx.metaSharing[sharingIdx.toNat]? with
        | some shared =>
          spine := Ix.Expr.mkApp spine
            (← decompileExprIn (.metaEntry sharingIdx.toNat) shared metaIdx)
        | none =>
          throw (.invalidShareIndex sharingIdx ctx.metaSharing.size
            "callSite collapsed")
    pure (applyMdata spine mdataLayers)
  | _, .var idx =>
    pure (applyMdata (Ix.Expr.mkBVar idx.toNat) mdataLayers)

  | _, .sort univIdx => do
    -- Level-spelling patch replay (canonicity §10.6): a patch keyed by
    -- this occurrence's arena index restores the original spelling via
    -- its virtual univ index.
    let effIdx := match (← getCtx).univPatches.get? currentIdx with
      | some idxs => idxs[0]?.getD univIdx
      | none => univIdx
    pure (applyMdata (Ix.Expr.mkSort (← getUniv effIdx)) mdataLayers)

  | _, .nat refIdx => do
    let blob ← getRef refIdx >>= lookupBlob
    pure (applyMdata (Ix.Expr.mkLit (.natVal (readNatBlob blob))) mdataLayers)

  | _, .str refIdx => do
    let blob ← getRef refIdx >>= lookupBlob
    let s ← readStringBlob blob
    pure (applyMdata (Ix.Expr.mkLit (.strVal s)) mdataLayers)

  -- Ref with arena metadata. Level-spelling patch replay (canonicity
  -- §10.6): the patch carries the FULL level-arg list in the virtual
  -- index space.
  | .ref nameAddr, .ref refIdx univIndices => do
    let name ← match (← getEnv).ixonEnv.names.get? nameAddr with
      | some n => pure n
      | none => getRef refIdx >>= lookupConstName
    let lvls ← decompileUnivIndices
      (((← getCtx).univPatches.get? currentIdx).getD univIndices)
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- Ref without arena metadata
  | _, .ref refIdx univIndices => do
    let name ← getRef refIdx >>= lookupConstName
    let lvls ← decompileUnivIndices
      (((← getCtx).univPatches.get? currentIdx).getD univIndices)
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- Rec with arena metadata (patch replay as in the Ref arm)
  | .ref nameAddr, .recur recIdx univIndices => do
    let name ← match (← getEnv).ixonEnv.names.get? nameAddr with
      | some n => pure n
      | none => getMutName recIdx
    let lvls ← decompileUnivIndices
      (((← getCtx).univPatches.get? currentIdx).getD univIndices)
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- Rec without arena metadata
  | _, .recur recIdx univIndices => do
    let name ← getMutName recIdx
    let lvls ← decompileUnivIndices
      (((← getCtx).univPatches.get? currentIdx).getD univIndices)
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- App with arena metadata
  | .app funIdx argIdx, .app fn arg => do
    let fnExpr ← decompileExprIn scope fn funIdx
    let argExpr ← decompileExprIn scope arg argIdx
    pure (applyMdata (Ix.Expr.mkApp fnExpr argExpr) mdataLayers)

  | _, .app fn arg => do
    let fnExpr ← decompileExprIn scope fn UInt64.MAX
    let argExpr ← decompileExprIn scope arg UInt64.MAX
    pure (applyMdata (Ix.Expr.mkApp fnExpr argExpr) mdataLayers)

  -- Lam with arena metadata
  | .binder nameAddr info tyChild bodyChild, .lam _ ty body => do
    let binderName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExprIn scope ty tyChild
    let bodyExpr ← decompileExprIn scope body bodyChild
    pure (applyMdata (Ix.Expr.mkLam binderName tyExpr bodyExpr info) mdataLayers)

  | _, .lam _ ty body => do
    let tyExpr ← decompileExprIn scope ty UInt64.MAX
    let bodyExpr ← decompileExprIn scope body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkLam Ix.Name.mkAnon tyExpr bodyExpr .default) mdataLayers)

  -- ForallE with arena metadata
  | .binder nameAddr info tyChild bodyChild, .all _ _ ty body => do
    let binderName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExprIn scope ty tyChild
    let bodyExpr ← decompileExprIn scope body bodyChild
    pure (applyMdata (Ix.Expr.mkForallE binderName tyExpr bodyExpr info) mdataLayers)

  | _, .all _ _ ty body => do
    let tyExpr ← decompileExprIn scope ty UInt64.MAX
    let bodyExpr ← decompileExprIn scope body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkForallE Ix.Name.mkAnon tyExpr bodyExpr .default) mdataLayers)

  -- Let with arena metadata
  | .letBinder nameAddr tyChild valChild bodyChild, .letE nonDep ty val body => do
    let letName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExprIn scope ty tyChild
    let valExpr ← decompileExprIn scope val valChild
    let bodyExpr ← decompileExprIn scope body bodyChild
    pure (applyMdata (Ix.Expr.mkLetE letName tyExpr valExpr bodyExpr nonDep.nonDep) mdataLayers)

  | _, .letE nonDep ty val body => do
    let tyExpr ← decompileExprIn scope ty UInt64.MAX
    let valExpr ← decompileExprIn scope val UInt64.MAX
    let bodyExpr ← decompileExprIn scope body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkLetE Ix.Name.mkAnon tyExpr valExpr bodyExpr nonDep.nonDep) mdataLayers)

  -- Prj with arena metadata
  | .prj structNameAddr child, .prj _typeRefIdx fieldIdx val => do
    let typeName ← lookupNameAddr structNameAddr
    let valExpr ← decompileExprIn scope val child
    pure (applyMdata (Ix.Expr.mkProj typeName fieldIdx.toNat valExpr) mdataLayers)

  | _, .prj typeRefIdx fieldIdx val => do
    let typeName ← getRef typeRefIdx >>= lookupConstName
    let valExpr ← decompileExprIn scope val UInt64.MAX
    pure (applyMdata (Ix.Expr.mkProj typeName fieldIdx.toNat valExpr) mdataLayers)

  | _, .share _ => throw (.badConstantFormat "unexpected Share in decompileExpr")

  modify fun s => { s with exprCache := s.exprCache.insert cacheKey result }
  pure result

/-- Decompile a primary expression (a constant's root) to Ix.Expr with
    arena-based metadata. -/
def decompileExpr (e : Ixon.Expr) (arenaIdx : UInt64) : DecompileM Ix.Expr :=
  decompileExprIn .primary e arenaIdx

/-! ## Type Conversion Helpers -/

def toIxSafety : DefinitionSafety → Lean.DefinitionSafety
  | .unsaf => .unsafe | .safe => .safe | .part => .partial

def toIxQuotKind : QuotKind → Lean.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

/-! ## ConstantMeta Extraction Helpers -/

def getNameAddr (cm : ConstantMeta) : Option Address :=
  match cm.info with
  | .defn name .. => some name | .axio name .. => some name
  | .quot name .. => some name | .indc name .. => some name
  | .ctor name .. => some name | .recr name .. => some name
  | .empty | .muts _ _ => none

def getLvlAddrs (cm : ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ lvls .. => lvls | .axio _ lvls .. => lvls
  | .quot _ lvls .. => lvls | .indc _ lvls .. => lvls
  | .ctor _ lvls .. => lvls | .recr _ lvls .. => lvls
  | .empty | .muts _ _ => #[]

def getArenaAndTypeRoot (cm : ConstantMeta) : ExprMetaArena × UInt64 :=
  match cm.info with
  | .defn _ _ _ _ arena typeRoot _ => (arena, typeRoot)
  | .axio _ _ arena typeRoot => (arena, typeRoot)
  | .quot _ _ arena typeRoot => (arena, typeRoot)
  | .indc _ _ _ _ _ arena typeRoot => (arena, typeRoot)
  | .ctor _ _ _ arena typeRoot => (arena, typeRoot)
  | .recr _ _ _ _ _ arena typeRoot _ => (arena, typeRoot)
  | .empty | .muts _ _ => ({}, 0)

def getAllAddrs (cm : ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ _ all .. => all | .indc _ _ _ all .. => all
  | .recr _ _ _ all .. => all | _ => #[]

def getCtxAddrs (cm : ConstantMeta) : Array Address :=
  match cm.info with
  | .defn _ _ _ ctx .. => ctx | .indc _ _ _ _ ctx .. => ctx
  | .recr _ _ _ _ ctx .. => ctx | _ => #[]

/-- Resolve name from ConstantMeta. -/
def decompileMetaName (cMeta : ConstantMeta) : DecompileM Ix.Name :=
  match getNameAddr cMeta with
  | some addr => lookupNameAddr addr
  | none => throw (.badConstantFormat "empty metadata, no name")

/-- Resolve level param names from ConstantMeta. -/
def decompileMetaLevels (cMeta : ConstantMeta) : DecompileM (Array Ix.Name) :=
  (getLvlAddrs cMeta).mapM lookupNameAddr

/-- Resolve all names from ConstantMeta. -/
def decompileMetaAll (cMeta : ConstantMeta) (fallback : Ix.Name) : DecompileM (Array Ix.Name) := do
  let addrs := getAllAddrs cMeta
  if addrs.isEmpty then return #[fallback]
  let mut names : Array Ix.Name := #[]
  for addr in addrs do
    match (← getEnv).ixonEnv.names.get? addr with
    | some n => names := names.push n
    | none => pure ()
  return if names.isEmpty then #[fallback] else names

/-- Resolve ctx names from ConstantMeta. -/
def decompileMetaCtx (cMeta : ConstantMeta) : DecompileM (Array Ix.Name) := do
  let env ← getEnv
  pure <| (getCtxAddrs cMeta).filterMap fun addr => env.ixonEnv.names.get? addr

/-- Build a BlockCtx from a Constant plus its per-constant metadata
    wrapper. `metaRefs`/`metaUnivs` extend the primary tables — the
    documented virtual-address contract (mirrors Rust
    `load_meta_extensions`); `metaSharing` rides its own dedicated field
    (Pass 3's decompile records; the legacy surgery replay), and `share` nodes inside it are read in the
    extended index space (`ShareScope`), never appended to `sharing`. The
    context is rebuilt per constant, so extensions never leak across
    sibling constants of a block. -/
def mkBlockCtx (cnst : Constant) (mutCtx : Array Ix.Name)
    (univParams : Array Ix.Name) (arena : ExprMetaArena)
    (cMeta : ConstantMeta := {}) : BlockCtx :=
  { refs := cnst.refs ++ cMeta.metaRefs,
    univs := cnst.univs ++ cMeta.metaUnivs,
    sharing := cnst.sharing,
    mutCtx, univParams, arena, metaSharing := cMeta.metaSharing,
    univPatches := cMeta.univPatches.foldl
      (init := {}) fun m p => m.insert p.arenaIdx p.univIdxs }

/-- Run with fresh block context and state. The constant's `metaSharing`
    is checked against its primary table first (`validateMetaSharing`, whose
    errors name the constant `name`), mirroring Rust
    `BlockCache::load_meta_extensions`. -/
def withFreshBlock (name : Ix.Name) (cnst : Constant) (mutCtx : Array Ix.Name)
    (univParams : Array Ix.Name) (arena : ExprMetaArena)
    (cMeta : ConstantMeta := {})
    (m : DecompileM α) : DecompileM α := do
  let env ← getEnv
  let ctx := mkBlockCtx cnst mutCtx univParams arena cMeta
  match validateMetaSharing ctx.sharing.size ctx.metaSharing name.pretty with
  | .error e => throw e
  | .ok () =>
    match DecompileM.run env ctx {} m with
    | .ok (a, _) => pure a
    | .error e => throw e

/-! ## Constant Decompilers → Ix.ConstantInfo -/

def decompileDefinition (d : Ixon.Definition) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let allNames ← decompileMetaAll cMeta name
  let mutCtx ← decompileMetaCtx cMeta
  let valueRoot := match cMeta.info with
    | .defn _ _ _ _ _ _ valueRoot => valueRoot
    | _ => (0 : UInt64)
  -- Hints come from the per-name `Named.hints` channel — the exact
  -- value `finalize_hints` recorded for this name (Rust
  -- decompile.rs:1549-1560). The per-address `Env.anonHints` channel is
  -- unusable here: alpha-identical definitions under different names
  -- share one constant address, so it only holds a merged winner
  -- (the `instInhabited*`/`UInt*.to*` family of whole-env mismatches).
  -- Absent → `.opaque`, matching the compiler's treatment of theorems
  -- and opaques.
  let ixonEnv := (← getEnv).ixonEnv
  let hints := match ixonEnv.named.get? name with
    | some named => named.hints.getD .opaque
    | none => .opaque
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock name cnst mutCtx univParams arena (cMeta := cMeta) do
    let typeExpr ← decompileExpr d.typ typeRoot
    let valueExpr ← decompileExpr d.value valueRoot
    let cv : Ix.ConstantVal := { name, levelParams := univParams, type := typeExpr }
    match d.kind with
    | .defn => pure (.defnInfo { cnst := cv, value := valueExpr, hints, safety := toIxSafety d.safety, all := allNames })
    | .thm => pure (.thmInfo { cnst := cv, value := valueExpr, all := allNames })
    | .opaq => pure (.opaqueInfo { cnst := cv, value := valueExpr, isUnsafe := d.safety == .unsaf, all := allNames })

def decompileAxiom (a : Ixon.Axiom) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock name cnst #[] univParams arena (cMeta := cMeta) do
    let typeExpr ← decompileExpr a.typ typeRoot
    pure (.axiomInfo { cnst := { name, levelParams := univParams, type := typeExpr }, isUnsafe := a.isUnsafe })

def decompileQuotient (q : Ixon.Quotient) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock name cnst #[] univParams arena (cMeta := cMeta) do
    let typeExpr ← decompileExpr q.typ typeRoot
    pure (.quotInfo { cnst := { name, levelParams := univParams, type := typeExpr }, kind := toIxQuotKind q.kind })

def decompileConstructor (ctor : Ixon.Constructor) (cnst : Constant)
    (cMeta : ConstantMeta) (inductName : Ix.Name)
    : DecompileM Ix.ConstructorVal := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock name cnst #[] univParams arena (cMeta := cMeta) do
    let typeExpr ← decompileExpr ctor.typ typeRoot
    pure { cnst := { name, levelParams := univParams, type := typeExpr },
           induct := inductName, cidx := ctor.cidx.toNat,
           numParams := ctor.params.toNat, numFields := ctor.fields.toNat,
           isUnsafe := ctor.isUnsafe }

def decompileRecursor (rec : Ixon.Recursor) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let allNames ← decompileMetaAll cMeta name
  let mutCtx ← decompileMetaCtx cMeta
  let (ruleRoots, ruleAddrs) := match cMeta.info with
    | .recr _ _ rules _ _ _ _ ruleRoots => (ruleRoots, rules)
    | _ => (#[], #[])
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock name cnst mutCtx univParams arena (cMeta := cMeta) do
    let typeExpr ← decompileExpr rec.typ typeRoot
    let ruleNames ← ruleAddrs.mapM lookupNameAddr
    let mut rules : Array Ix.RecursorRule := #[]
    for h : i in [:rec.rules.size] do
      let rule := rec.rules[i]
      let rhsRoot := ruleRoots[i]?.getD 0
      let rhs ← decompileExpr rule.rhs rhsRoot
      let ctorName := ruleNames[i]?.getD Ix.Name.mkAnon
      rules := rules.push { ctor := ctorName, nfields := rule.fields.toNat, rhs }
    pure (.recInfo { cnst := { name, levelParams := univParams, type := typeExpr },
                     all := allNames, numParams := rec.params.toNat,
                     numIndices := rec.indices.toNat, numMotives := rec.motives.toNat,
                     numMinors := rec.minors.toNat, rules, k := rec.k, isUnsafe := rec.isUnsafe })

def decompileInductive (ind : Ixon.Inductive) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM (Ix.InductiveVal × Array Ix.ConstructorVal) := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let allNames ← decompileMetaAll cMeta name
  let mutCtx ← decompileMetaCtx cMeta
  let ctorNameAddrs := match cMeta.info with
    | .indc _ _ ctors .. => ctors | _ => #[]
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  let typeExpr ← withFreshBlock name cnst mutCtx univParams arena (cMeta := cMeta) do
    decompileExpr ind.typ typeRoot
  let env ← getEnv
  let mut ctors : Array Ix.ConstructorVal := #[]
  let mut ctorNames : Array Ix.Name := #[]
  for h : i in [:ind.ctors.size] do
    let ctor := ind.ctors[i]
    let ctorMeta : ConstantMeta :=
      if let some ctorAddr := ctorNameAddrs[i]? then
        if let some ctorIxName := env.ixonEnv.names.get? ctorAddr then
          env.ixonEnv.named.fold (init := ConstantMeta.empty) fun acc ixN named =>
            if ixN == ctorIxName then named.constMeta else acc
        else .empty
      else .empty
    let ctorVal ← decompileConstructor ctor cnst ctorMeta name
    ctorNames := ctorNames.push ctorVal.cnst.name
    ctors := ctors.push ctorVal
  let indVal : Ix.InductiveVal := {
    cnst := { name, levelParams := univParams, type := typeExpr },
    numParams := ind.params.toNat, numIndices := ind.indices.toNat,
    all := allNames, ctors := ctorNames,
    -- temporary stub until we update the Lean compiler and decompiler semantics
    numNested := 0, isRec := false
    isUnsafe := ind.isUnsafe, isReflexive := false }
  pure (indVal, ctors)

/-! ## Projection Handling -/

def decompileProjection (cnst : Constant) (cMeta : ConstantMeta)
    (mutuals : Array MutConst)
    (blockSharing : Array Ixon.Expr) (blockRefs : Array Address) (blockUnivs : Array Ixon.Univ)
    : DecompileM (Array (Ix.Name × Ix.ConstantInfo)) := do
  let bc : Constant := { info := cnst.info, sharing := blockSharing, refs := blockRefs, univs := blockUnivs }
  match cnst.info with
  | .dPrj proj =>
    match mutuals[proj.idx.toNat]? with
    | some (.defn d) =>
      let info ← decompileDefinition d bc cMeta
      pure #[(info.getCnst.name, info)]
    | _ => throw (.badConstantFormat s!"dPrj index {proj.idx} not found")
  | .iPrj proj =>
    match mutuals[proj.idx.toNat]? with
    | some (.indc ind) =>
      let (indVal, ctorVals) ← decompileInductive ind bc cMeta
      let mut results := #[(indVal.cnst.name, Ix.ConstantInfo.inductInfo indVal)]
      for ctor in ctorVals do
        results := results.push (ctor.cnst.name, .ctorInfo ctor)
      pure results
    | _ => throw (.badConstantFormat s!"iPrj index {proj.idx} not found")
  | .rPrj proj =>
    match mutuals[proj.idx.toNat]? with
    | some (.recr rec) =>
      let info ← decompileRecursor rec bc cMeta
      pure #[(info.getCnst.name, info)]
    | _ => throw (.badConstantFormat s!"rPrj index {proj.idx} not found")
  | .cPrj _ => pure #[]
  | _ => pure #[]

/-! ## Main Entry Points -/

/-- Decompile a single named constant, purely. Returns Ix types. -/
def decompileOne (env : DecompileEnv) (ixonEnv : Ixon.Env)
    (_ixName : Ix.Name) (named : Ixon.Named)
    : Except String (Array (Ix.Name × Ix.ConstantInfo)) :=
  match ixonEnv.getConst? named.addr with
  | none => .ok #[]
  | some cnst =>
    let m : DecompileM (Array (Ix.Name × Ix.ConstantInfo)) :=
      match cnst.info with
      | .defn d => do
        let info ← decompileDefinition d cnst named.constMeta
        pure #[(info.getCnst.name, info)]
      | .axio ax => do
        let info ← decompileAxiom ax cnst named.constMeta
        pure #[(info.getCnst.name, info)]
      | .quot q => do
        let info ← decompileQuotient q cnst named.constMeta
        pure #[(info.getCnst.name, info)]
      | .recr rec => do
        let info ← decompileRecursor rec cnst named.constMeta
        pure #[(info.getCnst.name, info)]
      | .dPrj proj =>
        match ixonEnv.getConst? proj.block with
        | some { info := .muts mutuals, sharing, refs, univs } =>
          decompileProjection cnst named.constMeta mutuals sharing refs univs
        | _ => pure #[]
      | .iPrj proj =>
        match ixonEnv.getConst? proj.block with
        | some { info := .muts mutuals, sharing, refs, univs } =>
          decompileProjection cnst named.constMeta mutuals sharing refs univs
        | _ => pure #[]
      | .rPrj proj =>
        match ixonEnv.getConst? proj.block with
        | some { info := .muts mutuals, sharing, refs, univs } =>
          decompileProjection cnst named.constMeta mutuals sharing refs univs
        | _ => pure #[]
      | .cPrj _ => pure #[]
      | .muts _ => pure #[]
    match DecompileM.run env default {} m with
    | .ok (entries, _) => .ok entries
    | .error err => .error (toString err)

/-- Decompile a chunk of constants, purely. Returns results and errors. -/
def decompileChunk (env : DecompileEnv) (ixonEnv : Ixon.Env)
    (chunk : Array (Ix.Name × Ixon.Named))
    : Array (Ix.Name × Ix.ConstantInfo) × Array (Ix.Name × String) := Id.run do
  let mut results : Array (Ix.Name × Ix.ConstantInfo) := #[]
  let mut errors : Array (Ix.Name × String) := #[]
  for (ixName, named) in chunk do
    match decompileOne env ixonEnv ixName named with
    | .ok entries => results := results ++ entries
    | .error err => errors := errors.push (ixName, err)
  (results, errors)

/-- Decompile all constants in parallel using chunked pure Tasks. Returns Ix types.

    `skip` filters named entries out of the pass entirely — the Pass-1
    driver passes the aux_gen skip (`named.original.isSome &&
    isAuxGenSuffix name`, Rust `decompile_named_const`
    decompile.rs:3595-3597); aux constants are regenerated/recovered by
    Pass 2 instead. Default skips nothing (standalone whole-env use). -/
def decompileAllParallel (ixonEnv : Ixon.Env) (numWorkers : Nat := 32)
    (skip : Ix.Name → Ixon.Named → Bool := fun _ _ => false)
    : Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) := Id.run do
  let env : DecompileEnv := { ixonEnv }
  -- Collect all named entries into an array
  let mut allEntries : Array (Ix.Name × Ixon.Named) := #[]
  for (ixName, named) in ixonEnv.named do
    if !skip ixName named then
      allEntries := allEntries.push (ixName, named)
  let total := allEntries.size
  let chunkSize := (total + numWorkers - 1) / numWorkers
  -- Spawn one task per chunk
  let mut tasks : Array (Task (Array (Ix.Name × Ix.ConstantInfo) × Array (Ix.Name × String))) := #[]
  let mut offset := 0
  while offset < total do
    let endIdx := min (offset + chunkSize) total
    let chunk := allEntries[offset:endIdx]
    let task := Task.spawn (prio := .dedicated) fun () =>
      decompileChunk env ixonEnv chunk.toArray
    tasks := tasks.push task
    offset := endIdx
  -- Collect results
  let mut result : Std.HashMap Ix.Name Ix.ConstantInfo := {}
  let mut errors : Array (Ix.Name × String) := #[]
  for task in tasks do
    let (chunkResults, chunkErrors) := task.get
    for (n, info) in chunkResults do
      result := result.insert n info
    errors := errors ++ chunkErrors
  (result, errors)

/-- Decompile all constants in parallel, with IO logging. -/
def decompileAllParallelIO (ixonEnv : Ixon.Env)
    : IO (Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String)) := do
  let total := ixonEnv.named.size
  IO.println s!"  [Decompile] {total} named constants, spawning tasks..."
  let startTime ← IO.monoMsNow
  let (result, errors) := decompileAllParallel ixonEnv
  let elapsed := (← IO.monoMsNow) - startTime
  IO.println s!"  [Decompile] Done: {result.size} ok, {errors.size} errors in {elapsed}ms"
  pure (result, errors)

end Ix.DecompileM

end

