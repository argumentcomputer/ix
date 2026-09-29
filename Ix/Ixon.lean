/-
  Ixon: Alpha-invariant serialization format for Lean constants.

  This host module reexports the pure types and anonymous codecs from
  Ix.Ixon.Codec, and adds metadata, lazy records, environments, and hashing.
  The pure anonymous grammar is shared with the certified codec proofs.
-/
module
public import Ix.Address
public import Ix.Common
public import Ix.Environment
public import Ix.IxonMode
public import Ix.Ixon.Codec
public import Ix.Merkle

public section

namespace Ixon

open Ix (DefKind DefinitionSafety QuotKind)

-- These defaults intentionally use the host's BLAKE3-derived default address.
-- The pure data module does not import that backend or replace its value.
deriving instance Inhabited for InductiveProj
deriving instance Inhabited for ConstructorProj
deriving instance Inhabited for RecursorProj
deriving instance Inhabited for DefinitionProj

/-! ## Metadata Types -/

/-- Data values for KVMap metadata -/
inductive DataValue where
  | ofString (addr : Address)
  | ofBool (b : Bool)
  | ofName (addr : Address)
  | ofNat (addr : Address)
  | ofInt (addr : Address)
  | ofSyntax (addr : Address)
  deriving BEq, Repr, Inhabited, Hashable

/-- Key-value map for Lean.Expr.mdata -/
abbrev KVMap := Array (Address × DataValue)

/-- Entry in a `callSite` metadata node, representing one source-order
    argument. Mirrors Rust `ixon::metadata::CallSiteEntry`. -/
inductive CallSiteEntry where
  /-- Argument exists in canonical form at App-spine position `canonIdx`.
      `metaIdx` is the arena index for this argument's metadata subtree
      (Rust field name: `meta` — a reserved keyword here). -/
  | kept (canonIdx : UInt64) (metaIdx : UInt64)
  /-- Argument was collapsed. Expression stored in
      `ConstantMeta.metaSharing[sharingIdx]`. `metaIdx` is the arena index
      for this argument's metadata subtree. -/
  | collapsed (sharingIdx : UInt64) (metaIdx : UInt64)
  deriving BEq, Repr, Inhabited

/-- Arena node for per-expression metadata.
    Nodes are allocated bottom-up (children before parents) in the arena.
    Arena indices are UInt64 values pointing into `ExprMetaArena.nodes`. -/
inductive ExprMetaData where
  | leaf
  | app (fun_ : UInt64) (arg : UInt64)
  | binder (name : Address) (info : Lean.BinderInfo)
           (tyChild : UInt64) (bodyChild : UInt64)
  | letBinder (name : Address)
              (tyChild : UInt64) (valChild : UInt64) (bodyChild : UInt64)
  | ref (name : Address)
  | prj (structName : Address) (child : UInt64)
  | mdata (mdata : Array KVMap) (child : UInt64)
  /-- Surgered call-site: replaces the entire App-spine metadata chain
      (outermost App down to the Ref head) with a single node. `entries` are
      in SOURCE order; `canonMeta` holds canonical-order metadata roots (one
      per argument in the IXON App spine); `origHead` is
      `some (sharingIdx, meta)` when the call-site head itself was rewritten
      (evaporated-aux recursors). Mirrors Rust
      `ixon::metadata::ExprMetaData::CallSite`. -/
  | callSite (name : Address) (entries : Array CallSiteEntry)
             (canonMeta : Array UInt64) (origHead : Option (UInt64 × UInt64))
  /-- Eta adapter for a partial plan-bearing reference. The Ixon expression
      is a synthesized lambda telescope with a canonical call-site body;
      decompile discards `nSynth` binders and restores only `entries`, while
      meta ingress follows `wrapperMeta` through the ordinary synthesized
      Binder/CallSite metadata tree. -/
  | etaCallSite (nSynth : UInt64) (name : Address)
                (entries : Array CallSiteEntry) (canonMeta : Array UInt64)
                (wrapperMeta : UInt64)
  deriving BEq, Repr, Inhabited

/-- Arena for expression metadata within a single constant. -/
structure ExprMetaArena where
  nodes : Array ExprMetaData := #[]
  deriving BEq, Repr, Inhabited

def ExprMetaArena.alloc (arena : ExprMetaArena) (node : ExprMetaData)
    : ExprMetaArena × UInt64 :=
  let idx := arena.nodes.size.toUInt64
  ({ nodes := arena.nodes.push node }, idx)

/-- Count ExprMetaData nodes by type:
    (leaf, app, binder, letBinder, ref, prj, mdata, callSite) -/
def ExprMetaArena.countByType (arena : ExprMetaArena)
    : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  arena.nodes.foldl (init := (0, 0, 0, 0, 0, 0, 0, 0))
    fun (le, ap, bi, lb, rf, pj, md, cs) node =>
    match node with
    | .leaf => (le + 1, ap, bi, lb, rf, pj, md, cs)
    | .app .. => (le, ap + 1, bi, lb, rf, pj, md, cs)
    | .binder .. => (le, ap, bi + 1, lb, rf, pj, md, cs)
    | .letBinder .. => (le, ap, bi, lb + 1, rf, pj, md, cs)
    | .ref .. => (le, ap, bi, lb, rf + 1, pj, md, cs)
    | .prj .. => (le, ap, bi, lb, rf, pj + 1, md, cs)
    | .mdata .. => (le, ap, bi, lb, rf, pj, md + 1, cs)
    | .callSite .. | .etaCallSite .. => (le, ap, bi, lb, rf, pj, md, cs + 1)

/-- Count mdata items in an arena. -/
def ExprMetaArena.mdataItemCount (arena : ExprMetaArena) : Nat :=
  arena.nodes.foldl (init := 0) fun acc node =>
    match node with
    | .mdata mdata _ => acc + mdata.foldl (fun a kv => a + kv.size) 0
    | _ => acc

/-- Nested-auxiliary layout info for a mutual inductive block: paired
    permutation (`perm[sourceJ] = canonicalI`) plus per-source-position aux
    constructor counts. Lives in the `muts` metadata variant (never enters
    any constant's content hash). Mirrors Rust `ixon::env::AuxLayout`
    (`Vec<usize>` fields serialized as u64). -/
structure AuxLayout where
  perm : Array UInt64 := #[]
  sourceCtorCounts : Array UInt64 := #[]
  /-- `evaporated[sourceJ] ≠ 0`: this block owns the evaporation of source
      position `sourceJ` (alias to the external head's generic recursor +
      head-rewrite call-site plan). Positions canonical in another SCC of
      the same original mutual stay `PERM_OUT_OF_SCC` in `perm` with a `0`
      here. Same length as `perm` once populated (pre-field construction
      sites decode as all-`0` via this default). Mirrors Rust
      `ixon::env::AuxLayout.evaporated` (`Vec<bool>`, carried as 0/1
      u64s across the FFI). -/
  evaporated : Array UInt64 := #[]
  deriving BEq, Repr, Inhabited

/-- Per-constant metadata variant payload with arena-based expression
    metadata. Each variant stores an ExprMetaArena covering all expressions
    in that constant, plus root indices pointing into the arena. Mirrors
    Rust `ixon::metadata::ConstantMetaInfo`; the serialized/FFI wrapper
    around it (extension tables) is [`ConstantMeta`]. -/
inductive ConstantMetaInfo where
  | empty
  | defn (name : Address) (lvls : Array Address)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64) (valueRoot : UInt64)
  | axio (name : Address) (lvls : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | quot (name : Address) (lvls : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | indc (name : Address) (lvls : Array Address) (ctors : Array Address)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | ctor (name : Address) (lvls : Array Address) (induct : Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | recr (name : Address) (lvls : Array Address) (rules : Array Address)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
         (ruleRoots : Array UInt64)
  | muts (all : Array (Array Address)) (auxLayout : Option AuxLayout)
  deriving Inhabited, BEq, Repr

/-- Per-occurrence original level-spelling patch (canonicity §10.6):
    keyed by the metadata-arena node index of a `sort`/`ref`/`recur`
    occurrence whose original level-index list differs from its
    canonical one, carrying the FULL original list in the VIRTUAL univ
    index space (idx < `univs.size` → primary table entry, already
    canonical; idx ≥ `univs.size` → `metaUnivs[idx - univs.size]`,
    the original spelling). `sort` occurrences carry a 1-element list.
    Presentation-only: read by the decompiler and by META kernel
    ingress (the stage-2 decoration source); anon ingress — the trust
    boundary — never reads patches. -/
structure UnivPatch where
  arenaIdx : UInt64
  univIdxs : Array UInt64
  deriving Inhabited, BEq, Repr

/-- Per-constant metadata wrapper: variant payload + extension tables.
    The extension tables (`metaSharing`/`metaRefs`/`metaUnivs`) form a
    virtual address space extending the primary `Constant` tables, used by
    `callSite` nodes in the metadata arena for call-site surgery roundtrip
    and by `univPatches` for original level spellings (canonicity §10.6).
    Mirrors Rust `ixon::metadata::ConstantMeta`. -/
structure ConstantMeta where
  info : ConstantMetaInfo := .empty
  /-- Compiled Ixon expressions for collapsed call-site arguments. May
      contain `Share(idx)` references into the extended sharing table. -/
  metaSharing : Array Expr := #[]
  /-- Extension refs table (addresses referenced by collapsed arg
      expressions), serialized as raw 32-byte addresses (not name-indexed). -/
  metaRefs : Array Address := #[]
  /-- Extension univs table (universe terms in collapsed arg expressions,
      and original level spellings referenced by `univPatches`). -/
  metaUnivs : Array Univ := #[]
  /-- Original level-spelling patches, keyed by metadata-arena index
      (canonicity §10.6). Empty until the stage-2 compiler emits them. -/
  univPatches : Array UnivPatch := #[]
  deriving Inhabited, BEq, Repr

/-- Wrap a `ConstantMetaInfo` payload (no extension tables). Mirrors Rust
    `ConstantMeta::new`. -/
def ConstantMeta.new (info : ConstantMetaInfo) : ConstantMeta := { info }

/-- The default (empty-variant, no extension tables) wrapper — keeps the
    pre-wrapper `.empty` construction idiom working. -/
def ConstantMeta.empty : ConstantMeta := {}

/-- Whether this metadata has any wrapper extension payload (surgery
    tables or level-spelling patches). -/
def ConstantMeta.hasExtensions (cm : ConstantMeta) : Bool :=
  !cm.metaSharing.isEmpty || !cm.metaRefs.isEmpty || !cm.metaUnivs.isEmpty
    || !cm.univPatches.isEmpty

/-- Short kind name for diagnostics (mirrors Rust `kind_name`). -/
def ConstantMetaInfo.kindName : ConstantMetaInfo → String
  | .empty => "empty"
  | .defn .. => "def"
  | .axio .. => "axio"
  | .quot .. => "quot"
  | .indc .. => "indc"
  | .ctor .. => "ctor"
  | .recr .. => "rec"
  | .muts .. => "muts"

/-- Count total arena nodes in this ConstantMetaInfo. -/
def ConstantMetaInfo.exprMetaCount : ConstantMetaInfo → Nat
  | .empty => 0
  | .defn _ _ _ _ arena _ _ => arena.nodes.size
  | .axio _ _ arena _ => arena.nodes.size
  | .quot _ _ arena _ => arena.nodes.size
  | .indc _ _ _ _ _ arena _ => arena.nodes.size
  | .ctor _ _ _ arena _ => arena.nodes.size
  | .recr _ _ _ _ _ arena _ _ => arena.nodes.size
  | .muts _ _ => 0

/-- Count total arena nodes and mdata items in this ConstantMetaInfo. -/
def ConstantMetaInfo.exprMetaStats : ConstantMetaInfo → Nat × Nat
  | .empty => (0, 0)
  | .defn _ _ _ _ arena _ _ => (arena.nodes.size, arena.mdataItemCount)
  | .axio _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .quot _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .indc _ _ _ _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .ctor _ _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .recr _ _ _ _ _ arena _ _ => (arena.nodes.size, arena.mdataItemCount)
  | .muts _ _ => (0, 0)

/-- Count ExprMetaData nodes by type: (binder, letBinder, ref, prj, mdata)
    (compatible signature with old ExprMetas.countByType for comparison) -/
def ConstantMetaInfo.exprMetaByType : ConstantMetaInfo → Nat × Nat × Nat × Nat × Nat
  | .empty => (0, 0, 0, 0, 0)
  | cm =>
    let arena := match cm with
      | .defn _ _ _ _ a _ _ => a
      | .axio _ _ a _ => a
      | .quot _ _ a _ => a
      | .indc _ _ _ _ _ a _ => a
      | .ctor _ _ _ a _ => a
      | .recr _ _ _ _ _ a _ _ => a
      | .empty => {}
      | .muts _ _ => {}
    let (_, _, bi, lb, rf, pj, md, _) := arena.countByType
    (bi, lb, rf, pj, md)

/-- Wrapper delegator: count total arena nodes. -/
def ConstantMeta.exprMetaCount (cm : ConstantMeta) : Nat :=
  cm.info.exprMetaCount

/-- Wrapper delegator: count arena nodes and mdata items. -/
def ConstantMeta.exprMetaStats (cm : ConstantMeta) : Nat × Nat :=
  cm.info.exprMetaStats

/-- Wrapper delegator: count nodes by type. -/
def ConstantMeta.exprMetaByType (cm : ConstantMeta) : Nat × Nat × Nat × Nat × Nat :=
  cm.info.exprMetaByType

/-- A named constant with metadata.
    For aux_gen-rewritten constants, `original` stores the pre-rewrite
    (address, metadata) pair for decompile roundtrip fidelity. -/
structure Named where
  addr : Address
  constMeta : ConstantMeta := .empty
  original : Option (Address × ConstantMeta) := none
  /-- EXACT per-name reducibility hints (`none` for constants that carry
      none, e.g. theorems). Alpha-identical definitions under different
      names share one constant address, so the per-address
      `Env.anonHints` channel only holds a min-merged advisory winner —
      this field is the faithful per-definition value, serialized in
      each §5 entry's skippable header. Mirrors Rust `Named.hints`. -/
  hints : Option Lean.ReducibilityHints := none
  deriving Inhabited, BEq, Repr

/-- A cryptographic commitment -/
structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr, Inhabited

/-- Parse a `Constant` starting at byte offset `off` within `buf`, WITHOUT
    copying out a sub-buffer. The window length bounds the constant, so any
    bytes after it in `buf` are simply left unread (no trailing-bytes check).
    Zero-copy apart from the small interior string/nat reads `getConstant`
    performs regardless. -/
def deConstantAt (buf : ByteArray) (off : Nat) : Except String Constant :=
  match getConstant.run { idx := off, bytes := buf } with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Lazily-materialized constant: an offset window `(buf, off, len)` into a
    shared backing `ByteArray` plus an optional pre-materialized `Constant`.
    Mirrors the Rust kernel's `LazyConstant` (`src/ix/ixon/lazy.rs`) — the
    `ofSlice` form is the analog of its window-into-a-shared-buffer
    (`from_mmap_slice`) variant, except here the shared buffer is the resident
    `.ixe` bytes rather than an mmap.

    The lazy load path (`ofSlice`, used by `deEnvAnon`) points every constant
    at a window into the *one* `.ixe` buffer already resident in memory — no
    per-constant copy and no materialization. A freshly loaded env's
    steady-state cost is therefore just that single buffer (plus tiny per-entry
    offset records), which is what keeps loading e.g. `mathlib.ixe` from
    blowing past 100 GB when only a small closure is actually checked. Constant
    bodies are parsed on demand, and only for the closure that is visited.

    The build/compile path (`ofConstant`) serializes once into its own buffer
    and pre-populates `cache` so repeated `get`s during compilation are free. -/
structure LazyConstant where
  /-- Shared backing buffer. For `ofSlice` this is the whole `.ixe` buffer; for
      `ofConstant` it is a standalone buffer holding just this constant's
      serialized bytes. -/
  buf : ByteArray
  /-- Start offset of this constant's Tag4 body within `buf`. -/
  off : Nat := 0
  /-- Length of this constant's Tag4 body. -/
  len : Nat
  /-- Pre-materialized constant. `some` only for the build path; the lazy load
      path leaves this `none` and parses the window fresh on each `get`. -/
  cache : Option Constant := none
  deriving Inhabited

namespace LazyConstant

/-- Build from a structured constant (build/compile path). Serializes once into
    a standalone buffer and caches so `get` is free and `rawBytes` is ready. -/
def ofConstant (c : Constant) : LazyConstant :=
  let b := serConstant c
  { buf := b, off := 0, len := b.size, cache := some c }

/-- Build from an offset window into a shared buffer (zero-copy lazy load).
    `buf[off:off+len]` must be exactly `serConstant`'s output for the address
    this entry is stored under. -/
def ofSlice (buf : ByteArray) (off len : Nat) : LazyConstant :=
  { buf, off, len, cache := none }

/-- Materialize the constant, surfacing parse errors. Returns the cached value
    when present, otherwise parses the window in place (no copy). -/
def get (lc : LazyConstant) : Except String Constant :=
  match lc.cache with
  | some c => .ok c
  | none => deConstantAt lc.buf lc.off

/-- Materialize the constant, discarding parse errors. -/
def get? (lc : LazyConstant) : Option Constant :=
  match lc.cache with
  | some c => some c
  | none => (deConstantAt lc.buf lc.off).toOption

/-- Raw serialized bytes (the Tag4 constant body). Returns the backing buffer
    directly when the window spans all of it (the standalone case), and only
    copies out a sub-slice for a true window into a larger shared buffer. -/
def rawBytes (lc : LazyConstant) : ByteArray :=
  if lc.off == 0 && lc.len == lc.buf.size then lc.buf
  else lc.buf.extract lc.off (lc.off + lc.len)

end LazyConstant

/-- `ConstantInfo` variant tag, readable from a `LazyConstant`'s head byte
    without parsing the body. Mirrors Rust `ixon::lazy::ConstVariantTag`. -/
inductive ConstTag where
  | defn | recr | axio | quot | muts | iPrj | cPrj | rPrj | dPrj
  deriving BEq, Repr, Inhabited, DecidableEq

namespace LazyConstant

/-- Peek the `ConstantInfo` variant from the leading Tag4 head byte, without
    parsing the body — the cheap dispatch used by anon work enumeration
    (mirrors Rust `LazyConstant::peek_variant`). -/
def peekTag (lc : LazyConstant) : Except String ConstTag := do
  if lc.len == 0 || lc.off ≥ lc.buf.size then
    throw "LazyConstant.peekTag: empty bytes"
  let head := lc.buf[lc.off]!
  let flag := head >>> 4
  let large := head &&& 0b1000 != 0
  let small : UInt64 := (head &&& 0b0111).toUInt64
  if flag == Constant.FLAG_MUTS then
    return .muts
  if flag != Constant.FLAG then
    throw s!"LazyConstant.peekTag: unexpected Tag4 flag {flag} (head={head})"
  if large then
    throw s!"LazyConstant.peekTag: unexpected large-form Tag4 for non-Muts constant (head={head})"
  if small == ConstantInfo.CONST_DEFN then return .defn
  else if small == ConstantInfo.CONST_RECR then return .recr
  else if small == ConstantInfo.CONST_AXIO then return .axio
  else if small == ConstantInfo.CONST_QUOT then return .quot
  else if small == ConstantInfo.CONST_CPRJ then return .cPrj
  else if small == ConstantInfo.CONST_RPRJ then return .rPrj
  else if small == ConstantInfo.CONST_IPRJ then return .iPrj
  else if small == ConstantInfo.CONST_DPRJ then return .dPrj
  else throw s!"LazyConstant.peekTag: invalid ConstantInfo variant {small}"

end LazyConstant

/-! ## Metadata Serialization -/

/-- Type alias for name index (Address → u64). -/
abbrev NameIndex := Std.HashMap Address UInt64

/-- Type alias for reverse name index (position → Address). -/
abbrev NameReverseIndex := Array Address

/-- Put an address as an index. -/
def putIdx (addr : Address) (idx : NameIndex) : PutM Unit := do
  let i := idx.get? addr |>.getD 0
  putTag0 ⟨i⟩

/-- Get an address from an index. -/
def getIdx (rev : NameReverseIndex) : GetM Address := do
  let i := (← getTag0).size.toNat
  match rev[i]? with
  | some addr => pure addr
  | none => throw s!"invalid name index {i}, max {rev.size}"

/-- Put a vector of addresses as indices. -/
def putIdxVec (addrs : Array Address) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨addrs.size.toUInt64⟩
  for a in addrs do putIdx a idx

/-- Get a vector of addresses from indices. -/
def getIdxVec (rev : NameReverseIndex) : GetM (Array Address) := do
  let len := (← getTag0).size.toNat
  let mut v := #[]
  for _ in [0:len] do
    v := v.push (← getIdx rev)
  pure v

/-- Serialize BinderInfo. -/
def putBinderInfo : Lean.BinderInfo → PutM Unit
  | .default => putU8 0
  | .implicit => putU8 1
  | .strictImplicit => putU8 2
  | .instImplicit => putU8 3

def getBinderInfo : GetM Lean.BinderInfo := do
  match ← getU8 with
  | 0 => pure .default
  | 1 => pure .implicit
  | 2 => pure .strictImplicit
  | 3 => pure .instImplicit
  | x => throw s!"invalid BinderInfo {x}"

/-- Serialize ReducibilityHints fused into a single Tag0 value:
    0 = opaque, 1 = abbrev, h + 2 = regular h. The §3 wire form —
    mirrors Rust `serialize.rs::fuse_hint`. -/
def putFusedHint : Lean.ReducibilityHints → PutM Unit
  | .opaque => putTag0 ⟨0⟩
  | .abbrev => putTag0 ⟨1⟩
  | .regular n => putTag0 ⟨n.toUInt64 + 2⟩

def getFusedHint : GetM Lean.ReducibilityHints := do
  match (← getTag0).size with
  | 0 => pure .opaque
  | 1 => pure .abbrev
  | v =>
    let h := v - 2
    if h > (0xFFFFFFFF : UInt64) then
      throw s!"fused hint: Regular height {h} exceeds u32::MAX"
    else pure (.regular h.toUInt32)

/-- `putFusedHint` lifted over `Option`: 0 = none, otherwise the fused
    value + 1 (some opaque = 1, some abbrev = 2, some (regular h) =
    h + 3). The §5 per-name hint form; mirrors Rust `fuse_opt_hint`. -/
def putFusedOptHint : Option Lean.ReducibilityHints → PutM Unit
  | none => putTag0 ⟨0⟩
  | some .opaque => putTag0 ⟨1⟩
  | some .abbrev => putTag0 ⟨2⟩
  | some (.regular n) => putTag0 ⟨n.toUInt64 + 3⟩

def getFusedOptHint : GetM (Option Lean.ReducibilityHints) := do
  match (← getTag0).size with
  | 0 => pure none
  | 1 => pure (some .opaque)
  | 2 => pure (some .abbrev)
  | v =>
    let h := v - 3
    if h > (0xFFFFFFFF : UInt64) then
      throw s!"fused hint: Regular height {h} exceeds u32::MAX"
    else pure (some (.regular h.toUInt32))

/-- Order-independent merge for hint registration: alpha-equivalent
    definitions share one constant address but may carry different
    reducibility hints (e.g. one alias marked `@[reducible]`), and the
    winner must not depend on registration order. Keeps the minimum
    under `(tag, height)` with `opaque < abbrev < regular h` —
    commutative, associative, idempotent. Mirrors Rust
    `Env::register_hint`. -/
def mergeHints (a b : Lean.ReducibilityHints) : Lean.ReducibilityHints :=
  let key : Lean.ReducibilityHints → Nat × Nat
    | .opaque => (0, 0)
    | .abbrev => (1, 0)
    | .regular n => (2, n.toNat)
  let (a₁, a₂) := key a
  let (b₁, b₂) := key b
  if b₁ < a₁ || (b₁ == a₁ && b₂ < a₂) then b else a

/-- Serialize DataValue with indexed addresses.
    OfString/OfNat/OfInt/OfSyntax use raw 32-byte addresses (blob addresses, not in name index). -/
def putDataValueIndexed (dv : DataValue) (idx : NameIndex) : PutM Unit := do
  match dv with
  | .ofString a => putU8 0 *> Serialize.put a
  | .ofBool b => putU8 1 *> Serialize.put b
  | .ofName a => putU8 2 *> putIdx a idx
  | .ofNat a => putU8 3 *> Serialize.put a
  | .ofInt a => putU8 4 *> Serialize.put a
  | .ofSyntax a => putU8 5 *> Serialize.put a

def getDataValueIndexed (rev : NameReverseIndex) : GetM DataValue := do
  match ← getU8 with
  | 0 => .ofString <$> Serialize.get
  | 1 => .ofBool <$> Serialize.get
  | 2 => .ofName <$> getIdx rev
  | 3 => .ofNat <$> Serialize.get
  | 4 => .ofInt <$> Serialize.get
  | 5 => .ofSyntax <$> Serialize.get
  | x => throw s!"invalid DataValue tag {x}"

/-- Serialize KVMap with indexed addresses. -/
def putKVMapIndexed (kvmap : KVMap) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨kvmap.size.toUInt64⟩
  for (k, v) in kvmap do
    putIdx k idx
    putDataValueIndexed v idx

def getKVMapIndexed (rev : NameReverseIndex) : GetM KVMap := do
  let len := (← getTag0).size.toNat
  let mut kvmap := #[]
  for _ in [0:len] do
    let k ← getIdx rev
    let v ← getDataValueIndexed rev
    kvmap := kvmap.push (k, v)
  pure kvmap

/-- Serialize mdata stack (Array KVMap) with indexed addresses. -/
def putMdataStackIndexed (mdata : Array KVMap) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨mdata.size.toUInt64⟩
  for kv in mdata do putKVMapIndexed kv idx

def getMdataStackIndexed (rev : NameReverseIndex) : GetM (Array KVMap) := do
  let len := (← getTag0).size.toNat
  let mut mdata := #[]
  for _ in [0:len] do
    mdata := mdata.push (← getKVMapIndexed rev)
  pure mdata

/-- Serialize ExprMetaData with indexed addresses. Arena indices use Tag0 encoding. -/
def putExprMetaDataIndexed (em : ExprMetaData) (idx : NameIndex) : PutM Unit := do
  match em with
  | .leaf => putU8 0
  | .app f a =>
    putU8 1
    putTag0 ⟨f⟩
    putTag0 ⟨a⟩
  | .binder name info tyChild bodyChild =>
    let tag : UInt8 := 2 + match info with
      | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
    putU8 tag
    putIdx name idx
    putTag0 ⟨tyChild⟩
    putTag0 ⟨bodyChild⟩
  | .letBinder name tyChild valChild bodyChild =>
    putU8 6
    putIdx name idx
    putTag0 ⟨tyChild⟩
    putTag0 ⟨valChild⟩
    putTag0 ⟨bodyChild⟩
  | .ref name =>
    putU8 7
    putIdx name idx
  | .prj structName child =>
    putU8 8
    putIdx structName idx
    putTag0 ⟨child⟩
  | .mdata mdata child =>
    putU8 9
    putMdataStackIndexed mdata idx
    putTag0 ⟨child⟩
  | .callSite name entries canonMeta origHead =>
    putU8 10
    putIdx name idx
    putTag0 ⟨entries.size.toUInt64⟩
    for entry in entries do
      match entry with
      | .kept canonIdx metaIdx =>
        putU8 0
        putTag0 ⟨canonIdx⟩
        putTag0 ⟨metaIdx⟩
      | .collapsed sharingIdx metaIdx =>
        putU8 1
        putTag0 ⟨sharingIdx⟩
        putTag0 ⟨metaIdx⟩
    putTag0 ⟨canonMeta.size.toUInt64⟩
    for m in canonMeta do putTag0 ⟨m⟩
    match origHead with
    | none => putU8 0
    | some (sharingIdx, metaIdx) =>
      putU8 1
      putTag0 ⟨sharingIdx⟩
      putTag0 ⟨metaIdx⟩
  | .etaCallSite nSynth name entries canonMeta wrapperMeta =>
    putU8 11
    putTag0 ⟨nSynth⟩
    putIdx name idx
    putTag0 ⟨entries.size.toUInt64⟩
    for entry in entries do
      match entry with
      | .kept canonIdx metaIdx =>
        putU8 0
        putTag0 ⟨canonIdx⟩
        putTag0 ⟨metaIdx⟩
      | .collapsed sharingIdx metaIdx =>
        putU8 1
        putTag0 ⟨sharingIdx⟩
        putTag0 ⟨metaIdx⟩
    putTag0 ⟨canonMeta.size.toUInt64⟩
    for m in canonMeta do putTag0 ⟨m⟩
    putTag0 ⟨wrapperMeta⟩

def getExprMetaDataIndexed (rev : NameReverseIndex) : GetM ExprMetaData := do
  let tag ← getU8
  match tag with
  | 0 => pure .leaf
  | 1 =>
    let f := (← getTag0).size
    let a := (← getTag0).size
    pure (.app f a)
  | 2 | 3 | 4 | 5 =>
    let info := match tag with
      | 2 => Lean.BinderInfo.default | 3 => .implicit
      | 4 => .strictImplicit | _ => .instImplicit
    let name ← getIdx rev
    let tyChild := (← getTag0).size
    let bodyChild := (← getTag0).size
    pure (.binder name info tyChild bodyChild)
  | 6 =>
    let name ← getIdx rev
    let tyChild := (← getTag0).size
    let valChild := (← getTag0).size
    let bodyChild := (← getTag0).size
    pure (.letBinder name tyChild valChild bodyChild)
  | 7 =>
    let name ← getIdx rev
    pure (.ref name)
  | 8 =>
    let structName ← getIdx rev
    let child := (← getTag0).size
    pure (.prj structName child)
  | 9 =>
    let mdata ← getMdataStackIndexed rev
    let child := (← getTag0).size
    pure (.mdata mdata child)
  | 10 =>
    let name ← getIdx rev
    let numEntries := (← getTag0).size.toNat
    let mut entries : Array CallSiteEntry := #[]
    for _ in [0:numEntries] do
      let entry ← match ← getU8 with
        | 0 =>
          let canonIdx := (← getTag0).size
          let metaIdx := (← getTag0).size
          pure (CallSiteEntry.kept canonIdx metaIdx)
        | 1 =>
          let sharingIdx := (← getTag0).size
          let metaIdx := (← getTag0).size
          pure (CallSiteEntry.collapsed sharingIdx metaIdx)
        | x => throw s!"invalid CallSiteEntry tag {x}"
      entries := entries.push entry
    let numCanonMeta := (← getTag0).size.toNat
    let mut canonMeta : Array UInt64 := #[]
    for _ in [0:numCanonMeta] do
      canonMeta := canonMeta.push (← getTag0).size
    let origHead ← match ← getU8 with
      | 0 => pure none
      | 1 =>
        let sharingIdx := (← getTag0).size
        let metaIdx := (← getTag0).size
        pure (some (sharingIdx, metaIdx))
      | x => throw s!"invalid CallSite origHead tag {x}"
    pure (.callSite name entries canonMeta origHead)
  | 11 =>
    let nSynth := (← getTag0).size
    let name ← getIdx rev
    let numEntries := (← getTag0).size.toNat
    let mut entries : Array CallSiteEntry := #[]
    for _ in [0:numEntries] do
      let entry ← match ← getU8 with
        | 0 =>
          let canonIdx := (← getTag0).size
          let metaIdx := (← getTag0).size
          pure (CallSiteEntry.kept canonIdx metaIdx)
        | 1 =>
          let sharingIdx := (← getTag0).size
          let metaIdx := (← getTag0).size
          pure (CallSiteEntry.collapsed sharingIdx metaIdx)
        | x => throw s!"invalid CallSiteEntry tag {x}"
      entries := entries.push entry
    let numCanonMeta := (← getTag0).size.toNat
    let mut canonMeta : Array UInt64 := #[]
    for _ in [0:numCanonMeta] do
      canonMeta := canonMeta.push (← getTag0).size
    let wrapperMeta := (← getTag0).size
    pure (.etaCallSite nSynth name entries canonMeta wrapperMeta)
  | x => throw s!"invalid ExprMetaData tag {x}"

/-- Serialize ExprMetaArena (length-prefixed array of ExprMetaData nodes). -/
def putExprMetaArenaIndexed (arena : ExprMetaArena) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨arena.nodes.size.toUInt64⟩
  for node in arena.nodes do
    putExprMetaDataIndexed node idx

def getExprMetaArenaIndexed (rev : NameReverseIndex) : GetM ExprMetaArena := do
  let len := (← getTag0).size.toNat
  let mut nodes : Array ExprMetaData := #[]
  for _ in [0:len] do
    nodes := nodes.push (← getExprMetaDataIndexed rev)
  pure ⟨nodes⟩

/-- Serialize the ConstantMetaInfo variant payload with indexed addresses. -/
def putConstantMetaInfoIndexed (cm : ConstantMetaInfo) (idx : NameIndex) : PutM Unit := do
  match cm with
  | .empty => putU8 255
  | .defn name lvls all ctx arena typeRoot valueRoot =>
    putU8 0
    putIdx name idx
    putIdxVec lvls idx
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
    putTag0 ⟨valueRoot⟩
  | .axio name lvls arena typeRoot =>
    putU8 1
    putIdx name idx
    putIdxVec lvls idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .quot name lvls arena typeRoot =>
    putU8 2
    putIdx name idx
    putIdxVec lvls idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .indc name lvls ctors all ctx arena typeRoot =>
    putU8 3
    putIdx name idx
    putIdxVec lvls idx
    putIdxVec ctors idx
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .ctor name lvls induct arena typeRoot =>
    putU8 4
    putIdx name idx
    putIdxVec lvls idx
    putIdx induct idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .recr name lvls rules all ctx arena typeRoot ruleRoots =>
    putU8 5
    putIdx name idx
    putIdxVec lvls idx
    putIdxVec rules idx
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
    putTag0 ⟨ruleRoots.size.toUInt64⟩
    for r in ruleRoots do putTag0 ⟨r⟩
  | .muts all auxLayout =>
    putU8 6
    putTag0 ⟨all.size.toUInt64⟩
    for cls in all do
      putIdxVec cls idx
    -- Option AuxLayout: 0 tag = none, 1 tag = some(perm vec, ctor-count
    -- vec, evaporated flags). Vecs are Tag0 u64s; evaporated flags are
    -- one u8 (0/1) per entry (mirrors Rust `ConstantMetaInfo::Muts`).
    match auxLayout with
    | none => putU8 0
    | some layout =>
      putU8 1
      putTag0 ⟨layout.perm.size.toUInt64⟩
      for p in layout.perm do putTag0 ⟨p⟩
      putTag0 ⟨layout.sourceCtorCounts.size.toUInt64⟩
      for c in layout.sourceCtorCounts do putTag0 ⟨c⟩
      -- Construction sites that predate the field default
      -- `evaporated := #[]`; serialize per-position all-`0` flags for
      -- them (the FFI decode normalizes identically), so the wire form
      -- always carries `perm.size` flags and Lean/Rust bytes agree.
      let evaporated := if layout.evaporated.isEmpty && !layout.perm.isEmpty
        then Array.replicate layout.perm.size 0 else layout.evaporated
      putTag0 ⟨evaporated.size.toUInt64⟩
      for b in evaporated do putU8 (if b != 0 then 1 else 0)

/-- Serialize ConstantMeta (wrapper) with indexed addresses: the variant
    payload, then the three extension tables — sharing exprs (`putExpr`),
    refs (raw 32-byte addresses, NOT name-indexed), univs (`putUniv`) —
    then the level-spelling patches (per entry: Tag0 arenaIdx, Tag0 len,
    Tag0 virtual univ indices; canonicity §10.6). Mirrors Rust
    `ConstantMeta::put_with`. -/
def putConstantMetaIndexed (cm : ConstantMeta) (idx : NameIndex) : PutM Unit := do
  putConstantMetaInfoIndexed cm.info idx
  putTag0 ⟨cm.metaSharing.size.toUInt64⟩
  for e in cm.metaSharing do putExpr e
  putTag0 ⟨cm.metaRefs.size.toUInt64⟩
  for a in cm.metaRefs do Serialize.put a
  putTag0 ⟨cm.metaUnivs.size.toUInt64⟩
  for u in cm.metaUnivs do putUniv u
  putTag0 ⟨cm.univPatches.size.toUInt64⟩
  for p in cm.univPatches do
    putTag0 ⟨p.arenaIdx⟩
    putTag0 ⟨p.univIdxs.size.toUInt64⟩
    for i in p.univIdxs do putTag0 ⟨i⟩

def getConstantMetaInfoIndexed (rev : NameReverseIndex) : GetM ConstantMetaInfo := do
  let cm ← match ← getU8 with
    | 255 => pure .empty
    | 0 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let all ← getIdxVec rev
      let ctx ← getIdxVec rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      let valueRoot := (← getTag0).size
      pure (.defn name lvls all ctx arena typeRoot valueRoot)
    | 1 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      pure (.axio name lvls arena typeRoot)
    | 2 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      pure (.quot name lvls arena typeRoot)
    | 3 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let ctors ← getIdxVec rev
      let all ← getIdxVec rev
      let ctx ← getIdxVec rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      pure (.indc name lvls ctors all ctx arena typeRoot)
    | 4 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let induct ← getIdx rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      pure (.ctor name lvls induct arena typeRoot)
    | 5 =>
      let name ← getIdx rev
      let lvls ← getIdxVec rev
      let rules ← getIdxVec rev
      let all ← getIdxVec rev
      let ctx ← getIdxVec rev
      let arena ← getExprMetaArenaIndexed rev
      let typeRoot := (← getTag0).size
      let numRuleRoots := (← getTag0).size.toNat
      let mut ruleRoots : Array UInt64 := #[]
      for _ in [0:numRuleRoots] do
        ruleRoots := ruleRoots.push (← getTag0).size
      pure (.recr name lvls rules all ctx arena typeRoot ruleRoots)
    | 6 =>
      let n := (← getTag0).size.toNat
      let mut all : Array (Array Address) := #[]
      for _ in [0:n] do
        all := all.push (← getIdxVec rev)
      let auxLayoutTag ← getU8
      let auxLayout ← match auxLayoutTag with
        | 0 => pure none
        | 1 => do
          let nPerm := (← getTag0).size.toNat
          let mut perm : Array UInt64 := #[]
          for _ in [0:nPerm] do
            perm := perm.push (← getTag0).size
          let nCounts := (← getTag0).size.toNat
          let mut sourceCtorCounts : Array UInt64 := #[]
          for _ in [0:nCounts] do
            sourceCtorCounts := sourceCtorCounts.push (← getTag0).size
          let nEvap := (← getTag0).size.toNat
          let mut evaporated : Array UInt64 := #[]
          for _ in [0:nEvap] do
            match ← getU8 with
            | 0 => evaporated := evaporated.push 0
            | 1 => evaporated := evaporated.push 1
            | x => throw s!"invalid ConstantMeta muts evaporated flag {x}"
          pure (some { perm, sourceCtorCounts, evaporated : AuxLayout })
        | x => throw s!"invalid ConstantMeta muts aux_layout tag {x}"
      pure (.muts all auxLayout)
    | x => throw s!"invalid ConstantMeta tag {x}"
  pure cm

/-- Deserialize ConstantMeta (wrapper): variant payload + the three
    extension tables + the level-spelling patches. Mirrors Rust
    `ConstantMeta::get_with`. An old (pre-normal-levels) file first
    trips here or at the §5 framing assert — both carry the recompile
    hint. -/
def getConstantMetaIndexed (rev : NameReverseIndex) : GetM ConstantMeta := do
  let info ← getConstantMetaInfoIndexed rev
  let sharingLen := (← getTag0).size.toNat
  let mut metaSharing : Array Expr := #[]
  for _ in [0:sharingLen] do
    metaSharing := metaSharing.push (← getExpr)
  let refsLen := (← getTag0).size.toNat
  let mut metaRefs : Array Address := #[]
  for _ in [0:refsLen] do
    metaRefs := metaRefs.push (← Serialize.get (α := Address))
  let univsLen := (← getTag0).size.toNat
  let mut metaUnivs : Array Univ := #[]
  for _ in [0:univsLen] do
    metaUnivs := metaUnivs.push (← getUniv)
  let patchesLen := (← getTag0).size.toNat
  let mut univPatches : Array UnivPatch := #[]
  for _ in [0:patchesLen] do
    let arenaIdx := (← getTag0).size
    let idxsLen := (← getTag0).size.toNat
    let mut univIdxs : Array UInt64 := #[]
    for _ in [0:idxsLen] do
      univIdxs := univIdxs.push (← getTag0).size
    univPatches := univPatches.push { arenaIdx, univIdxs }
  pure { info, metaSharing, metaRefs, metaUnivs, univPatches }

/-- Serialize Comm (simple - just two addresses). -/
def putComm (c : Comm) : PutM Unit := do
  Serialize.put c.secret
  Serialize.put c.payload

def getComm : GetM Comm := do
  let secret ← Serialize.get
  let payload ← Serialize.get
  pure ⟨secret, payload⟩

instance : Serialize Comm where
  put := putComm
  get := getComm

/-- Convenience serialization for Comm (untagged). -/
def serComm (c : Comm) : ByteArray := runPut (putComm c)
def deComm (bytes : ByteArray) : Except String Comm := runGet getComm bytes

/-- Serialize Comm with Tag4{0xE, 1} header. -/
def putCommTagged (c : Comm) : PutM Unit := do
  putTag4 ⟨0xE, 1⟩
  putComm c

/-- Serialize Comm with Tag4{0xE, 1} header to bytes. -/
def serCommTagged (c : Comm) : ByteArray := runPut (putCommTagged c)

/-- Compute commitment address: blake3(Tag4{0xE,5} + secret + payload). -/
def Comm.commit (c : Comm) : Address := Address.blake3 (serCommTagged c)

/-! ## Ixon Environment -/

/-- The Ixon environment, containing all compiled constants.
    Mirrors Rust's `ix::ixon::env::Env` structure. -/
structure Env where
  /-- Alpha-invariant constants: Address → lazily-materialized constant.
      Stored as serialized bytes ([`LazyConstant`]) and parsed on demand so a
      freshly loaded env only pays for the constants it actually touches. -/
  consts : Std.HashMap Address LazyConstant := {}
  /-- Named references: Ix.Name → Named (includes address + metadata) -/
  named : Std.HashMap Ix.Name Named := {}
  /-- Raw data blobs: Address → bytes -/
  blobs : Std.HashMap Address ByteArray := {}
  /-- Hash-consed name components: Address → Ix.Name -/
  names : Std.HashMap Address Ix.Name := {}
  /-- Cryptographic commitments: Address → Comm -/
  comms : Std.HashMap Address Comm := {}
  /-- Reverse index: constant Address → Ix.Name -/
  addrToName : Std.HashMap Address Ix.Name := {}
  /-- Distinguished root constant for bundle envs; `none` for whole
      environments. A pointer, not a proof: readers check
      `main ∈ consts`, and consumers holding an externally-expected
      address must compare against it. -/
  main : Option Address := none
  /-- Explicit trust boundary for thin bundles: addresses (constants
      or blobs) the receiver is expected to already have. Serialized
      as a strictly ascending leaf list; `Ix.Merkle.merkleRootCanonical`
      over it reproduces the root a `Claim.assumptions` commits to. -/
  assumptions : Std.HashSet Address := {}
  /-- Reducibility hints, keyed by constant address — the single home
      for hints (they do not appear in `ConstantMeta`). The compiler
      populates this map; `putEnv` serializes it as the hints section
      and `getEnv` reads it back. Mirrors Rust `Env.anon_hints`. -/
  anonHints : Std.HashMap Address Lean.ReducibilityHints := {}
  deriving Inhabited

namespace Env

/-- Store a constant at the given address. Caches the materialized value. -/
def storeConst (env : Env) (addr : Address) (const : Constant) : Env :=
  { env with consts := env.consts.insert addr (LazyConstant.ofConstant const) }

/-- Get a constant by address, materializing on demand. -/
def getConst? (env : Env) (addr : Address) : Option Constant :=
  (env.consts.get? addr).bind LazyConstant.get?

/-- Register a name with full Named metadata. -/
def registerName (env : Env) (name : Ix.Name) (named : Named) : Env :=
  { env with
    named := env.named.insert name named
    addrToName := env.addrToName.insert named.addr name }

/-- Register a name with just an address (empty metadata). -/
def registerNameAddr (env : Env) (name : Ix.Name) (addr : Address) : Env :=
  env.registerName name { addr, constMeta := .empty }

/-- Look up a name's address. -/
def getAddr? (env : Env) (name : Ix.Name) : Option Address :=
  env.named.get? name |>.map (·.addr)

/-- Look up a name's Named entry. -/
def getNamed? (env : Env) (name : Ix.Name) : Option Named :=
  env.named.get? name

/-- Look up an address's name. -/
def getName? (env : Env) (addr : Address) : Option Ix.Name :=
  env.addrToName.get? addr

/-- Store a blob and return its content address. -/
def storeBlob (env : Env) (bytes : ByteArray) : Env × Address :=
  let addr := Address.blake3 bytes
  ({ env with blobs := env.blobs.insert addr bytes }, addr)

/-- Get a blob by address. -/
def getBlob? (env : Env) (addr : Address) : Option ByteArray :=
  env.blobs.get? addr

/-- Store a commitment. -/
def storeComm (env : Env) (addr : Address) (comm : Comm) : Env :=
  { env with comms := env.comms.insert addr comm }

/-- Get a commitment by address. -/
def getComm? (env : Env) (addr : Address) : Option Comm :=
  env.comms.get? addr

/-- Number of constants. -/
def constCount (env : Env) : Nat := env.consts.size

/-- Number of blobs. -/
def blobCount (env : Env) : Nat := env.blobs.size

/-- Number of named constants. -/
def namedCount (env : Env) : Nat := env.named.size

/-- Number of commitments. -/
def commCount (env : Env) : Nat := env.comms.size

instance : Repr Env where
  reprPrec env _ := s!"Env({env.constCount} consts, {env.blobCount} blobs, {env.namedCount} named)"

end Env

/-! ## KVMap resolution (kernel ingress)

Mirror of `crates/ixon/src/metadata.rs::resolve_kvmap` and its `deser_*`
helpers: resolve an Ixon KVMap (address-based) to Lean-level MData
(name/value pairs) against an `Env`. Kernel meta-mode ingress uses this to
materialize `Expr.mdata` layers; it lives here (not the decompiler) because
it only needs `Env` blob/name lookups.

Rust semantics preserved exactly: entries whose names/blobs cannot be
resolved are silently DROPPED (`filter_map` + `?` in Rust — `Option` here),
never errors. -/

/-- Byte cursor for deserializing syntax blobs (`Option`-valued to mirror
    the Rust `deser_*` family). -/
structure DeserCursor where
  bytes : ByteArray
  pos : Nat := 0

namespace DeserCursor

def u8? (c : DeserCursor) : Option (UInt8 × DeserCursor) :=
  if h : c.pos < c.bytes.size then
    some (c.bytes[c.pos], { c with pos := c.pos + 1 })
  else none

/-- Tag0 varint (same format as `getTag0`): head byte < 128 is the value;
    otherwise `head % 128 + 1` little-endian extra bytes follow. -/
def tag0? (c : DeserCursor) : Option (UInt64 × DeserCursor) := do
  let (head, c) ← c.u8?
  if head < 128 then
    some (head.toUInt64, c)
  else
    let extra := (head % 128).toNat + 1
    let mut val : UInt64 := 0
    let mut cur := c
    for i in [0:extra] do
      let (b, c') ← cur.u8?
      val := val ||| (b.toUInt64 <<< (i * 8).toUInt64)
      cur := c'
    some (val, cur)

def addr? (c : DeserCursor) : Option (Address × DeserCursor) :=
  if c.pos + 32 ≤ c.bytes.size then
    some (⟨c.bytes.extract c.pos (c.pos + 32)⟩, { c with pos := c.pos + 32 })
  else none

end DeserCursor

/-- Mirror of `metadata.rs::deser_int` (compile-side `OfInt` blob encoding). -/
def deserIntBlob (bytes : ByteArray) : Option Ix.Int :=
  if bytes.size == 0 then none
  else
    let rest := bytes.extract 1 bytes.size
    match bytes[0]! with
    | 0 => some (.ofNat (Nat.fromBytesLE rest.data))
    | 1 => some (.negSucc (Nat.fromBytesLE rest.data))
    | _ => none

def deserSubstring (env : Env) (c : DeserCursor) :
    Option (Ix.Substring × DeserCursor) := do
  let (strAddr, c) ← c.addr?
  let s ← (← env.getBlob? strAddr) |> String.fromUTF8?
  let (startPos, c) ← c.tag0?
  let (stopPos, c) ← c.tag0?
  some (⟨s, startPos.toNat, stopPos.toNat⟩, c)

def deserSourceInfo (env : Env) (c : DeserCursor) :
    Option (Ix.SourceInfo × DeserCursor) := do
  let (tag, c) ← c.u8?
  match tag with
  | 0 =>
    let (leading, c) ← deserSubstring env c
    let (leadingPos, c) ← c.tag0?
    let (trailing, c) ← deserSubstring env c
    let (trailingPos, c) ← c.tag0?
    some (.original leading leadingPos.toNat trailing trailingPos.toNat, c)
  | 1 =>
    let (start, c) ← c.tag0?
    let (stop, c) ← c.tag0?
    let (canonical, c) ← c.u8?
    some (.synthetic start.toNat stop.toNat (canonical != 0), c)
  | 2 => some (.none, c)
  | _ => none

def deserPreresolved (env : Env) (c : DeserCursor) :
    Option (Ix.SyntaxPreresolved × DeserCursor) := do
  let (tag, c) ← c.u8?
  match tag with
  | 0 =>
    let (nameAddr, c) ← c.addr?
    let name ← env.names[nameAddr]?
    some (.namespace name, c)
  | 1 =>
    let (nameAddr, c) ← c.addr?
    let name ← env.names[nameAddr]?
    let (count, c) ← c.tag0?
    let mut fields : Array String := #[]
    let mut cur := c
    for _ in [0:count.toNat] do
      let (fieldAddr, c') ← cur.addr?
      let field ← (← env.getBlob? fieldAddr) |> String.fromUTF8?
      fields := fields.push field
      cur := c'
    some (.decl name fields, cur)
  | _ => none

/-- Mirror of `metadata.rs::deser_syntax` (compile-side
    `serialize_syntax_inner` encoding). -/
partial def deserSyntax (env : Env) (c : DeserCursor) :
    Option (Ix.Syntax × DeserCursor) := do
  let (tag, c) ← c.u8?
  match tag with
  | 0 => some (.missing, c)
  | 1 =>
    let (info, c) ← deserSourceInfo env c
    let (kindAddr, c) ← c.addr?
    let kind ← env.names[kindAddr]?
    let (argCount, c) ← c.tag0?
    let mut args : Array Ix.Syntax := #[]
    let mut cur := c
    for _ in [0:argCount.toNat] do
      let (arg, c') ← deserSyntax env cur
      args := args.push arg
      cur := c'
    some (.node info kind args, cur)
  | 2 =>
    let (info, c) ← deserSourceInfo env c
    let (valAddr, c) ← c.addr?
    let val ← (← env.getBlob? valAddr) |> String.fromUTF8?
    some (.atom info val, c)
  | 3 =>
    let (info, c) ← deserSourceInfo env c
    let (rawVal, c) ← deserSubstring env c
    let (valAddr, c) ← c.addr?
    let val ← env.names[valAddr]?
    let (prCount, c) ← c.tag0?
    let mut preresolved : Array Ix.SyntaxPreresolved := #[]
    let mut cur := c
    for _ in [0:prCount.toNat] do
      let (pr, c') ← deserPreresolved env cur
      preresolved := preresolved.push pr
      cur := c'
    some (.ident info rawVal val preresolved, cur)
  | _ => none

/-- Resolve one address-based `DataValue` to its Lean-level form. -/
def resolveDataValue (env : Env) : DataValue → Option Ix.DataValue
  | .ofString a => do some (.ofString (← (← env.getBlob? a) |> String.fromUTF8?))
  | .ofBool b => some (.ofBool b)
  | .ofName a => do some (.ofName (← env.names[a]?))
  | .ofNat a => do some (.ofNat (Nat.fromBytesLE (← env.getBlob? a).data))
  | .ofInt a => do some (.ofInt (← deserIntBlob (← env.getBlob? a)))
  | .ofSyntax a => do
    let bytes ← env.getBlob? a
    let (syn, _) ← deserSyntax env ⟨bytes, 0⟩
    some (.ofSyntax syn)

/-- Resolve an Ixon KVMap to Lean-level MData pairs. Unresolvable entries
    are dropped (Rust `filter_map` parity). -/
def resolveKVMap (env : Env) (kvm : KVMap) : Array (Ix.Name × Ix.DataValue) :=
  kvm.filterMap fun (addr, dv) => do
    let name ← env.names[addr]?
    let resolved ← resolveDataValue env dv
    some (name, resolved)

/-! ## Raw FFI Types for Env -/

/-- Raw FFI structure for a constant: Address → Constant.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawConst where
  addr : Address
  const : Constant
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a named entry: Ix.Name → (Address, ConstantMeta).
    Array-based version for FFI compatibility (no HashMap). -/
structure RawNamed where
  name : Ix.Name
  addr : Address
  constMeta : ConstantMeta
  /-- Pre-aux_gen (address, metadata) for rewritten constants (mirrors
      `Named.original`) — without it, the FFI env value path would drop
      the §5 original edges that the pure parser preserves. -/
  original : Option (Address × ConstantMeta) := none
  /-- Per-name reducibility hints (mirrors `Named.hints`). -/
  hints : Option Lean.ReducibilityHints := none
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a blob: Address → ByteArray.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawBlob where
  addr : Address
  bytes : ByteArray
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a commitment: Address → Comm.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawComm where
  addr : Address
  comm : Comm
  deriving Repr, Inhabited, BEq

/-- Raw FFI name entry: address → Ix.Name mapping.
    Used to transfer the full names table across FFI. -/
structure RawNameEntry where
  addr : Address
  name : Ix.Name
  deriving Repr, Inhabited, BEq

/-- Raw FFI environment structure using arrays instead of HashMaps.
    This is the array-based equivalent of `Env` for FFI compatibility.
    Field order matters: the Rust mirror (`LeanIxonRawEnv`) addresses
    constructor slots positionally (0-7). -/
structure RawEnv where
  consts : Array RawConst
  named : Array RawNamed
  blobs : Array RawBlob
  comms : Array RawComm
  names : Array RawNameEntry := #[]
  /-- Bundle root (`Env.main`). -/
  main : Option Address := none
  /-- Bundle trust boundary (`Env.assumptions`), sorted ascending. -/
  assumptions : Array Address := #[]
  /-- Explicit reducibility hints (`Env.anonHints`), sorted by address. -/
  anonHints : Array (Address × Lean.ReducibilityHints) := #[]
  deriving Repr, Inhabited, BEq

namespace RawEnv

/-- Recursively add all name components to the names map.
    Uses Ix.Name.getHash for address computation. -/
partial def addNameComponents (names : Std.HashMap Address Ix.Name) (name : Ix.Name) : Std.HashMap Address Ix.Name :=
  let addr := name.getHash
  if names.contains addr then names
  else
    let names := names.insert addr name
    match name with
    | .anonymous _ => names
    | .str parent _ _ => addNameComponents names parent
    | .num parent _ _ => addNameComponents names parent

/-- Recursively add all name components to the names map AND store string components as blobs.
    This matches Rust's behavior for deduplication of string data. -/
partial def addNameComponentsWithBlobs
    (names : Std.HashMap Address Ix.Name)
    (blobs : Std.HashMap Address ByteArray)
    (name : Ix.Name)
    : Std.HashMap Address Ix.Name × Std.HashMap Address ByteArray :=
  let addr := name.getHash
  if names.contains addr then (names, blobs)
  else
    let names := names.insert addr name
    match name with
    | .anonymous _ => (names, blobs)
    | .str parent s _ =>
      -- Store string component as blob for deduplication
      let strBytes := s.toUTF8
      let strAddr := Address.blake3 strBytes
      let blobs := blobs.insert strAddr strBytes
      addNameComponentsWithBlobs names blobs parent
    | .num parent _ _ =>
      addNameComponentsWithBlobs names blobs parent

/-- Convert RawEnv to Env with HashMaps.
    This is done on the Lean side for correct hash function usage. -/
def toEnv (raw : RawEnv) : Env := Id.run do
  let mut env : Env := {}
  for ⟨addr, const⟩ in raw.consts do
    env := env.storeConst addr const
  -- Load the full names table (includes binder names, level params, etc.)
  -- Use addNameComponents to store at canonical addresses (name.getHash)
  -- and ensure all parent components are present for topological consistency.
  for ⟨_, name⟩ in raw.names do
    env := { env with names := addNameComponents env.names name }
  for ⟨name, addr, constMeta, original, hints⟩ in raw.named do
    -- Also add name components for indexed serialization
    env := { env with names := addNameComponents env.names name }
    env := env.registerName name { addr, constMeta, original, hints }
  for ⟨addr, bytes⟩ in raw.blobs do
    env := { env with blobs := env.blobs.insert addr bytes }
  for ⟨addr, comm⟩ in raw.comms do
    env := env.storeComm addr comm
  return { env with
    main := raw.main
    assumptions := raw.assumptions.foldl (·.insert ·) {}
    anonHints := raw.anonHints.foldl (fun m (a, h) => m.insert a h) {} }

end RawEnv

/-! ## Env Serialization -/

namespace Env

/-- Convert Env with HashMaps to RawEnv with Arrays for FFI.
    Includes the full names table for round-trip fidelity. The
    set-shaped bundle fields are sorted so the transfer is
    deterministic (matches Rust `ixon_env_to_decoded`). -/
def toRawEnv (env : Env) : RawEnv := {
  consts := env.consts.toArray.map fun (addr, lc) =>
    { addr, const := lc.get?.getD default }
  named := env.named.toArray.map fun (name, n) =>
    { name, addr := n.addr, constMeta := n.constMeta,
      original := n.original, hints := n.hints }
  blobs := env.blobs.toArray.map fun (addr, bytes) => { addr, bytes }
  comms := env.comms.toArray.map fun (addr, comm) => { addr, comm }
  names := env.names.toArray.map fun (addr, name) => { addr, name }
  main := env.main
  assumptions := env.assumptions.toList.toArray.qsort
    fun a b => (compare a b).isLT
  anonHints := env.anonHints.toList.toArray.qsort
    fun a b => (compare a.1 b.1).isLT
}

/-- Tag4 flag for Env (0xE). -/
def FLAG : UInt8 := 0xE

/-- `.ixe` format version, carried in the header's Tag4 size field.
    Any change to serialized bytes bumps this; readers reject a
    mismatch and there is no back-compat reading of old versions —
    `.ixe` files are regenerated artifacts. Mirrors Rust
    `Env::VERSION` in `crates/ixon/src/serialize.rs`. -/
def VERSION : UInt64 := 2

/-- Serialize a name component (references parent by address).
    Format: tag (1 byte) + parent_addr (32 bytes) + data -/
def putNameComponent (name : Ix.Name) : PutM Unit := do
  match name with
  | .anonymous _ => putU8 0
  | .str parent s _ =>
    putU8 1
    Serialize.put parent.getHash
    putTag0 ⟨s.utf8ByteSize.toUInt64⟩
    putBytes s.toUTF8
  | .num parent n _ =>
    putU8 2
    Serialize.put parent.getHash
    let bytes := ByteArray.mk (Nat.toBytesLE n)
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

/-- Deserialize a name component using a lookup table for parents. -/
def getNameComponent (namesLookup : Std.HashMap Address Ix.Name) : GetM Ix.Name := do
  let tag ← getU8
  match tag with
  | 0 => pure Ix.Name.mkAnon
  | 1 =>
    let parentAddr ← Serialize.get
    let parent ← match namesLookup.get? parentAddr with
      | some p => pure p
      | none => throw s!"getNameComponent: missing parent address {reprStr (toString parentAddr)}"
    let len := (← getTag0).size.toNat
    let sBytes ← getBytes len
    match String.fromUTF8? sBytes with
    | some s => pure (Ix.Name.mkStr parent s)
    | none => throw "getNameComponent: invalid UTF-8"
  | 2 =>
    let parentAddr ← Serialize.get
    let parent ← match namesLookup.get? parentAddr with
      | some p => pure p
      | none => throw s!"getNameComponent: missing parent address {reprStr (toString parentAddr)}"
    let len := (← getTag0).size.toNat
    let nBytes ← getBytes len
    pure (Ix.Name.mkNat parent (Nat.fromBytesLE nBytes.data))
  | t => throw s!"getNameComponent: invalid tag {t}"

/-- Topologically sort names so parents come before children. -/
partial def topologicalSortNames (names : Std.HashMap Address Ix.Name) : Array (Address × Ix.Name) :=
  -- DFS topological sort: visit parent before child
  -- This matches the Rust implementation
  let anonAddr := Ix.Name.mkAnon.getHash
  let rec visit (name : Ix.Name) (visited : Std.HashSet Address) (result : Array (Address × Ix.Name))
      : Std.HashSet Address × Array (Address × Ix.Name) :=
    let addr := name.getHash
    if visited.contains addr then (visited, result)
    else
      -- Visit parent first
      let (visited, result) := match name with
        | .anonymous _ => (visited, result)
        | .str parent _ _ => visit parent visited result
        | .num parent _ _ => visit parent visited result
      let visited := visited.insert addr
      let result := result.push (addr, name)
      (visited, result)
  -- Include the anonymous name first so it gets index 0 in the name
  -- index (arena nodes frequently reference it as a binder name).
  -- Matches Rust `topological_sort_names`, which emits it explicitly —
  -- required for byte-identical writer output across the mirrors.
  let initVisited : Std.HashSet Address := ({} : Std.HashSet Address).insert anonAddr
  let initResult : Array (Address × Ix.Name) := #[(anonAddr, Ix.Name.mkAnon)]
  -- Sort names by address before iterating to ensure deterministic DFS order
  let sortedEntries := names.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  let (_, result) := sortedEntries.foldl (init := (initVisited, initResult)) fun (visited, result) (_, name) =>
    visit name visited result
  result

/-- Serialize an Env to bytes.

    Runs in `ExceptT String PutM`: the §3/§5 sections key their entries
    by §2/§4 indices, so hints keyed outside `consts` or named entries
    referencing unstored constants/names are unrepresentable and must
    fail at write time (mirrors Rust `Env::put`). -/
def putEnv (env : Env) : ExceptT String PutM Unit := do
  -- Header: Tag4 with flag=0xE, size=VERSION (format version)
  putTag4 ⟨FLAG, VERSION⟩

  -- Canonical merkle root over consts addresses (matches Rust Env::put).
  -- Always 32 bytes: for empty const sets, the sentinel
  -- `Ix.Merkle.zeroAddress` is used (cannot collide with any non-empty
  -- canonical root, which is always a Blake3 hash).
  let constAddrs : Array Address :=
    (env.consts.toList.toArray.map (·.1))
  let root := (Ix.Merkle.merkleRootCanonical constAddrs).getD Ix.Merkle.zeroAddress
  Serialize.put root

  -- Bundle header fields: main (Option, 0/1-tagged) + assumptions
  -- (strictly ascending address list). Matches Rust `Env::put`.
  match env.main with
  | none => putU8 0
  | some addr => do
    putU8 1
    Serialize.put addr
  let assumptions := env.assumptions.toList.toArray.qsort
    fun a b => (compare a b).isLT
  putTag0 ⟨assumptions.size.toUInt64⟩
  for addr in assumptions do
    Serialize.put addr

  -- Section 1: Blobs (Address -> bytes)
  let blobs := env.blobs.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨blobs.size.toUInt64⟩
  for (addr, bytes) in blobs do
    Serialize.put addr
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

  -- Section 2: Consts (Address -> Tag0-length-prefixed Tag4 constant bytes)
  --
  -- The Tag0 length sidecar is added at the env-section level so a lazy
  -- loader can slice each constant without parsing its Tag4 envelope.
  -- The length is NOT part of the content-addressed bytes: the address
  -- is `Address.hash` over the Tag4 constant body alone (which is
  -- exactly what `serConstant` produces).
  let consts := env.consts.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨consts.size.toUInt64⟩
  for (addr, lc) in consts do
    Serialize.put addr
    -- The lazy entry already holds exactly `serConstant`'s output, so write
    -- its bytes directly — no re-materialization or re-serialization.
    let bytes := lc.rawBytes
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

  -- Rank of each constant in §2's ascending-address order — §3 hint
  -- entries and §5 named entries key their constants through it.
  let constIdx : Std.HashMap Address UInt64 := consts.zipIdx.foldl
    (fun acc ((addr, _), i) => acc.insert addr i.toUInt64) {}

  -- Section 3: anon_hints — the canonical hint channel for the
  -- anon/lazy readers, placed before the metadata sections so they can
  -- stop right after it. Serialized straight from `env.anonHints`, the
  -- single home for hints, as delta-coded §2 ranks + fused hints (the
  -- address sort is load-bearing: it makes the ranks strictly
  -- ascending). Matches Rust `Env::put`.
  let hintPairs := env.anonHints.toList.toArray.qsort
    fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨hintPairs.size.toUInt64⟩
  let mut prevRank : UInt64 := 0 -- rank + 1 of the previous entry
  for (addr, hints) in hintPairs do
    match constIdx.get? addr with
    | none => throw s!"putEnv: anon_hints key {reprStr (toString addr)} not \
                       present in consts — hints must be keyed by stored \
                       constant addresses"
    | some rank =>
      putTag0 ⟨rank + 1 - prevRank⟩
      putFusedHint hints
      prevRank := rank + 1

  -- Section 4: Names (Address -> Name component)
  -- Topologically sorted so parents come before children, with ties broken by address
  let sortedNames := topologicalSortNames env.names
  -- Build name index from sorted positions (matching Rust)
  let nameIdx := sortedNames.zipIdx.foldl
    (fun acc ((addr, _), i) => acc.insert addr i.toUInt64) {}
  putTag0 ⟨sortedNames.size.toUInt64⟩
  for (addr, name) in sortedNames do
    Serialize.put addr
    putNameComponent name

  -- Section 5: Named (name §4-index -> Named with metadata; the
  -- entry's constant is a §2 rank). Entry order stays ascending name
  -- hash. Each entry carries its EXACT per-name hint in the header,
  -- then a length-prefixed metadata blob so hint scanners can skip the
  -- bodies. `original` keeps a raw address: it can reference an
  -- assumed constant that is NOT stored in §2 (prune cut bundles).
  let named := env.named.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨named.size.toUInt64⟩
  for (name, namedEntry) in named do
    -- The name's stored hash is bytewise its §4 component address.
    match nameIdx.get? name.getHash with
    | none => throw s!"putEnv: named key {reprStr (toString name.getHash)} \
                       not present in the name table"
    | some i => putTag0 ⟨i⟩
    match constIdx.get? namedEntry.addr with
    | none => throw s!"putEnv: named entry constant \
                       {reprStr (toString namedEntry.addr)} not present in \
                       consts — named entries must reference stored constants"
    | some rank => putTag0 ⟨rank⟩
    putFusedOptHint namedEntry.hints
    -- Metadata blob: ConstantMeta + original as Option (0 = none,
    -- 1 = some(addr, meta)), length-prefixed.
    let blob := runPut do
      putConstantMetaIndexed namedEntry.constMeta nameIdx
      match namedEntry.original with
      | none => putU8 0
      | some (origAddr, origMeta) =>
        putU8 1
        Serialize.put origAddr
        putConstantMetaIndexed origMeta nameIdx
    putTag0 ⟨blob.size.toUInt64⟩
    putBytes blob

  -- Section 6: Comms (Address -> Comm)
  let comms := env.comms.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨comms.size.toUInt64⟩
  for (addr, comm) in comms do
    Serialize.put addr
    putComm comm

/-- Deserialize an Env from bytes (pure Lean, full metadata). Used for
    round-trip (`deEnv`) on small/in-memory envs. The lazy/anon `.ixe` check
    path does **not** go through here — it uses the Rust parser via
    `deEnvAnon` / `rsDeEnvLazyFFI`, which handles every metadata variant and
    returns zero-copy constant windows. -/
def getEnv : GetM Env := do
  -- Header
  let tag ← getTag4
  if tag.flag != FLAG then
    throw s!"Env.get: expected flag 0x{FLAG.toNat.toDigits 16}, got 0x{tag.flag.toNat.toDigits 16}"
  if tag.size != VERSION then
    throw s!"Env.get: expected .ixe format version {VERSION}, got {tag.size} — recompile the artifact"

  -- Canonical merkle root (fixed 32 bytes). For empty const sets the
  -- stored value is `Ix.Merkle.zeroAddress`. Verified at end against
  -- the recomputed root.
  let storedRoot : Address ← Serialize.get

  -- Bundle header fields: main (Option) + strictly ascending
  -- assumptions list. A pre-bundle-format `.ixe` has the §1 blob
  -- count here, so a bad tag most likely means a stale file.
  let mainTag ← getU8
  let main : Option Address ← match mainTag with
    | 0 => pure none
    | 1 => some <$> Serialize.get
    | x => throw s!"Env.get: invalid main tag {x} in bundle header — \
                    possibly a pre-bundle-format .ixe; recompile it"
  let numAssumptions := (← getTag0).size
  let mut assumptionArr : Array Address := #[]
  for _ in [:numAssumptions.toNat] do
    let addr : Address ← Serialize.get
    if let some prev := assumptionArr.back? then
      if !(compare prev addr).isLT then
        throw "Env.get: assumptions not strictly ascending"
    assumptionArr := assumptionArr.push addr

  let mut env : Env := {
    main
    assumptions := assumptionArr.foldl (·.insert ·) {}
  }

  -- Section 1: Blobs (hash-verified per entry: a swapped blob would
  -- otherwise silently change a Nat/String literal's value — the
  -- consts merkle root covers only constant addresses)
  let numBlobs := (← getTag0).size
  for _ in [:numBlobs.toNat] do
    let addr ← Serialize.get
    let len := (← getTag0).size
    let bytes ← getBytes len.toNat
    if Address.blake3 bytes != addr then
      throw s!"Env.get: blob bytes hash mismatch for {reprStr (toString addr)}"
    env := { env with blobs := env.blobs.insert addr bytes }

  -- Section 2: Consts (length-prefixed; see putEnv for rationale).
  -- Per-entry integrity: bytes must hash to the stored address. The
  -- file order (strictly ascending addresses — enforced, since §3/§5
  -- indices resolve against it) is retained as `constOrder`.
  let numConsts := (← getTag0).size
  let mut constOrder : Array Address := #[]
  for _ in [:numConsts.toNat] do
    let addr ← Serialize.get
    let len := (← getTag0).size
    let bytes ← getBytes len.toNat
    if Address.blake3 bytes != addr then
      throw s!"Env.get: const bytes hash mismatch for {reprStr (toString addr)}"
    if let some prev := constOrder.back? then
      if !(compare prev addr).isLT then
        throw "Env.get: §2 constants not in strictly ascending address order"
    constOrder := constOrder.push addr
    match deConstant bytes with
    | .ok constant => env := env.storeConst addr constant
    | .error e =>
      throw s!"Env.get: bad constant bytes for addr {reprStr (toString addr)}: {e}"

  -- `main` must reference a constant actually present in the file.
  if let some m := main then
    if !env.consts.contains m then
      throw s!"Env.get: main {reprStr (toString m)} not present in consts"

  -- Section 3: anon_hints — delta-coded §2 ranks + fused hints.
  let numHints := (← getTag0).size
  if numHints.toNat > constOrder.size then
    throw s!"Env.get: hint count {numHints} exceeds const count \
             {constOrder.size} — possibly a pre-compact-keys .ixe; \
             recompile it"
  let mut cursor : Nat := 0
  for _ in [:numHints.toNat] do
    let delta := (← getTag0).size
    if delta == 0 then
      throw "Env.get: zero hint index delta (§3 must be strictly \
             ascending) — possibly a pre-compact-keys .ixe; recompile it"
    let idx := cursor + delta.toNat - 1
    let addr ← match constOrder[idx]? with
      | some a => pure a
      | none =>
        throw s!"Env.get: hint index {idx} out of range ({constOrder.size} \
                 consts) — possibly a pre-compact-keys .ixe; recompile it"
    let hints ← getFusedHint
    env := { env with anonHints := env.anonHints.insert addr hints }
    cursor := idx + 1

  -- Section 4: Names (build lookup table AND reverse index)
  let numNames := (← getTag0).size
  let mut namesLookup : Std.HashMap Address Ix.Name := {}
  let mut nameRev : NameReverseIndex := #[]
  -- Always include anonymous name
  namesLookup := namesLookup.insert Ix.Name.mkAnon.getHash Ix.Name.mkAnon
  for _ in [:numNames.toNat] do
    let addr ← Serialize.get
    let name ← getNameComponent namesLookup
    nameRev := nameRev.push addr
    namesLookup := namesLookup.insert addr name
    env := { env with names := env.names.insert addr name }

  -- Section 5: Named (name §4-index -> Named with metadata; the
  -- entry's constant is a §2 rank; the per-name hint sits in the
  -- header before the length-prefixed metadata blob; `original` stays
  -- a raw address)
  let numNamed := (← getTag0).size
  for _ in [:numNamed.toNat] do
    let nameIdx := (← getTag0).size.toNat
    let nameAddr ← match nameRev[nameIdx]? with
      | some a => pure (a : Address)
      | none =>
        throw s!"Env.get: §5 name index {nameIdx} out of range \
                 ({nameRev.size} names) — possibly a pre-compact-keys .ixe; \
                 recompile it"
    let constRank := (← getTag0).size.toNat
    let constAddr ← match constOrder[constRank]? with
      | some a => pure a
      | none =>
        throw s!"Env.get: §5 constant index {constRank} out of range \
                 ({constOrder.size} consts) — possibly a pre-compact-keys \
                 .ixe; recompile it"
    let hints ← getFusedOptHint
    let metaLen := (← getTag0).size.toNat
    let stBefore ← get
    if stBefore.bytes.size - stBefore.idx < metaLen then
      throw s!"Env.get: §5 metadata blob needs {metaLen} bytes, have \
               {stBefore.bytes.size - stBefore.idx} — possibly a \
               pre-compact-keys .ixe; recompile it"
    let constMeta ← getConstantMetaIndexed nameRev
    -- Deserialize original as Option: 0 = None, 1 = Some(addr, meta)
    let origTag ← getU8
    let original ← match origTag with
    | 0 => pure none
    | 1 => do
      let origAddr ← Serialize.get (α := Address)
      let origMeta ← getConstantMetaIndexed nameRev
      pure (some (origAddr, origMeta))
    | x => throw s!"getEnv: Named.original: invalid tag {x}"
    -- The header's length must frame exactly the parsed bytes.
    let stAfter ← get
    if stAfter.idx - stBefore.idx != metaLen then
      throw s!"Env.get: §5 metadata blob length mismatch (header says \
               {metaLen}, parsed {stAfter.idx - stBefore.idx}) — possibly a \
               pre-normal-levels .ixe; recompile it"
    match namesLookup.get? nameAddr with
    | some name =>
      let namedEntry : Named := { addr := constAddr, constMeta, original, hints }
      env := { env with
        named := env.named.insert name namedEntry
        addrToName := env.addrToName.insert constAddr name }
    | none =>
      throw s!"getEnv: named entry references unknown name address {reprStr (toString nameAddr)}"

  -- Section 6: Comms
  let numComms := (← getTag0).size
  for _ in [:numComms.toNat] do
    let addr ← Serialize.get (α := Address)
    let comm ← getComm
    env := { env with comms := env.comms.insert addr comm }

  -- Verify the stored merkle root against the recomputed value —
  -- `constOrder` is the §2 key set (ascending, enforced above). Empty
  -- const set → expected = zeroAddress.
  let computedRoot :=
    (Ix.Merkle.merkleRootCanonical constOrder).getD Ix.Merkle.zeroAddress
  if computedRoot != storedRoot then
    throw "Env.get: merkle root mismatch"

  -- Comms is the final section; trailing bytes are truncation damage
  -- or concatenated garbage. (Mirrors Rust `Env::get`; the early-stop
  -- readers cannot make this check by design.)
  let st ← get
  if st.idx != st.bytes.size then
    throw s!"Env.get: {st.bytes.size - st.idx} trailing bytes after final section"

  pure env

end Env

/-! ### Verified lazy env load (streaming serde gate)

`deEnv` + `serEnv` materialize every §2 constant and every §5 metadata
arena, then rebuild the whole 3+ GB byte image to compare — at
whole-Mathlib scale that is a >100 GiB resident spike (measured), while
the serialized format was explicitly designed for skipping (§2 bodies
and §5 metadata blobs are length-prefixed). The verified lazy load
keeps the gate's exact strength — every unit of the file is parsed with
the pure reader, re-serialized with the pure writer, and compared
byte-for-byte against its input span, with the spans covering the file
gaplessly — but transiently, one unit at a time. What it retains:
constants as zero-copy `LazyConstant.ofSlice` windows, §5 rows with
their metadata as byte windows (`NamedRow`, materialized per name on
demand), and the compact sections (blobs, names, hints, comms) eagerly.

Writer-contract checks the whole-image compare used to catch
structurally are asserted directly: §1/§2/§6 ascending key order, §5
ascending name order, §4 order equal to `topologicalSortNames` of the
parsed name set, the merkle root, and the trailing-bytes check. -/

/-- One §5 entry with its metadata deferred as a byte window into the
    backing buffer. `materialize` parses the window into a full `Named`. -/
structure NamedRow where
  name : Ix.Name
  /-- §4 position of `name` (the wire key). -/
  nameIdx : UInt64
  /-- §2 rank of `addr` (the wire key). -/
  constRank : UInt64
  addr : Address
  hints : Option Lean.ReducibilityHints := none
  /-- Offset/length of the metadata blob (ConstantMeta + original). -/
  metaOff : Nat
  metaLen : Nat
  deriving Inhabited

/-- Result of `deEnvVerifiedLazy`: a lazily-backed `Env` (constants are
    `ofSlice` windows; `named` is EMPTY — use `namedRows`), plus the §5
    rows and the §4 reverse index needed to materialize their metadata. -/
structure LazyEnvParts where
  /-- `named := {}`; everything else populated (consts lazily). -/
  env : Env
  namedRows : Array NamedRow
  /-- Row index by name. -/
  rowIdx : Std.HashMap Ix.Name Nat
  nameRev : NameReverseIndex
  /-- The full serialized image; every window points into it. -/
  backing : ByteArray

/-- Parse a `NamedRow`'s metadata window into a full `Named`. -/
def NamedRow.materialize (row : NamedRow) (backing : ByteArray)
    (rev : NameReverseIndex) : Except String Named :=
  let getm : GetM Named := do
    let constMeta ← getConstantMetaIndexed rev
    let origTag ← getU8
    let original ← match origTag with
      | 0 => pure none
      | 1 => do
        let origAddr : Address ← Serialize.get
        let origMeta ← getConstantMetaIndexed rev
        pure (some (origAddr, origMeta))
      | x => throw s!"NamedRow.materialize: invalid original tag {x}"
    pure { addr := row.addr, constMeta, original, hints := row.hints }
  match getm.run { idx := row.metaOff, bytes := backing } with
  | .ok n _ => .ok n
  | .error e _ => .error e

/-- `frag == bytes[start : start + frag.size]`, no copy. -/
def fragMatchesAt (bytes : ByteArray) (start : Nat) (frag : ByteArray) : Bool := Id.run do
  if start + frag.size > bytes.size then return false
  for i in [0:frag.size] do
    if bytes[start + i]! != frag[i]! then return false
  return true

/-- Require the pure writer's bytes for the unit parsed since `start` to
    reproduce the input span exactly. Units are checked back-to-back from
    offset 0, so together with the trailing-bytes check the spans cover
    the whole image. -/
private def reserCheck (label : String) (start : Nat) (frag : ByteArray) : GetM Unit := do
  let st ← get
  if start + frag.size != st.idx then
    throw s!"serde gate ({label}): writer produced {frag.size} bytes for \
the {st.idx - start}-byte span at offset {start}"
  unless fragMatchesAt st.bytes start frag do
    throw s!"serde gate ({label}): writer bytes differ from input in span \
{start}..{st.idx}"

/-- Coarse progress marker from the pure loader (immediate stderr via
    `dbgTrace`; the CLI's stdout is block-buffered and useless for
    locating where a long load is). -/
@[inline] private def loadTrace (msg : String) : GetM Unit :=
  dbgTrace s!"[deEnvVerifiedLazy] {msg}" fun _ => pure ()

/-- Streaming counterpart of `deEnv` + `serEnv` roundtrip verification.
    See the section comment above. -/
def getEnvVerifiedLazy : GetM LazyEnvParts := do
  -- Header (verified as one span; the root's VALUE is verified against
  -- the recomputed merkle root after §2, exactly as `getEnv` does).
  let hdrStart := (← get).idx
  let tag ← getTag4
  if tag.flag != Env.FLAG then
    throw s!"Env.get: expected flag 0x{Env.FLAG.toNat.toDigits 16}, got 0x{tag.flag.toNat.toDigits 16}"
  if tag.size != Env.VERSION then
    throw s!"Env.get: expected .ixe format version {Env.VERSION}, got {tag.size} — recompile the artifact"
  let storedRoot : Address ← Serialize.get
  let mainTag ← getU8
  let main : Option Address ← match mainTag with
    | 0 => pure none
    | 1 => some <$> Serialize.get
    | x => throw s!"Env.get: invalid main tag {x} in bundle header — \
                    possibly a pre-bundle-format .ixe; recompile it"
  let numAssumptions := (← getTag0).size
  let mut assumptionArr : Array Address := #[]
  for _ in [:numAssumptions.toNat] do
    let addr : Address ← Serialize.get
    if let some prev := assumptionArr.back? then
      if !(compare prev addr).isLT then
        throw "Env.get: assumptions not strictly ascending"
    assumptionArr := assumptionArr.push addr
  reserCheck "header" hdrStart <| runPut do
    putTag4 ⟨Env.FLAG, Env.VERSION⟩
    Serialize.put storedRoot
    match main with
    | none => putU8 0
    | some addr => do putU8 1; Serialize.put addr
    putTag0 ⟨assumptionArr.size.toUInt64⟩
    for addr in assumptionArr do Serialize.put addr

  let mut env : Env := {
    main
    assumptions := assumptionArr.foldl (·.insert ·) {}
  }

  -- Section 1: Blobs (hash-verified; ascending order is the writer's
  -- sort contract, asserted here since no whole-image compare runs).
  let s1Start := (← get).idx
  let numBlobs := (← getTag0).size
  reserCheck "§1 count" s1Start <| runPut (putTag0 ⟨numBlobs⟩)
  loadTrace s!"header ok; §1 blobs: {numBlobs}"
  let mut prevBlobAddr : Option Address := none
  for _ in [:numBlobs.toNat] do
    let eStart := (← get).idx
    let addr ← Serialize.get
    let len := (← getTag0).size
    let bytes ← getBytes len.toNat
    if Address.blake3 bytes != addr then
      throw s!"Env.get: blob bytes hash mismatch for {reprStr (toString addr)}"
    if let some prev := prevBlobAddr then
      if !(compare prev addr).isLT then
        throw "Env.get: §1 blobs not in strictly ascending address order"
    prevBlobAddr := some addr
    env := { env with blobs := env.blobs.insert addr bytes }
    reserCheck "§1 blob" eStart <| runPut do
      Serialize.put addr
      putTag0 ⟨bytes.size.toUInt64⟩
      putBytes bytes

  -- Section 2: Consts. The body is parsed with the pure reader and
  -- re-serialized with the pure writer (the gate's core), then retained
  -- only as a zero-copy window.
  let s2Start := (← get).idx
  let numConsts := (← getTag0).size
  reserCheck "§2 count" s2Start <| runPut (putTag0 ⟨numConsts⟩)
  loadTrace s!"§2 consts: {numConsts}"
  let mut constOrder : Array Address := #[]
  let backing := (← get).bytes
  for _ in [:numConsts.toNat] do
    let eStart := (← get).idx
    let addr ← Serialize.get
    let len := (← getTag0).size
    let bodyStart := (← get).idx
    let bytes ← getBytes len.toNat
    if Address.blake3 bytes != addr then
      throw s!"Env.get: const bytes hash mismatch for {reprStr (toString addr)}"
    if let some prev := constOrder.back? then
      if !(compare prev addr).isLT then
        throw "Env.get: §2 constants not in strictly ascending address order"
    constOrder := constOrder.push addr
    if constOrder.size % 100000 == 0 then
      loadTrace s!"§2 at {constOrder.size}/{numConsts} (byte {eStart})"
    match deConstant bytes with
    | .ok constant =>
      reserCheck "§2 const" eStart <| runPut do
        Serialize.put addr
        putTag0 ⟨len⟩
        putBytes (serConstant constant)
      env := { env with
        consts := env.consts.insert addr
          (LazyConstant.ofSlice backing bodyStart len.toNat) }
    | .error e =>
      throw s!"Env.get: bad constant bytes for addr {reprStr (toString addr)}: {e}"

  if let some m := main then
    if !env.consts.contains m then
      throw s!"Env.get: main {reprStr (toString m)} not present in consts"

  -- Section 3: anon_hints (delta-coded §2 ranks; ascending by design).
  let s3Start := (← get).idx
  let numHints := (← getTag0).size
  reserCheck "§3 count" s3Start <| runPut (putTag0 ⟨numHints⟩)
  if numHints.toNat > constOrder.size then
    throw s!"Env.get: hint count {numHints} exceeds const count \
             {constOrder.size} — possibly a pre-compact-keys .ixe; \
             recompile it"
  let mut cursor : Nat := 0
  for _ in [:numHints.toNat] do
    let eStart := (← get).idx
    let delta := (← getTag0).size
    if delta == 0 then
      throw "Env.get: zero hint index delta (§3 must be strictly \
             ascending) — possibly a pre-compact-keys .ixe; recompile it"
    let idx := cursor + delta.toNat - 1
    let addr ← match constOrder[idx]? with
      | some a => pure a
      | none =>
        throw s!"Env.get: hint index {idx} out of range ({constOrder.size} \
                 consts) — possibly a pre-compact-keys .ixe; recompile it"
    let hints ← getFusedHint
    env := { env with anonHints := env.anonHints.insert addr hints }
    cursor := idx + 1
    reserCheck "§3 hint" eStart <| runPut do
      putTag0 ⟨delta⟩
      putFusedHint hints

  -- Section 4: Names. Order must equal the writer's topological sort of
  -- the parsed set (the whole-image compare used to pin this).
  let s4Start := (← get).idx
  let numNames := (← getTag0).size
  reserCheck "§4 count" s4Start <| runPut (putTag0 ⟨numNames⟩)
  loadTrace s!"§3 done; §4 names: {numNames}"
  let mut namesLookup : Std.HashMap Address Ix.Name := {}
  let mut nameRev : NameReverseIndex := #[]
  namesLookup := namesLookup.insert Ix.Name.mkAnon.getHash Ix.Name.mkAnon
  for _ in [:numNames.toNat] do
    let eStart := (← get).idx
    let addr ← Serialize.get
    let name ← Env.getNameComponent namesLookup
    nameRev := nameRev.push addr
    namesLookup := namesLookup.insert addr name
    env := { env with names := env.names.insert addr name }
    reserCheck "§4 name" eStart <| runPut do
      Serialize.put addr
      Env.putNameComponent name
  loadTrace "§4 parsed; topological order check"
  let sortedNames := Env.topologicalSortNames env.names
  if sortedNames.map (·.1) != nameRev then
    throw "serde gate (§4): name order differs from the writer's \
           topological sort of the same name set"

  -- §5 metadata re-serialization resolves name references through the
  -- §4 positions, exactly as the writer does.
  let fileNameIdx : NameIndex := nameRev.zipIdx.foldl
    (fun acc (addr, i) => acc.insert addr i.toUInt64) {}

  -- Section 5: Named — header fields eager, metadata parsed and
  -- writer-checked transiently, retained as a window.
  let s5Start := (← get).idx
  let numNamed := (← getTag0).size
  reserCheck "§5 count" s5Start <| runPut (putTag0 ⟨numNamed⟩)
  loadTrace s!"§5 named: {numNamed}"
  let mut namedRows : Array NamedRow := #[]
  let mut rowIdx : Std.HashMap Ix.Name Nat := {}
  let mut prevName : Option Ix.Name := none
  for _ in [:numNamed.toNat] do
    let eStart := (← get).idx
    let nameIdx := (← getTag0).size
    let nameAddr ← match nameRev[nameIdx.toNat]? with
      | some a => pure (a : Address)
      | none =>
        throw s!"Env.get: §5 name index {nameIdx} out of range \
                 ({nameRev.size} names) — possibly a pre-compact-keys .ixe; \
                 recompile it"
    let constRank := (← getTag0).size
    let constAddr ← match constOrder[constRank.toNat]? with
      | some a => pure a
      | none =>
        throw s!"Env.get: §5 constant index {constRank} out of range \
                 ({constOrder.size} consts) — possibly a pre-compact-keys \
                 .ixe; recompile it"
    let hints ← getFusedOptHint
    let metaLen := (← getTag0).size.toNat
    let stBefore ← get
    if stBefore.bytes.size - stBefore.idx < metaLen then
      throw s!"Env.get: §5 metadata blob needs {metaLen} bytes, have \
               {stBefore.bytes.size - stBefore.idx} — possibly a \
               pre-compact-keys .ixe; recompile it"
    let constMeta ← getConstantMetaIndexed nameRev
    let origTag ← getU8
    let original ← match origTag with
    | 0 => pure none
    | 1 => do
      let origAddr : Address ← Serialize.get
      let origMeta ← getConstantMetaIndexed nameRev
      pure (some (origAddr, origMeta))
    | x => throw s!"getEnv: Named.original: invalid tag {x}"
    let stAfter ← get
    if stAfter.idx - stBefore.idx != metaLen then
      throw s!"Env.get: §5 metadata blob length mismatch (header says \
               {metaLen}, parsed {stAfter.idx - stBefore.idx}) — possibly a \
               pre-normal-levels .ixe; recompile it"
    let name ← match namesLookup.get? nameAddr with
      | some name => pure name
      | none =>
        throw s!"getEnv: named entry references unknown name address {reprStr (toString nameAddr)}"
    if let some prev := prevName then
      if !(compare prev name).isLT then
        throw "serde gate (§5): named entries not in ascending name order"
    prevName := some name
    reserCheck "§5 named" eStart <| runPut do
      putTag0 ⟨nameIdx⟩
      putTag0 ⟨constRank⟩
      putFusedOptHint hints
      let blob := runPut do
        putConstantMetaIndexed constMeta fileNameIdx
        match original with
        | none => putU8 0
        | some (origAddr, origMeta) =>
          putU8 1
          Serialize.put origAddr
          putConstantMetaIndexed origMeta fileNameIdx
      putTag0 ⟨blob.size.toUInt64⟩
      putBytes blob
    rowIdx := rowIdx.insert name namedRows.size
    namedRows := namedRows.push
      { name, nameIdx, constRank, addr := constAddr, hints,
        metaOff := stBefore.idx, metaLen }
    if namedRows.size % 100000 == 0 then
      loadTrace s!"§5 at {namedRows.size}/{numNamed} (byte {eStart})"
    env := { env with addrToName := env.addrToName.insert constAddr name }

  -- Section 6: Comms.
  let s6Start := (← get).idx
  let numComms := (← getTag0).size
  reserCheck "§6 count" s6Start <| runPut (putTag0 ⟨numComms⟩)
  let mut prevCommAddr : Option Address := none
  for _ in [:numComms.toNat] do
    let eStart := (← get).idx
    let addr : Address ← Serialize.get
    let comm ← getComm
    if let some prev := prevCommAddr then
      if !(compare prev addr).isLT then
        throw "Env.get: §6 comms not in strictly ascending address order"
    prevCommAddr := some addr
    env := { env with comms := env.comms.insert addr comm }
    reserCheck "§6 comm" eStart <| runPut do
      Serialize.put addr
      putComm comm

  let computedRoot :=
    (Ix.Merkle.merkleRootCanonical constOrder).getD Ix.Merkle.zeroAddress
  if computedRoot != storedRoot then
    throw "Env.get: merkle root mismatch"

  let st ← get
  if st.idx != st.bytes.size then
    throw s!"Env.get: {st.bytes.size - st.idx} trailing bytes after final section"

  loadTrace "done"
  pure { env, namedRows, rowIdx, nameRev, backing }

/-- Run the streaming verified lazy load over an image. -/
def deEnvVerifiedLazy (bytes : ByteArray) : Except String LazyEnvParts :=
  match getEnvVerifiedLazy.run { idx := 0, bytes } with
  | .ok parts _ => .ok parts
  | .error e _ => .error e

/-- Materialize every §5 row into `env.named` — the eager `deEnv` view,
    for consumers not yet converted to per-row streaming. -/
def LazyEnvParts.materializeAllNamed (parts : LazyEnvParts) : Except String Env := do
  let mut env := parts.env
  for row in parts.namedRows do
    let named ← row.materialize parts.backing parts.nameRev
    env := { env with named := env.named.insert row.name named }
  return env

/-- Fully eager view: `materializeAllNamed` plus parsed-and-cached
    constants. Consumers that re-read constants repeatedly (the
    decompiler resolves its block `Muts` per projection) need the parse
    cached, or window re-parsing turns quadratic on big blocks. -/
def LazyEnvParts.materializeAll (parts : LazyEnvParts) : Except String Env := do
  let mut env ← parts.materializeAllNamed
  let mut consts : Std.HashMap Address LazyConstant := {}
  for (addr, lc) in env.consts do
    match lc.get with
    | .ok c => consts := consts.insert addr (LazyConstant.ofConstant c)
    | .error e =>
      throw s!"materializeAll: constant {reprStr (toString addr)}: {e}"
  return { env with consts }

/-- Serialize an Env to bytes. Fails when the env is not
    self-contained: §3 hints and §5 named entries are index-keyed on
    the wire, so keys outside the stored consts/names are
    unrepresentable (see `Env.putEnv`). -/
def serEnv (env : Env) : Except String ByteArray :=
  match (Env.putEnv env).run.run ByteArray.empty with
  | (.ok _, bytes) => .ok bytes
  | (.error e, _) => .error e

/-- Deserialize an Env from bytes (full metadata, pure Lean). -/
def deEnv (bytes : ByteArray) : Except String Env := runGet Env.getEnv bytes

/-- Compute section sizes for debugging.
    Returns (blobs, consts, anonHints, names, named, comms). -/
def envSectionSizes (env : Env) : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  -- Blobs section
  let blobsBytes := runPut do
    let blobs := env.blobs.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨blobs.size.toUInt64⟩
    for (addr, bytes) in blobs do
      Serialize.put addr
      putTag0 ⟨bytes.size.toUInt64⟩
      putBytes bytes

  -- Consts section
  let constsBytes := runPut do
    let consts := env.consts.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨consts.size.toUInt64⟩
    for (addr, lc) in consts do
      Serialize.put addr
      putBytes lc.rawBytes

  -- anon_hints section: delta-coded §2 ranks + fused hints. The sort
  -- is load-bearing (delta widths depend on it). Sizes assume a
  -- well-formed env — an out-of-consts key falls back to rank 0 here
  -- (diagnostics only; `serEnv` is where that is a hard error).
  let sortedConstAddrs := (env.consts.toList.toArray.map (·.1)).qsort
    fun a b => (compare a b).isLT
  let constIdx : Std.HashMap Address UInt64 := sortedConstAddrs.zipIdx.foldl
    (fun acc (addr, i) => acc.insert addr i.toUInt64) {}
  let hintsBytes := runPut do
    let hintPairs := env.anonHints.toList.toArray.qsort
      fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨hintPairs.size.toUInt64⟩
    let mut prevRank : UInt64 := 0
    for (addr, hints) in hintPairs do
      let rank := constIdx.get? addr |>.getD 0
      putTag0 ⟨rank + 1 - prevRank⟩
      putFusedHint hints
      prevRank := rank + 1

  -- Names section
  let namesBytes := runPut do
    let sortedNames := Env.topologicalSortNames env.names
    putTag0 ⟨sortedNames.size.toUInt64⟩
    for (addr, name) in sortedNames do
      Serialize.put addr
      Env.putNameComponent name

  -- Named section (name §4-index + const §2 rank + fused hint +
  -- length-prefixed metadata blob; absolute indices, so per-entry
  -- sizes are iteration-order independent — never delta-code here).
  -- Missing keys fall back to index 0 (diagnostics only).
  let namedBytes := runPut do
    let sortedNames := Env.topologicalSortNames env.names
    let nameIdx : NameIndex := sortedNames.zipIdx.foldl
      (fun acc ((addr, _), i) => acc.insert addr i.toUInt64) {}
    let named := env.named.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨named.size.toUInt64⟩
    for (name, namedEntry) in named do
      putTag0 ⟨nameIdx.get? name.getHash |>.getD 0⟩
      putTag0 ⟨constIdx.get? namedEntry.addr |>.getD 0⟩
      putFusedOptHint namedEntry.hints
      let blob := runPut do
        putConstantMetaIndexed namedEntry.constMeta nameIdx
        match namedEntry.original with
        | none => putU8 0
        | some (origAddr, origMeta) =>
          putU8 1
          Serialize.put origAddr
          putConstantMetaIndexed origMeta nameIdx
      putTag0 ⟨blob.size.toUInt64⟩
      putBytes blob

  -- Comms section
  let commsBytes := runPut do
    let comms := env.comms.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨comms.size.toUInt64⟩
    for (addr, comm) in comms do
      Serialize.put addr
      putComm comm

  ( blobsBytes.size, constsBytes.size, hintsBytes.size, namesBytes.size,
    namedBytes.size, commsBytes.size )

/-! ## Rust FFI Serialization -/

@[extern "rs_ser_env"]
opaque rsSerEnvFFI : @& RawEnv → ByteArray

/-- Serialize an Ixon.Env to bytes using Rust. -/
def rsSerEnv (env : Env) : ByteArray :=
  rsSerEnvFFI env.toRawEnv

@[extern "rs_de_env"]
opaque rsDeEnvFFI : @& ByteArray → Except String RawEnv

/-- Deserialize bytes to an Ixon.Env using Rust (full, eager materialization). -/
def rsDeEnv (bytes : ByteArray) : Except String Env :=
  return (← rsDeEnvFFI bytes).toEnv

/-! ### Lazy/anon deserialization (zero-copy `.ixe` load for the check path)

The Rust side (`rs_de_env_lazy`) parses the env once — reusing the proven
parser, so every metadata variant (e.g. `CallSite`) is handled — and returns:
constants as `(addr, offset, len)` windows into the buffer we pass in,
`name → addr`, per-`Defn` reducibility hints, and copied blobs. We then
reconstruct an `Env` whose constants are byte-window `LazyConstant`s over that
*same* buffer, so no constant body is copied across the FFI boundary and only
the checked closure is ever materialized. This is the Lean counterpart of the
Rust kernel's anon load (`get_anon`): lazy + metadata-light. (The `.ixe` is
held resident via `readBinFile` rather than mmap'd; see `get_anon_mmap` for the
mmap variant the native kernel uses.) -/

/-- A constant as an offset window `[offset, offset+len)` into the source buffer. -/
structure RawConstSlice where
  addr : Address
  offset : UInt64
  len : UInt64
  deriving Inhabited

/-- A named entry reduced to `name → addr`. -/
structure RawNamedLite where
  name : Ix.Name
  addr : Address
  /-- Per-name reducibility hints from the §5 entry header. -/
  hints : Option Lean.ReducibilityHints := none
  deriving Inhabited

/-- Metadata-light env returned by `rs_de_env_lazy`. Field order
    matters: the Rust builder addresses constructor slots 0-5. -/
structure RawEnvLazy where
  consts : Array RawConstSlice
  named : Array RawNamedLite
  blobs : Array RawBlob
  /-- Bundle root (`Env.main`) from the header. -/
  main : Option Address := none
  /-- Bundle trust boundary (`Env.assumptions`), in header order. -/
  assumptions : Array Address := #[]
  /-- Reducibility hints (`Env.anonHints`) from the hints section. -/
  anonHints : Array (Address × Lean.ReducibilityHints) := #[]
  deriving Inhabited

/-- Reconstruct an `Env` from a `RawEnvLazy` and the original buffer `buf`.
    Constants become `LazyConstant.ofSlice buf offset len` — zero-copy windows
    that share `buf`. `buf` MUST be the exact buffer passed to `rs_de_env_lazy`
    (offsets are relative to it). -/
def RawEnvLazy.toEnv (raw : RawEnvLazy) (buf : ByteArray) : Env := Id.run do
  let mut env : Env := { main := raw.main
                         assumptions := raw.assumptions.foldl (·.insert ·) {}
                         anonHints := raw.anonHints.foldl
                           (fun m (a, h) => m.insert a h) {} }
  for ⟨addr, offset, len⟩ in raw.consts do
    env := { env with
      consts := env.consts.insert addr
        (LazyConstant.ofSlice buf offset.toNat len.toNat) }
  for n in raw.named do
    env := env.registerName n.name
      { addr := n.addr, constMeta := .empty, hints := n.hints }
  for ⟨addr, bytes⟩ in raw.blobs do
    env := { env with blobs := env.blobs.insert addr bytes }
  return env

@[extern "rs_de_env_lazy"]
opaque rsDeEnvLazyFFI : @& ByteArray → Except String RawEnvLazy

/-- Lazy, zero-copy, metadata-light deserialization for the Aiur check path.
    Constants are byte-window `LazyConstant`s into `bytes` (parsed on demand,
    only for the checked closure); binder metadata is dropped, keeping just
    `name → addr` and per-`Defn` hints. The returned env borrows `bytes` — keep
    it reachable (the windows hold references, so it stays alive automatically).
    This is the Lean counterpart of the Rust kernel's anon load (`get_anon`):
    lazy + metadata-light, over a resident buffer. -/
def deEnvAnon (bytes : ByteArray) : Except String Env :=
  return (← rsDeEnvLazyFFI bytes).toEnv bytes

/-- Anonymous-only deserialization: keep blobs + consts + anon_hints
    and stop — the metadata sections (names/named/comms) are laid out
    after the hints and never touched. Returns a `RawEnv` whose
    `named`/`names`/`comms` arrays are empty. -/
@[extern "rs_de_env_anon"]
opaque rsDeEnvAnonFFI : @& ByteArray → Except String RawEnv

/-- Anonymous-only `rsDeEnv`. The returned `Env` has empty
    `named`/`names`/`comms` (and `addrToName`) and is suitable for
    anon-mode kernel workflows. -/
def rsDeEnvAnon (bytes : ByteArray) : Except String Env :=
  return (← rsDeEnvAnonFFI bytes).toEnv

/-! ### Env diff (`rs_diff_envs`)

The diff is computed in Rust (`ixon::diff::diff_envs`): both inputs are
parsed with the full reader (so `Named.original` participates), the
report below is marshaled back with names pre-rendered (`Name::pretty`)
and pre-sorted, addresses raw. Field order in these structures matters:
the Rust builders address constructor slots positionally (see
`crates/ffi/src/lean_ixon/diff.rs` and the `LeanIxonEnvDiff` layout in
`crates/ffi/src/lean.rs`). -/

/-- Per-env entity counts for the diff header. -/
structure EnvStats where
  consts : UInt64
  named : UInt64
  blobs : UInt64
  comms : UInt64
  deriving Inhabited, BEq

/-- One name present in both envs whose constant address changed.
    `fields` is never empty: `"kind"` marks a variant change and
    `"encoding"` an address change with no detected semantic field
    difference (table reorder / sharing-decision churn). `metaFields`
    is only populated in meta mode. `rippled` is the root-cause
    verdict: true iff the address change is fully explained by
    dependency re-addressing (re-classified under the old→new quotient
    of all changed rows, every residual label is
    `"encoding"`/`"block-siblings"`); `fields` stays the strict
    classification. -/
structure NamedDiff where
  name : String
  oldAddr : Address
  newAddr : Address
  oldKind : String
  newKind : String
  fields : Array String
  metaFields : Array String
  rippled : Bool
  deriving Inhabited, BEq

/-- Report produced by `rsDiffEnvs`. Set-difference lists are complete
    (display layers cap as needed); name-keyed arrays are sorted by
    pretty name, address arrays ascending. -/
structure EnvDiff where
  /-- `none` = unchanged, otherwise `(first env's main, second's)`. -/
  mainChanged : Option (Option Address × Option Address)
  assumptionsAdded : Array Address
  assumptionsRemoved : Array Address
  namedAdded : Array (String × Address)
  namedRemoved : Array (String × Address)
  namedChanged : Array NamedDiff
  /-- Same constant address, different metadata (meta mode only). -/
  namedMetaOnly : Array (String × Array String)
  commsAdded : Array Address
  commsRemoved : Array Address
  commsChanged : Array Address
  constsOnlyA : Array Address
  constsOnlyB : Array Address
  blobsOnlyA : Array Address
  blobsOnlyB : Array Address
  /-- Hint deltas for constants present in BOTH envs, rendered as
      `"opaque" | "abbrev" | "regular(N)" | "none"`. -/
  hintsChanged : Array (Address × String × String)
  statsA : EnvStats
  statsB : EnvStats
  deriving Inhabited, BEq

/-- True when no difference was found (ignores `statsA`/`statsB`,
    which are always populated). -/
def EnvDiff.isEmpty (d : EnvDiff) : Bool :=
  d.mainChanged.isNone
  && d.assumptionsAdded.isEmpty && d.assumptionsRemoved.isEmpty
  && d.namedAdded.isEmpty && d.namedRemoved.isEmpty
  && d.namedChanged.isEmpty && d.namedMetaOnly.isEmpty
  && d.commsAdded.isEmpty && d.commsRemoved.isEmpty && d.commsChanged.isEmpty
  && d.constsOnlyA.isEmpty && d.constsOnlyB.isEmpty
  && d.blobsOnlyA.isEmpty && d.blobsOnlyB.isEmpty
  && d.hintsChanged.isEmpty

@[extern "rs_diff_envs"]
opaque rsDiffEnvsFFI : @& ByteArray → @& ByteArray → Bool → Except String EnvDiff

/-- Diff two serialized envs in Rust. `compareMeta := false` (the
    default) compares only anonymous structure — name→addr changes with
    per-field classification, consts/blobs sets, comms,
    `main`/`assumptions`, and reducibility hints; `compareMeta := true`
    additionally compares `Named` metadata content (`namedMetaOnly` +
    `NamedDiff.metaFields`). -/
def rsDiffEnvs (a b : ByteArray) (compareMeta : Bool := false) :
    Except String EnvDiff :=
  rsDiffEnvsFFI a b compareMeta

@[extern "rs_diff_env_files"]
opaque rsDiffEnvFilesFFI : @& String → @& String → Bool → IO EnvDiff

/-- File-path variant of `rsDiffEnvs`: memory-maps both `.ixe` files
    (constant windows stay zero-copy mmap slices backed by the OS page
    cache) and diffs via the lazy reader in both modes — `ConstantMeta`
    is never bulk-materialized; meta mode streams both §5 named
    sections in a lockstep merge-join. The leanest diff path for
    multi-GB envs. Failures surface as `IO` errors. -/
def rsDiffEnvFiles (a b : String) (compareMeta : Bool := false) :
    IO EnvDiff :=
  rsDiffEnvFilesFFI a b compareMeta

/-- Byte-equality of two files: metadata length fast path, then an
    mmap memcmp — no heap reads. -/
@[extern "rs_ixe_files_equal"]
opaque rsIxeFilesEqual : @& String → @& String → IO Bool

/-! ### Env pack (`rs_pack_env`) -/

/-- Pack a value bundle in Rust: memory-map the env at `envPath`
    (lazy reader — metadata is never bulk-materialized), resolve
    `mainName` (displayed form) to its constant address, prune to the
    self-contained closure — `main` set, reached cut-points recorded in
    `assumptions`; display metadata carried to fixpoint by re-streaming
    §5 per round, or skipped entirely when `anon` is true (value
    closure + §3 hints only, the minimal typecheck/eval artifact) —
    validate (`Env::validate_closed`), and write the bundle to
    `outPath`. `assume` entries resolve as displayed names first, else
    as 64-hex constant addresses. Failures surface as `IO` errors.
    Arg order: envPath, mainName, assume, outPath, anon, verbose. -/
@[extern "rs_pack_env"]
opaque rsPackEnv : @& String → @& String → @& Array String → @& String →
  Bool → Bool → IO Unit

/-! ## Canonical merkle root over consts -/

@[extern "rs_env_merkle_root"]
opaque rsEnvMerkleRootFFI : @& RawEnv → ByteArray

/--
Compute the canonical merkle root over an Ixon env's `consts.keys()` via
the Rust implementation. Returns `none` for an empty const set, otherwise
the 32-byte root wrapped in `some`.

The same value is stored in the env's on-disk Tag4 header (see
`Env::put`/`Env::get` in `src/ix/ixon/serialize.rs`).
-/
def rsEnvMerkleRoot (env : Env) : Option Address :=
  let bytes := rsEnvMerkleRootFFI env.toRawEnv
  if bytes.size == 0 then none
  else if bytes.size == 32 then some ⟨bytes⟩
  else none

/--
Pure-Lean canonical merkle root over a `RawEnv`'s consts addresses.
Used as a cross-check against the Rust FFI: both should agree.
-/
def RawEnv.merkleRoot (env : RawEnv) : Option Address :=
  Ix.Merkle.merkleRootCanonical (env.consts.map (·.addr))

/-- Pure-Lean canonical merkle root for an `Env`. -/
def Env.merkleRoot (env : Env) : Option Address :=
  env.toRawEnv.merkleRoot

end Ixon

end
