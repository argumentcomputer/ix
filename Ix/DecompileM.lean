/-
  DecompileM: Decompilation from the Ixon format to Ix types.

  This module decompiles the Ixon format (with indirection tables, sharing,
  and per-expression metadata arenas) back to Ix expressions and constants.
  It is the inverse of the compilation pipeline.

  The output is Ix.Expr / Ix.ConstantInfo (with content hashes), NOT Lean.Expr.
  Conversion from Ix.Expr → Lean.Expr (decanonicalization) is a separate trivial step.
  This design enables cheap hash-based comparison of decompiled results.
-/

import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.Environment
import Ix.Common

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

/-- Decompilation error type. Variant order matches Rust DecompileError (tags 0–10). -/
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

instance : ToString DecompileError := ⟨DecompileError.toString⟩

/-! ## Context and State Structures -/

/-- Global decompilation environment (reader, immutable). -/
structure DecompileEnv where
  ixonEnv : Ixon.Env
  deriving Inhabited

/-- Per-block context for decompiling a single constant (reader, immutable per-block). -/
structure BlockCtx where
  refs : Array Address
  univs : Array Ixon.Univ
  sharing : Array Ixon.Expr
  mutCtx : Array Ix.Name       -- mutual context: index = Rec index
  univParams : Array Ix.Name   -- universe parameter names
  arena : ExprMetaArena
  deriving Inhabited

/-- Per-block mutable state (caches). -/
structure BlockState where
  exprCache : Std.HashMap (UInt64 × UInt64) Ix.Expr := {}
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

def BlobCursor.readTag0 (c : BlobCursor) : DecompileM (UInt64 × BlobCursor) := do
  let (head, c) ← c.readByte
  if head < 128 then pure (head.toUInt64, c)
  else
    let extraBytes := (head % 128).toNat + 1
    if c.pos + extraBytes > c.bytes.size then
      throw (.badConstantFormat "BlobCursor.readTag0: need more bytes")
    let mut val : UInt64 := 0
    let mut cur := c
    for i in [:extraBytes] do
      let (b, c') ← cur.readByte
      val := val ||| (b.toUInt64 <<< (i * 8).toUInt64)
      cur := c'
    pure (val, cur)

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
  let (startPos, c) ← c.readTag0
  let (stopPos, c) ← c.readTag0
  pure (⟨s, startPos.toNat, stopPos.toNat⟩, c)

def deserializeSourceInfo (c : BlobCursor) : DecompileM (Ix.SourceInfo × BlobCursor) := do
  let (tag, c) ← c.readByte
  match tag with
  | 0 =>
    let (leading, c) ← deserializeSubstring c
    let (leadingPos, c) ← c.readTag0
    let (trailing, c) ← deserializeSubstring c
    let (trailingPos, c) ← c.readTag0
    pure (.original leading leadingPos.toNat trailing trailingPos.toNat, c)
  | 1 =>
    let (start, c) ← c.readTag0
    let (stop, c) ← c.readTag0
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
    let (count, c) ← c.readTag0
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
    let (argCount, c) ← c.readTag0
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
    let (prCount, c) ← c.readTag0
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

/-- Decompile an expression to Ix.Expr with arena-based metadata. -/
partial def decompileExpr (e : Ixon.Expr) (arenaIdx : UInt64) : DecompileM Ix.Expr := do
  -- 1. Expand Share transparently
  match e with
  | .share idx =>
    let ctx ← getCtx
    match ctx.sharing[idx.toNat]? with
    | some sharedExpr => decompileExpr sharedExpr arenaIdx
    | none => throw (.invalidShareIndex idx ctx.sharing.size "")
  | _ =>

  -- Check cache
  let cacheKey := (hash e, arenaIdx)
  if let some cached := (← get).exprCache.get? cacheKey then return cached

  -- 2. Follow mdata chain
  let mut currentIdx := arenaIdx
  let mut mdataLayers : Array (Array (Ix.Name × Ix.DataValue)) := #[]
  let mut done := false
  while !done do
    match ← getArenaNode currentIdx with
    | .mdata kvmaps child =>
      for kvm in kvmaps do
        mdataLayers := mdataLayers.push (← decompileKVMap kvm)
      currentIdx := child
    | _ => done := true

  let node ← getArenaNode currentIdx

  -- 3. Match (arenaNode, ixonExpr) → Ix.Expr
  let result ← match node, e with
  | _, .var idx =>
    pure (applyMdata (Ix.Expr.mkBVar idx.toNat) mdataLayers)

  | _, .sort univIdx => do
    pure (applyMdata (Ix.Expr.mkSort (← getUniv univIdx)) mdataLayers)

  | _, .nat refIdx => do
    let blob ← getRef refIdx >>= lookupBlob
    pure (applyMdata (Ix.Expr.mkLit (.natVal (readNatBlob blob))) mdataLayers)

  | _, .str refIdx => do
    let blob ← getRef refIdx >>= lookupBlob
    let s ← readStringBlob blob
    pure (applyMdata (Ix.Expr.mkLit (.strVal s)) mdataLayers)

  -- Ref with arena metadata
  | .ref nameAddr, .ref _refIdx univIndices => do
    let name ← lookupNameAddr nameAddr
    let lvls ← decompileUnivIndices univIndices
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- Ref without arena metadata
  | _, .ref _refIdx _univIndices => do
    throw (.badConstantFormat "ref without arena metadata")

  -- Rec with arena metadata
  | .ref nameAddr, .recur recIdx univIndices => do
    let name ← match (← getEnv).ixonEnv.names.get? nameAddr with
      | some n => pure n
      | none => getMutName recIdx
    let lvls ← decompileUnivIndices univIndices
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- Rec without arena metadata
  | _, .recur recIdx univIndices => do
    let name ← getMutName recIdx
    let lvls ← decompileUnivIndices univIndices
    pure (applyMdata (Ix.Expr.mkConst name lvls) mdataLayers)

  -- App with arena metadata
  | .app funIdx argIdx, .app fn arg => do
    let fnExpr ← decompileExpr fn funIdx
    let argExpr ← decompileExpr arg argIdx
    pure (applyMdata (Ix.Expr.mkApp fnExpr argExpr) mdataLayers)

  | _, .app fn arg => do
    let fnExpr ← decompileExpr fn UInt64.MAX
    let argExpr ← decompileExpr arg UInt64.MAX
    pure (applyMdata (Ix.Expr.mkApp fnExpr argExpr) mdataLayers)

  -- Lam with arena metadata
  | .binder nameAddr info tyChild bodyChild, .lam ty body => do
    let binderName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExpr ty tyChild
    let bodyExpr ← decompileExpr body bodyChild
    pure (applyMdata (Ix.Expr.mkLam binderName tyExpr bodyExpr info) mdataLayers)

  | _, .lam ty body => do
    let tyExpr ← decompileExpr ty UInt64.MAX
    let bodyExpr ← decompileExpr body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkLam Ix.Name.mkAnon tyExpr bodyExpr .default) mdataLayers)

  -- ForallE with arena metadata
  | .binder nameAddr info tyChild bodyChild, .all ty body => do
    let binderName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExpr ty tyChild
    let bodyExpr ← decompileExpr body bodyChild
    pure (applyMdata (Ix.Expr.mkForallE binderName tyExpr bodyExpr info) mdataLayers)

  | _, .all ty body => do
    let tyExpr ← decompileExpr ty UInt64.MAX
    let bodyExpr ← decompileExpr body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkForallE Ix.Name.mkAnon tyExpr bodyExpr .default) mdataLayers)

  -- Let with arena metadata
  | .letBinder nameAddr tyChild valChild bodyChild, .letE nonDep ty val body => do
    let letName ← lookupNameAddrOrAnon nameAddr
    let tyExpr ← decompileExpr ty tyChild
    let valExpr ← decompileExpr val valChild
    let bodyExpr ← decompileExpr body bodyChild
    pure (applyMdata (Ix.Expr.mkLetE letName tyExpr valExpr bodyExpr nonDep) mdataLayers)

  | _, .letE nonDep ty val body => do
    let tyExpr ← decompileExpr ty UInt64.MAX
    let valExpr ← decompileExpr val UInt64.MAX
    let bodyExpr ← decompileExpr body UInt64.MAX
    pure (applyMdata (Ix.Expr.mkLetE Ix.Name.mkAnon tyExpr valExpr bodyExpr nonDep) mdataLayers)

  -- Prj with arena metadata
  | .prj structNameAddr child, .prj _typeRefIdx fieldIdx val => do
    let typeName ← lookupNameAddr structNameAddr
    let valExpr ← decompileExpr val child
    pure (applyMdata (Ix.Expr.mkProj typeName fieldIdx.toNat valExpr) mdataLayers)

  | _, .prj _typeRefIdx _fieldIdx _val => do
    throw (.badConstantFormat "prj without arena metadata")

  | _, .share _ => throw (.badConstantFormat "unexpected Share in decompileExpr")

  modify fun s => { s with exprCache := s.exprCache.insert cacheKey result }
  pure result

/-! ## Type Conversion Helpers -/

def toIxSafety : DefinitionSafety → Lean.DefinitionSafety
  | .unsaf => .unsafe | .safe => .safe | .part => .partial

def toIxQuotKind : QuotKind → Lean.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

/-! ## ConstantMeta Extraction Helpers -/

def getNameAddr : ConstantMeta → Option Address
  | .defn name .. => some name | .axio name .. => some name
  | .quot name .. => some name | .indc name .. => some name
  | .ctor name .. => some name | .recr name .. => some name
  | .empty => none

def getLvlAddrs : ConstantMeta → Array Address
  | .defn _ lvls .. => lvls | .axio _ lvls .. => lvls
  | .quot _ lvls .. => lvls | .indc _ lvls .. => lvls
  | .ctor _ lvls .. => lvls | .recr _ lvls .. => lvls
  | .empty => #[]

def getArenaAndTypeRoot : ConstantMeta → ExprMetaArena × UInt64
  | .defn _ _ _ _ _ arena typeRoot _ => (arena, typeRoot)
  | .axio _ _ arena typeRoot => (arena, typeRoot)
  | .quot _ _ arena typeRoot => (arena, typeRoot)
  | .indc _ _ _ _ _ arena typeRoot => (arena, typeRoot)
  | .ctor _ _ _ arena typeRoot => (arena, typeRoot)
  | .recr _ _ _ _ _ arena typeRoot _ => (arena, typeRoot)
  | .empty => ({}, 0)

def getAllAddrs : ConstantMeta → Array Address
  | .defn _ _ _ all .. => all | .indc _ _ _ all .. => all
  | .recr _ _ _ all .. => all | _ => #[]

def getCtxAddrs : ConstantMeta → Array Address
  | .defn _ _ _ _ ctx .. => ctx | .indc _ _ _ _ ctx .. => ctx
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

/-- Build a BlockCtx from a Constant. -/
def mkBlockCtx (cnst : Constant) (mutCtx : Array Ix.Name)
    (univParams : Array Ix.Name) (arena : ExprMetaArena) : BlockCtx :=
  { refs := cnst.refs, univs := cnst.univs, sharing := cnst.sharing, mutCtx, univParams, arena }

/-- Run with fresh block context and state. -/
def withFreshBlock (cnst : Constant) (mutCtx : Array Ix.Name)
    (univParams : Array Ix.Name) (arena : ExprMetaArena)
    (m : DecompileM α) : DecompileM α := do
  let env ← getEnv
  match DecompileM.run env (mkBlockCtx cnst mutCtx univParams arena) {} m with
  | .ok (a, _) => pure a
  | .error e => throw e

/-! ## Constant Decompilers → Ix.ConstantInfo -/

def decompileDefinition (d : Ixon.Definition) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let allNames ← decompileMetaAll cMeta name
  let mutCtx ← decompileMetaCtx cMeta
  let (hints, valueRoot) := match cMeta with
    | .defn _ _ hints _ _ _ _ valueRoot => (hints, valueRoot)
    | _ => (.opaque, (0 : UInt64))
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock cnst mutCtx univParams arena do
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
  withFreshBlock cnst #[] univParams arena do
    let typeExpr ← decompileExpr a.typ typeRoot
    pure (.axiomInfo { cnst := { name, levelParams := univParams, type := typeExpr }, isUnsafe := a.isUnsafe })

def decompileQuotient (q : Ixon.Quotient) (cnst : Constant) (cMeta : ConstantMeta)
    : DecompileM Ix.ConstantInfo := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock cnst #[] univParams arena do
    let typeExpr ← decompileExpr q.typ typeRoot
    pure (.quotInfo { cnst := { name, levelParams := univParams, type := typeExpr }, kind := toIxQuotKind q.kind })

def decompileConstructor (ctor : Ixon.Constructor) (cnst : Constant)
    (cMeta : ConstantMeta) (inductName : Ix.Name)
    : DecompileM Ix.ConstructorVal := do
  let name ← decompileMetaName cMeta
  let univParams ← decompileMetaLevels cMeta
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock cnst #[] univParams arena do
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
  let (ruleRoots, ruleAddrs) := match cMeta with
    | .recr _ _ rules _ _ _ _ ruleRoots => (ruleRoots, rules)
    | _ => (#[], #[])
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  withFreshBlock cnst mutCtx univParams arena do
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
  let ctorNameAddrs := match cMeta with
    | .indc _ _ ctors .. => ctors | _ => #[]
  let (arena, typeRoot) := getArenaAndTypeRoot cMeta
  let typeExpr ← withFreshBlock cnst mutCtx univParams arena do
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
    numNested := ind.nested.toNat, isRec := ind.recr,
    isUnsafe := ind.isUnsafe, isReflexive := ind.refl }
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
  match ixonEnv.consts.get? named.addr with
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
        match ixonEnv.consts.get? proj.block with
        | some { info := .muts mutuals, sharing, refs, univs } =>
          decompileProjection cnst named.constMeta mutuals sharing refs univs
        | _ => pure #[]
      | .iPrj proj =>
        match ixonEnv.consts.get? proj.block with
        | some { info := .muts mutuals, sharing, refs, univs } =>
          decompileProjection cnst named.constMeta mutuals sharing refs univs
        | _ => pure #[]
      | .rPrj proj =>
        match ixonEnv.consts.get? proj.block with
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

/-- Decompile all constants in parallel using chunked pure Tasks. Returns Ix types. -/
def decompileAllParallel (ixonEnv : Ixon.Env) (numWorkers : Nat := 32)
    : Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) := Id.run do
  let env : DecompileEnv := { ixonEnv }
  -- Collect all named entries into an array
  let mut allEntries : Array (Ix.Name × Ixon.Named) := #[]
  for (ixName, named) in ixonEnv.named do
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

/-! ## Rust FFI Decompilation -/

@[extern "rs_decompile_env"]
opaque rsDecompileEnvFFI : @& Ixon.RawEnv → Except DecompileError (Array (Ix.Name × Ix.ConstantInfo))

/-- Decompile an Ixon.Env to Ix.ConstantInfo using Rust. -/
def rsDecompileEnv (env : Ixon.Env) : Except DecompileError (Std.HashMap Ix.Name Ix.ConstantInfo) := do
  let arr ← rsDecompileEnvFFI env.toRawEnv
  return arr.foldl (init := {}) fun m (name, info) => m.insert name info

end Ix.DecompileM
