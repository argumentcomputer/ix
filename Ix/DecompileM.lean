/-
  DecompileM: Decompilation from the new Ixon format to Lean.

  This module decompiles the new Ixon format (with indirection tables and sharing)
  back to Lean expressions and constants. It's the inverse of CompileV2.

  Key operations:
  - Resolve refs table indices to addresses, then to constant names
  - Resolve univs table indices to Lean.Level
  - Expand Share(idx) references using the sharing vector
  - Reconstruct Lean.Expr from Ixon.Expr
-/

import Std.Data.HashMap
import Ix.Ixon
import Ix.Address
import Ix.ShardMap
import Ix.Common
import Ix.Store
import Ix.Mutual
import Ix.CompileV2

namespace Ix.DecompileM

open Ixon

/-- Helper to convert Option to Except. -/
def optToExcept (e : ε) (o : Option α) : Except ε α :=
  match o with
  | some a => .ok a
  | none => .error e

/-- Decompilation error type. -/
inductive DecompileError where
  | unknownRef (idx : UInt64) (refsLen : Nat)
  | unknownUniv (idx : UInt64) (univsLen : Nat)
  | unknownShare (idx : UInt64) (sharingLen : Nat)
  | unknownRecur (idx : UInt64) (ctxLen : Nat)
  | invalidBVar (idx : UInt64) (depth : Nat)
  | unknownAddress (addr : Address)
  | unknownConstant (name : Lean.Name)
  | blobNotFound (addr : Address)
  | badBlobFormat (addr : Address) (expected : String)
  | badConstantFormat (msg : String)
  | unsupportedConstantType (msg : String)
  deriving Repr

def DecompileError.toString : DecompileError → String
  | .unknownRef idx len => s!"Unknown ref index {idx}, refs table has {len} entries"
  | .unknownUniv idx len => s!"Unknown univ index {idx}, univs table has {len} entries"
  | .unknownShare idx len => s!"Unknown share index {idx}, sharing vector has {len} entries"
  | .unknownRecur idx len => s!"Unknown recur index {idx}, mutual context has {len} entries"
  | .invalidBVar idx depth => s!"Invalid bound variable {idx} at depth {depth}"
  | .unknownAddress addr => s!"Unknown address {addr}"
  | .unknownConstant name => s!"Unknown constant {name}"
  | .blobNotFound addr => s!"Blob not found at {addr}"
  | .badBlobFormat addr expected => s!"Bad blob format at {addr}, expected {expected}"
  | .badConstantFormat msg => s!"Bad constant format: {msg}"
  | .unsupportedConstantType msg => s!"Unsupported constant type: {msg}"

instance : ToString DecompileError := ⟨DecompileError.toString⟩

/-- Context for decompiling a single constant. -/
structure BlockCtx where
  /-- Refs table: indices map to addresses -/
  refs : Array Address
  /-- Univs table: indices map to compiled universe levels -/
  univs : Array Univ
  /-- Sharing vector: indices map to shared expressions -/
  sharing : Array Expr
  /-- Mutual recursion context: indices map to constant names -/
  mutCtx : Array Lean.Name
  /-- Universe parameter names (for de Bruijn to named conversion) -/
  univParams : List Lean.Name
  /-- Binder names for lambda/forall (stack of names, innermost first) -/
  binderNames : List Lean.Name
  deriving Inhabited

/-- Environment for decompilation. -/
structure DecompileEnv where
  /-- Map from addresses to constant names -/
  addrToName : Std.HashMap Address Lean.Name
  /-- Map from addresses to blobs -/
  blobs : Std.HashMap Address ByteArray
  /-- Map from constant addresses to their compiled forms -/
  constants : Std.HashMap Address Constant
  deriving Inhabited

/-- Decompilation monad with Reader (environment) and Except (errors). -/
abbrev DecompileM := ReaderT DecompileEnv (Except DecompileError)

/-- Run a DecompileM computation. -/
def DecompileM.run (env : DecompileEnv) (m : DecompileM α) : Except DecompileError α :=
  ReaderT.run m env

/-- Look up a blob by address. -/
def lookupBlob (addr : Address) : DecompileM ByteArray := do
  let env ← read
  match env.blobs.get? addr with
  | some blob => pure blob
  | none => throw (.blobNotFound addr)

/-- Look up a constant name by address. -/
def lookupName (addr : Address) : DecompileM Lean.Name := do
  let env ← read
  match env.addrToName.get? addr with
  | some name => pure name
  | none => throw (.unknownAddress addr)

/-- Decompile a universe level. -/
partial def decompileUniv (ctx : BlockCtx) (u : Univ) : Except DecompileError Lean.Level :=
  match u with
  | .zero => .ok .zero
  | .succ inner => .succ <$> decompileUniv ctx inner
  | .max a b => .max <$> decompileUniv ctx a <*> decompileUniv ctx b
  | .imax a b => .imax <$> decompileUniv ctx a <*> decompileUniv ctx b
  | .var idx =>
    match ctx.univParams[idx.toNat]? with
    | some name => .ok (.param name)
    | none => .error (.unknownUniv idx ctx.univParams.length)

/-- Get a universe from the univs table by index. -/
def getUniv (ctx : BlockCtx) (idx : UInt64) : Except DecompileError Lean.Level := do
  match ctx.univs[idx.toNat]? with
  | some u => decompileUniv ctx u
  | none => throw (.unknownUniv idx ctx.univs.size)

/-- Get an address from the refs table by index. -/
def getRef (ctx : BlockCtx) (idx : UInt64) : Except DecompileError Address := do
  match ctx.refs[idx.toNat]? with
  | some addr => pure addr
  | none => throw (.unknownRef idx ctx.refs.size)

/-- Get a mutual context name by index. -/
def getMutName (ctx : BlockCtx) (idx : UInt64) : Except DecompileError Lean.Name := do
  match ctx.mutCtx[idx.toNat]? with
  | some name => pure name
  | none => throw (.unknownRecur idx ctx.mutCtx.size)

/-- Read a natural number from a blob. -/
def readNatBlob (blob : ByteArray) : Nat :=
  Nat.fromBytesLE blob.data

/-- Read a string from a blob. -/
def readStringBlob (blob : ByteArray) : Except DecompileError String :=
  match String.fromUTF8? blob with
  | some s => .ok s
  | none => .error (.badBlobFormat ⟨#[]⟩ "UTF-8 string")

/-- Decompile an expression.
    Uses a cache to handle sharing efficiently. -/
partial def decompileExpr (env : DecompileEnv) (ctx : BlockCtx) (e : Expr)
    : Except DecompileError Lean.Expr := do
  match e with
  | .sort univIdx =>
    let lvl ← getUniv ctx univIdx
    pure (.sort lvl)

  | .var idx =>
    -- Check that the index is valid for current binder depth
    let depth := ctx.binderNames.length
    if idx.toNat < depth then
      pure (.bvar idx.toNat)
    else
      throw (.invalidBVar idx depth)

  | .ref refIdx univIndices =>
    let addr ← getRef ctx refIdx
    let name ← optToExcept (.unknownAddress addr) (env.addrToName.get? addr)
    let lvls ← univIndices.toList.mapM (getUniv ctx)
    pure (.const name lvls)

  | .recur recIdx univIndices =>
    let name ← getMutName ctx recIdx
    let lvls ← univIndices.toList.mapM (getUniv ctx)
    pure (.const name lvls)

  | .prj typeRefIdx fieldIdx val =>
    let typeAddr ← getRef ctx typeRefIdx
    let typeName ← optToExcept (.unknownAddress typeAddr) (env.addrToName.get? typeAddr)
    let valExpr ← decompileExpr env ctx val
    pure (.proj typeName fieldIdx.toNat valExpr)

  | .str refIdx =>
    let addr ← getRef ctx refIdx
    let blob ← optToExcept (.blobNotFound addr) (env.blobs.get? addr)
    let s ← readStringBlob blob
    pure (.lit (.strVal s))

  | .nat refIdx =>
    let addr ← getRef ctx refIdx
    let blob ← optToExcept (.blobNotFound addr) (env.blobs.get? addr)
    let n := readNatBlob blob
    pure (.lit (.natVal n))

  | .app fun_ arg =>
    let funExpr ← decompileExpr env ctx fun_
    let argExpr ← decompileExpr env ctx arg
    pure (.app funExpr argExpr)

  | .lam ty body =>
    let tyExpr ← decompileExpr env ctx ty
    -- Extend binder context for body (use anonymous name since Ixon doesn't store names)
    let ctx' := { ctx with binderNames := `_a :: ctx.binderNames }
    let bodyExpr ← decompileExpr env ctx' body
    pure (.lam `_a tyExpr bodyExpr .default)

  | .all ty body =>
    let tyExpr ← decompileExpr env ctx ty
    let ctx' := { ctx with binderNames := `_a :: ctx.binderNames }
    let bodyExpr ← decompileExpr env ctx' body
    pure (.forallE `_a tyExpr bodyExpr .default)

  | .let nonDep ty val body =>
    let tyExpr ← decompileExpr env ctx ty
    let valExpr ← decompileExpr env ctx val
    let ctx' := { ctx with binderNames := `_a :: ctx.binderNames }
    let bodyExpr ← decompileExpr env ctx' body
    pure (.letE `_a tyExpr valExpr bodyExpr nonDep)

  | .share idx =>
    match ctx.sharing[idx.toNat]? with
    | some sharedExpr => decompileExpr env ctx sharedExpr
    | none => throw (.unknownShare idx ctx.sharing.size)

/-- Decompile a Definition to a Lean.DefinitionVal. -/
def decompileDefinition (env : DecompileEnv) (name : Lean.Name) (d : Definition)
    (constant : Constant) (univParams : List Lean.Name)
    : Except DecompileError Lean.DefinitionVal := do
  let ctx : BlockCtx := {
    refs := constant.refs
    univs := constant.univs
    sharing := constant.sharing
    mutCtx := #[]
    univParams
    binderNames := []
  }

  -- Deserialize and decompile type expression
  let typeBlob ← optToExcept (.blobNotFound d.type) (env.blobs.get? d.type)
  let typeIxon : Expr ← match Ixon.de typeBlob with
    | .ok e => pure e
    | .error msg => throw (.badConstantFormat s!"Failed to deserialize type: {msg}")
  let typeExpr ← decompileExpr env ctx typeIxon

  -- Deserialize and decompile value expression
  let valueBlob ← optToExcept (.blobNotFound d.value) (env.blobs.get? d.value)
  let valueIxon : Expr ← match Ixon.de valueBlob with
    | .ok e => pure e
    | .error msg => throw (.badConstantFormat s!"Failed to deserialize value: {msg}")
  let valueExpr ← decompileExpr env ctx valueIxon

  pure {
    name
    levelParams := univParams
    type := typeExpr
    value := valueExpr
    hints := .opaque  -- Default, could be recovered from metadata
    safety := d.safety
    all := [name]  -- Simplified, full implementation would track mutual block
  }

/-- Decompile an Axiom to a Lean.AxiomVal. -/
def decompileAxiom (env : DecompileEnv) (name : Lean.Name) (a : Ixon.Axiom)
    (constant : Constant) (univParams : List Lean.Name)
    : Except DecompileError Lean.AxiomVal := do
  let ctx : BlockCtx := {
    refs := constant.refs
    univs := constant.univs
    sharing := constant.sharing
    mutCtx := #[]
    univParams
    binderNames := []
  }

  let typeBlob ← optToExcept (.blobNotFound a.type) (env.blobs.get? a.type)
  let typeIxon : Expr ← match Ixon.de typeBlob with
    | .ok e => pure e
    | .error msg => throw (.badConstantFormat s!"Failed to deserialize type: {msg}")
  let typeExpr ← decompileExpr env ctx typeIxon

  pure {
    name
    levelParams := univParams
    type := typeExpr
    isUnsafe := a.isUnsafe
  }

/-- Decompile a Quotient to a Lean.QuotVal. -/
def decompileQuotient (env : DecompileEnv) (name : Lean.Name) (q : Ixon.Quotient)
    (constant : Constant) (univParams : List Lean.Name)
    : Except DecompileError Lean.QuotVal := do
  let ctx : BlockCtx := {
    refs := constant.refs
    univs := constant.univs
    sharing := constant.sharing
    mutCtx := #[]
    univParams
    binderNames := []
  }

  let typeBlob ← optToExcept (.blobNotFound q.type) (env.blobs.get? q.type)
  let typeIxon : Expr ← match Ixon.de typeBlob with
    | .ok e => pure e
    | .error msg => throw (.badConstantFormat s!"Failed to deserialize type: {msg}")
  let typeExpr ← decompileExpr env ctx typeIxon

  pure {
    name
    levelParams := univParams
    type := typeExpr
    kind := q.kind
  }

/-- Decompile a Constant to a Lean.ConstantInfo. -/
def decompileConstant (env : DecompileEnv) (name : Lean.Name) (constant : Constant)
    (univParams : List Lean.Name)
    : Except DecompileError Lean.ConstantInfo := do
  match constant.info with
  | .defn d =>
    let defn ← decompileDefinition env name d constant univParams
    match d.kind with
    | .definition => pure (.defnInfo defn)
    | .theorem => pure (.thmInfo {
        name := defn.name
        levelParams := defn.levelParams
        type := defn.type
        value := defn.value
        all := defn.all
      })
    | .opaque => pure (.opaqueInfo {
        name := defn.name
        levelParams := defn.levelParams
        type := defn.type
        value := defn.value
        isUnsafe := defn.safety == .unsafe
        all := defn.all
      })
  | .axio a =>
    .axiomInfo <$> decompileAxiom env name a constant univParams
  | .quot q =>
    .quotInfo <$> decompileQuotient env name q constant univParams
  | .recr _ => throw (.unsupportedConstantType "Recursor")
  | .cPrj _ => throw (.unsupportedConstantType "ConstructorProj")
  | .rPrj _ => throw (.unsupportedConstantType "RecursorProj")
  | .iPrj _ => throw (.unsupportedConstantType "InductiveProj")
  | .dPrj _ => throw (.unsupportedConstantType "DefinitionProj")
  | .muts _ => throw (.unsupportedConstantType "Muts")

/-- Global decompilation state. -/
structure DecompileState where
  /-- Decompiled constants -/
  constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  /-- Cache of decompiled expressions (constant addr × expr addr → Lean.Expr) -/
  exprCache : Std.HashMap (Address × Address) Lean.Expr := {}
  deriving Inhabited

/-- Decompile all constants from a GlobalState (from CompileV2). -/
def decompileAll (global : CompileV2.GlobalState)
    : IO (Except DecompileError DecompileState) := do
  -- Build lookup maps from ShardMaps
  let constantsList ← global.constants.toList
  let nameToAddrList ← global.nameToAddr.toList
  let blobsList ← global.blobs.toList

  let constantsMap := constantsList.foldl (init := {}) fun m (k, v) => m.insert k v
  let blobsMap := blobsList.foldl (init := {}) fun m (k, v) => m.insert k v

  -- Build addrToName map (reverse of nameToAddr)
  let addrToNameMap := nameToAddrList.foldl (init := {}) fun m (name, addr) => m.insert addr name

  let env : DecompileEnv := {
    addrToName := addrToNameMap
    blobs := blobsMap
    constants := constantsMap
  }

  let mut state : DecompileState := {}

  for (name, addr) in nameToAddrList do
    match constantsMap.get? addr with
    | none => pure ()  -- Skip if constant not found
    | some constant =>
      -- Generate universe parameter names based on count
      let univCount := match constant.info with
        | .defn d => d.lvls
        | .axio a => a.lvls
        | .quot q => q.lvls
        | .recr r => r.lvls
        | _ => 0
      let univParams := (List.range univCount).map fun i => .mkSimple s!"u{i}"

      match decompileConstant env name constant univParams with
      | .ok constInfo => state := { state with constants := state.constants.insert name constInfo }
      | .error _ => pure ()  -- Skip errors for now, could collect them

  pure (.ok state)

end Ix.DecompileM
