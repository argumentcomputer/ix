/-
  Kernel Convert: Ixon.Env → Kernel.Env conversion.

  Two modes:
  - `convert` produces `Kernel.Env .meta` with full names and binder info
  - `convertAnon` produces `Kernel.Env .anon` with all metadata as ()

  Much simpler than DecompileM: no Blake3 hash computation, no mdata reconstruction.
-/
import Ix.Kernel.Types
import Ix.Ixon

namespace Ix.Kernel.Convert

open Ix (Name)
open Ixon (Constant ConstantInfo ConstantMeta MutConst Named)

/-! ## Universe conversion -/

partial def convertUniv (m : MetaMode) (levelParamNames : Array (MetaField m Ix.Name) := #[])
    : Ixon.Univ → Level m
  | .zero => .zero
  | .succ l => .succ (convertUniv m levelParamNames l)
  | .max l₁ l₂ => .max (convertUniv m levelParamNames l₁) (convertUniv m levelParamNames l₂)
  | .imax l₁ l₂ => .imax (convertUniv m levelParamNames l₁) (convertUniv m levelParamNames l₂)
  | .var idx =>
    let name := if h : idx.toNat < levelParamNames.size then levelParamNames[idx.toNat] else default
    .param idx.toNat name

/-! ## Expression conversion monad -/

structure ConvertEnv (m : MetaMode) where
  sharing : Array Ixon.Expr
  refs : Array Address
  univs : Array Ixon.Univ
  blobs : Std.HashMap Address ByteArray
  recurAddrs : Array Address := #[]
  arena : Ixon.ExprMetaArena := {}
  names : Std.HashMap Address Ix.Name := {}
  levelParamNames : Array (MetaField m Ix.Name) := #[]
  binderNames : List (MetaField m Ix.Name) := []

structure ConvertState (m : MetaMode) where
  exprCache : Std.HashMap (UInt64 × UInt64) (Expr m) := {}

inductive ConvertError where
  | refOutOfBounds (refIdx : UInt64) (refsSize : Nat)
  | recurOutOfBounds (recIdx : UInt64) (recurAddrsSize : Nat)
  | prjRefOutOfBounds (typeRefIdx : UInt64) (refsSize : Nat)
  | missingMemberAddr (memberIdx : Nat) (numMembers : Nat)
  | unresolvableCtxAddr (addr : Address)
  | missingName (nameAddr : Address)

instance : ToString ConvertError where
  toString
    | .refOutOfBounds idx sz => s!"ref index {idx} out of bounds (refs.size={sz})"
    | .recurOutOfBounds idx sz => s!"recur index {idx} out of bounds (recurAddrs.size={sz})"
    | .prjRefOutOfBounds idx sz => s!"proj type ref index {idx} out of bounds (refs.size={sz})"
    | .missingMemberAddr idx n => s!"no address for member {idx} (numMembers={n})"
    | .unresolvableCtxAddr addr => s!"unresolvable ctx address {addr}"
    | .missingName addr => s!"missing name for address {addr}"

abbrev ConvertM (m : MetaMode) := ReaderT (ConvertEnv m) (StateT (ConvertState m) (ExceptT ConvertError Id))

def ConvertState.init (_ : ConvertEnv m) : ConvertState m := {}

def ConvertM.run (env : ConvertEnv m) (x : ConvertM m α) : Except ConvertError α :=
  match x env |>.run (ConvertState.init env) with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- Run a ConvertM computation with existing state, return result and final state. -/
def ConvertM.runWith (env : ConvertEnv m) (st : ConvertState m) (x : ConvertM m α)
    : Except ConvertError (α × ConvertState m) :=
  x env |>.run st

/-! ## Expression conversion -/

def resolveUnivs (m : MetaMode) (idxs : Array UInt64) : ConvertM m (Array (Level m)) := do
  let ctx ← read
  return idxs.map fun i =>
    if h : i.toNat < ctx.univs.size
    then convertUniv m ctx.levelParamNames ctx.univs[i.toNat]
    else .zero

def decodeBlobNat (bytes : ByteArray) : Nat := Id.run do
  let mut acc := 0
  for i in [:bytes.size] do
    acc := acc + bytes[i]!.toNat * 256 ^ i
  return acc

def decodeBlobStr (bytes : ByteArray) : String :=
  String.fromUTF8! bytes

/-- Look up an arena node by index, automatically unwrapping `.mdata` wrappers. -/
partial def getArenaNode (idx : Option UInt64) : ConvertM m (Option Ixon.ExprMetaData) := do
  match idx with
  | none => return none
  | some i =>
    let ctx ← read
    if h : i.toNat < ctx.arena.nodes.size
    then match ctx.arena.nodes[i.toNat] with
      | .mdata _ child => getArenaNode (some child)
      | node => return some node
    else return none

def mkMetaName (m : MetaMode) (name? : Option Ix.Name) : MetaField m Ix.Name :=
  match m with
  | .meta => name?.getD default
  | .anon => ()

/-- Resolve a name hash Address to a MetaField name via the names table. -/
def resolveName (nameAddr : Address) : ConvertM m (MetaField m Ix.Name) := do
  let ctx ← read
  match ctx.names.get? nameAddr with
  | some name => return (mkMetaName m (some name))
  | none => throw (.missingName nameAddr)

partial def convertExpr (m : MetaMode) (expr : Ixon.Expr) (metaIdx : Option UInt64 := none)
    : ConvertM m (Expr m) := do
  -- 1. Expand share transparently, passing arena index through (same as DecompileM)
  match expr with
  | .share idx =>
    let ctx ← read
    if h : idx.toNat < ctx.sharing.size then
      convertExpr m ctx.sharing[idx.toNat] metaIdx
    else return default
  | _ =>

  -- 1b. Handle .var before cache (binder names are context-dependent)
  if let .var idx := expr then
    let name := match (← read).binderNames[idx.toNat]? with
      | some n => n | none => default
    return (.bvar idx.toNat name)

  -- 2. Check cache (keyed on expression hash + arena index)
  let cacheKey := (hash expr, metaIdx.getD UInt64.MAX)
  if let some cached := (← get).exprCache.get? cacheKey then return cached

  -- 3. Resolve arena node
  let node ← getArenaNode metaIdx

  -- 4. Convert expression
  let result ← match expr with
  | .sort idx => do
    let ctx ← read
    if h : idx.toNat < ctx.univs.size
    then pure (.sort (convertUniv m ctx.levelParamNames ctx.univs[idx.toNat]))
    else pure (.sort .zero)
  | .var _ => pure default  -- unreachable, handled above
  | .ref refIdx univIdxs => do
    let ctx ← read
    let levels ← resolveUnivs m univIdxs
    let addr ← match ctx.refs[refIdx.toNat]? with
      | some a => pure a
      | none => throw (.refOutOfBounds refIdx ctx.refs.size)
    let name ← match node with
      | some (.ref nameAddr) => resolveName nameAddr
      | _ => pure default
    pure (.const addr levels name)
  | .recur recIdx univIdxs => do
    let ctx ← read
    let levels ← resolveUnivs m univIdxs
    let addr ← match ctx.recurAddrs[recIdx.toNat]? with
      | some a => pure a
      | none => throw (.recurOutOfBounds recIdx ctx.recurAddrs.size)
    let name ← match node with
      | some (.ref nameAddr) => resolveName nameAddr
      | _ => pure default
    pure (.const addr levels name)
  | .prj typeRefIdx fieldIdx struct => do
    let ctx ← read
    let typeAddr ← match ctx.refs[typeRefIdx.toNat]? with
      | some a => pure a
      | none => throw (.prjRefOutOfBounds typeRefIdx ctx.refs.size)
    let (structChild, typeName) ← match node with
      | some (.prj structNameAddr child) => do
        let n ← resolveName structNameAddr
        pure (some child, n)
      | _ => pure (none, default)
    let s ← convertExpr m struct structChild
    pure (.proj typeAddr fieldIdx.toNat s typeName)
  | .str blobRefIdx => do
    let ctx ← read
    if h : blobRefIdx.toNat < ctx.refs.size then
      let blobAddr := ctx.refs[blobRefIdx.toNat]
      match ctx.blobs.get? blobAddr with
      | some bytes => pure (.lit (.strVal (decodeBlobStr bytes)))
      | none => pure (.lit (.strVal ""))
    else pure (.lit (.strVal ""))
  | .nat blobRefIdx => do
    let ctx ← read
    if h : blobRefIdx.toNat < ctx.refs.size then
      let blobAddr := ctx.refs[blobRefIdx.toNat]
      match ctx.blobs.get? blobAddr with
      | some bytes => pure (.lit (.natVal (decodeBlobNat bytes)))
      | none => pure (.lit (.natVal 0))
    else pure (.lit (.natVal 0))
  | .app fn arg => do
    let (fnChild, argChild) := match node with
      | some (.app f a) => (some f, some a)
      | _ => (none, none)
    let f ← convertExpr m fn fnChild
    let a ← convertExpr m arg argChild
    pure (.app f a)
  | .lam ty body => do
    let (name, bi, tyChild, bodyChild) ← match node with
      | some (.binder nameAddr info tyC bodyC) => do
        let n ← resolveName nameAddr
        let i : MetaField m Lean.BinderInfo := match m with | .meta => info | .anon => ()
        pure (n, i, some tyC, some bodyC)
      | _ => pure (default, default, none, none)
    let t ← convertExpr m ty tyChild
    let b ← withReader (fun env => { env with binderNames := name :: env.binderNames })
              (convertExpr m body bodyChild)
    pure (.lam t b name bi)
  | .all ty body => do
    let (name, bi, tyChild, bodyChild) ← match node with
      | some (.binder nameAddr info tyC bodyC) => do
        let n ← resolveName nameAddr
        let i : MetaField m Lean.BinderInfo := match m with | .meta => info | .anon => ()
        pure (n, i, some tyC, some bodyC)
      | _ => pure (default, default, none, none)
    let t ← convertExpr m ty tyChild
    let b ← withReader (fun env => { env with binderNames := name :: env.binderNames })
              (convertExpr m body bodyChild)
    pure (.forallE t b name bi)
  | .letE _nonDep ty val body => do
    let (name, tyChild, valChild, bodyChild) ← match node with
      | some (.letBinder nameAddr tyC valC bodyC) => do
        let n ← resolveName nameAddr
        pure (n, some tyC, some valC, some bodyC)
      | _ => pure (default, none, none, none)
    let t ← convertExpr m ty tyChild
    let v ← convertExpr m val valChild
    let b ← withReader (fun env => { env with binderNames := name :: env.binderNames })
              (convertExpr m body bodyChild)
    pure (.letE t v b name)
  | .share _ => pure default  -- unreachable, handled above

  -- 5. Cache and return
  modify fun s => { s with exprCache := s.exprCache.insert cacheKey result }
  pure result

/-! ## Enum conversions -/

def convertHints : Lean.ReducibilityHints → ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h

def convertSafety : Ix.DefinitionSafety → DefinitionSafety
  | .unsaf => .unsafe
  | .safe => .safe
  | .part => .partial

def convertQuotKind : Ix.QuotKind → QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-! ## Constant conversion helpers -/

def mkConvertEnv (m : MetaMode) (c : Constant) (blobs : Std.HashMap Address ByteArray)
    (recurAddrs : Array Address := #[])
    (arena : Ixon.ExprMetaArena := {})
    (names : Std.HashMap Address Ix.Name := {})
    (levelParamNames : Array (MetaField m Ix.Name) := #[]) : ConvertEnv m :=
  { sharing := c.sharing, refs := c.refs, univs := c.univs, blobs, recurAddrs, arena, names,
    levelParamNames }

def mkConstantVal (m : MetaMode) (numLvls : UInt64) (typ : Expr m)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default) : ConstantVal m :=
  { numLevels := numLvls.toNat, type := typ, name, levelParams }

/-! ## Factored constant conversion helpers -/

/-- Extract arena from ConstantMeta. -/
def metaArena : ConstantMeta → Ixon.ExprMetaArena
  | .defn _ _ _ _ _ a _ _ => a
  | .axio _ _ a _ => a
  | .quot _ _ a _ => a
  | .indc _ _ _ _ _ a _ => a
  | .ctor _ _ _ a _ => a
  | .recr _ _ _ _ _ a _ _ => a
  | .empty => {}

/-- Extract type root index from ConstantMeta. -/
def metaTypeRoot? : ConstantMeta → Option UInt64
  | .defn _ _ _ _ _ _ r _ => some r
  | .axio _ _ _ r => some r
  | .quot _ _ _ r => some r
  | .indc _ _ _ _ _ _ r => some r
  | .ctor _ _ _ _ r => some r
  | .recr _ _ _ _ _ _ r _ => some r
  | .empty => none

/-- Extract value root index from ConstantMeta (defn only). -/
def metaValueRoot? : ConstantMeta → Option UInt64
  | .defn _ _ _ _ _ _ _ r => some r
  | .empty => none
  | _ => none

/-- Extract level param name addresses from ConstantMeta. -/
def metaLvlAddrs : ConstantMeta → Array Address
  | .defn _ lvls _ _ _ _ _ _ => lvls
  | .axio _ lvls _ _ => lvls
  | .quot _ lvls _ _ => lvls
  | .indc _ lvls _ _ _ _ _ => lvls
  | .ctor _ lvls _ _ _ => lvls
  | .recr _ lvls _ _ _ _ _ _ => lvls
  | .empty => #[]

/-- Resolve level param addresses to MetaField names via the names table. -/
def resolveLevelParams (m : MetaMode) (names : Std.HashMap Address Ix.Name)
    (lvlAddrs : Array Address) : Array (MetaField m Ix.Name) :=
  match m with
  | .anon => lvlAddrs.map fun _ => ()
  | .meta => lvlAddrs.map fun addr => names.getD addr default

/-- Build the MetaField levelParams value from resolved names. -/
def mkLevelParams (m : MetaMode) (names : Std.HashMap Address Ix.Name)
    (lvlAddrs : Array Address) : MetaField m (Array Ix.Name) :=
  match m with
  | .anon => ()
  | .meta => lvlAddrs.map fun addr => names.getD addr default

/-- Resolve an array of name-hash addresses to a MetaField array of names. -/
def resolveMetaNames (m : MetaMode) (names : Std.HashMap Address Ix.Name)
    (addrs : Array Address) : MetaField m (Array Ix.Name) :=
  match m with | .anon => () | .meta => addrs.map fun a => names.getD a default

/-- Resolve a single name-hash address to a MetaField name. -/
def resolveMetaName (m : MetaMode) (names : Std.HashMap Address Ix.Name)
    (addr : Address) : MetaField m Ix.Name :=
  match m with | .anon => () | .meta => names.getD addr default

/-- Extract rule root indices from ConstantMeta (recr only). -/
def metaRuleRoots : ConstantMeta → Array UInt64
  | .recr _ _ _ _ _ _ _ rs => rs
  | _ => #[]

def convertRule (m : MetaMode) (rule : Ixon.RecursorRule) (ctorAddr : Address)
    (ctorName : MetaField m Ix.Name := default)
    (ruleRoot : Option UInt64 := none) :
    ConvertM m (Ix.Kernel.RecursorRule m) := do
  let rhs ← convertExpr m rule.rhs ruleRoot
  return { ctor := ctorAddr, ctorName, nfields := rule.fields.toNat, rhs }

def convertDefinition (m : MetaMode) (d : Ixon.Definition)
    (hints : ReducibilityHints) (all : Array Address)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty)
    (allNames : MetaField m (Array Ix.Name) := default) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m d.typ (metaTypeRoot? cMeta)
  let value ← convertExpr m d.value (metaValueRoot? cMeta)
  let cv := mkConstantVal m d.lvls typ name levelParams
  match d.kind with
  | .defn => return .defnInfo { toConstantVal := cv, value, hints, safety := convertSafety d.safety, all, allNames }
  | .opaq => return .opaqueInfo { toConstantVal := cv, value, isUnsafe := d.safety == .unsaf, all, allNames }
  | .thm => return .thmInfo { toConstantVal := cv, value, all, allNames }

def convertAxiom (m : MetaMode) (a : Ixon.Axiom)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m a.typ (metaTypeRoot? cMeta)
  let cv := mkConstantVal m a.lvls typ name levelParams
  return .axiomInfo { toConstantVal := cv, isUnsafe := a.isUnsafe }

def convertQuotient (m : MetaMode) (q : Ixon.Quotient)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m q.typ (metaTypeRoot? cMeta)
  let cv := mkConstantVal m q.lvls typ name levelParams
  return .quotInfo { toConstantVal := cv, kind := convertQuotKind q.kind }

def convertInductive (m : MetaMode) (ind : Ixon.Inductive)
    (ctorAddrs all : Array Address)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty)
    (allNames : MetaField m (Array Ix.Name) := default)
    (ctorNames : MetaField m (Array Ix.Name) := default) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m ind.typ (metaTypeRoot? cMeta)
  let cv := mkConstantVal m ind.lvls typ name levelParams
  let v : Ix.Kernel.InductiveVal m :=
    { toConstantVal := cv, numParams := ind.params.toNat,
      numIndices := ind.indices.toNat, all, ctors := ctorAddrs, allNames, ctorNames,
      numNested := ind.nested.toNat, isRec := ind.recr, isUnsafe := ind.isUnsafe,
      isReflexive := ind.refl }
  return .inductInfo v

def convertConstructor (m : MetaMode) (c : Ixon.Constructor)
    (inductAddr : Address)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty)
    (inductName : MetaField m Ix.Name := default) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m c.typ (metaTypeRoot? cMeta)
  let cv := mkConstantVal m c.lvls typ name levelParams
  let v : Ix.Kernel.ConstructorVal m :=
    { toConstantVal := cv, induct := inductAddr, inductName,
      cidx := c.cidx.toNat, numParams := c.params.toNat, numFields := c.fields.toNat,
      isUnsafe := c.isUnsafe }
  return .ctorInfo v

def convertRecursor (m : MetaMode) (r : Ixon.Recursor)
    (all ruleCtorAddrs : Array Address)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty)
    (allNames : MetaField m (Array Ix.Name) := default)
    (ruleCtorNames : Array (MetaField m Ix.Name) := #[]) : ConvertM m (Ix.Kernel.ConstantInfo m) := do
  let typ ← convertExpr m r.typ (metaTypeRoot? cMeta)
  let cv := mkConstantVal m r.lvls typ name levelParams
  let ruleRoots := (metaRuleRoots cMeta)
  let mut rules : Array (Ix.Kernel.RecursorRule m) := #[]
  for i in [:r.rules.size] do
    let ctorAddr := if h : i < ruleCtorAddrs.size then ruleCtorAddrs[i] else default
    let ctorName := if h : i < ruleCtorNames.size then ruleCtorNames[i] else default
    let ruleRoot := if h : i < ruleRoots.size then some ruleRoots[i] else none
    rules := rules.push (← convertRule m r.rules[i]! ctorAddr ctorName ruleRoot)
  let v : Ix.Kernel.RecursorVal m :=
    { toConstantVal := cv, all, allNames,
      numParams := r.params.toNat, numIndices := r.indices.toNat,
      numMotives := r.motives.toNat, numMinors := r.minors.toNat,
      rules, k := r.k, isUnsafe := r.isUnsafe }
  return .recInfo v

/-! ## Metadata helpers -/

/-- Build a direct name-hash Address → constant Address lookup table. -/
def buildHashToAddr (ixonEnv : Ixon.Env) : Std.HashMap Address Address := Id.run do
  let mut acc : Std.HashMap Address Address := {}
  for (nameHash, name) in ixonEnv.names do
    match ixonEnv.named.get? name with
    | some entry => acc := acc.insert nameHash entry.addr
    | none => pure ()
  return acc

/-- Extract block address from a projection constant, if it is one. -/
def projBlockAddr : Ixon.ConstantInfo → Option Address
  | .iPrj prj => some prj.block
  | .cPrj prj => some prj.block
  | .rPrj prj => some prj.block
  | .dPrj prj => some prj.block
  | _ => none

/-! ## BlockIndex -/

/-- Cross-reference index for projections within a single muts block.
    Built from the block group before conversion so we can derive addresses
    without relying on metadata. -/
structure BlockIndex where
  /-- memberIdx → iPrj address (inductive type address) -/
  inductAddrs : Std.HashMap UInt64 Address := {}
  /-- memberIdx → Array of cPrj addresses, ordered by cidx -/
  ctorAddrs : Std.HashMap UInt64 (Array Address) := {}
  /-- All iPrj addresses in the block (the `all` array for inductives/recursors) -/
  allInductAddrs : Array Address := #[]
  /-- memberIdx → primary projection address (for .recur resolution).
      iPrj for inductives, dPrj for definitions. -/
  memberAddrs : Std.HashMap UInt64 Address := {}

/-- Build a BlockIndex from a group of projections. -/
def buildBlockIndex (projections : Array (Address × Constant)) : BlockIndex := Id.run do
  let mut inductAddrs : Std.HashMap UInt64 Address := {}
  let mut ctorEntries : Std.HashMap UInt64 (Array (UInt64 × Address)) := {}
  let mut allInductAddrs : Array Address := #[]
  let mut memberAddrs : Std.HashMap UInt64 Address := {}
  for (addr, projConst) in projections do
    match projConst.info with
    | .iPrj prj =>
      inductAddrs := inductAddrs.insert prj.idx addr
      allInductAddrs := allInductAddrs.push addr
      memberAddrs := memberAddrs.insert prj.idx addr
    | .cPrj prj =>
      let entries := ctorEntries.getD prj.idx #[]
      ctorEntries := ctorEntries.insert prj.idx (entries.push (prj.cidx, addr))
    | .dPrj prj =>
      memberAddrs := memberAddrs.insert prj.idx addr
    | .rPrj prj =>
      -- Only set if no iPrj/dPrj already set for this member
      if !memberAddrs.contains prj.idx then
        memberAddrs := memberAddrs.insert prj.idx addr
    | _ => pure ()
  -- Sort constructor entries by cidx and extract just addresses
  let mut ctorAddrs : Std.HashMap UInt64 (Array Address) := {}
  for (idx, entries) in ctorEntries do
    let sorted := entries.insertionSort (fun a b => a.1 < b.1)
    ctorAddrs := ctorAddrs.insert idx (sorted.map (·.2))
  { inductAddrs, ctorAddrs, allInductAddrs, memberAddrs }

/-- All constructor addresses in declaration order (by inductive member index, then cidx).
    This matches the order of RecursorVal.rules in the Lean kernel. -/
def BlockIndex.allCtorAddrsInOrder (bIdx : BlockIndex) : Array Address := Id.run do
  let sorted := bIdx.inductAddrs.toArray.insertionSort (fun a b => a.1 < b.1)
  let mut result : Array Address := #[]
  for (idx, _) in sorted do
    result := result ++ (bIdx.ctorAddrs.getD idx #[])
  result

/-- Build recurAddrs array from BlockIndex. Maps member index → projection address. -/
def buildRecurAddrs (bIdx : BlockIndex) (numMembers : Nat) : Except ConvertError (Array Address) := do
  let mut addrs : Array Address := #[]
  for i in [:numMembers] do
    match bIdx.memberAddrs.get? i.toUInt64 with
    | some addr => addrs := addrs.push addr
    | none => throw (.missingMemberAddr i numMembers)
  return addrs

/-! ## Projection conversion -/

/-- Convert a single projection constant as a ConvertM action.
    Uses BlockIndex for cross-references instead of metadata. -/
def convertProjAction (m : MetaMode)
    (addr : Address) (c : Constant)
    (blockConst : Constant) (bIdx : BlockIndex)
    (name : MetaField m Ix.Name := default)
    (levelParams : MetaField m (Array Ix.Name) := default)
    (cMeta : ConstantMeta := .empty)
    (names : Std.HashMap Address Ix.Name := {})
    : Except String (ConvertM m (Ix.Kernel.ConstantInfo m)) := do
  let .muts members := blockConst.info
    | .error s!"projection block is not a muts at {addr}"
  match c.info with
  | .iPrj prj =>
    if h : prj.idx.toNat < members.size then
      match members[prj.idx.toNat] with
      | .indc ind =>
        let ctorAs := bIdx.ctorAddrs.getD prj.idx #[]
        let allNs := resolveMetaNames m names (match cMeta with | .indc _ _ _ a _ _ _ => a | _ => #[])
        let ctorNs := resolveMetaNames m names (match cMeta with | .indc _ _ c _ _ _ _ => c | _ => #[])
        .ok (convertInductive m ind ctorAs bIdx.allInductAddrs name levelParams cMeta allNs ctorNs)
      | _ => .error s!"iPrj at {addr} does not point to an inductive"
    else .error s!"iPrj index out of bounds at {addr}"
  | .cPrj prj =>
    if h : prj.idx.toNat < members.size then
      match members[prj.idx.toNat] with
      | .indc ind =>
        if h2 : prj.cidx.toNat < ind.ctors.size then
          let ctor := ind.ctors[prj.cidx.toNat]
          let inductAddr := bIdx.inductAddrs.getD prj.idx default
          let inductNm := resolveMetaName m names (match cMeta with | .ctor _ _ i _ _ => i | _ => default)
          .ok (convertConstructor m ctor inductAddr name levelParams cMeta inductNm)
        else .error s!"cPrj cidx out of bounds at {addr}"
      | _ => .error s!"cPrj at {addr} does not point to an inductive"
    else .error s!"cPrj index out of bounds at {addr}"
  | .rPrj prj =>
    if h : prj.idx.toNat < members.size then
      match members[prj.idx.toNat] with
      | .recr r =>
        let ruleCtorAs := bIdx.allCtorAddrsInOrder
        let allNs := resolveMetaNames m names (match cMeta with | .recr _ _ _ a _ _ _ _ => a | _ => #[])
        let metaRules := match cMeta with | .recr _ _ rules _ _ _ _ _ => rules | _ => #[]
        let ruleCtorNs := metaRules.map fun x => resolveMetaName m names x
        .ok (convertRecursor m r bIdx.allInductAddrs ruleCtorAs name levelParams cMeta allNs ruleCtorNs)
      | _ => .error s!"rPrj at {addr} does not point to a recursor"
    else .error s!"rPrj index out of bounds at {addr}"
  | .dPrj prj =>
    if h : prj.idx.toNat < members.size then
      match members[prj.idx.toNat] with
      | .defn d =>
        let hints := match cMeta with
          | .defn _ _ h _ _ _ _ _ => convertHints h
          | _ => .opaque
        let allNs := resolveMetaNames m names (match cMeta with | .defn _ _ _ a _ _ _ _ => a | _ => #[])
        .ok (convertDefinition m d hints bIdx.allInductAddrs name levelParams cMeta allNs)
      | _ => .error s!"dPrj at {addr} does not point to a definition"
    else .error s!"dPrj index out of bounds at {addr}"
  | _ => .error s!"not a projection at {addr}"

/-! ## Work items -/

/-- An entry to convert: address, constant, name, and metadata. -/
structure ConvertEntry (m : MetaMode) where
  addr : Address
  const : Constant
  name : MetaField m Ix.Name
  constMeta : ConstantMeta

/-- A work item: either a standalone constant or a complete block group. -/
inductive WorkItem (m : MetaMode) where
  | standalone (entry : ConvertEntry m)
  | block (blockAddr : Address) (entries : Array (ConvertEntry m))

/-- Extract ctx addresses from ConstantMeta (mutual context for .recur resolution). -/
def metaCtxAddrs : ConstantMeta → Array Address
  | .defn _ _ _ _ ctx .. => ctx
  | .indc _ _ _ _ ctx .. => ctx
  | .recr _ _ _ _ ctx .. => ctx
  | _ => #[]

/-- Extract parent inductive name-hash address from ConstantMeta (ctor only). -/
def metaInductAddr : ConstantMeta → Address
  | .ctor _ _ induct _ _ => induct
  | _ => default

/-- Resolve ctx name-hash addresses to constant addresses for recurAddrs. -/
def resolveCtxAddrs (hashToAddr : Std.HashMap Address Address) (ctx : Array Address)
    : Except ConvertError (Array Address) :=
  ctx.mapM fun x =>
    match hashToAddr.get? x with
    | some addr => .ok addr
    | none => .error (.unresolvableCtxAddr x)

/-- Convert a standalone (non-projection) constant. -/
def convertStandalone (m : MetaMode) (hashToAddr : Std.HashMap Address Address)
    (ixonEnv : Ixon.Env) (entry : ConvertEntry m) :
    Except String (Option (Ix.Kernel.ConstantInfo m)) := do
  let cMeta := entry.constMeta
  let recurAddrs ← (resolveCtxAddrs hashToAddr (metaCtxAddrs cMeta)).mapError toString
  let lvlNames := resolveLevelParams m ixonEnv.names (metaLvlAddrs cMeta)
  let lps := mkLevelParams m ixonEnv.names (metaLvlAddrs cMeta)
  let cEnv := mkConvertEnv m entry.const ixonEnv.blobs
    (recurAddrs := recurAddrs) (arena := (metaArena cMeta)) (names := ixonEnv.names)
    (levelParamNames := lvlNames)
  match entry.const.info with
  | .defn d =>
    let hints := match cMeta with
      | .defn _ _ h _ _ _ _ _ => convertHints h
      | _ => .opaque
    let allHashAddrs := match cMeta with
      | .defn _ _ _ a _ _ _ _ => a
      | _ => #[]
    let all := allHashAddrs.map fun x => hashToAddr.getD x x
    let allNames := resolveMetaNames m ixonEnv.names allHashAddrs
    let ci ← (ConvertM.run cEnv (convertDefinition m d hints all entry.name lps cMeta allNames)).mapError toString
    return some ci
  | .axio a =>
    let ci ← (ConvertM.run cEnv (convertAxiom m a entry.name lps cMeta)).mapError toString
    return some ci
  | .quot q =>
    let ci ← (ConvertM.run cEnv (convertQuotient m q entry.name lps cMeta)).mapError toString
    return some ci
  | .recr r =>
    let pair : Array Address × Array Address := match cMeta with
      | .recr _ _ rules all _ _ _ _ => (all, rules)
      | _ => (#[entry.addr], #[])
    let (metaAll, metaRules) := pair
    let all := metaAll.map fun x => hashToAddr.getD x x
    let ruleCtorAddrs := metaRules.map fun x => hashToAddr.getD x x
    let allNames := resolveMetaNames m ixonEnv.names metaAll
    let ruleCtorNames := metaRules.map fun x => resolveMetaName m ixonEnv.names x
    let ci ← (ConvertM.run cEnv (convertRecursor m r all ruleCtorAddrs entry.name lps cMeta allNames ruleCtorNames)).mapError toString
    return some ci
  | .muts _ => return none
  | _ => return none  -- projections handled separately

/-- Convert a complete block group (all projections share cache + recurAddrs). -/
def convertWorkBlock (m : MetaMode)
    (ixonEnv : Ixon.Env) (blockAddr : Address)
    (entries : Array (ConvertEntry m))
    (results : Array (Address × Ix.Kernel.ConstantInfo m)) (errors : Array (Address × String))
    : Array (Address × Ix.Kernel.ConstantInfo m) × Array (Address × String) := Id.run do
  let mut results := results
  let mut errors := errors
  match ixonEnv.getConst? blockAddr with
  | some blockConst =>
    -- Dedup projections by address for buildBlockIndex (avoid duplicate allInductAddrs)
    let mut canonicalProjs : Array (Address × Constant) := #[]
    let mut seenAddrs : Std.HashSet Address := {}
    for e in entries do
      if !seenAddrs.contains e.addr then
        canonicalProjs := canonicalProjs.push (e.addr, e.const)
        seenAddrs := seenAddrs.insert e.addr
    let bIdx := buildBlockIndex canonicalProjs
    let numMembers := match blockConst.info with
      | .muts members => members.size
      | _ => 0
    let recurAddrs ← match buildRecurAddrs bIdx numMembers with
      | .ok addrs => pure addrs
      | .error e =>
        for entry in entries do
          errors := errors.push (entry.addr, toString e)
        return (results, errors)
    -- Base env (no arena/levelParamNames — each projection sets its own)
    let baseEnv := mkConvertEnv m blockConst ixonEnv.blobs recurAddrs (names := ixonEnv.names)
    let mut state := ConvertState.init baseEnv
    let shareCache := match m with | .anon => true | .meta => false
    for entry in entries do
      if !shareCache then
        state := ConvertState.init baseEnv
      let cMeta := entry.constMeta
      let lvlNames := resolveLevelParams m ixonEnv.names (metaLvlAddrs cMeta)
      let lps := mkLevelParams m ixonEnv.names (metaLvlAddrs cMeta)
      let cEnv := { baseEnv with arena := (metaArena cMeta), levelParamNames := lvlNames }
      match convertProjAction m entry.addr entry.const blockConst bIdx entry.name lps cMeta ixonEnv.names with
      | .ok action =>
        match ConvertM.runWith cEnv state action with
        | .ok (ci, state') =>
          state := state'
          results := results.push (entry.addr, ci)
        | .error e =>
          errors := errors.push (entry.addr, toString e)
      | .error e => errors := errors.push (entry.addr, e)
  | none =>
    for entry in entries do
      errors := errors.push (entry.addr, s!"block not found: {blockAddr}")
  (results, errors)

/-- Convert a chunk of work items. -/
def convertChunk (m : MetaMode) (hashToAddr : Std.HashMap Address Address)
    (ixonEnv : Ixon.Env) (chunk : Array (WorkItem m))
    : Array (Address × Ix.Kernel.ConstantInfo m) × Array (Address × String) := Id.run do
  let mut results : Array (Address × Ix.Kernel.ConstantInfo m) := #[]
  let mut errors : Array (Address × String) := #[]
  for item in chunk do
    match item with
    | .standalone entry =>
      match convertStandalone m hashToAddr ixonEnv entry with
      | .ok (some ci) => results := results.push (entry.addr, ci)
      | .ok none => pure ()
      | .error e => errors := errors.push (entry.addr, e)
    | .block blockAddr entries =>
      (results, errors) := convertWorkBlock m ixonEnv blockAddr entries results errors
  (results, errors)

/-! ## Top-level conversion -/

/-- Convert an entire Ixon.Env to a Kernel.Env with primitives and quotInit flag.
    Iterates named constants first (with full metadata), then picks up anonymous
    constants not in named. Groups projections by block and parallelizes. -/
def convertEnv (m : MetaMode) (ixonEnv : Ixon.Env) (numWorkers : Nat := 32)
    : Except String (Ix.Kernel.Env m × Primitives × Bool) :=
  -- Build primitives with quot addresses
  let prims : Primitives := Id.run do
    let mut p := buildPrimitives
    for (addr, c) in ixonEnv.consts do
      match c.info with
      | .quot q => match q.kind with
        | .type => p := { p with quotType := addr }
        | .ctor => p := { p with quotCtor := addr }
        | .lift => p := { p with quotLift := addr }
        | .ind  => p := { p with quotInd := addr }
      | _ => pure ()
    return p
  let quotInit := Id.run do
    for (_, c) in ixonEnv.consts do
      if let .quot _ := c.info then return true
    return false
  let hashToAddr := buildHashToAddr ixonEnv
  let (constants, allErrors) := Id.run do
    -- Phase 1: Build entries from named constants (have names + metadata)
    let mut entries : Array (ConvertEntry m) := #[]
    let mut seen : Std.HashSet Address := {}
    for (ixName, named) in ixonEnv.named do
      let addr := named.addr
      match ixonEnv.consts.get? addr with
      | some c =>
        let name := mkMetaName m (some ixName)
        entries := entries.push { addr, const := c, name, constMeta := named.constMeta }
        seen := seen.insert addr
      | none => pure ()
    -- Phase 2: Pick up anonymous constants not covered by named
    for (addr, c) in ixonEnv.consts do
      if !seen.contains addr then
        entries := entries.push { addr, const := c, name := default, constMeta := .empty }
    -- Phase 2.5: In .anon mode, dedup all entries by address (copies identical).
    -- In .meta mode, keep all entries (named variants have distinct metadata).
    let shouldDedup := match m with | .anon => true | .meta => false
    if shouldDedup then
      let mut dedupedEntries : Array (ConvertEntry m) := #[]
      let mut seenDedup : Std.HashSet Address := {}
      for entry in entries do
        if !seenDedup.contains entry.addr then
          dedupedEntries := dedupedEntries.push entry
          seenDedup := seenDedup.insert entry.addr
      entries := dedupedEntries
    -- Phase 3: Group into standalones and block groups
    -- Use (blockAddr, ctxKey) to disambiguate colliding block addresses
    let mut standalones : Array (ConvertEntry m) := #[]
    -- Pass 1: Build nameHash → ctx map from entries with ctx
    let mut nameHashToCtx : Std.HashMap Address (Array Address) := {}
    let mut projEntries : Array (Address × ConvertEntry m) := #[]
    for entry in entries do
      match projBlockAddr entry.const.info with
      | some blockAddr =>
        projEntries := projEntries.push (blockAddr, entry)
        let ctx := metaCtxAddrs entry.constMeta
        if ctx.size > 0 then
          for nameHash in ctx do
            nameHashToCtx := nameHashToCtx.insert nameHash ctx
      | none => standalones := standalones.push entry
    -- Pass 2: Group by (blockAddr, ctxKey) to avoid collisions
    let mut blockGroups : Std.HashMap (Address × UInt64) (Array (ConvertEntry m)) := {}
    for (blockAddr, entry) in projEntries do
      let ctx0 := metaCtxAddrs entry.constMeta
      let ctx := if ctx0.size > 0 then ctx0
        else nameHashToCtx.getD (metaInductAddr entry.constMeta) #[]
      let ctxKey := hash ctx
      let key := (blockAddr, ctxKey)
      blockGroups := blockGroups.insert key
        ((blockGroups.getD key #[]).push entry)
    -- Phase 4: Build work items
    let mut workItems : Array (WorkItem m) := #[]
    for entry in standalones do
      workItems := workItems.push (.standalone entry)
    for ((blockAddr, _), blockEntries) in blockGroups do
      workItems := workItems.push (.block blockAddr blockEntries)
    -- Phase 5: Chunk work items and parallelize
    let total := workItems.size
    let chunkSize := (total + numWorkers - 1) / numWorkers
    let mut tasks : Array (Task (Array (Address × Ix.Kernel.ConstantInfo m) × Array (Address × String))) := #[]
    let mut offset := 0
    while offset < total do
      let endIdx := min (offset + chunkSize) total
      let chunk := workItems[offset:endIdx]
      let task := Task.spawn (prio := .dedicated) fun () =>
        convertChunk m hashToAddr ixonEnv chunk.toArray
      tasks := tasks.push task
      offset := endIdx
    -- Phase 6: Collect results
    let mut constants : Ix.Kernel.Env m := default
    let mut allErrors : Array (Address × String) := #[]
    for task in tasks do
      let (chunkResults, chunkErrors) := task.get
      for (addr, ci) in chunkResults do
        constants := constants.insert addr ci
      allErrors := allErrors ++ chunkErrors
    (constants, allErrors)
  if !allErrors.isEmpty then
    let msgs := allErrors[:min 10 allErrors.size].toArray.map fun (addr, e) => s!"  {addr}: {e}"
    .error s!"conversion errors ({allErrors.size}):\n{"\n".intercalate msgs.toList}"
  else
    .ok (constants, prims, quotInit)

/-- Convert an Ixon.Env to a Kernel.Env with full metadata. -/
def convert (ixonEnv : Ixon.Env) : Except String (Ix.Kernel.Env .meta × Primitives × Bool) :=
  convertEnv .meta ixonEnv

/-- Convert an Ixon.Env to a Kernel.Env without metadata. -/
def convertAnon (ixonEnv : Ixon.Env) : Except String (Ix.Kernel.Env .anon × Primitives × Bool) :=
  convertEnv .anon ixonEnv

end Ix.Kernel.Convert
