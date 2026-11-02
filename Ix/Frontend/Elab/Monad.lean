/-
  Ix.Frontend.Elab.Monad: Pure, deterministic elaboration environment,
  local context, metavariable context, and monad (`IxElabM`) for the Ix Frontend.

  Carries:
  - `consts : NameMap Ix.ConstantInfo` (elaborated kernel constants)
  - `binderContracts : NameMap (Array Ixon.BinderContract × Ixon.ValueContract)`
  - `letContracts : NameMap (Array Ixon.LetContract)`
  - `structTable : NameMap StructInfo` (for structure projections, anonymous constructors, `{ ... }` syntax)
  - `instances : Array InstanceEntry` (for bounded backtracking typeclass synthesis)
  - `importMap : IxImportMap` (first-class `Name -> Address` and content-hash import table)
-/
module

public import Ix.Frontend.SccPass
public import IxC.Ixon.Types

@[expose] public section

namespace Ix.Frontend.Elab

open Ix.Frontend

/-! ## Structure & Typeclass Metadata Tables -/

/-- Metadata for a single field of a `structure` or `class`. -/
structure StructFieldInfo where
  fieldName  : Ix.Name
  projFnName : Ix.Name
  fieldIdx   : Nat
  binderInfo : Lean.BinderInfo       := .default
  contract   : Ixon.BinderContract   := default
  defaultVal : Option Ix.Syntax      := none
  isSubobject : Bool                 := false
  deriving Repr, Inhabited

/-- Registered metadata for an elaborated `structure` or `class`. -/
structure StructInfo where
  structName : Ix.Name
  ctorName   : Ix.Name
  numParams  : Nat
  fields     : Array StructFieldInfo := #[]
  parents    : Array Ix.Name         := #[]
  isClass    : Bool                  := false
  deriving Repr, Inhabited

/-- Registered typeclass `instance` entry for bounded synthesis. -/
structure InstanceEntry where
  instName  : Ix.Name
  className : Ix.Name
  prio      : Nat := 1000
  deriving Repr, Inhabited

/-! ## Pure Elaboration Environment (`IxElabEnv`) -/

/-- Pure elaboration environment holding kernel constants, substructural contracts,
    structure/class tables, and `IxImportMap`. -/
structure IxElabEnv where
  consts          : NameMap Ix.ConstantInfo                                    := NameMap.empty
  constOrder      : Array Ix.Name                                              := #[]
  binderContracts : NameMap (Array Ixon.BinderContract × Ixon.ValueContract)   := NameMap.empty
  letContracts    : NameMap (Array Ixon.LetContract)                           := NameMap.empty
  structTable     : NameMap StructInfo                                         := NameMap.empty
  classSet        : NameSet                                                    := NameSet.empty
  instances       : Array InstanceEntry                                        := #[]
  importMap       : IxImportMap                                                := IxImportMap.empty
  deriving Repr, Inhabited

namespace IxElabEnv

def empty : IxElabEnv := {}

/-- Look up a constant in `consts`. -/
def find? (env : IxElabEnv) (name : Ix.Name) : Option Ix.ConstantInfo :=
  env.consts.get? name

/-- True if `name` is a registered constant in `env`. -/
def contains (env : IxElabEnv) (name : Ix.Name) : Bool :=
  env.consts.contains name

/-- True if `name` is a constructor in `env`. -/
def isCtor (env : IxElabEnv) (name : Ix.Name) : Bool :=
  match env.consts.get? name with
  | some (.ctorInfo _) => true
  | _ => false

/-- Insert or update a constant in `env`, recording its insertion order. -/
def addConst (env : IxElabEnv) (ci : Ix.ConstantInfo) : IxElabEnv :=
  let name := (Expr.ConstantInfo.getCnstPure ci).name
  let constOrder := if env.consts.contains name then env.constOrder else env.constOrder.push name
  { env with
    consts := env.consts.insert name ci
    constOrder := constOrder }

/-- Record substructural binder & return contracts for declaration `name`. -/
def addContracts (env : IxElabEnv) (name : Ix.Name)
    (bcs : Array Ixon.BinderContract) (ret : Ixon.ValueContract)
    (lcs : Array Ixon.LetContract := #[]) : IxElabEnv :=
  let env :=
    if bcs.isEmpty && ret == default then env
    else { env with binderContracts := env.binderContracts.insert name (bcs, ret) }
  if lcs.isEmpty then env
  else { env with letContracts := env.letContracts.insert name lcs }

/-- Register a `StructInfo` (and mark `classSet` if `info.isClass`). -/
def addStructInfo (env : IxElabEnv) (info : StructInfo) : IxElabEnv :=
  let classSet := if info.isClass then env.classSet.insert info.structName else env.classSet
  { env with
    structTable := env.structTable.insert info.structName info
    classSet    := classSet }

/-- Register a global typeclass instance. -/
def addInstance (env : IxElabEnv) (entry : InstanceEntry) : IxElabEnv :=
  { env with instances := env.instances.push entry }

/-- Convert `IxElabEnv.consts` into an `Ix.Environment` (`Std.HashMap Ix.Name Ix.ConstantInfo`),
    populating canonical 32-byte `Address` Merkle digests on every exported constant. -/
def toIxEnvironment (env : IxElabEnv) : Ix.Environment :=
  let init : Ix.Environment :=
    { consts := @Std.HashMap.emptyWithCapacity Ix.Name Ix.ConstantInfo Ix.Name.instBEq Ix.Name.instHashable 8 }
  env.constOrder.foldl (fun acc n =>
    match env.consts.get? n with
    | some ci =>
      let n' := Name.rehash n
      let ci' := Expr.ConstantInfo.rehash ci
      { consts := acc.consts.insert n' ci' }
    | none    => acc) init

/-- Construct an `IxElabEnv` pre-populated from an existing `Ix.Environment`. -/
def ofIxEnvironment (ixEnv : Ix.Environment) : IxElabEnv :=
  ixEnv.consts.fold (fun acc name ci =>
    { acc with
      consts := acc.consts.insert name ci
      constOrder := acc.constOrder.push name }) IxElabEnv.empty

/-- Register an imported constant `ci` at content address `addr` so that both `#<addr>`
    and `map LocalName := #<addr>` resolve to `ci.getCnst.name`. -/
def registerImportedConst (env : IxElabEnv) (addr : Address) (ci : Ix.ConstantInfo) : IxElabEnv :=
  let env1 := env.addConst ci
  { env1 with importMap := env1.importMap.insertName (Expr.ConstantInfo.getCnstPure ci).name addr }

end IxElabEnv

/-! ## Local Context (`LocalDecl`, `LocalContext`) -/

/-- A local free variable declaration (`cdecl` for `fun`/`forall` binders, `ldecl` for `let`/`have`). -/
structure LocalDecl where
  fvarId     : Ix.Name
  userName   : Ix.Name
  type       : Ix.Expr
  value?     : Option Ix.Expr      := none
  binderInfo : Lean.BinderInfo     := .default
  contract   : Ixon.BinderContract := default
  letKind?   : Option Ixon.LetKind := none
  deriving Repr, Inhabited

/-- Pure local context storing local declarations in telescope order. -/
structure LocalContext where
  decls      : Array LocalDecl   := #[]
  byFVarId   : NameMap LocalDecl := NameMap.empty
  byUserName : NameMap LocalDecl := NameMap.empty
  deriving Repr, Inhabited

namespace LocalContext

def empty : LocalContext := {}

def addDecl (lctx : LocalContext) (d : LocalDecl) : LocalContext :=
  { decls      := lctx.decls.push d
    byFVarId   := lctx.byFVarId.insert d.fvarId d
    byUserName := if Name.isAnonymous d.userName then lctx.byUserName
                  else lctx.byUserName.insert d.userName d }

def findFVar? (lctx : LocalContext) (fvarId : Ix.Name) : Option LocalDecl :=
  lctx.byFVarId.get? fvarId

def findUserName? (lctx : LocalContext) (userName : Ix.Name) : Option LocalDecl :=
  lctx.byUserName.get? userName

end LocalContext

/-! ## Metavariable Context (`MetavarDecl`, `MetavarContext`) -/

/-- Declaration of an expression metavariable `?m` in a local context. -/
structure MetavarDecl where
  mvarId   : Ix.Name
  userName : Ix.Name
  lctx     : LocalContext
  type     : Ix.Expr
  deriving Repr, Inhabited

/-- Pure metavariable context tracking expression and universe level metavariables. -/
structure MetavarContext where
  decls       : NameMap MetavarDecl := NameMap.empty
  exprAssigns : NameMap Ix.Expr     := NameMap.empty
  lvlAssigns  : NameMap Ix.Level    := NameMap.empty
  deriving Repr, Inhabited

namespace MetavarContext

def empty : MetavarContext := {}

def addExprMVarDecl (mctx : MetavarContext) (d : MetavarDecl) : MetavarContext :=
  { mctx with decls := mctx.decls.insert d.mvarId d }

def assignExpr (mctx : MetavarContext) (mvarId : Ix.Name) (val : Ix.Expr) : MetavarContext :=
  { mctx with exprAssigns := mctx.exprAssigns.insert mvarId val }

def assignLevel (mctx : MetavarContext) (uvarId : Ix.Name) (lvl : Ix.Level) : MetavarContext :=
  { mctx with lvlAssigns := mctx.lvlAssigns.insert uvarId lvl }

def getExprAssignment? (mctx : MetavarContext) (mvarId : Ix.Name) : Option Ix.Expr :=
  mctx.exprAssigns.get? mvarId

def getLevelAssignment? (mctx : MetavarContext) (uvarId : Ix.Name) : Option Ix.Level :=
  mctx.lvlAssigns.get? uvarId

def findDecl? (mctx : MetavarContext) (mvarId : Ix.Name) : Option MetavarDecl :=
  mctx.decls.get? mvarId

end MetavarContext

/-! ## Elaboration Errors, Context, State, and `IxElabM` Monad -/

/-- Structured elaboration error with optional byte offset. -/
structure ElabError where
  pos? : Option Nat := none
  msg  : String
  deriving BEq, Repr, Inhabited

instance : ToString ElabError where
  toString err :=
    match err.pos? with
    | some p => s!"elaboration error at byte {p}: {err.msg}"
    | none   => s!"elaboration error: {err.msg}"

/-- Read-only context for `IxElabM`. -/
structure ElabContext where
  lctx       : LocalContext  := LocalContext.empty
  scope      : ScopeSnapshot := {}
  modIdx     : ModuleIndex   := {}
  currDecl?  : Option Ix.Name := none
  univParams : List Ix.Name  := []
  refPos?    : Option Nat    := none
  deriving Repr, Inhabited

/-- Mutable state for `IxElabM`. -/
structure ElabState where
  env             : IxElabEnv                  := IxElabEnv.empty
  mctx            : MetavarContext             := MetavarContext.empty
  nextId          : Nat                        := 0
  autoBoundUnivs  : List Ix.Name               := []
  localLetContracts : Array Ixon.LetContract   := #[]
  deriving Repr, Inhabited

/-- Pure, deterministic elaboration monad. -/
abbrev IxElabM (α : Type) := ReaderT ElabContext (StateT ElabState (Except ElabError)) α

namespace IxElabM

def run (act : IxElabM α) (ctx : ElabContext := {}) (st : ElabState := {}) :
    Except ElabError (α × ElabState) :=
  (act ctx).run st

def run' (act : IxElabM α) (ctx : ElabContext := {}) (st : ElabState := {}) :
    Except ElabError α := do
  let (a, _) ← (act ctx).run st
  return a

end IxElabM

/-- Throw an `ElabError` at the current syntax position (or `stx`'s position if provided). -/
def throwElabError (msg : String) (stx? : Option Ix.Syntax := none) : IxElabM α := do
  let ctx ← read
  let pos? := match stx? with
    | some stx => (Syntax.getPos? stx).orElse (fun _ => ctx.refPos?)
    | none     => ctx.refPos?
  throw { pos?, msg }

/-- Run `act` with `stx`'s source position as the default error position. -/
def withRef (stx : Ix.Syntax) (act : IxElabM α) : IxElabM α := do
  match Syntax.getPos? stx with
  | some p => withReader (fun ctx => { ctx with refPos? := some p }) act
  | none   => act

/-- Generate a fresh deterministic numeric index in `IxElabM`. -/
def mkFreshIdx : IxElabM Nat := do
  let st ← get
  let idx := st.nextId
  set { st with nextId := idx + 1 }
  return idx

/-- Generate a fresh unique `Ix.Name` with prefix `pre`. -/
def mkFreshName (pre : String := "_uniq") : IxElabM Ix.Name := do
  let idx ← mkFreshIdx
  return Name.mkNat (Name.simple pre) idx

/-- Run `act` in an extended `LocalContext`. -/
def withLocalDecl (userName : Ix.Name) (type : Ix.Expr)
    (bi : Lean.BinderInfo := .default)
    (contract : Ixon.BinderContract := default)
    (k : Ix.Name → Ix.Expr → IxElabM α) : IxElabM α := do
  let fvarId ← mkFreshName "_fvar"
  let fvarExpr := Expr.mkFVar fvarId
  let decl : LocalDecl := { fvarId, userName, type, binderInfo := bi, contract }
  withReader (fun ctx => { ctx with lctx := ctx.lctx.addDecl decl }) (k fvarId fvarExpr)

/-- Run `act` in an extended `LocalContext` with a local `let` binding. -/
def withLetDecl (userName : Ix.Name) (type val : Ix.Expr)
    (contract : Ixon.BinderContract := default)
    (letKind : Ixon.LetKind := .value)
    (_nonDep : Bool := false)
    (k : Ix.Name → Ix.Expr → IxElabM α) : IxElabM α := do
  let fvarId ← mkFreshName "_fvar"
  let fvarExpr := Expr.mkFVar fvarId
  let decl : LocalDecl :=
    { fvarId, userName, type, value? := some val, contract, letKind? := some letKind }
  withReader (fun ctx => { ctx with lctx := ctx.lctx.addDecl decl }) (k fvarId fvarExpr)

/-- Save and restore `ElabState` on failure (for backtracking typeclass synthesis or `try`). -/
def observing? (act : IxElabM α) : IxElabM (Option α) := do
  let saved ← get
  let ctx ← read
  match (act ctx).run saved with
  | .ok (a, st') =>
    set st'
    return some a
  | .error _ =>
    set saved
    return none

end Ix.Frontend.Elab
