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
open Ix.Frontend.Parser

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
    structure/class tables, declarative macro rules, and `IxImportMap`. -/
structure IxElabEnv where
  consts           : NameMap Ix.ConstantInfo                                    := NameMap.empty
  constOrder       : List Ix.Name                                               := []
  binderContracts  : NameMap (Array Ixon.BinderContract × Ixon.ValueContract)   := NameMap.empty
  letContracts     : NameMap (Array Ixon.LetContract)                           := NameMap.empty
  structTable      : NameMap StructInfo                                         := NameMap.empty
  classSet         : NameSet                                                    := NameSet.empty
  instances        : List InstanceEntry                                         := []
  instancesByClass : NameMap (List InstanceEntry)                               := NameMap.empty
  importMap        : IxImportMap                                                := IxImportMap.empty
  macroRules       : List MacroRule                                             := []
  deriving Repr, Inhabited

namespace IxElabEnv

def empty : IxElabEnv := {}

@[inline] def bindEnv (env : IxElabEnv) (k : IxElabEnv → α) : α :=
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    consts.bindMap fun consts' =>
    Ix.Frontend.Parser.SyntaxStack.bindList constOrder fun constOrder' =>
    binderContracts.bindMap fun binderContracts' =>
    letContracts.bindMap fun letContracts' =>
    structTable.bindMap fun structTable' =>
    classSet.bindSet fun classSet' =>
    Ix.Frontend.Parser.SyntaxStack.bindList instances fun instances' =>
    instancesByClass.bindMap fun instancesByClass' =>
    Ix.Frontend.Parser.SyntaxStack.bindList macroRules fun macroRules' =>
      k ⟨consts', constOrder', binderContracts', letContracts', structTable', classSet', instances', instancesByClass', importMap, macroRules'⟩

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
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    let name := (Expr.ConstantInfo.getCnstPure ci).name
    let constOrder1 := if consts.contains name then constOrder else name :: constOrder
    Ix.Frontend.Parser.SyntaxStack.bindList constOrder1 fun constOrder' =>
    (consts.insert name ci).bindMap fun consts' =>
      ⟨consts', constOrder', binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩

/-- Record substructural binder & return contracts for declaration `name`. -/
def addContracts (env : IxElabEnv) (name : Ix.Name)
    (bcs : Array Ixon.BinderContract) (ret : Ixon.ValueContract)
    (lcs : Array Ixon.LetContract := #[]) : IxElabEnv :=
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    let binderContracts1 :=
      if bcs.isEmpty && ret == default then binderContracts
      else binderContracts.insert name (bcs, ret)
    let letContracts1 :=
      if lcs.isEmpty then letContracts
      else letContracts.insert name lcs
    binderContracts1.bindMap fun binderContracts' =>
    letContracts1.bindMap fun letContracts' =>
      ⟨consts, constOrder, binderContracts', letContracts', structTable, classSet, instances, instancesByClass, importMap, macroRules⟩

/-- Register a `StructInfo` (and mark `classSet` if `info.isClass`). -/
def addStructInfo (env : IxElabEnv) (info : StructInfo) : IxElabEnv :=
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    let classSet1 := if info.isClass then classSet.insert info.structName else classSet
    (structTable.insert info.structName info).bindMap fun structTable' =>
    classSet1.bindSet fun classSet' =>
      ⟨consts, constOrder, binderContracts, letContracts, structTable', classSet', instances, instancesByClass, importMap, macroRules⟩

/-- Register a global typeclass instance. -/
def addInstance (env : IxElabEnv) (entry : InstanceEntry) : IxElabEnv :=
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    let prev := instancesByClass.get? entry.className |>.getD []
    (instancesByClass.insert entry.className (entry :: prev)).bindMap fun instancesByClass' =>
      ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, entry :: instances, instancesByClass', importMap, macroRules⟩

/-- Register a declarative `MacroRule` in `env`. -/
def addMacroRule (env : IxElabEnv) (rule : MacroRule) : IxElabEnv :=
  match env with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    Ix.Frontend.Parser.SyntaxStack.bindList (rule :: macroRules) fun macroRules' =>
      ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules'⟩

/-- Register a list of `MacroRule`s in `env`. -/
def addMacroRules (env : IxElabEnv) (rules : List MacroRule) : IxElabEnv :=
  rules.foldl (fun acc r => acc.addMacroRule r) env

/-- Convert `IxElabEnv.consts` into an `Ix.Environment` (`Std.HashMap Ix.Name Ix.ConstantInfo`),
    populating canonical 32-byte `Address` Merkle digests on every exported constant. -/
def toIxEnvironment (env : IxElabEnv) : Ix.Environment :=
  let init : Ix.Environment :=
    { consts := @Std.HashMap.emptyWithCapacity Ix.Name Ix.ConstantInfo Ix.Name.instBEq Ix.Name.instHashable 8 }
  env.constOrder.reverse.foldl (fun acc n =>
    match env.consts.get? n with
    | some ci =>
      let n' := Name.rehash n
      let ci' := Expr.ConstantInfo.rehash ci
      { consts := acc.consts.insert n' ci' }
    | none    => acc) init

/-- Construct an `IxElabEnv` pre-populated from an existing `Ix.Environment`. -/
def ofIxEnvironment (ixEnv : Ix.Environment) : IxElabEnv :=
  ixEnv.consts.fold (fun acc _ ci =>
    acc.addConst (match ci with | _ => ci)) IxElabEnv.empty
  |>.bindEnv id

/-- Update the `importMap` of an `IxElabEnv` strictly without projection chains. -/
def withImportMap : IxElabEnv → IxImportMap → IxElabEnv
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, _, macroRules⟩, importMap' =>
    ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap', macroRules⟩

/-- Register an imported constant `ci` at content address `addr` so that both `#<addr>`
    and `map LocalName := #<addr>` resolve to `ci.getCnst.name`. -/
def registerImportedConst (env : IxElabEnv) (addr : Address) (ci : Ix.ConstantInfo) : IxElabEnv :=
  match env.addConst ci with
  | ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap, macroRules⟩ =>
    let importMap' := importMap.insertName (Expr.ConstantInfo.getCnstPure ci).name addr
    ⟨consts, constOrder, binderContracts, letContracts, structTable, classSet, instances, instancesByClass, importMap', macroRules⟩

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
  nonDep     : Bool                := false
  deriving Repr, Inhabited

/-- Pure local context storing local declarations in reverse telescope order (`revDecls`, most-recent first). -/
structure LocalContext where
  revDecls   : List LocalDecl    := []
  byFVarId   : NameMap LocalDecl := NameMap.empty
  byUserName : NameMap LocalDecl := NameMap.empty
  deriving Repr, Inhabited

namespace LocalContext

def empty : LocalContext := {}

def addDecl (lctx : LocalContext) (d : LocalDecl) : LocalContext :=
  match lctx with
  | ⟨revDecls, byFVarId, byUserName⟩ =>
    (byFVarId.insert d.fvarId d).bindMap fun byFVarId' =>
      if Name.isAnonymous d.userName then
        ⟨d :: revDecls, byFVarId', byUserName⟩
      else
        (byUserName.insert d.userName d).bindMap fun byUserName' =>
          ⟨d :: revDecls, byFVarId', byUserName'⟩

def findFVar? (lctx : LocalContext) (fvarId : Ix.Name) : Option LocalDecl :=
  lctx.byFVarId.get? fvarId

abbrev find? (lctx : LocalContext) (fvarId : Ix.Name) : Option LocalDecl :=
  lctx.byFVarId.get? fvarId

abbrev decls (lctx : LocalContext) : List LocalDecl :=
  lctx.revDecls.reverse

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

/-- Delayed metavariable assignment `?m := mkLambdaFVarsList lctx fvars ?pendingMVar`,
    enabling non-continuation `intro`, `have`, and `let` tactics over `TacticState.goals`. -/
structure DelayedMVarAssign where
  lctx        : LocalContext
  fvars       : List Ix.Name
  pendingMVar : Ix.Name
  deriving Repr, Inhabited

/-- Pure metavariable context tracking expression and universe level metavariables. -/
structure MetavarContext where
  decls          : NameMap MetavarDecl       := NameMap.empty
  exprAssigns    : NameMap Ix.Expr           := NameMap.empty
  lvlAssigns     : NameMap Ix.Level          := NameMap.empty
  delayedAssigns : NameMap DelayedMVarAssign := NameMap.empty
  deriving Repr, Inhabited

namespace MetavarContext

def empty : MetavarContext := {}

@[inline] def bindMCtx (mctx : MetavarContext) (k : MetavarContext → α) : α :=
  match mctx with
  | ⟨decls, exprAssigns, lvlAssigns, delayedAssigns⟩ =>
    decls.bindMap fun decls' =>
    exprAssigns.bindMap fun exprAssigns' =>
    lvlAssigns.bindMap fun lvlAssigns' =>
    delayedAssigns.bindMap fun delayedAssigns' =>
      k ⟨decls', exprAssigns', lvlAssigns', delayedAssigns'⟩

def addExprMVarDecl (mctx : MetavarContext) (d : MetavarDecl) : MetavarContext :=
  match mctx with
  | ⟨decls, exprAssigns, lvlAssigns, delayedAssigns⟩ =>
    (decls.insert d.mvarId d).bindMap fun decls' =>
      ⟨decls', exprAssigns, lvlAssigns, delayedAssigns⟩

def assignExpr (mctx : MetavarContext) (mvarId : Ix.Name) (val : Ix.Expr) : MetavarContext :=
  match mctx with
  | ⟨decls, exprAssigns, lvlAssigns, delayedAssigns⟩ =>
    (exprAssigns.insert mvarId val).bindMap fun exprAssigns' =>
      ⟨decls, exprAssigns', lvlAssigns, delayedAssigns⟩

def assignLevel (mctx : MetavarContext) (uvarId : Ix.Name) (lvl : Ix.Level) : MetavarContext :=
  match mctx with
  | ⟨decls, exprAssigns, lvlAssigns, delayedAssigns⟩ =>
    (lvlAssigns.insert uvarId lvl).bindMap fun lvlAssigns' =>
      ⟨decls, exprAssigns, lvlAssigns', delayedAssigns⟩

def assignDelayed (mctx : MetavarContext) (mvarId : Ix.Name) (d : DelayedMVarAssign) : MetavarContext :=
  match mctx with
  | ⟨decls, exprAssigns, lvlAssigns, delayedAssigns⟩ =>
    (delayedAssigns.insert mvarId d).bindMap fun delayedAssigns' =>
      ⟨decls, exprAssigns, lvlAssigns, delayedAssigns'⟩

def getExprAssignment? (mctx : MetavarContext) (mvarId : Ix.Name) : Option Ix.Expr :=
  mctx.exprAssigns.get? mvarId

def getLevelAssignment? (mctx : MetavarContext) (uvarId : Ix.Name) : Option Ix.Level :=
  mctx.lvlAssigns.get? uvarId

def getDelayedAssignment? (mctx : MetavarContext) (mvarId : Ix.Name) : Option DelayedMVarAssign :=
  mctx.delayedAssigns.get? mvarId

def isExprAssigned (mctx : MetavarContext) (mvarId : Ix.Name) : Bool :=
  (mctx.exprAssigns.get? mvarId).isSome || (mctx.delayedAssigns.get? mvarId).isSome

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

/-- Update `st.mctx` strictly without creating `{ st with ... }` projection chains. -/
@[inline] def modifyMCtx (f : MetavarContext → MetavarContext) : IxElabM Unit := fun _ st =>
  match st with
  | ⟨env, mctx, nextId, autoUnivs, letContracts⟩ =>
    (f mctx).bindMCtx fun mctx' =>
      .ok ((), ⟨env, mctx', nextId, autoUnivs, letContracts⟩)

/-- Update `st.env` strictly without creating `{ st with ... }` projection chains. -/
@[inline] def modifyEnv (f : IxElabEnv → IxElabEnv) : IxElabM Unit := fun _ st =>
  match st with
  | ⟨env, mctx, nextId, autoUnivs, letContracts⟩ =>
    (f env).bindEnv fun env' =>
      .ok ((), ⟨env', mctx, nextId, autoUnivs, letContracts⟩)

/-- Throw an `ElabError` at the current syntax position (or `stx`'s position if provided). -/
def throwElabError (msg : String) (stx? : Option Ix.Syntax := none) : IxElabM α := do
  let ctx ← read
  let pos? := match stx? with
    | some stx => (Syntax.getPos? stx).orElse (fun _ => ctx.refPos?)
    | none     => ctx.refPos?
  throw { pos?, msg }

/-- Run `act` with `stx`'s source position attached to any uncaught `ElabError`.
    Does ZERO `Syntax.getPos?` traversals and ZERO `ElabContext` copies on `.ok`! -/
def withRef (stx : Ix.Syntax) (act : IxElabM α) : IxElabM α := fun ctx st =>
  match (act ctx).run st with
  | .ok res => .ok res
  | .error err =>
    match err.pos? with
    | some _ => .error err
    | none   => .error { err with pos? := (Syntax.getPos? stx).orElse (fun _ => ctx.refPos?) }

/-- Generate a fresh deterministic numeric index in `IxElabM`, strictly forcing `idx + 1`
    and destructuring `ElabState` so no `Proj` or `Nat.add` chains accumulate. -/
def mkFreshIdx : IxElabM Nat := fun _ st =>
  match st with
  | ⟨env, mctx, idx, autoUnivs, letContracts⟩ =>
    let nextIdx := idx + 1
    if Nat.beq nextIdx 0 then
      .ok (idx, ⟨env, mctx, 0, autoUnivs, letContracts⟩)
    else
      .ok (idx, ⟨env, mctx, nextIdx, autoUnivs, letContracts⟩)

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
  fun ctx st =>
    match ctx with
    | ⟨lctx, scope, modIdx, currDecl?, univParams, refPos?⟩ =>
      match lctx.addDecl decl with
      | ⟨revDecls', byFVarId', byUserName'⟩ =>
        (k fvarId fvarExpr ⟨⟨revDecls', byFVarId', byUserName'⟩, scope, modIdx, currDecl?, univParams, refPos?⟩).run st

/-- Run `act` in an extended `LocalContext` with a local `let` binding. -/
def withLetDecl (userName : Ix.Name) (type val : Ix.Expr)
    (contract : Ixon.BinderContract := default)
    (letKind : Ixon.LetKind := .value)
    (nonDep : Bool := false)
    (k : Ix.Name → Ix.Expr → IxElabM α) : IxElabM α := do
  let fvarId ← mkFreshName "_fvar"
  let fvarExpr := Expr.mkFVar fvarId
  let decl : LocalDecl :=
    { fvarId, userName, type, value? := some val, contract, letKind? := some letKind, nonDep }
  fun ctx st =>
    match ctx with
    | ⟨lctx, scope, modIdx, currDecl?, univParams, refPos?⟩ =>
      match lctx.addDecl decl with
      | ⟨revDecls', byFVarId', byUserName'⟩ =>
        (k fvarId fvarExpr ⟨⟨revDecls', byFVarId', byUserName'⟩, scope, modIdx, currDecl?, univParams, refPos?⟩).run st

/-- Save and restore `ElabState` on failure (for backtracking typeclass synthesis or `try`). -/
def observing? (act : IxElabM α) : IxElabM (Option α) := fun ctx saved =>
  match (act ctx).run saved with
  | .ok (a, st') => .ok (some a, st')
  | .error _     => .ok (none, saved)

/-- Expand top-level declarative `MacroRule`s on `stx` up to `fuel` steps. -/
def expandMacroM (fuel : Nat) (stx : Ix.Syntax) : IxElabM Ix.Syntax := do
  let st ← get
  if st.env.macroRules.isEmpty then return stx
  else return expandTopMacroPure fuel st.env.macroRules stx

end Ix.Frontend.Elab
