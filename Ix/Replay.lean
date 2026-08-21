/-
  `Ix.Replay`: kernel replay planning over plain constant maps.

  Reconstructs the kernel `Declaration`s that produce a set of
  `ConstantInfo`s and orders them topologically, so callers can replay
  them through `Lean.Kernel.Environment.addDecl` / `Lean.addDecl` in
  dependency order. Pure planning — no kernel interaction here.

  Shared by `import_ixe` materialization (`Ix/ImportIxe.lean`), the
  `#ixeval` closure walk (`Ix/IxEval.lean`), and tests. Also home to
  the reference-collection helpers (`expressionReferences`,
  `constantInfoReferences`) — the closure substrate the planner and
  its callers share — and `renderKernelException` for uniform replay
  diagnostics.

  Note on qualification: bare `Expr`/`Name`/`ConstantInfo` inside the
  `Ix` namespace resolve to ix's own mirror types, so Lean's are
  `Lean.`-qualified explicitly throughout (repo convention).
-/
module

public import Lean

public section

namespace Ix.Replay

/-! ## Reference collection -/

private unsafe structure ExpressionReferenceState where
  visited : Lean.PtrSet Lean.Expr := Lean.mkPtrSet
  references : Lean.NameSet := {}

private unsafe abbrev ExpressionReferenceM := StateM ExpressionReferenceState

private unsafe def expressionReferencesUnsafe (expr : Lean.Expr) :
    Lean.NameSet :=
  let rec visit (expr : Lean.Expr) : ExpressionReferenceM Unit := do
    if (← get).visited.contains expr then return
    modify fun state => { state with visited := state.visited.insert expr }
    match expr with
    | .forallE _ domain body _ | .lam _ domain body _ =>
      visit domain
      visit body
    | .mdata _ body => visit body
    | .letE _ type value body _ =>
      visit type
      visit value
      visit body
    | .app fn arg =>
      visit fn
      visit arg
    | .proj typeName _ value =>
      modify fun state => {
        state with references := state.references.insert typeName }
      visit value
    | .const name _ =>
      modify fun state => {
        state with references := state.references.insert name }
    | _ => pure ()
  (do
    visit expr
    return (← get).references : ExpressionReferenceM Lean.NameSet).run' {}

@[implemented_by expressionReferencesUnsafe]
private opaque expressionReferencesImpl (_expr : Lean.Expr) : Lean.NameSet :=
  {}

/-- All constant references of an expression, including `Expr.proj`
    structure names, with pointer-cached DAG traversal. -/
def expressionReferences (expr : Lean.Expr) : Lean.NameSet :=
  expressionReferencesImpl expr

def constantInfoReferences (info : Lean.ConstantInfo) : Lean.NameSet :=
  let result := expressionReferences info.type
  match info.value? (allowOpaque := true) with
  | some value => expressionReferences value ++ result
  | none => match info with
    | .inductInfo val => result ++ Lean.NameSet.ofList val.ctors
    | .ctorInfo val => result.insert val.name
    | .recInfo val => result ++ Lean.NameSet.ofList val.all
    | _ => result

/-! ## Replay planning -/

/-- Accept a `DefinitionVal.all` list as unsafe-mutual grouping metadata
    only when every member is an owned definition carrying the same
    list — code-generating metaprograms may copy a recursor's `all` into
    an unrelated definition. -/
def definitionWorkGroup (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) (val : Lean.DefinitionVal) : List Lean.Name :=
  Id.run do
    if val.safety == .safe || !val.all.contains name then
      return [name]
    for member in val.all do
      match owned.find? member with
      | some (.defnInfo memberVal) =>
        unless memberVal.safety == val.safety && memberVal.all == val.all do
          return [name]
      | _ => return [name]
    return val.all

/-- The replay-work key that produces `name`: inductive blocks key on
    `all.head`, constructors and recursors on their block's key, unsafe
    mutual definitions on the group head; everything else is its own
    item. -/
def canonicalWorkKey (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) : Lean.Name :=
  match owned.find? name with
  | some (.inductInfo val) => val.all.head?.getD name
  | some (.ctorInfo val) =>
      match owned.find? val.induct with
      | some (.inductInfo inductiveVal) =>
          inductiveVal.all.head?.getD val.induct
      | _ => val.induct
  | some (.recInfo val) => val.all.head?.getD name
  | some (.defnInfo val) => (definitionWorkGroup owned name val).head?.getD name
  | _ => name

private def sourceInductiveDeclaration
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (val : Lean.InductiveVal) :
    Except String Lean.Declaration := do
  let mut types : List Lean.InductiveType := []
  for typeName in val.all do
    let some (.inductInfo typeVal) := owned.find? typeName
      | throw s!"missing inductive `{typeName}` from mutual block rooted at `{val.name}`"
    let mut ctors : List Lean.Constructor := []
    for ctorName in typeVal.ctors do
      let some (.ctorInfo ctorVal) := find? ctorName
        | throw s!"missing constructor `{ctorName}` for inductive `{typeName}`"
      ctors := ctors.concat { name := ctorName, type := ctorVal.type }
    types := types.concat { name := typeName, type := typeVal.type, ctors }
  return .inductDecl val.levelParams val.numParams types val.isUnsafe

/-- The `Declaration` that replays `info`, or `none` when the constant
    is produced by another work item (constructors, recursors, non-head
    inductive/mutual members) or by the base env (`Quot`). `find?`
    resolves constructor lookups (callers back it by the source
    environment or the materialized constant map). -/
private def sourceDeclaration?
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (name : Lean.Name)
    (info : Lean.ConstantInfo) : Except String (Option Lean.Declaration) := do
  match info with
  | .axiomInfo val => return some (.axiomDecl val)
  | .defnInfo val =>
      if val.safety != .safe then
        let group := definitionWorkGroup owned name val
        if group.head? != some name then return none
        let mut vals : List Lean.DefinitionVal := []
        for defName in group do
          let some (.defnInfo defVal) := owned.find? defName
            | throw s!"missing definition `{defName}` from mutual block rooted at `{name}`"
          vals := vals.concat defVal
        return some (.mutualDefnDecl vals)
      else
        return some (.defnDecl val)
  | .thmInfo val => return some (.thmDecl val)
  | .opaqueInfo val => return some (.opaqueDecl val)
  | .inductInfo val =>
      if val.all.head? == some name then
        return some (← sourceInductiveDeclaration find? owned val)
      else
        return none
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return none

def renderKernelException : Lean.Kernel.Exception → String
  | .unknownConstant _ n => s!"unknown constant `{n}`"
  | .alreadyDeclared _ n => s!"`{n}` already declared"
  | .declTypeMismatch _ _ _ => "declaration type mismatch"
  | .declHasMVars _ n _ => s!"`{n}` has metavariables"
  | .declHasFVars _ n _ => s!"`{n}` has free variables"
  | .funExpected _ _ _ => "function expected"
  | .typeExpected _ _ _ => "type expected"
  | .letTypeMismatch _ _ n _ _ => s!"let type mismatch at `{n}`"
  | .exprTypeMismatch _ _ _ _ => "expression type mismatch"
  | .appTypeMismatch _ _ _ _ _ => "application type mismatch"
  | .invalidProj _ _ _ => "invalid projection"
  | .thmTypeIsNotProp _ n _ => s!"theorem type of `{n}` is not a Prop"
  | .other msg => msg
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .interrupted => "interrupted"

private structure WorkItem where
  key : Lean.Name
  decl : Lean.Declaration
  deps : Lean.NameSet

/-- Reconstruct the kernel `Declaration`s that replay `owned` and order
    them topologically (Kahn's algorithm, name-sorted ready sets for
    determinism). Pure planning — no kernel interaction; dependencies
    outside `owned` are assumed satisfied by the caller's base
    environment. `find?` resolves constructor lookups during inductive
    reconstruction. Shared by `import_ixe` materialization
    (`Ix/ImportIxe.lean`) and the catalog replay driver. -/
def planDeclarations (owned : Lean.NameMap Lean.ConstantInfo)
    (find? : Lean.Name → Option Lean.ConstantInfo) :
    Except String (Array (Lean.Name × Lean.Declaration)) := do
  -- Work items keyed by canonical head, with owned-only dependencies.
  let mut producedBy : Lean.NameMap Lean.Name := {}
  let mut membersOfKey : Lean.NameMap (Array Lean.Name) := {}
  for (name, _) in owned do
    let key := canonicalWorkKey owned name
    producedBy := producedBy.insert name key
    membersOfKey := membersOfKey.insert key
      ((membersOfKey.find? key).getD #[] |>.push name)
  let mut items : Lean.NameMap WorkItem := {}
  for (name, info) in owned do
    let some decl ← sourceDeclaration? find? owned name info | continue
    let key := name
    -- Dependencies: references of every constant this item produces,
    -- mapped to their producing items.
    let mut deps : Lean.NameSet := {}
    for member in (membersOfKey.find? key).getD #[] do
      let some memberInfo := owned.find? member | continue
      for reference in constantInfoReferences memberInfo do
        match producedBy.find? reference with
        | some refKey => if refKey != key then deps := deps.insert refKey
        | none => pure ()
    items := items.insert key { key, decl, deps }
  -- Kahn's algorithm with name-sorted ready set for determinism.
  let mut plan : Array (Lean.Name × Lean.Declaration) := #[]
  let mut added : Lean.NameSet := {}
  let mut pending := items
  while !pending.isEmpty do
    let mut ready : Array WorkItem := #[]
    for (_, item) in pending do
      if item.deps.all (added.contains ·) then
        ready := ready.push item
    if ready.isEmpty then
      let cycle := pending.foldl (init := #[]) fun acc k _ => acc.push k
      throw s!"dependency cycle among replay items: {cycle[0:8].toArray}"
    let readySorted := ready.qsort fun a b => a.key.quickCmp b.key == .lt
    for item in readySorted do
      plan := plan.push (item.key, item.decl)
      added := added.insert item.key
      pending := pending.erase item.key
  return plan

end Ix.Replay
