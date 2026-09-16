module

public import Ix.Compile.SourceContract.Registry
public import Ix.SemanticContract

/-! Resolve occurrence contracts against the original source, then decorate
the corresponding binders before hashing, canonicalization, or sharing. -/

@[expose] public section

namespace Ix.Compile

def ResolvedBinderContract.semantic (binder : ResolvedBinderContract) :
    Ix.SemanticContract.Contract := {
  kind := match binder.kind with | .lam => .lam | .all => .all | .letE => .letE
  binder := ⟨binder.uses, binder.value⟩
  result := binder.result.getD .shared
  letKind := binder.letKind }

def decorateExpr (contract : ResolvedSourceContract) (root : SourceRoot)
    (path : List SourceStep) (expr : Lean.Expr) : Except String Lean.Expr := do
  let result ← do
    match expr with
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure expr
    | .fvar _ | .mvar _ => throw "source transport: open elaboration variable"
    | .app fn arg =>
      pure <| .app (← decorateExpr contract root (path ++ [.appFn]) fn)
        (← decorateExpr contract root (path ++ [.appArg]) arg)
    | .lam name type body info =>
      pure <| .lam name (← decorateExpr contract root (path ++ [.binderType]) type)
        (← decorateExpr contract root (path ++ [.binderBody]) body) info
    | .forallE name type body info =>
      pure <| .forallE name (← decorateExpr contract root (path ++ [.binderType]) type)
        (← decorateExpr contract root (path ++ [.binderBody]) body) info
    | .letE name type value body nonDep =>
      pure <| .letE name (← decorateExpr contract root (path ++ [.letType]) type)
        (← decorateExpr contract root (path ++ [.letValue]) value)
        (← decorateExpr contract root (path ++ [.letBody]) body) nonDep
    | .proj name field value =>
      pure <| .proj name field (← decorateExpr contract root (path ++ [.projection]) value)
    | .mdata data inner =>
      unless (Ix.SemanticContract.leanFields data).isEmpty do
        throw "source transport: reserved semantic metadata in unprocessed source"
      let data : Lean.MData := ⟨data.entries.filter fun (key, _) => !sourceAnnotationKey.isPrefixOf key⟩
      let inner ← decorateExpr contract root (path ++ [.metadata]) inner
      pure <| if data.entries.isEmpty then inner else .mdata data inner
  match contract.binders.find? (·.site == ⟨root, path⟩) with
  | none => return result
  | some binder =>
    let semantic := binder.semantic
    return if semantic.isOrdinary then result else semantic.attach result
termination_by sizeOf expr

def ResolvedSourceContract.decorate (contract : ResolvedSourceContract) :
    Except String Lean.ConstantInfo := do
  let source := contract.source
  let type ← decorateExpr contract .type [] source.type
  match source with
  | .defnInfo info =>
    return .defnInfo { info with type, value := ← decorateExpr contract .body [] info.value }
  | .thmInfo info =>
    return .thmInfo { info with type, value := ← decorateExpr contract .body [] info.value }
  | .opaqueInfo info =>
    return .opaqueInfo { info with type, value := ← decorateExpr contract .body [] info.value }
  | .axiomInfo info => return .axiomInfo { info with type }
  | _ => throw s!"source transport: annotated inductive/constructor/recursor transformations are unsupported: {source.name}"

def exprHasSemanticContracts (expr : Lean.Expr) : Bool :=
  (expr.find? fun
    | .mdata data _ => !(Ix.SemanticContract.leanFields data).isEmpty
    | _ => false).isSome

def sourceHasSemanticContracts (source : Lean.ConstantInfo) : Bool :=
  exprHasSemanticContracts source.type ||
    ((sourceBody? source).map exprHasSemanticContracts).getD false ||
    match source with
    | .recInfo info => info.rules.any (exprHasSemanticContracts ·.rhs)
    | _ => false

def ResolvedCompileInput.decorate (input : ResolvedCompileInput) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  input.constants.mapM fun (name, source) => do
    if sourceHasSemanticContracts source then
      throw s!"source transport: reserved semantic metadata in unprocessed source: {name}"
    match input.contracts.find? (·.source.name == name) with
    | none => return (name, source)
    | some contract => return (name, ← contract.decorate)

/-- Construct an explicit input from binder metadata when no external
registration table is available (for example, an isolated constant list). -/
def CompileInput.fromAnnotations (constants : List (Lean.Name × Lean.ConstantInfo)) :
    Except SourceContractError CompileInput := do
  let mut contracts := #[]
  for (_, source) in constants do
    if sourceHasAnnotations source then
      contracts := contracts.push (← SourceContract.fromAnnotations source)
  return { constants, contracts }

/-- Resolve and decorate once, before either compiler sees the source. -/
def CompileInput.prepare (input : CompileInput) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let resolved ← input.resolve.mapError toString
  resolved.decorate

def prepareSourceConstants (constants : List (Lean.Name × Lean.ConstantInfo)) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let input ← (CompileInput.fromAnnotations constants).mapError toString
  input.prepare

def prepareRegisteredConstants (env : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let input ← (compileInputFromEnv env constants).mapError toString
  input.prepare

end Ix.Compile

end
