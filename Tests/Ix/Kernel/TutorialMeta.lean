/-
  Meta infrastructure for kernel tutorial tests.
  Adapted from lean-kernel-arena tutorial/Tutorial/Meta.lean.

  Provides:
  - `good_def`, `bad_def`, `good_thm`, `bad_thm` command macros
  - `good_decl`, `bad_decl` for raw Declaration values
  - `good_raw_consts`, `bad_raw_consts` for directly inserting ConstantInfo
  - `good_consts`, `bad_consts` for referencing existing constants
  - `unchecked` term elaborator (bypasses type checking)
  - `addConstInfos` (bypasses kernel entirely for bad inductives)
  - Test case registry via env extension
-/
import Lean

open Lean Elab Term Command Meta
open Lean.Parser.Command

namespace Tests.Ix.Kernel.TutorialMeta

/-! ## Outcome and test case registry -/

inductive Outcome where | good | bad
  deriving Repr, BEq

structure TestCase where
  decls : Array Name
  outcome : Outcome
  renamings : Array (Name × Name) := #[]
  deriving Repr

instance : Inhabited TestCase where
  default := { decls := #[], outcome := .good }

/-- Persistent environment extension to accumulate test cases across module imports. -/
initialize testCasesExt : SimplePersistentEnvExtension TestCase (Array TestCase) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr tc => arr.push tc
    addImportedFn := fun arrs => Id.run do
      let mut result := #[]
      for arr in arrs do
        result := result ++ arr
      return result
  }

def registerTestCase (tc : TestCase) : CoreM Unit :=
  modifyEnv fun env => testCasesExt.addEntry env tc

def getTestCases (env : Environment) : Array TestCase :=
  testCasesExt.getState env

/-! ## Raw constant storage for inductives that can't go through the kernel -/

/-- Persistent extension to store raw ConstantInfos that bypass the kernel.
    These are collected by the test runner and passed to the Rust FFI separately. -/
initialize rawConstsExt : SimplePersistentEnvExtension ConstantInfo (Array ConstantInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr ci => arr.push ci
    addImportedFn := fun arrs => Id.run do
      let mut result := #[]
      for arr in arrs do
        result := result ++ arr
      return result
  }

def registerRawConst (ci : ConstantInfo) : CoreM Unit :=
  modifyEnv fun env => rawConstsExt.addEntry env ci

def getRawConsts (env : Environment) : Array ConstantInfo :=
  rawConstsExt.getState env

/-- Insert ConstantInfos, using addDecl where possible and raw storage otherwise. -/
def addConstInfos (cis : Array Lean.ConstantInfo) : CoreM Unit := do
  for ci in cis do
    match ci with
    | .axiomInfo v =>
      withOptions (fun o => debug.skipKernelTC.set o true) do addDecl (.axiomDecl v)
    | .defnInfo v =>
      withOptions (fun o => debug.skipKernelTC.set o true) do addDecl (.defnDecl v)
    | .thmInfo v =>
      withOptions (fun o => debug.skipKernelTC.set o true) do addDecl (.thmDecl v)
    | .opaqueInfo v =>
      withOptions (fun o => debug.skipKernelTC.set o true) do addDecl (.opaqueDecl v)
    | _ =>
      -- inductInfo, ctorInfo, recInfo, quotInfo: can't go through addDecl.
      -- Store in raw extension for the test runner to collect.
      registerRawConst ci

/-! ## unchecked term elaborator -/

syntax (name := unchecked) "unchecked" term : term

@[term_elab «unchecked»]
def elabUnchecked : TermElab := fun stx expectedType? => do
  match stx with
  | `(unchecked $t) =>
    let some expectedType := expectedType? |
      tryPostpone
      throwError "invalid 'unchecked', expected type required"
    let e ← elabTerm t none
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    mvar.mvarId!.assign e
    return mvar
  | _ => throwUnsupportedSyntax

/-! ## Core helpers -/

def addTestCaseDeclCore (decl : Lean.Declaration) (outcome : Outcome) (skipTC := false) : CoreM Unit := do
  match skipTC, outcome with
  | false, .good => addDecl decl
  | _, _ =>
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl decl
  registerTestCase { decls := decl.getNames.toArray, outcome }

def addTestCaseDecl (declName : Name) (levelParams : List Name) (typeExpr valueExpr : Expr)
    (outcome : Outcome) (declKind : ConstantKind) (skipTC := false) : CoreM Unit := do
  let decl ← match declKind with
    | .defn => pure <| .defnDecl {
        name := declName, levelParams, type := typeExpr, value := valueExpr,
        hints := .opaque, safety := .safe
      }
    | .thm => pure <| .thmDecl {
        name := declName, levelParams, type := typeExpr, value := valueExpr
      }
    | _ => throwError "Unsupported declaration kind: {repr declKind}"
  addTestCaseDeclCore decl outcome (skipTC := skipTC)

open TSyntax.Compat in
def elabAndAddTestCaseDecl (name : TSyntax ``declId) (type value : Term) (outcome : Outcome)
    (declKind : ConstantKind) (skipTC := false) : CommandElabM Unit := liftTermElabM do
  let (declName, lparams) ← match name with
    | `(declId| $n:ident) => pure (n.getId, [])
    | `(declId| $n:ident .{ $[$ls:ident],* }) => pure (n.getId, ls.toList.map (·.getId))
    | _ => throwUnsupportedSyntax
  withLevelNames lparams do
    let typeExpr ← elabTermAndSynthesize type none
    let valueExpr ← elabTermAndSynthesize value (some typeExpr)
    synthesizeSyntheticMVarsNoPostponing
    let typeExpr ← instantiateMVars typeExpr
    let valueExpr ← instantiateMVars valueExpr
    addTestCaseDecl declName lparams typeExpr valueExpr outcome declKind (skipTC := skipTC)

/-! ## Command macros -/

elab "good_def " name:declId ":" type:term ":=" value:term : command =>
  elabAndAddTestCaseDecl name type value .good .defn

elab "bad_def " name:declId ":" type:term ":=" value:term : command =>
  elabAndAddTestCaseDecl name type value .bad .defn

elab "good_thm " name:declId ":" type:term ":=" value:term : command =>
  elabAndAddTestCaseDecl name type value .good .thm

elab "bad_thm " name:declId ":" type:term ":=" value:term : command =>
  elabAndAddTestCaseDecl name type value .bad .thm

open TSyntax.Compat in
def elabRawTestDecl (decl : Term) (outcome : Outcome) : CommandElabM Unit := liftTermElabM do
  let expectedType := Lean.mkConst ``Lean.Declaration
  let declExpr ← elabTerm decl (some expectedType)
  synthesizeSyntheticMVarsNoPostponing
  let declExpr ← instantiateMVars declExpr
  let decl ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Lean.Declaration) expectedType declExpr
  addTestCaseDeclCore decl outcome

elab "good_decl " decl:term : command => elabRawTestDecl decl .good
elab "bad_decl " decl:term : command => elabRawTestDecl decl .bad

open TSyntax.Compat in
def elabRawTestCIs (cis : Term) (outcome : Outcome) : CommandElabM Unit := liftTermElabM do
  let expectedType := mkApp (Lean.mkConst ``Array [0]) (Lean.mkConst ``Lean.ConstantInfo)
  let cisExpr ← elabTerm cis (some expectedType)
  let cisExpr ← instantiateMVars cisExpr
  synthesizeSyntheticMVarsNoPostponing
  let cis ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Array Lean.ConstantInfo) expectedType cisExpr
  addConstInfos cis
  registerTestCase { decls := cis.map (·.name), outcome }

elab "good_raw_consts " ci:term : command => elabRawTestCIs ci .good
elab "bad_raw_consts " ci:term : command => elabRawTestCIs ci .bad

def elabTestConsts (names : Term) (outcome : Outcome) (renamingsTerm? : Option Term := none) : CommandElabM Unit := liftTermElabM do
  let expectedType := mkApp (Lean.mkConst ``Array [0]) (Lean.mkConst ``Lean.Name)
  let namesExpr ← elabTerm names (some expectedType)
  let namesExpr ← instantiateMVars namesExpr
  let nameVals ← Lean.Meta.MetaM.run' <| unsafe Meta.evalExpr (α := Array Lean.Name) expectedType namesExpr
  let cis ← nameVals.mapM Lean.getConstInfo
  let renamingsArr ← match renamingsTerm? with
    | some renamingsTerm =>
      let nameType := Lean.mkConst ``Name
      let pairType := mkApp2 (Lean.mkConst ``Prod [0, 0]) nameType nameType
      let renamingsType := mkApp (Lean.mkConst ``Array [0]) pairType
      let renamingsExpr ← elabTerm renamingsTerm (some renamingsType)
      let renamingsExpr ← instantiateMVars renamingsExpr
      synthesizeSyntheticMVarsNoPostponing
      Lean.Meta.MetaM.run' <|
        unsafe Meta.evalExpr (α := Array (Name × Name)) renamingsType renamingsExpr
    | none => pure #[]
  registerTestCase { decls := cis.map (·.name), outcome, renamings := renamingsArr }

syntax (name := goodConsts) "good_consts " term (" renaming " term)? : command
syntax (name := badConsts) "bad_consts " term (" renaming " term)? : command

private def elabConstsCmd (outcome : Outcome) : CommandElab := fun stx => do
  let names : Term := ⟨stx[1]⟩
  let renamingsTerm? : Option Term :=
    if stx[2].isNone then none else some ⟨stx[2][1]⟩
  elabTestConsts names outcome renamingsTerm?

@[command_elab goodConsts] def elabGoodConsts : CommandElab := elabConstsCmd .good
@[command_elab badConsts] def elabBadConsts : CommandElab := elabConstsCmd .bad

/-! ## Expression helpers -/

def arrow (dom codom : Expr) (n := `x) : Expr :=
  Lean.mkForall n BinderInfo.default dom codom

def dummyRecInfo (indName : Lean.Name) : Lean.ConstantInfo :=
  .recInfo {
    name := indName ++ `rec, levelParams := [], type := .sort 0,
    all := [indName], numParams := 0, numIndices := 0,
    numMotives := 0, numMinors := 0, rules := [], k := false, isUnsafe := false
  }

end Tests.Ix.Kernel.TutorialMeta
