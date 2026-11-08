/-
  Ix.Frontend.AuxGen: Surgery-Free Auxiliary Definition Generator for the Ix Frontend.

  Because the Ix Frontend canonicalizes mutual inductive blocks and constructor
  orders BEFORE generating recursors and auxiliary definitions (`Ix.Frontend.CanonBlock`),
  all generated auxiliaries (`.rec`, `.recOn`, `.casesOn`, `._ctorIdx`, and structure
  field projections) are constructed directly in canonical constructor order with
  zero post-hoc environment surgery!
-/
module

public import Ix.Frontend.CanonBlock

@[expose] public section

namespace Ix.Frontend.AuxGen

open Ix.Frontend
open Ix.Frontend.Elab

/-! ## Telescope Opening & Closing Helpers (Pure FVar Space) -/

/-- A local binder declaration in pure FVar space for `AuxGen`. -/
structure AuxLocalDecl where
  fvarId     : Ix.Name
  binderName : Ix.Name
  domain     : Ix.Expr
  binderInfo : Lean.BinderInfo := .default
  deriving Repr

instance : Inhabited AuxLocalDecl where
  default := {
    fvarId     := Name.mkAnon
    binderName := Name.mkAnon
    domain     := Expr.mkBVar 0
    binderInfo := .default
  }

/-- Create a deterministic fresh FVar `(fvarId, Expr.mkFVar fvarId)`. -/
def mkAuxFVar (pfx : String) (idx : Nat) : Ix.Name × Ix.Expr :=
  let id := Name.mkStr Name.mkAnon s!"_{pfx}_{idx}"
  (id, Expr.mkFVar id)

/-- Peel up to `maxBinders` leading `.forallE` binders of `e`, substituting fresh FVars
    with prefix `pfx` starting at `startIdx`. Returns `(fvars, decls, remainingBody)`. -/
def openForallTelescope : Nat → Ix.Expr → String → Nat → Array Ix.Expr → Array AuxLocalDecl →
    Array Ix.Expr × Array AuxLocalDecl × Ix.Expr
  | 0, e, _, _, fvars, decls => (fvars, decls, e)
  | n + 1, e, pfx, idx, fvars, decls =>
    match stripMData e with
    | .forallE nm dom body bi _ =>
      let (fvId, fvExpr) := mkAuxFVar pfx idx
      let bodyInst := instantiate1 body fvExpr
      let decl : AuxLocalDecl := { fvarId := fvId, binderName := nm, domain := dom, binderInfo := bi }
      openForallTelescope n bodyInst pfx (idx + 1) (fvars.push fvExpr) (decls.push decl)
    | _ => (fvars, decls, e)

/-- Count total leading `.forallE` binders of `e` (bounded by 256). -/
def countForalls : Nat → Ix.Expr → Nat
  | 0, _ => 0
  | fuel + 1, e =>
    match stripMData e with
    | .forallE _ _ body _ _ => 1 + countForalls fuel body
    | _ => 0

/-- Close an expression `body` over `decls` into nested `.forallE` binders. -/
def closeForalls (decls : Array AuxLocalDecl) (body : Ix.Expr) : Ix.Expr :=
  decls.foldr (fun d acc =>
    let bName := if Name.isAnonymous d.binderName then Name.simple "x" else d.binderName
    Expr.mkForallE bName d.domain (abstractFVar d.fvarId acc) d.binderInfo) body

/-- Close an expression `body` over `decls` into nested `.lam` binders. -/
def closeLambdas (decls : Array AuxLocalDecl) (body : Ix.Expr) : Ix.Expr :=
  decls.foldr (fun d acc =>
    let bName := if Name.isAnonymous d.binderName then Name.simple "x" else d.binderName
    Expr.mkLam bName d.domain (abstractFVar d.fvarId acc) d.binderInfo) body

/-! ## Recursor (`.rec`) Generation Over Canonical Inductive Blocks -/

/-- Check if `fieldDom` is a recursive occurrence of one of the inductive types in `indNames`:
    either direct `I params idxArgs...` or functional `(a₁ : A₁) → ... → I params idxArgs...`.
    Returns `some (indIdx, argDecls, idxArgs)` when recursive. -/
def analyzeRecursiveField (indNames : Array Ix.Name) (numParams : Nat)
    (fieldDom : Ix.Expr) (pfx : String) : Option (Nat × Array AuxLocalDecl × Array Ix.Expr) :=
  let nBinders := countForalls 64 fieldDom
  let (_, argDecls, retTy) := openForallTelescope nBinders fieldDom pfx 0 #[] #[]
  let (headFn, headArgs) := getAppFnArgs retTy
  match headFn with
  | .const nm _ _ =>
    match indNames.idxOf? nm with
    | some indIdx =>
      if headArgs.size ≥ numParams then
        let idxArgs := headArgs.extract numParams headArgs.size
        some (indIdx, argDecls, idxArgs)
      else none
    | none => none
  | _ => none

/-- Generate the canonical recursor (`Ix.RecursorVal`) for target inductive `targetIdx`
    in a canonicalized mutual inductive block `items : Array (Ix.InductiveVal × Array Ix.ConstructorVal)`. -/
def generateBlockRecursor (items : Array (Ix.InductiveVal × Array Ix.ConstructorVal))
    (targetIdx : Nat) : Option Ix.RecursorVal := do
  let (targetInd, _) ← items[targetIdx]?
  let firstInd := (items.getD 0 (targetInd, #[])).1
  let indNames : Array Ix.Name := items.map (·.1.cnst.name)
  let nMotives := items.size
  let nParams := targetInd.numParams
  let baseLevelParams := firstInd.cnst.levelParams
  let indUnivs : Array Ix.Level := baseLevelParams.map Level.mkParam

  -- Peel `nParams` parameters from `targetInd.cnst.type`
  let (paramFVars, paramDecls, afterParams) :=
    openForallTelescope nParams targetInd.cnst.type "p" 0 #[] #[]
  let paramDeclsImplicit := paramDecls.map fun d => { d with binderInfo := .implicit }

  -- Determine universe level of the inductive's resulting Sort
  let (_, _, targetSortExpr) := openForallTelescope targetInd.numIndices afterParams "i_tmp" 0 #[] #[]
  let indSortLvl : Ix.Level := match stripMData targetSortExpr with
    | .sort u _ => u
    | _         => Level.mkSucc Level.mkZero
  let isPropInd : Bool := match indSortLvl with
    | .zero _ => true
    | _       => false

  -- Prop inductives with > 1 constructor eliminate only into `Prop` (`Level.mkZero`),
  -- while `Type`-valued inductives (and singleton/empty `Prop` inductives like `Eq`, `True`, `False`, `And`)
  -- eliminate into an arbitrary motive sort `Sort u_motive`!
  let totalCtors := items.foldl (fun acc (_, cs) => acc + cs.size) 0
  let elimIntoAnySort : Bool := !isPropInd || totalCtors ≤ 1
  let uMotiveName : Ix.Name :=
    let base := Name.simple "u_motive"
    if baseLevelParams.contains base then Name.simple "u_motive_1" else base
  let recLevelParams : Array Ix.Name :=
    if elimIntoAnySort then #[uMotiveName] ++ baseLevelParams else baseLevelParams
  let motiveSort : Ix.Expr :=
    if elimIntoAnySort then Expr.mkSort (Level.mkParam uMotiveName) else Expr.mkProp

  -- Build Motive declarations `motive_0, ..., motive_{nMotives - 1}`
  let mut motiveFVars : Array Ix.Expr := #[]
  let mut motiveDecls : Array AuxLocalDecl := #[]
  for ((iv, _), mIdx) in items.zipIdx do
    let ivAfterParams := paramFVars.foldl (fun cur p =>
      match stripMData cur with
      | .forallE _ _ b _ _ => instantiate1 b p
      | other => other) iv.cnst.type
    let (idxFVars, idxDecls, _) :=
      openForallTelescope iv.numIndices ivAfterParams s!"midx_{mIdx}" 0 #[] #[]
    let indApp := Expr.mkAppN (Expr.mkConst iv.cnst.name indUnivs) (paramFVars ++ idxFVars)
    let (majId, _) := mkAuxFVar s!"mmaj_{mIdx}" 0
    let majDecl : AuxLocalDecl :=
      { fvarId := majId, binderName := Name.simple "t", domain := indApp, binderInfo := .default }
    let motiveDom := closeForalls (idxDecls.push majDecl) motiveSort
    let motiveName := if nMotives == 1 then Name.simple "motive" else Name.simple s!"motive_{mIdx + 1}"
    let (mFvId, mFvExpr) := mkAuxFVar "motive" mIdx
    motiveFVars := motiveFVars.push mFvExpr
    motiveDecls := motiveDecls.push
      { fvarId := mFvId, binderName := motiveName, domain := motiveDom, binderInfo := .implicit }

  -- Build Minor premise declarations and RecursorRules across all constructors in canonical order
  let mut minorFVars : Array Ix.Expr := #[]
  let mut minorDecls : Array AuxLocalDecl := #[]
  let mut minorByCtor : NameMap (Ix.Expr × Array (Option (Nat × Array AuxLocalDecl × Array Ix.Expr))) := NameMap.empty
  let mut minorCounter : Nat := 0

  for ((_, ctors), mIdx) in items.zipIdx do
    let motiveFVar := motiveFVars.getD mIdx (Expr.mkBVar 0)
    for ctor in ctors do
      -- Substitute `paramFVars` for the first `nParams` binders of `ctor.cnst.type`
      let ctorAfterParams := paramFVars.foldl (fun cur p =>
        match stripMData cur with
        | .forallE _ _ b _ _ => instantiate1 b p
        | other => other) ctor.cnst.type
      let (fieldFVars, fieldDecls, ctorRetTy) :=
        openForallTelescope ctor.numFields ctorAfterParams s!"cf_{minorCounter}" 0 #[] #[]
      -- Analyze each field for recursive occurrences to synthesize Inductive Hypotheses (IHs)
      let mut ihDecls : Array AuxLocalDecl := #[]
      let mut fieldRecSpecs : Array (Option (Nat × Array AuxLocalDecl × Array Ix.Expr)) := #[]
      for (fDecl, fIdx) in fieldDecls.zipIdx do
        let fVar := fieldFVars.getD fIdx (Expr.mkBVar 0)
        match analyzeRecursiveField indNames nParams fDecl.domain s!"iharg_{minorCounter}_{fIdx}" with
        | some (recIndIdx, argDecls, idxArgs) =>
          let recMotive := motiveFVars.getD recIndIdx motiveFVar
          let argFVars := argDecls.map fun d => Expr.mkFVar d.fvarId
          let appliedField := Expr.mkAppN fVar argFVars
          let ihTarget := Expr.mkAppN recMotive (idxArgs.push appliedField)
          let ihDom := closeForalls argDecls ihTarget
          let ihName := match fDecl.binderName with
            | .str _ s _ => Name.simple s!"{s}_ih"
            | _          => Name.simple s!"ih_{fIdx}"
          let (ihFvId, _) := mkAuxFVar s!"ih_{minorCounter}" fIdx
          ihDecls := ihDecls.push
            { fvarId := ihFvId, binderName := ihName, domain := ihDom, binderInfo := .default }
          fieldRecSpecs := fieldRecSpecs.push (some (recIndIdx, argDecls, idxArgs))
        | none =>
          fieldRecSpecs := fieldRecSpecs.push none
      -- Extract index arguments from `ctorRetTy = I params idxArgs...`
      let (_, ctorRetArgs) := getAppFnArgs ctorRetTy
      let ctorIdxArgs := ctorRetArgs.extract nParams ctorRetArgs.size
      let ctorValApp := Expr.mkAppN (Expr.mkConst ctor.cnst.name indUnivs) (paramFVars ++ fieldFVars)
      let minorRet := Expr.mkAppN motiveFVar (ctorIdxArgs.push ctorValApp)
      let minorDom := closeForalls (fieldDecls ++ ihDecls) minorRet
      let minorBinderName := match ctor.cnst.name with
        | .str _ s _ => Name.simple s
        | other      => other
      let (minFvId, minFvExpr) := mkAuxFVar "minor" minorCounter
      minorFVars := minorFVars.push minFvExpr
      minorDecls := minorDecls.push
        { fvarId := minFvId, binderName := minorBinderName, domain := minorDom, binderInfo := .default }
      minorByCtor := minorByCtor.insert ctor.cnst.name (minFvExpr, fieldRecSpecs)
      minorCounter := minorCounter + 1

  -- Build target indices and major premise for `targetInd`
  let targetAfterParams := paramFVars.foldl (fun cur p =>
    match stripMData cur with
    | .forallE _ _ b _ _ => instantiate1 b p
    | other => other) targetInd.cnst.type
  let (targetIdxFVars, targetIdxDecls, _) :=
    openForallTelescope targetInd.numIndices targetAfterParams "tidx" 0 #[] #[]
  let targetIdxDeclsImplicit := targetIdxDecls.map fun d => { d with binderInfo := .implicit }
  let majorDom := Expr.mkAppN (Expr.mkConst targetInd.cnst.name indUnivs) (paramFVars ++ targetIdxFVars)
  let (majFvId, majFvExpr) := mkAuxFVar "major" 0
  let majorDecl : AuxLocalDecl :=
    { fvarId := majFvId, binderName := Name.simple "t", domain := majorDom, binderInfo := .default }

  let targetMotive := motiveFVars.getD targetIdx (Expr.mkBVar 0)
  let recReturn := Expr.mkAppN targetMotive (targetIdxFVars.push majFvExpr)
  let allRecDecls := paramDeclsImplicit ++ motiveDecls ++ minorDecls ++ targetIdxDeclsImplicit ++ #[majorDecl]
  let recType := closeForalls allRecDecls recReturn

  -- Build `RecursorRule`s for `targetInd`'s constructors
  let (_, targetCtors) := items.getD targetIdx (targetInd, #[])
  let recUnivArgs : Array Ix.Level := recLevelParams.map Level.mkParam
  let mut rules : Array Ix.RecursorRule := #[]
  for ctor in targetCtors do
    let (minorFv, fieldRecSpecs) ← minorByCtor.get? ctor.cnst.name
    let ctorAfterParams := paramFVars.foldl (fun cur p =>
      match stripMData cur with
      | .forallE _ _ b _ _ => instantiate1 b p
      | other => other) ctor.cnst.type
    let (fieldFVars, fieldDecls, _) :=
      openForallTelescope ctor.numFields ctorAfterParams s!"rf_{ctor.cidx}" 0 #[] #[]
    let mut ihExprs : Array Ix.Expr := #[]
    for (spec?, fIdx) in fieldRecSpecs.zipIdx do
      match spec? with
      | none => pure ()
      | some (recIndIdx, argDecls, idxArgs) =>
        let (recIndVal, _) := items.getD recIndIdx (targetInd, #[])
        let recName := Name.mkStr recIndVal.cnst.name "rec"
        let recConst := Expr.mkConst recName recUnivArgs
        let fVar := fieldFVars.getD fIdx (Expr.mkBVar 0)
        let argFVars := argDecls.map fun d => Expr.mkFVar d.fvarId
        let appliedField := Expr.mkAppN fVar argFVars
        let recCall := Expr.mkAppN recConst
          (paramFVars ++ motiveFVars ++ minorFVars ++ idxArgs ++ #[appliedField])
        let ihLam := closeLambdas argDecls recCall
        ihExprs := ihExprs.push ihLam
    let ruleBody := Expr.mkAppN minorFv (fieldFVars ++ ihExprs)
    let ruleLamDecls :=
      (paramDeclsImplicit ++ motiveDecls ++ minorDecls ++ fieldDecls).map fun d =>
        { d with binderInfo := .default }
    let rhs := closeLambdas ruleLamDecls ruleBody
    rules := rules.push { ctor := ctor.cnst.name, nfields := ctor.numFields, rhs }

  let isK : Bool :=
    match targetCtors[0]? with
    | some c0 => isPropInd && targetCtors.size == 1 && c0.numFields == 0 && targetInd.numIndices > 0
    | none    => false

  let recName := Name.mkStr targetInd.cnst.name "rec"
  return {
    cnst := {
      name        := recName
      levelParams := recLevelParams
      type        := recType
    }
    all        := indNames
    numParams  := nParams
    numIndices := targetInd.numIndices
    numMotives := nMotives
    numMinors  := minorDecls.size
    rules      := rules
    k          := isK
    isUnsafe   := targetInd.isUnsafe
  }

/-! ## `.recOn` Generation -/

/-- Generate `<Ind>.recOn` by reordering `.rec` binders from
    `[params, motives, minors, indices, major]` to `[params, motives, indices, major, minors]`. -/
def generateRecOn (indName : Ix.Name) (recVal : Ix.RecursorVal) : Option Ix.DefinitionVal := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices
  let acSize := nParams + nMotives
  let total := acSize + nMinors + nIndices + 1

  let (fvars, decls, body) := openForallTelescope total recVal.cnst.type "ro" 0 #[] #[]
  if fvars.size < total then none
  else
    let recUnivs := recVal.cnst.levelParams.map Level.mkParam
    let recApp := Expr.mkAppN (Expr.mkConst recVal.cnst.name recUnivs) fvars
    let reordered : Array AuxLocalDecl :=
      decls.extract 0 acSize ++
      decls.extract (acSize + nMinors) total ++
      decls.extract acSize (acSize + nMinors)
    let recOnType := closeForalls reordered body
    let recOnValue := closeLambdas reordered recApp
    let recOnName := Name.mkStr indName "recOn"
    some {
      cnst := {
        name        := recOnName
        levelParams := recVal.cnst.levelParams
        type        := recOnType
      }
      value  := recOnValue
      hints  := .abbrev
      safety := if recVal.isUnsafe then .unsafe else .safe
      all    := #[recOnName]
    }

/-! ## `.casesOn` Generation (Single & Mutual Inductives) -/

/-- Generate `<Ind>.casesOn` (eliminator without inductive hypotheses, with
    indices and major premise placed before the minor premises). -/
def generateCasesOn (indVal : Ix.InductiveVal) (ctors : Array Ix.ConstructorVal)
    (recVal : Ix.RecursorVal) : Option Ix.DefinitionVal := do
  -- Only single-motive inductives use the direct `casesOn` construction here
  if recVal.numMotives != 1 then none
  else
    let nParams := recVal.numParams
    let nMinors := ctors.size
    let nIndices := recVal.numIndices
    let acSize := nParams + 1
    let total := acSize + nMinors + nIndices + 1
    let (recFVars, recDecls, recBody) := openForallTelescope total recVal.cnst.type "co" 0 #[] #[]
    if recFVars.size < total then none
    else
      let paramDecls := recDecls.extract 0 nParams
      let motiveDecl := recDecls.getD nParams default
      let recMinorDecls := recDecls.extract acSize (acSize + nMinors)
      let indexAndMajorDecls := recDecls.extract (acSize + nMinors) total

      let paramFVars := recFVars.extract 0 nParams
      let motiveFVar := recFVars.getD nParams (Expr.mkBVar 0)
      let indexAndMajorFVars := recFVars.extract (acSize + nMinors) total

      -- For each constructor `i`, strip any trailing IH binders from `recMinorDecls[i].domain`
      -- keeping only the first `ctors[i].numFields` field binders!
      let mut coMinorDecls : Array AuxLocalDecl := #[]
      let mut recMinorArgs : Array Ix.Expr := #[]
      for (ctor, i) in ctors.zipIdx do
        let rMinorDecl := recMinorDecls.getD i default
        let nAllMinorBinders := countForalls 64 rMinorDecl.domain
        let (allFieldFVars, allFieldDecls, minorRet) :=
          openForallTelescope nAllMinorBinders rMinorDecl.domain s!"cof_{i}" 0 #[] #[]
        let nonIhDecls := allFieldDecls.extract 0 ctor.numFields
        let nonIhFVars := allFieldFVars.extract 0 ctor.numFields
        let coMinorDom := closeForalls nonIhDecls minorRet
        let (coMinFvId, coMinFvExpr) := mkAuxFVar "comin" i
        coMinorDecls := coMinorDecls.push
          { fvarId := coMinFvId
            binderName := rMinorDecl.binderName
            domain := coMinorDom
            binderInfo := .default }
        let wrapperBody := Expr.mkAppN coMinFvExpr nonIhFVars
        let wrapperLam := closeLambdas allFieldDecls wrapperBody
        recMinorArgs := recMinorArgs.push wrapperLam

      let finalDecls := paramDecls ++ #[motiveDecl] ++ indexAndMajorDecls ++ coMinorDecls
      let coType := closeForalls finalDecls recBody
      let recUnivs := recVal.cnst.levelParams.map Level.mkParam
      let recCall := Expr.mkAppN
        (Expr.mkConst recVal.cnst.name recUnivs)
        (paramFVars ++ #[motiveFVar] ++ recMinorArgs ++ indexAndMajorFVars)
      let coValue := closeLambdas finalDecls recCall
      let coName := Name.mkStr indVal.cnst.name "casesOn"
      some {
        cnst := {
          name        := coName
          levelParams := recVal.cnst.levelParams
          type        := coType
        }
        value  := coValue
        hints  := .abbrev
        safety := if recVal.isUnsafe then .unsafe else .safe
        all    := #[coName]
      }

/-! ## `._ctorIdx` Generation -/

/-- Generate `<Ind>._ctorIdx` mapping each constructor `c_i` to `i : Nat` via `<Ind>.casesOn`. -/
def generateCtorIdx (indVal : Ix.InductiveVal) (ctors : Array Ix.ConstructorVal)
    (recVal : Ix.RecursorVal) : Option Ix.DefinitionVal := do
  -- `._ctorIdx` requires eliminating into `Type 0` (`Sort 1`), so `recVal` must have a motive universe parameter
  if recVal.cnst.levelParams.size != indVal.cnst.levelParams.size + 1 then none
  else
    let nParams := indVal.numParams
    let nIndices := indVal.numIndices
    let baseUnivs := indVal.cnst.levelParams.map Level.mkParam
    let (paramFVars, paramDecls, afterParams) :=
      openForallTelescope nParams indVal.cnst.type "cip" 0 #[] #[]
    let paramDeclsImplicit := paramDecls.map fun d => { d with binderInfo := .implicit }
    let (idxFVars, idxDecls, _) :=
      openForallTelescope nIndices afterParams "cii" 0 #[] #[]
    let idxDeclsImplicit := idxDecls.map fun d => { d with binderInfo := .implicit }
    let indApp := Expr.mkAppN (Expr.mkConst indVal.cnst.name baseUnivs) (paramFVars ++ idxFVars)
    let (xFvId, xFvExpr) := mkAuxFVar "cix" 0
    let xDecl : AuxLocalDecl :=
      { fvarId := xFvId, binderName := Name.simple "x", domain := indApp, binderInfo := .default }

    let natConst := Expr.mkConst (Name.simple "Nat") #[]
    let allDecls := paramDeclsImplicit ++ idxDeclsImplicit ++ #[xDecl]
    let ctorIdxType := closeForalls allDecls natConst

    let ctorIdxName := Name.mkStr indVal.cnst.name "_ctorIdx"
    if ctors.size ≤ 1 then
      let val := closeLambdas allDecls (Expr.mkNatLit 0)
      some {
        cnst := { name := ctorIdxName, levelParams := indVal.cnst.levelParams, type := ctorIdxType }
        value  := val
        hints  := .abbrev
        safety := if indVal.isUnsafe then .unsafe else .safe
        all    := #[ctorIdxName]
      }
    else
      -- Build `<Ind>.casesOn` call with motive `λ indices... x => Nat` at motive level `1` (`Type 0`)
      let casesOnName := Name.mkStr indVal.cnst.name "casesOn"
      let casesOnUnivs := #[Level.mkSucc Level.mkZero] ++ baseUnivs
      let motiveLam := closeLambdas (idxDecls ++ #[xDecl]) natConst
      let mut minorLams : Array Ix.Expr := #[]
      for (ctor, cidx) in ctors.zipIdx do
        let ctorAfterParams := paramFVars.foldl (fun cur p =>
          match stripMData cur with
          | .forallE _ _ b _ _ => instantiate1 b p
          | other => other) ctor.cnst.type
        let (_, fieldDecls, _) :=
          openForallTelescope ctor.numFields ctorAfterParams s!"cif_{cidx}" 0 #[] #[]
        let minorLam := closeLambdas fieldDecls (Expr.mkNatLit cidx)
        minorLams := minorLams.push minorLam
      let casesOnApp := Expr.mkAppN
        (Expr.mkConst casesOnName casesOnUnivs)
        (paramFVars ++ #[motiveLam] ++ idxFVars ++ #[xFvExpr] ++ minorLams)
      let ctorIdxValue := closeLambdas allDecls casesOnApp
      some {
        cnst := { name := ctorIdxName, levelParams := indVal.cnst.levelParams, type := ctorIdxType }
        value  := ctorIdxValue
        hints  := .abbrev
        safety := if indVal.isUnsafe then .unsafe else .safe
        all    := #[ctorIdxName]
      }

/-! ## Structure Field Projection Generation -/

/-- Generate projection definitions `<Struct>.<field_i>` for a single-constructor
    `structure` or `class` using kernel `.proj <Struct> i self` nodes. -/
def generateStructProjections (indVal : Ix.InductiveVal) (ctorVal : Ix.ConstructorVal)
    (fieldNames : Array Ix.Name) (isClass : Bool := false) : Array Ix.DefinitionVal := Id.run do
  let nParams := indVal.numParams
  let baseUnivs := indVal.cnst.levelParams.map Level.mkParam
  let (paramFVars, paramDecls, _) :=
    openForallTelescope nParams indVal.cnst.type "sp" 0 #[] #[]
  let paramDeclsImplicit := paramDecls.map fun d => { d with binderInfo := .implicit }
  let structApp := Expr.mkAppN (Expr.mkConst indVal.cnst.name baseUnivs) paramFVars
  let (selfFvId, selfFvExpr) := mkAuxFVar "self" 0
  let selfBi : Lean.BinderInfo := if isClass then .instImplicit else .default
  let selfDecl : AuxLocalDecl :=
    { fvarId := selfFvId, binderName := Name.simple "self", domain := structApp, binderInfo := selfBi }

  -- Walk the constructor's field telescope, substituting `.proj Struct j self` for earlier fields
  let mut curCtorTy := paramFVars.foldl (fun cur p =>
    match stripMData cur with
    | .forallE _ _ b _ _ => instantiate1 b p
    | other => other) ctorVal.cnst.type
  let mut out : Array Ix.DefinitionVal := #[]
  for i in [:ctorVal.numFields] do
    match stripMData curCtorTy with
    | .forallE _ fieldDom restBody _ _ =>
      let projExpr := Expr.mkProj indVal.cnst.name i selfFvExpr
      curCtorTy := instantiate1 restBody projExpr
      match fieldNames[i]? with
      | some projName =>
        let allDecls := paramDeclsImplicit.push selfDecl
        let projType := closeForalls allDecls fieldDom
        let projVal := closeLambdas allDecls projExpr
        out := out.push {
          cnst := {
            name        := projName
            levelParams := indVal.cnst.levelParams
            type        := projType
          }
          value  := projVal
          hints  := .abbrev
          safety := if indVal.isUnsafe then .unsafe else .safe
          all    := #[projName]
        }
      | none => pure ()
    | _ => pure ()
  return out

/-! ## Complete Auxiliary Suite Registration for an Inductive Block -/

/-- Register a canonicalized inductive block `(indVal, ctors)` and all of its
    surgery-free auxiliaries (`.rec`, `.recOn`, `.casesOn`, `._ctorIdx`) into `env : IxElabEnv`. -/
def registerCanonicalInductiveBlock (env : IxElabEnv)
    (canonItems : Array (Ix.InductiveVal × Array Ix.ConstructorVal)) : IxElabEnv := Id.run do
  let mut env := env
  -- 1. Register all `InductiveVal`s and `ConstructorVal`s in canonical order
  for (iv, ctors) in canonItems do
    env := env.addConst (.inductInfo iv)
    for ctor in ctors do
      env := env.addConst (.ctorInfo ctor)
  -- 2. Generate and register `.rec`, `.recOn`, `.casesOn`, and `._ctorIdx` for each inductive
  for ((iv, ctors), idx) in canonItems.zipIdx do
    match generateBlockRecursor canonItems idx with
    | none => pure ()
    | some recVal =>
      env := env.addConst (.recInfo recVal)
      if let some recOnDef := generateRecOn iv.cnst.name recVal then
        env := env.addConst (.defnInfo recOnDef)
      if let some casesOnDef := generateCasesOn iv ctors recVal then
        env := env.addConst (.defnInfo casesOnDef)
        if env.contains (Name.simple "Nat") then
          if let some ctorIdxDef := generateCtorIdx iv ctors recVal then
            env := env.addConst (.defnInfo ctorIdxDef)
  return env

end Ix.Frontend.AuxGen
