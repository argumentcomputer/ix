/-
  Ix.Frontend.Elab.Term: Pure, deterministic, fuel-bounded bidirectional term,
  binder, pattern-match, and tactic elaborator for the Ix Frontend.

  Directly elaborates:
  - Substructural usage (`0`, `1`, `&`), ownership (`!`), and locality (`~`) contracts
    on `fun`, `forall`/arrows, `let`, and `let borrow`, attaching `ix.contract` frames
    and recording `Ixon.BinderContract`, `Ixon.ValueContract`, and `Ixon.LetContract`.
  - Implicit argument insertion and bounded backtracking typeclass synthesis (`[...]`).
  - Content-hash references (`#<64-hex-chars>`) and `IxImportMap` name resolution.
  - Structure literals `{ field := val, ... }`, anonymous constructors `⟨a, b⟩`, and `.field` projections.
  - Pattern matching (`match ... with`) lowered into canonical `<Ind>.casesOn` applications.
  - Core tactic blocks (`by intro; exact; apply; refine; rfl; assumption; constructor; have; let; change; cases; induction`).
-/
module

public import Ix.Frontend.AuxGen
public import Ix.Frontend.Elab.Tactic

@[expose] public section

namespace Ix.Frontend.Elab

open Ix.Frontend
open Ix.Frontend.Parser
open Ix.Frontend.AuxGen

/-! ## Universe Level Elaboration -/

/-- Elaborate a universe level syntax tree into an `Ix.Level`. -/
def elabLevel : Nat → Ix.Syntax → IxElabM Ix.Level
  | 0, stx => throwElabError "elaborator fuel exhausted in universe level" (some stx)
  | fuel + 1, stx => withRef stx do
    match stx with
    | .ident _ _ id _ =>
      if Name.isAnonymous id || id == Name.simple "_" then
        mkFreshLevelMVar
      else
        let ctx ← read
        let st ← get
        if ctx.univParams.contains id || ctx.scope.levelNames.contains id ||
           st.autoBoundUnivs.contains id then
          return Level.mkParam id
        else
          -- Auto-bind universe parameter name
          modify fun s => { s with autoBoundUnivs := s.autoBoundUnivs ++ [id] }
          return Level.mkParam id
    | .node _ kind args =>
      if kind == SyntaxKind.levelLit then
        let numStr := Syntax.getAtomVal (args.getD 0 .missing)
        let n := (parseNatLiteral numStr).getD 0
        return Level.ofNat n
      else if kind == SyntaxKind.levelAdd then
        let base ← elabLevel fuel (args.getD 0 .missing)
        let numNode := args.getD 2 .missing
        let numStr := Syntax.getAtomVal (Syntax.getArg numNode 0)
        let offset := (parseNatLiteral numStr).getD 0
        return (List.range offset).foldl (fun acc _ => Level.mkSucc acc) base
      else if kind == SyntaxKind.levelMax then
        let children := Syntax.getArgs (args.getD 1 .missing)
        let lvls ← children.mapM (elabLevel fuel)
        match lvls.toList with
        | []      => return Level.mkZero
        | u :: us => return us.foldl Level.mkMax u
      else if kind == SyntaxKind.levelIMax then
        let children := Syntax.getArgs (args.getD 1 .missing)
        let lvls ← children.mapM (elabLevel fuel)
        match lvls.toList with
        | []      => return Level.mkZero
        | [u]     => return u
        | u :: us =>
          let rev := (u :: us).reverse
          match rev with
          | last :: initRev =>
            return initRev.foldl (fun acc x => Level.mkIMax x acc) last
          | [] => return Level.mkZero
      else
        throwElabError s!"unexpected universe level syntax '{Name.toStringTotal kind}'" (some stx)
    | _ =>
      throwElabError "expected universe level" (some stx)

/-! ## Substructural Binder Decoding -/

/-- Decoded binder specification before type elaboration. -/
structure ParsedBinderGroup where
  names      : Array Ix.Name
  typeStx?   : Option Ix.Syntax
  binderInfo : Lean.BinderInfo
  contract   : Ixon.BinderContract
  deriving Repr, Inhabited

/-- Decode a single bracketed or simple binder node (`explicitBinder`, `implicitBinder`,
    `strictImplicitBinder`, `instBinder`) into a `ParsedBinderGroup`. -/
def decodeBinderNode (bStx : Ix.Syntax) : ParsedBinderGroup :=
  let k := Syntax.getKind bStx
  let bi : Lean.BinderInfo :=
    if k == SyntaxKind.implicitBinder then .implicit
    else if k == SyntaxKind.strictImplicitBinder then .strictImplicit
    else if k == SyntaxKind.instBinder then .instImplicit
    else .default
  if k == SyntaxKind.explicitBinder || k == SyntaxKind.implicitBinder ||
     k == SyntaxKind.strictImplicitBinder || k == SyntaxKind.instBinder then
    let bPrefNode := Syntax.getArg bStx 0
    let idsNode   := Syntax.getArg bStx 1
    let vPrefNode := Syntax.getArg bStx 2
    let tyNode    := Syntax.getArg bStx 3
    let parsedContract :=
      mergeParsedContracts (decodeContractPrefix bPrefNode) (decodeContractPrefix vPrefNode)
    let names := (Syntax.getArgs idsNode).map fun idStx =>
      if Syntax.getAtomVal idStx == "_" then Name.mkAnon
      else Syntax.getId idStx
    let names := if names.isEmpty then #[Name.mkAnon] else names
    let typeStx? :=
      if Syntax.isNone tyNode || Syntax.isMissing tyNode then none
      else some tyNode
    { names, typeStx?, binderInfo := bi, contract := parsedContract.toBinderContract }
  else
    let id := if Syntax.getAtomVal bStx == "_" then Name.mkAnon else Syntax.getId bStx
    { names := #[id], typeStx? := none, binderInfo := .default, contract := default }

/-! ## Structure Projection & Dot-Notation Resolution -/

/-- Elaborate a `.field` or `.0` projection on an already-elaborated `baseExpr`. -/
def elabProjOnExpr (fuel : Nat) (baseExpr : Ix.Expr) (fieldStx : Ix.Syntax) : IxElabM Ix.Expr := do
  -- 1. Numeric projection `base.0`, `base.1`, `base.2` (1-based `.1`/`.2` or 0-based `.0`)
  if Syntax.isOfKind fieldStx SyntaxKind.numLit then
    let nStr := Syntax.getAtomVal (Syntax.getArg fieldStx 0)
    let rawIdx := (parseNatLiteral nStr).getD 0
    let baseTy ← inferType fuel baseExpr
    let baseTyWhnf ← whnf fuel baseTy
    let (headFn, _) := getAppFnArgs baseTyWhnf
    match headFn with
    | .const structName _ _ =>
      let idx := if rawIdx > 0 then rawIdx - 1 else 0
      return Expr.mkProj structName idx baseExpr
    | _ =>
      throwElabError s!"cannot project index .{rawIdx} from non-structure type" (some fieldStx)
  else
    let fieldId := Syntax.getId fieldStx
    let baseTy ← inferType fuel baseExpr
    let baseTyWhnf ← whnf fuel baseTy
    let (headFn, headArgs) := getAppFnArgs baseTyWhnf
    let st ← get
    match headFn with
    | .const typeName typeUnivs _ =>
      -- Check if `typeName` is a registered `structure` / `class` with field `fieldId`
      match st.env.structTable.get? typeName with
      | some sInfo =>
        match sInfo.fields.find? (fun f => f.fieldName == fieldId) with
        | some fInfo =>
          return Expr.mkProj typeName fInfo.fieldIdx baseExpr
        | none =>
          -- Generalized dot-notation: `<TypeName>.<fieldId>` applied to `baseExpr`
          let methodName := Name.append typeName fieldId
          if st.env.contains methodName then
            let (mConst, mTy) ← mkConstWithFreshMVarLevels methodName
            let (applied, instGoals, _) ← openForallMVars 16 mConst mTy []
            for g in instGoals do
              let gTy ← inferType fuel g
              if let some instVal ← synthInstance? 8 gTy then
                let _ ← isDefEq fuel g instVal
            return Expr.mkApp applied baseExpr
          else
            throwElabError s!"unknown field or method '{Name.toStringTotal fieldId}' on '{Name.toStringTotal typeName}'" (some fieldStx)
      | none =>
        -- Check if `<typeName>.<fieldId>` is a function/constructor or if `fieldToStruct` knows the index
        let methodName := Name.append typeName fieldId
        if st.env.contains methodName then
          let _ := typeUnivs
          let _ := headArgs
          let (mConst, _) ← mkConstWithFreshMVarLevels methodName
          return Expr.mkApp mConst baseExpr
        else
          throwElabError s!"unknown field '{Name.toStringTotal fieldId}' on type '{Name.toStringTotal typeName}'" (some fieldStx)
    | _ =>
      throwElabError s!"cannot project field '{Name.toStringTotal fieldId}' from expression of unknown structure type" (some fieldStx)

/-- Split a hierarchical `Ix.Name` into `(rootComponentName, remainingFieldStrings)`. -/
def splitRootAndFields (n : Ix.Name) : Option (Ix.Name × List String) :=
  match Name.components n with
  | root :: rest@(_ :: _) => some (Name.simple root, rest)
  | _ => none

/-- Resolve and elaborate an identifier (with optional explicit `.{u, v}` levels). -/
def elabIdentWithLevels (fuel : Nat) (idStx : Ix.Syntax) (explicitLvls? : Option (Array Ix.Level)) :
    IxElabM Ix.Expr := withRef idStx do
  let rawId := Syntax.getId idStx
  let ctx ← read
  let st ← get
  -- 1. Check local context for exact match
  match ctx.lctx.findUserName? rawId with
  | some decl =>
    return Expr.mkFVar decl.fvarId
  | none =>
    -- 2. Check if `rawId` is `localVar.field1.field2` where `localVar` is in `ctx.lctx`
    match splitRootAndFields rawId with
    | some (rootName, fieldStrs) =>
      match ctx.lctx.findUserName? rootName with
      | some rootDecl =>
        let mut curExpr := Expr.mkFVar rootDecl.fvarId
        for fStr in fieldStrs do
          curExpr ← elabProjOnExpr fuel curExpr (Syntax.mkSimpleIdent (Name.simple fStr))
        return curExpr
      | none =>
        -- Fall through to global constant resolution
        let resolved := resolveIdentInScope ctx.scope ctx.modIdx (fun n => st.env.contains n) rawId
        let mappedResolved :=
          if st.env.contains resolved then resolved
          else match ctx.modIdx.importMap.lookupName? resolved <|> st.env.importMap.lookupName? resolved with
            | some addr =>
              (st.env.constOrder.find? fun nm =>
                Name.computeHash nm == addr || st.env.importMap.lookupName? nm == some addr).getD resolved
            | none => resolved
        if st.env.contains mappedResolved then
          match explicitLvls? with
          | some lvls => return Expr.mkConst mappedResolved lvls
          | none =>
            let (cExpr, _) ← mkConstWithFreshMVarLevels mappedResolved
            return cExpr
        else
          throwElabError s!"unknown identifier '{Name.toStringTotal rawId}'" (some idStx)
    | none =>
      -- 3. Global constant resolution in `scope`
      let resolved := resolveIdentInScope ctx.scope ctx.modIdx (fun n => st.env.contains n) rawId
      let mappedResolved :=
        if st.env.contains resolved then resolved
        else match ctx.modIdx.importMap.lookupName? resolved <|> st.env.importMap.lookupName? resolved with
          | some addr =>
            (st.env.constOrder.find? fun nm =>
              Name.computeHash nm == addr || st.env.importMap.lookupName? nm == some addr).getD resolved
          | none => resolved
      if st.env.contains mappedResolved then
        match explicitLvls? with
        | some lvls => return Expr.mkConst mappedResolved lvls
        | none =>
          let (cExpr, _) ← mkConstWithFreshMVarLevels mappedResolved
          return cExpr
      else
        throwElabError s!"unknown identifier '{Name.toStringTotal rawId}'" (some idStx)

/-! ## Implicit Argument Insertion & Expected Type Coercion -/

/-- Ensure `ty` is a `Sort`, skipping redundant re-checks on `.forallE` nodes whose
    domain and codomain were already checked when constructed. -/
def ensureSortIfNotForall (fuel : Nat) (ty : Ix.Expr) : IxElabM Unit :=
  match stripMData ty with
  | .forallE _ _ _ _ _ => return ()
  | _                  => do let _ ← ensureSort fuel ty

/-- Fast pure lookup for built-in binary operators without rebuilding `defaultParserEnv`. -/
def findBuiltinOpTarget? (sym : String) : Option Ix.Name :=
  if sym == "="   then some (Name.simple "Eq")
  else if sym == "≠"   then some (Name.simple "Ne")
  else if sym == "+"   then some (Name.mkStr2 "HAdd" "hAdd")
  else if sym == "-"   then some (Name.mkStr2 "HSub" "hSub")
  else if sym == "*"   then some (Name.mkStr2 "HMul" "hMul")
  else if sym == "/"   then some (Name.mkStr2 "HDiv" "hDiv")
  else if sym == "%"   then some (Name.mkStr2 "HMod" "hMod")
  else if sym == "^"   then some (Name.mkStr2 "HPow" "hPow")
  else if sym == "++"  then some (Name.mkStr2 "HAppend" "hAppend")
  else if sym == "::"  then some (Name.mkStr2 "List" "cons")
  else if sym == "=="  then some (Name.mkStr2 "BEq" "beq")
  else if sym == "!="  then some (Name.mkStr2 "BEq" "bne")
  else if sym == "<"   then some (Name.mkStr2 "LT" "lt")
  else if sym == "≤" || sym == "<=" then some (Name.mkStr2 "LE" "le")
  else if sym == ">"   then some (Name.mkStr2 "GT" "gt")
  else if sym == "≥" || sym == ">=" then some (Name.mkStr2 "GE" "ge")
  else if sym == "&&"  then some (Name.simple "and")
  else if sym == "||"  then some (Name.simple "or")
  else if sym == "∧" || sym == "/\\" then some (Name.simple "And")
  else if sym == "∨" || sym == "\\/" then some (Name.simple "Or")
  else if sym == "↔" || sym == "<->" then some (Name.simple "Iff")
  else if sym == "×"   then some (Name.simple "Prod")
  else if sym == "∘"   then some (Name.mkStr2 "Function" "comp")
  else if sym == "<|>" then some (Name.mkStr2 "HOrElse" "hOrElse")
  else if sym == ">>"  then some (Name.mkStr2 "HAndThen" "hAndThen")
  else if sym == ">>=" then some (Name.mkStr2 "Bind" "bind")
  else if sym == "<$>" then some (Name.mkStr2 "Functor" "map")
  else if sym == "<*>" then some (Name.mkStr2 "Seq" "seq")
  else none

/-- Concise, pure pretty-printer for `Ix.Expr` in error messages (avoids `Repr Ix.Expr`). -/
def ppExprShort : Nat → Ix.Expr → String
  | 0, _ => "..."
  | _, .bvar i _ => s!"#{i}"
  | _, .fvar n _ => Name.toStringTotal n
  | _, .mvar n _ => s!"?{Name.toStringTotal n}"
  | _, .sort _ _ => "Sort"
  | _, .const n _ _ => Name.toStringTotal n
  | fuel + 1, .app f a _ => s!"({ppExprShort fuel f} {ppExprShort fuel a})"
  | fuel + 1, .lam n t b _ _ => s!"(fun {Name.toStringTotal n} : {ppExprShort fuel t} => {ppExprShort fuel b})"
  | fuel + 1, .forallE n t b _ _ =>
    if Name.isAnonymous n then s!"({ppExprShort fuel t} → {ppExprShort fuel b})"
    else s!"(({Name.toStringTotal n} : {ppExprShort fuel t}) → {ppExprShort fuel b})"
  | fuel + 1, .letE n _ v b _ _ => s!"(let {Name.toStringTotal n} := {ppExprShort fuel v}; {ppExprShort fuel b})"
  | _, .lit (.natVal n) _ => s!"{n}"
  | _, .lit (.strVal s) _ => s!"\"{s}\""
  | fuel + 1, .mdata _ x _ => ppExprShort fuel x
  | fuel + 1, .proj s i x _ => s!"{ppExprShort fuel x}.{Name.toStringTotal s}.{i}"

/-- Check that `expr` with already-computed type `actualTy` is definitionally equal to `expectedType`. -/
def ensureHasKnownType (fuel : Nat) (stx : Ix.Syntax) (expr : Ix.Expr)
    (actualTy : Ix.Expr) (expectedType? : Option Ix.Expr) : IxElabM Ix.Expr := do
  match expectedType? with
  | none => instantiateMVars 16 expr
  | some expTy =>
    let expTyWhnf ← whnfForall fuel expTy
    -- If `expTyWhnf` is NOT an implicit forall, peel implicit binders on `actualTy`
    let shouldPeelImplicits : Bool := match stripMData expTyWhnf with
      | .forallE _ _ _ bi _ => bi == .default
      | _                   => true
    let (expr', instGoals, actualTy') ←
      if shouldPeelImplicits then insertImplicitArgs 16 expr actualTy []
      else pure (expr, [], actualTy)
    let ok ← isDefEq fuel actualTy' expTy
    if !ok then
      let actNorm ← instantiateMVars 16 actualTy'
      let expNorm ← instantiateMVars 16 expTy
      throwElabError s!"type mismatch: term has type '{ppExprShort 8 actNorm}' but is expected to have type '{ppExprShort 8 expNorm}'" (some stx)
    for g in instGoals.reverse do
      let gTy ← inferType fuel g
      if let some instVal ← synthInstance? 8 gTy then
        let _ ← isDefEq fuel g instVal
    instantiateMVars 16 expr'

/-- Check that `expr` has type definitionally equal to `expectedType` (inserting trailing
    implicit arguments if `expr`'s type has leading implicit binders while `expectedType` does not). -/
def ensureHasType (fuel : Nat) (stx : Ix.Syntax) (expr : Ix.Expr)
    (expectedType? : Option Ix.Expr) : IxElabM Ix.Expr := do
  match expectedType? with
  | none => instantiateMVars 16 expr
  | some _ =>
    let actualTy ← inferType fuel expr
    ensureHasKnownType fuel stx expr actualTy expectedType?

/-! ## Core Bidirectional Term Elaborator (`elabTerm`) -/

/-- Flatten nested `SyntaxKind.appTerm` nodes into `(headStx, #[arg₁, ..., argₙ])`. -/
def flattenAppSyntax : Nat → Ix.Syntax → List Ix.Syntax → Ix.Syntax × Array Ix.Syntax
  | 0, stx, acc => (stx, Array.mk acc)
  | fuel + 1, stx@(.node _ k args), acc =>
    if k == SyntaxKind.appTerm && args.size == 2 then
      flattenAppSyntax fuel (Syntax.listGetD args.toList 0 .missing) (Syntax.listGetD args.toList 1 .missing :: acc)
    else
      (stx, Array.mk acc)
  | _, stx, acc => (stx, Array.mk acc)

/-- A single flattened binder variable with its optional syntax domain, `BinderInfo`, and `BinderContract`. -/
structure FlatBinderItem where
  name       : Ix.Name
  typeStx?   : Option Ix.Syntax
  binderInfo : Lean.BinderInfo
  contract   : Ixon.BinderContract

/-- Flatten a list of `ParsedBinderGroup`s into a flat list of `FlatBinderItem`s. -/
def flattenBinderGroups (groups : List ParsedBinderGroup) : List FlatBinderItem :=
  groups.flatMap fun grp =>
    grp.names.toList.map fun nm =>
      { name := nm, typeStx? := grp.typeStx?, binderInfo := grp.binderInfo, contract := grp.contract }

/-- Elaborate a flat list of `FlatBinderItem`s structurally on `List`, running `k fvarIds` inside the extended `LocalContext`. -/
def elabFlatBinderItems (elabTermRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr) :
    List FlatBinderItem → List Ix.Name → (Array Ix.Name → IxElabM α) → IxElabM α
  | [], revFVars, k => k (Array.mk revFVars.reverse)
  | item :: restItems, revFVars, k => do
    let domTy ← match item.typeStx? with
      | some tyStx =>
        let ty ← elabTermRec tyStx none
        let _ ← ensureSort 32 ty
        pure ty
      | none =>
        let u ← mkFreshLevelMVar
        mkFreshExprMVar (Expr.mkSort u) item.name
    withLocalDecl item.name domTy item.binderInfo item.contract fun fvId _ =>
      elabFlatBinderItems elabTermRec restItems (fvId :: revFVars) k

/-- Elaborate a sequence of `ParsedBinderGroup`s, running `k fvarIds` inside the extended `LocalContext`. -/
def elabBinderGroups (elabTermRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (groups : List ParsedBinderGroup) (accFVars : Array Ix.Name) (k : Array Ix.Name → IxElabM α) : IxElabM α :=
  elabFlatBinderItems elabTermRec (flattenBinderGroups groups) accFVars.toList.reverse k

/-- Extract constructor pattern `(ctorName?, boundVarNames)` from a pattern `Syntax`. -/
def decodeConstructorPattern (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (env : IxElabEnv) (pat : Ix.Syntax) : Option (Ix.Name × Array Ix.Name) :=
  let (headStx, argStxs) := flattenAppSyntax 256 pat []
  if Syntax.isOfKind headStx SyntaxKind.numLit then
    let nStr := Syntax.getAtomVal (Syntax.getArg headStx 0)
    match parseNatLiteral nStr with
    | some 0 => some (Name.mkStr2 "Nat" "zero", #[])
    | _      => none
  else
    match headStx with
    | .ident _ _ id _ =>
      let resolved := resolveIdentInScope scope modIdx (fun n => env.contains n) id
      if env.isCtor resolved || modIdx.isModuleCtor resolved then
        let varNames := argStxs.map fun a =>
          if Syntax.isOfKind a SyntaxKind.holeTerm || Syntax.getAtomVal a == "_" then
            Name.mkAnon
          else
            Syntax.getId a
        some (resolved, varNames)
      else
        none
    | _ => none

/-- Main bidirectional term elaborator, structurally recursive on `fuel : Nat`. -/
def elabTerm : Nat → Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr
  | 0, stx, _ => throwElabError "elaborator fuel exhausted in term" (some stx)
  | fuel + 1, stx, expectedType? => withRef stx do
    let elabRec (s : Ix.Syntax) (exp? : Option Ix.Expr) : IxElabM Ix.Expr :=
      elabTerm fuel s exp?
    match stx with
    | .missing =>
      throwElabError "missing syntax node in term"
    -- 1. Bare identifier
    | .ident .. =>
      let e ← elabIdentWithLevels fuel stx none
      ensureHasType fuel stx e expectedType?
    -- 2. Bare `true` / `false` atoms
    | .atom _ val =>
      if val == "true" || val == "false" then
        let boolCtor := Name.mkStr2 "Bool" val
        let st ← get
        let targetName := if st.env.contains boolCtor then boolCtor else Name.simple val
        let (e, _) ← mkConstWithFreshMVarLevels targetName
        ensureHasType fuel stx e expectedType?
      else
        throwElabError s!"unexpected atom '{val}' in term" (some stx)
    -- 3. Composite syntax nodes
    | .node _ kind args =>
      -- 3.1. Hole `_`
      if kind == SyntaxKind.holeTerm then
        let ty ← match expectedType? with
          | some t => pure t
          | none   =>
            let u ← mkFreshLevelMVar
            mkFreshExprMVar (Expr.mkSort u)
        mkFreshExprMVar ty
      -- 3.2. `Prop` (`Sort 0`)
      else if kind == SyntaxKind.propTerm then
        ensureHasType fuel stx Expr.mkProp expectedType?
      -- 3.3. `Type [u]` (`Sort (u + 1)`)
      else if kind == SyntaxKind.typeTerm then
        let argNode := args.getD 1 .missing
        let lvl ←
          if Syntax.isNone argNode || Syntax.isMissing argNode then
            pure Level.mkZero
          else if Syntax.isOfKind argNode SyntaxKind.nullKind then
            match Syntax.getOptional? argNode with
            | some lStx => elabLevel fuel lStx
            | none      => pure Level.mkZero
          else
            elabLevel fuel argNode
        let res := Expr.mkSort (Level.mkSucc lvl)
        ensureHasType fuel stx res expectedType?
      -- 3.4. `Sort [u]`
      else if kind == SyntaxKind.sortTerm then
        let optNode := args.getD 1 .missing
        let lvl ← match Syntax.getOptional? optNode with
          | some lStx => elabLevel fuel lStx
          | none      => pure Level.mkZero
        let res := Expr.mkSort lvl
        ensureHasType fuel stx res expectedType?
      -- 3.5. Numeric literal
      else if kind == SyntaxKind.numLit then
        let numStr := Syntax.getAtomVal (args.getD 0 .missing)
        let n := (parseNatLiteral numStr).getD 0
        let rawLit := Expr.mkNatLit n
        let st ← get
        let ofNatName := Name.mkStr2 "OfNat" "ofNat"
        let instOfNatNatName := Name.simple "instOfNatNat"
        let natConst := Expr.mkConst (Name.simple "Nat") #[]
        let litExpr :=
          if st.env.contains ofNatName && st.env.contains instOfNatNatName then
            let instExpr := Expr.mkApp (Expr.mkConst instOfNatNatName #[]) rawLit
            Expr.mkAppN (Expr.mkConst ofNatName #[Level.mkZero]) #[natConst, rawLit, instExpr]
          else
            rawLit
        ensureHasKnownType fuel stx litExpr natConst expectedType?
      -- 3.6. String literal
      else if kind == SyntaxKind.strLit then
        let strVal := Syntax.getAtomVal (args.getD 0 .missing)
        let litExpr := Expr.mkStrLit strVal
        ensureHasType fuel stx litExpr expectedType?
      -- 3.7. Character literal `'c'` (`Char.ofNat c.toNat` or nat literal fallback)
      else if kind == SyntaxKind.charLit then
        let chStr := Syntax.getAtomVal (args.getD 0 .missing)
        let code := match chStr.toList with
          | c :: _ => c.toNat
          | []     => 0
        let st ← get
        let charOfNat := Name.mkStr2 "Char" "ofNat"
        let res :=
          if st.env.contains charOfNat then
            Expr.mkApp (Expr.mkConst charOfNat #[]) (Expr.mkNatLit code)
          else
            Expr.mkNatLit code
        ensureHasType fuel stx res expectedType?
      -- 3.8. Content-hash reference `#<64-hex>`
      else if kind == SyntaxKind.hashRef then
        let hexStr := Syntax.getAtomVal (args.getD 0 .missing)
        match parseHexAddress hexStr with
        | none => throwElabError s!"invalid 64-hex-char content address '#{hexStr}'" (some stx)
        | some addr =>
          let st ← get
          -- Search `importMap.nameToAddr` or `env.consts` for a constant with matching address/hash
          let foundName? := st.env.constOrder.find? fun nm =>
            Name.computeHash nm == addr || st.env.importMap.lookupName? nm == some addr
          match foundName? with
          | some nm =>
            let (e, _) ← mkConstWithFreshMVarLevels nm
            ensureHasType fuel stx e expectedType?
          | none =>
            throwElabError s!"unresolved content address '#{hexStr}'" (some stx)
      -- 3.9. Explicit `@ident.{u, v}` or `ident.{u, v}` (`SyntaxKind.explicitTerm`)
      else if kind == SyntaxKind.explicitTerm then
        let isAt := Syntax.getAtomVal (args.getD 0 .missing) == "@"
        let idStx := if isAt then args.getD 1 .missing else args.getD 0 .missing
        let univsNode := if isAt then args.getD 2 .missing else args.getD 1 .missing
        let explicitLvls? ←
          if Syntax.isNone univsNode then
            if isAt then
              -- `@ident` without `.{...}` still gets fresh level mvars, just no implicit term args
              pure none
            else
              pure none
          else
            let ls ← (Syntax.getArgs univsNode).mapM (elabLevel fuel)
            pure (some ls)
        let e ← elabIdentWithLevels fuel idStx explicitLvls?
        if isAt then
          -- Do NOT peel implicit arguments when `@` was used!
          match expectedType? with
          | none => return e
          | some expTy =>
            let actTy ← inferType fuel e
            let ok ← isDefEq fuel actTy expTy
            if !ok then throwElabError "type mismatch on @-explicit term" (some stx)
            instantiateMVars 16 e
        else
          ensureHasType fuel stx e expectedType?
      -- 3.10. Type ascription `(e : vPref T)`
      else if kind == SyntaxKind.typeAscription then
        let termStx := args.getD 1 .missing
        let tyStx   := args.getD 4 .missing
        let ascTy ← elabRec tyStx none
        let _ ← ensureSort 32 ascTy
        let e ← elabRec termStx (some ascTy)
        ensureHasType fuel stx e expectedType?
      -- 3.11. Non-dependent function arrow `A → !B` (`SyntaxKind.arrowTerm`)
      else if kind == SyntaxKind.arrowTerm then
        -- args: #[domStx, "→", vPrefNode, codStx]
        let domStx    := args.getD 0 .missing
        let vPrefNode := args.getD 2 .missing
        let codStx    := args.getD 3 .missing
        -- Check if `domStx` starts with a usage/value modifier in case of bare `A → !B`
        let domTy ← elabRec domStx none
        let _ ← ensureSortIfNotForall 32 domTy
        let retContract := (decodeContractPrefix vPrefNode).toValueContract
        let codTy ← withLocalDecl Name.mkAnon domTy .default default fun fvId _ => do
          let cTy ← elabRec codStx none
          let _ ← ensureSortIfNotForall 32 cTy
          if containsFVar fvId cTy then
            return abstractFVar fvId cTy
          else
            return cTy
        let arrowExpr := Expr.mkForallContract Name.mkAnon domTy codTy .default default retContract
        ensureHasType fuel stx arrowExpr expectedType?
      -- 3.12. Dependent Pi `forall binders, vPref body` or `(binders) → vPref body` (`SyntaxKind.forallTerm`)
      else if kind == SyntaxKind.forallTerm then
        let isKw := match args[0]? with
          | some (.atom _ kw) => kw == "forall" || kw == "∀"
          | _ => false
        let bindersNode := if isKw then args.getD 1 .missing else args.getD 0 .missing
        let vPrefNode   := if isKw then args.getD 3 .missing else args.getD 2 .missing
        let bodyStx     := if isKw then args.getD 4 .missing else args.getD 3 .missing
        let retContract := (decodeContractPrefix vPrefNode).toValueContract
        let groups := (Syntax.getArgs bindersNode).toList.map decodeBinderNode
        let piExpr ← elabBinderGroups elabRec groups #[] fun fvars => do
          let bodyTy ← elabRec bodyStx none
          let _ ← ensureSortIfNotForall 32 bodyTy
          mkForallFVars fvars bodyTy retContract
        ensureHasType fuel stx piExpr expectedType?
      -- 3.13. Lambda `fun binders => body` (`SyntaxKind.funTerm`)
      else if kind == SyntaxKind.funTerm then
        let bindersNode := args.getD 1 .missing
        let bodyStx     := args.getD 3 .missing
        let groups := (Syntax.getArgs bindersNode).toList.map decodeBinderNode
        let items := flattenBinderGroups groups
        -- Propagate expected `.forallE` domain types onto unannotated lambda binders structurally on `items : List FlatBinderItem`!
        let rec elabFunItems (remItems : List FlatBinderItem) (curExp? : Option Ix.Expr)
            (curFVars : Array Ix.Name) : IxElabM Ix.Expr := do
          match remItems with
          | [] =>
            let bodyExpr ← elabRec bodyStx curExp?
            mkLambdaFVars curFVars bodyExpr
          | item :: restItems =>
            let (expDom?, nextExpFn?) ← match curExp? with
              | some eTy =>
                let eTyW ← whnf 32 eTy
                match stripMData eTyW with
                | .forallE _ d b _ _ => pure (some d, some b)
                | _                  => pure (none, none)
              | none => pure (none, none)
            let domTy ← match item.typeStx? with
              | some tyStx =>
                let t ← elabRec tyStx none
                let _ ← ensureSort 32 t
                if let some expD := expDom? then
                  let _ ← isDefEq 32 t expD
                pure t
              | none =>
                match expDom? with
                | some expD => pure expD
                | none =>
                  let u ← mkFreshLevelMVar
                  mkFreshExprMVar (Expr.mkSort u) item.name
            withLocalDecl item.name domTy item.binderInfo item.contract fun fvId fvExpr => do
              let nextExp? := nextExpFn?.map fun b => instantiate1 b fvExpr
              elabFunItems restItems nextExp? (curFVars.push fvId)
        let lamExpr ← elabFunItems items expectedType? #[]
        ensureHasType fuel stx lamExpr expectedType?
      -- 3.14. `let` and `let borrow` (`SyntaxKind.letTerm`, `SyntaxKind.letBorrowTerm`)
      else if kind == SyntaxKind.letTerm || kind == SyntaxKind.letBorrowTerm then
        let isBorrow := kind == SyntaxKind.letBorrowTerm
        let bPrefNode   := if isBorrow then args.getD 2 .missing else args.getD 1 .missing
        let idStx       := if isBorrow then args.getD 3 .missing else args.getD 2 .missing
        let bindersNode := if isBorrow then args.getD 4 .missing else args.getD 3 .missing
        let optTyNode   := if isBorrow then args.getD 5 .missing else args.getD 4 .missing
        let valStx      := if isBorrow then args.getD 7 .missing else args.getD 6 .missing
        let bodyStx     := if isBorrow then args.getD 9 .missing else args.getD 8 .missing

        let letName :=
          let id := Syntax.getId idStx
          if Name.isAnonymous id then Name.simple "x" else id
        let bParsed := decodeContractPrefix bPrefNode
        let (vParsed, optTyStx?) :=
          if Syntax.getNumArgs optTyNode >= 3 then
            -- optTyNode is `null #[ ":", vPref, ty ]`
            let vp := decodeContractPrefix (Syntax.getArg optTyNode 1)
            (vp, some (Syntax.getArg optTyNode 2))
          else
            ({}, none)
        let merged := mergeParsedContracts bParsed vParsed
        let binderContract : Ixon.BinderContract :=
          if isBorrow then
            { uses := merged.uses.getD .many, value := .localShared }
          else
            merged.toBinderContract
        let letKind : Ixon.LetKind := if isBorrow then .borrowShared else .value
        let paramGroups := (Syntax.getArgs bindersNode).toList.map decodeBinderNode
        let (letTy, letVal) ← elabBinderGroups elabRec paramGroups #[] fun fvars => do
          let expValTy? ← match optTyStx? with
            | some tyStx =>
              let t ← elabRec tyStx none
              let _ ← ensureSort 32 t
              pure (some t)
            | none => pure none
          let vExpr ← elabRec valStx expValTy?
          let vTy ← match expValTy? with
            | some t => pure t
            | none   => inferType fuel vExpr
          let fullTy ← mkForallFVars fvars vTy
          let fullVal ← mkLambdaFVars fvars vExpr
          return (fullTy, fullVal)
        withLetDecl letName letTy letVal binderContract letKind false fun fvId _ => do
          let bodyExpr ← elabRec bodyStx expectedType?
          let nonDep := !containsFVar fvId bodyExpr
          let absBody := abstractFVar fvId bodyExpr
          let lc : Ixon.LetContract := { nonDep, kind := letKind, binder := binderContract }
          modify fun st => { st with localLetContracts := st.localLetContracts.push lc }
          let letExpr := Expr.mkLetContract letName letTy letVal absBody nonDep binderContract letKind
          ensureHasType fuel stx letExpr expectedType?
      -- 3.15. `have h [: T] := v; body` (`SyntaxKind.haveTerm` — non-dependent `letE`)
      else if kind == SyntaxKind.haveTerm then
        let idStx     := args.getD 1 .missing
        let optTyNode := args.getD 2 .missing
        let valStx    := args.getD 4 .missing
        let bodyStx   := args.getD 6 .missing
        let hName :=
          let id := Syntax.getId idStx
          if Name.isAnonymous id then Name.simple "h" else id
        let expTy? ←
          if Syntax.getNumArgs optTyNode >= 2 then
            let t ← elabRec (Syntax.getArg optTyNode 1) none
            let _ ← ensureSort 32 t
            pure (some t)
          else
            pure none
        let vExpr ← elabRec valStx expTy?
        let vTy ← match expTy? with
          | some t => pure t
          | none   => inferType fuel vExpr
        withLetDecl hName vTy vExpr default .value true fun fvId _ => do
          let bodyExpr ← elabRec bodyStx expectedType?
          let absBody := abstractFVar fvId bodyExpr
          let lc : Ixon.LetContract := { nonDep := true, kind := .value, binder := default }
          modify fun st => { st with localLetContracts := st.localLetContracts.push lc }
          let res := Expr.mkLetE hName vTy vExpr absBody true
          ensureHasType fuel stx res expectedType?
      -- 3.16. Projection `base.field` or `base.0` (`SyntaxKind.projTerm`)
      else if kind == SyntaxKind.projTerm then
        let baseStx  := args.getD 0 .missing
        let fieldStx := args.getD 2 .missing
        let baseExpr ← elabRec baseStx none
        let projExpr ← elabProjOnExpr fuel baseExpr fieldStx
        ensureHasType fuel stx projExpr expectedType?
      -- 3.17. Binary infix operator `lhs op rhs` (`SyntaxKind.binOpTerm`)
      else if kind == SyntaxKind.binOpTerm then
        let lhsStx := args.getD 0 .missing
        let opAtom := args.getD 1 .missing
        let rhsStx := args.getD 2 .missing
        let sym := Syntax.getAtomVal opAtom
        -- Fast lookup in `findBuiltinOpTarget?` (avoiding `defaultParserEnv` rebuild in `IxVM`)
        let targetName? := (findBuiltinOpTarget? sym).orElse fun _ =>
          (defaultParserEnv.operators.find? (fun op => op.symbol == sym)).bind (·.targetFn)
        let st ← get
        match targetName? with
        | some targetName =>
          -- Special handling for `=` (`Eq`), `≠` (`Ne`)
          if (sym == "=" && st.env.contains (Name.simple "Eq")) ||
             (sym == "≠" && st.env.contains (Name.simple "Ne")) then
            let relName := if sym == "=" then Name.simple "Eq" else Name.simple "Ne"
            let lhs ← elabRec lhsStx none
            let lhsTyRaw ← inferType fuel lhs
            let lhsTy ← instantiateMVars 16 lhsTyRaw
            let rhs ← elabRec rhsStx (some lhsTy)
            let u ← ensureSort 32 lhsTy
            let uNorm := normalizeLevel u
            let relExpr := Expr.mkAppN (Expr.mkConst relName #[uNorm]) #[lhsTy, lhs, rhs]
            ensureHasKnownType fuel stx relExpr Expr.mkProp expectedType?
          else
            -- Check if `targetName` exists in `st.env`; otherwise try common fallbacks (e.g. `Nat.add`, `And`, etc.)
            let actualFnName? : Option Ix.Name :=
              if st.env.contains targetName then some targetName
              else match sym with
                | "+"  => if st.env.contains (Name.mkStr2 "Nat" "add") then some (Name.mkStr2 "Nat" "add") else none
                | "-"  => if st.env.contains (Name.mkStr2 "Nat" "sub") then some (Name.mkStr2 "Nat" "sub") else none
                | "*"  => if st.env.contains (Name.mkStr2 "Nat" "mul") then some (Name.mkStr2 "Nat" "mul") else none
                | "/"  => if st.env.contains (Name.mkStr2 "Nat" "div") then some (Name.mkStr2 "Nat" "div") else none
                | "%"  => if st.env.contains (Name.mkStr2 "Nat" "mod") then some (Name.mkStr2 "Nat" "mod") else none
                | "==" => if st.env.contains (Name.mkStr2 "Nat" "beq") then some (Name.mkStr2 "Nat" "beq") else none
                | "≤" | "<=" => if st.env.contains (Name.mkStr2 "Nat" "ble") then some (Name.mkStr2 "Nat" "ble") else none
                | _    => none
            match actualFnName? with
            | some fnName =>
              let fnIdStx := Syntax.mkSimpleIdent fnName
              let appStx := Syntax.mkNode SyntaxKind.appTerm
                #[Syntax.mkNode SyntaxKind.appTerm #[fnIdStx, lhsStx], rhsStx]
              elabRec appStx expectedType?
            | none =>
              -- Try resolving `targetName`'s short component in current lexical scope!
              let short := match Name.components targetName with
                | _ :: s :: _ => Name.simple s
                | [s]         => Name.simple s
                | []          => targetName
              let fnIdStx := Syntax.mkSimpleIdent short
              let appStx := Syntax.mkNode SyntaxKind.appTerm
                #[Syntax.mkNode SyntaxKind.appTerm #[fnIdStx, lhsStx], rhsStx]
              elabRec appStx expectedType?
        | none =>
          throwElabError s!"unknown binary operator '{sym}'" (some stx)
      -- 3.18. Unary operator (`¬`, `!`, `-`) (`SyntaxKind.unaryOpTerm`)
      else if kind == SyntaxKind.unaryOpTerm then
        let opSym := Syntax.getAtomVal (args.getD 0 .missing)
        let argStx := args.getD 1 .missing
        let fnName := match opSym with
          | "¬" => Name.simple "Not"
          | "!" => Name.mkStr2 "Bool" "not"
          | _   => Name.mkStr2 "Neg" "neg"
        let appStx := Syntax.mkNode SyntaxKind.appTerm #[Syntax.mkSimpleIdent fnName, argStx]
        elabRec appStx expectedType?
      -- 3.19. Anonymous constructor `⟨a₁, ..., aₙ⟩` (`SyntaxKind.anonCtor`)
      else if kind == SyntaxKind.anonCtor then
        let elemStxs := Syntax.getArgs (args.getD 1 .missing)
        match expectedType? with
        | none =>
          throwElabError "anonymous constructor ⟨...⟩ requires a known expected type" (some stx)
        | some expTy =>
          let expTyWhnf ← whnf fuel expTy
          let (headFn, _) := getAppFnArgs expTyWhnf
          let st ← get
          match headFn with
          | .const indName _ _ =>
            match st.env.find? indName with
            | some (.inductInfo ival) =>
              match ival.ctors[0]? with
              | some ctorName =>
                let ctorIdStx := Syntax.mkSimpleIdent ctorName
                let appStx := elemStxs.foldl (fun acc e =>
                  Syntax.mkNode SyntaxKind.appTerm #[acc, e]) ctorIdStx
                elabRec appStx (some expTyWhnf)
              | none => throwElabError s!"inductive '{Name.toStringTotal indName}' has no constructors for ⟨...⟩" (some stx)
            | _ => throwElabError s!"expected inductive/structure type for ⟨...⟩, got '{Name.toStringTotal indName}'" (some stx)
          | _ => throwElabError "expected known inductive or structure type for ⟨...⟩" (some stx)
      -- 3.20. Structure instance `{ [base with] field₁ := val₁, ... }` (`SyntaxKind.structInst`)
      else if kind == SyntaxKind.structInst then
        let withNode    := args.getD 1 .missing
        let assignsNode := args.getD 2 .missing
        let baseExpr? ←
          if Syntax.isNone withNode || Syntax.isMissing withNode then
            pure none
          else
            let b ← elabRec withNode expectedType?
            pure (some b)
        let expTy ← match expectedType?, baseExpr? with
          | some t, _ => whnf fuel t
          | none, some b =>
            let bTy ← inferType fuel b
            whnf fuel bTy
          | none, none =>
            throwElabError "structure literal '{ ... }' requires an expected structure type" (some stx)
        let (headFn, _) := getAppFnArgs expTy
        let st ← get
        match headFn with
        | .const structName _ _ =>
          match st.env.structTable.get? structName with
          | none =>
            throwElabError s!"'{Name.toStringTotal structName}' is not a registered structure" (some stx)
          | some sInfo =>
            -- Map field assignments `field := val`
            let mut assignedMap : NameMap Ix.Syntax := NameMap.empty
            for assignStx in Syntax.getArgs assignsNode do
              let fId := Syntax.getId (Syntax.getArg assignStx 0)
              let vStx := Syntax.getArg assignStx 2
              assignedMap := assignedMap.insert fId vStx
            let (ctorConst, ctorTy) ← mkConstWithFreshMVarLevels sInfo.ctorName
            let (ctorApplied, instGoals, afterParamsTy) ← insertImplicitArgs 16 ctorConst ctorTy []
            let mut curFn := ctorApplied
            let mut curTy := afterParamsTy
            for fInfo in sInfo.fields do
              let curTyWhnf ← whnf fuel curTy
              let (domTy, nextBody) ← match stripMData curTyWhnf with
                | .forallE _ d b _ _ => pure (d, b)
                | _ => throwElabError s!"unexpected constructor type for structure '{Name.toStringTotal structName}'" (some stx)
              let fValExpr ← match assignedMap.get? fInfo.fieldName with
                | some vStx => elabRec vStx (some domTy)
                | none =>
                  match baseExpr?, fInfo.defaultVal with
                  | some bExpr, _ =>
                    pure (Expr.mkProj structName fInfo.fieldIdx bExpr)
                  | none, some defStx =>
                    elabRec defStx (some domTy)
                  | none, none =>
                    throwElabError s!"missing field '{Name.toStringTotal fInfo.fieldName}' in structure '{Name.toStringTotal structName}'" (some stx)
              curFn := Expr.mkApp curFn fValExpr
              curTy := instantiate1 nextBody fValExpr
            for g in instGoals.reverse do
              let gTy ← inferType fuel g
              if let some instVal ← synthInstance? 8 gTy then
                let _ ← isDefEq fuel g instVal
            ensureHasType fuel stx curFn (some expTy)
        | _ =>
          throwElabError "structure literal '{ ... }' requires a known structure type" (some stx)
      -- 3.21. Tuple `(a, b, ...)` (`SyntaxKind.tupleTerm`)
      else if kind == SyntaxKind.tupleTerm then
        if args.size == 2 then
          -- `()` unit literal
          let st ← get
          let unitCtor :=
            if st.env.contains (Name.mkStr2 "Unit" "unit") then Name.mkStr2 "Unit" "unit"
            else Name.mkStr2 "PUnit" "unit"
          let (e, _) ← mkConstWithFreshMVarLevels unitCtor
          ensureHasType fuel stx e expectedType?
        else
          let first := args.getD 1 .missing
          let rest := (Syntax.getArgs (args.getD 3 .missing)).toList
          let allElems := first :: rest
          let rec buildPairs : List Ix.Syntax → Ix.Syntax
            | []      => Syntax.mkSimpleIdent (Name.mkStr2 "Unit" "unit")
            | [x]     => x
            | x :: xs =>
              let rhs := buildPairs xs
              let prodMk := Syntax.mkSimpleIdent (Name.mkStr2 "Prod" "mk")
              Syntax.mkNode SyntaxKind.appTerm
                #[Syntax.mkNode SyntaxKind.appTerm #[prodMk, x], rhs]
          elabRec (buildPairs allElems) expectedType?
      -- 3.22. List literal `[a, b, c]` (`SyntaxKind.listLit`)
      else if kind == SyntaxKind.listLit then
        let elems := (Syntax.getArgs (args.getD 1 .missing)).toList
        let rec buildList : List Ix.Syntax → Ix.Syntax
          | []      => Syntax.mkSimpleIdent (Name.mkStr2 "List" "nil")
          | x :: xs =>
            let tail := buildList xs
            let consId := Syntax.mkSimpleIdent (Name.mkStr2 "List" "cons")
            Syntax.mkNode SyntaxKind.appTerm
              #[Syntax.mkNode SyntaxKind.appTerm #[consId, x], tail]
        elabRec (buildList elems) expectedType?
      -- 3.23. `if [h :] cond then t else e` (`SyntaxKind.ifTerm`)
      else if kind == SyntaxKind.ifTerm then
        let isDep := args.size == 8
        let condStx := if isDep then args.getD 3 .missing else args.getD 2 .missing
        let thenStx := if isDep then args.getD 5 .missing else args.getD 4 .missing
        let elseStx := if isDep then args.getD 7 .missing else args.getD 6 .missing
        let st ← get
        if st.env.contains (Name.mkStr2 "Bool" "casesOn") && !isDep then
          -- Lower boolean `if c then t else e` directly to `Bool.casesOn (motive := fun _ => T) c e t`
          -- (since `Bool.false` has `cidx = 0` and `Bool.true` has `cidx = 1`!)
          let boolTy := Expr.mkConst (Name.simple "Bool") #[]
          let condExpr ← elabRec condStx (some boolTy)
          let branchTy ← match expectedType? with
            | some t => pure t
            | none =>
              let u ← mkFreshLevelMVar
              mkFreshExprMVar (Expr.mkSort u)
          let thenExpr ← elabRec thenStx (some branchTy)
          let elseExpr ← elabRec elseStx (some branchTy)
          let branchSort ← ensureSort 32 branchTy
          let motive := Expr.mkLam (Name.simple "b") boolTy (liftLooseBVars branchTy 1) .default
          let casesOnConst := Expr.mkConst (Name.mkStr2 "Bool" "casesOn") #[branchSort]
          let res := Expr.mkAppN casesOnConst #[motive, condExpr, elseExpr, thenExpr]
          ensureHasType fuel stx res expectedType?
        else
          let iteId := Syntax.mkSimpleIdent (if isDep then Name.simple "dite" else Name.simple "ite")
          let appStx := #[condStx, thenStx, elseStx].foldl
            (fun acc a => Syntax.mkNode SyntaxKind.appTerm #[acc, a]) iteId
          elabRec appStx expectedType?
      -- 3.24. Pattern matching `match d with | pat => rhs ...` (`SyntaxKind.matchTerm`)
      else if kind == SyntaxKind.matchTerm then
        let discrs := Syntax.getArgs (args.getD 1 .missing)
        let alts   := Syntax.getArgs (args.getD 3 .missing)
        if discrs.isEmpty then
          throwElabError "match expression requires at least one discriminant" (some stx)
        let discrStx := discrs.getD 0 .missing
        let discrExpr ← elabRec discrStx none
        let discrTy ← inferType fuel discrExpr
        let discrTyWhnf ← whnf fuel discrTy
        let (headFn, headArgs) := getAppFnArgs discrTyWhnf
        let resTy ← match expectedType? with
          | some t => pure t
          | none =>
            let u ← mkFreshLevelMVar
            mkFreshExprMVar (Expr.mkSort u)
        let ctx ← read
        let st ← get
        match headFn with
        | .const indName indUnivs _ =>
          match st.env.find? indName with
          | some (.inductInfo ival) =>
            let casesOnName := Name.mkStr indName "casesOn"
            match st.env.find? casesOnName with
            | some (.defnInfo casesOnDef) =>
              -- Determine motive universe level if `casesOn` takes an extra universe param
              let casesOnUnivs ←
                if casesOnDef.cnst.levelParams.size == indUnivs.size + 1 then
                  let uMot ← ensureSort 32 resTy
                  pure (#[uMot] ++ indUnivs)
                else
                  pure indUnivs
              let params := headArgs.extract 0 ival.numParams
              let indices := headArgs.extract ival.numParams headArgs.size
              -- Build motive `λ (i₁ : Idx₁) ... (x : I params indices) => resTy`
              let (_, _, afterParams) := openForallTelescope ival.numParams
                (substExprLevelParams ival.cnst.levelParams indUnivs ival.cnst.type) "mp" 0 #[] #[]
              let afterParamsInst := params.foldl (fun cur p =>
                match stripMData cur with
                | .forallE _ _ b _ _ => instantiate1 b p
                | other => other) (substExprLevelParams ival.cnst.levelParams indUnivs ival.cnst.type)
              let _ := afterParams
              let (idxFVars, idxDecls, _) := openForallTelescope ival.numIndices afterParamsInst "midx" 0 #[] #[]
              let majDom := Expr.mkAppN (Expr.mkConst indName indUnivs) (params ++ idxFVars)
              let (majFvId, _) := mkAuxFVar "mmaj" 0
              let majDecl : AuxLocalDecl := { fvarId := majFvId, binderName := Name.simple "x", domain := majDom }
              let motiveLam := closeLambdas (idxDecls.push majDecl) resTy

              -- For each constructor `ctorName` in canonical `ival.ctors`, find the matching `matchAlt`
              let mut minorExprs : Array Ix.Expr := #[]
              for ctorName in ival.ctors do
                match st.env.find? ctorName with
                | some (.ctorInfo cval) =>
                  -- Find first matching alternative: either constructor pattern for `ctorName` or catch-all variable/`_`
                  let matchedAlt? := alts.findSome? fun altStx =>
                    let pats := Syntax.getArgs (Syntax.getArg altStx 1)
                    let pat0 := pats.getD 0 .missing
                    let rhsStx := Syntax.getArg altStx 3
                    match decodeConstructorPattern ctx.scope ctx.modIdx st.env pat0 with
                    | some (patCtor, varNames) =>
                      if patCtor == ctorName then some (some varNames, none, rhsStx)
                      else none
                    | none =>
                      -- Catch-all variable or `_` pattern
                      let catchVar :=
                        if Syntax.isOfKind pat0 SyntaxKind.holeTerm || Syntax.getAtomVal pat0 == "_" then
                          Name.mkAnon
                        else
                          Syntax.getId pat0
                      some (none, some catchVar, rhsStx)
                  match matchedAlt? with
                  | none =>
                    throwElabError s!"non-exhaustive match: missing case for constructor '{Name.toStringTotal ctorName}'" (some stx)
                  | some (ctorVars?, catchVar?, rhsStx) =>
                    -- Open the constructor's `numFields` field binders into `lctx`
                    let ctorInstTy := params.foldl (fun cur p =>
                      match stripMData cur with
                      | .forallE _ _ b _ _ => instantiate1 b p
                      | other => other) (substExprLevelParams cval.cnst.levelParams indUnivs cval.cnst.type)
                    let rec elabCtorFields (remFields : Nat) (curCtorTy : Ix.Expr)
                        (fIdx : Nat) (fvarIds : Array Ix.Name) (fvarExprs : Array Ix.Expr) : IxElabM Ix.Expr := do
                      match remFields with
                      | 0 =>
                        -- If this was a catch-all variable `v`, bind `v := ctor params fvarExprs`
                        match catchVar? with
                        | some vName =>
                          if !Name.isAnonymous vName then
                            let ctorApp := Expr.mkAppN (Expr.mkConst ctorName indUnivs) (params ++ fvarExprs)
                            let ctorAppTy ← inferType fuel ctorApp
                            withLetDecl vName ctorAppTy ctorApp default .value false fun _ _ => do
                              let rhsExpr ← elabRec rhsStx (some resTy)
                              mkLambdaFVars fvarIds rhsExpr
                          else
                            let rhsExpr ← elabRec rhsStx (some resTy)
                            mkLambdaFVars fvarIds rhsExpr
                        | none =>
                          let rhsExpr ← elabRec rhsStx (some resTy)
                          mkLambdaFVars fvarIds rhsExpr
                      | rem + 1 =>
                        let curW ← whnf fuel curCtorTy
                        match stripMData curW with
                        | .forallE defName fDom fBody _ _ =>
                          let userVarName := match ctorVars? with
                            | some vs =>
                              let vn := vs.getD fIdx Name.mkAnon
                              if Name.isAnonymous vn then defName else vn
                            | none => defName
                          withLocalDecl userVarName fDom .default default fun fvId fvExpr =>
                            elabCtorFields rem (instantiate1 fBody fvExpr) (fIdx + 1)
                              (fvarIds.push fvId) (fvarExprs.push fvExpr)
                        | _ =>
                          throwElabError s!"unexpected constructor type for '{Name.toStringTotal ctorName}'" (some stx)
                    let minorLam ← elabCtorFields cval.numFields ctorInstTy 0 #[] #[]
                    minorExprs := minorExprs.push minorLam
                | _ =>
                  throwElabError s!"missing constructor info for '{Name.toStringTotal ctorName}'" (some stx)
              let casesOnConst := Expr.mkConst casesOnName casesOnUnivs
              let fullApp := Expr.mkAppN casesOnConst
                (params ++ #[motiveLam] ++ indices ++ #[discrExpr] ++ minorExprs)
              ensureHasType fuel stx fullApp (some resTy)
            | _ =>
              throwElabError s!"'{Name.toStringTotal casesOnName}' not found for match expression" (some stx)
          | _ =>
            throwElabError s!"discriminant type '{Name.toStringTotal indName}' is not an inductive type" (some stx)
        | _ =>
          throwElabError "match discriminant must have an inductive type" (some discrStx)
      -- 3.25. Tactic block `by tac₁; tac₂; ...` (`SyntaxKind.byTactic`)
      else if kind == SyntaxKind.byTactic then
        let tacSeq := args.getD 1 .missing
        let goalTy ← match expectedType? with
          | some t => pure t
          | none   =>
            let u ← mkFreshLevelMVar
            mkFreshExprMVar (Expr.mkSort u)
        let rootGoal ← mkFreshExprMVar goalTy (Name.simple "goal")
        let rootGoalId := match rootGoal with
          | .mvar id _ => id
          | _          => Name.mkAnon
        evalTacticSeq elabRec fuel tacSeq rootGoalId
        let solved ← instantiateMVars 32 rootGoal
        ensureHasType fuel stx solved expectedType?
      -- 3.26. Function application `f a₁ ... aₙ` (`SyntaxKind.appTerm`)
      else if kind == SyntaxKind.appTerm then
        let (fnStx, argStxs) := flattenAppSyntax 256 stx []
        let isExplicitAt :=
          Syntax.isOfKind fnStx SyntaxKind.explicitTerm &&
          Syntax.getAtomVal (Syntax.getArg fnStx 0) == "@"
        let fnExpr ← elabRec fnStx none
        let fnTy ← inferType fuel fnExpr
        let mut curFn := fnExpr
        let mut curTy := fnTy
        let mut pendingInstGoals : List Ix.Expr := []
        for argStx in argStxs.toList do
          if !isExplicitAt then
            let (fn', instGs, ty') ← insertImplicitArgs 16 curFn curTy pendingInstGoals
            curFn := fn'
            pendingInstGoals := instGs
            curTy := ty'
          let curTyWhnf ← whnfForall fuel curTy
          match stripMData curTyWhnf with
          | .forallE _ dom body _ _ =>
            let argExpr ← elabRec argStx (some dom)
            curFn := Expr.mkApp curFn argExpr
            curTy := instantiate1 body argExpr
          | _ =>
            -- Unify `curTyWhnf` with `(x : ?A) → ?B`
            let u1 ← mkFreshLevelMVar
            let u2 ← mkFreshLevelMVar
            let domMVar ← mkFreshExprMVar (Expr.mkSort u1)
            let codMVar ← mkFreshExprMVar (Expr.mkSort u2)
            let arrowTy := Expr.mkArrow domMVar (liftLooseBVars codMVar 1)
            let _ ← isDefEq fuel curTyWhnf arrowTy
            let argExpr ← elabRec argStx (some domMVar)
            curFn := Expr.mkApp curFn argExpr
            curTy := codMVar
        -- Solve pending `[...]` typeclass instance goals now that arguments are unified
        for instGoal in pendingInstGoals.reverse do
          let gTy ← inferType fuel instGoal
          if let some instVal ← synthInstance? 8 gTy then
            let _ ← isDefEq fuel instGoal instVal
        ensureHasKnownType fuel stx curFn curTy expectedType?
      else
        throwElabError s!"unsupported syntax node '{Name.toStringTotal kind}' in term" (some stx)

end Ix.Frontend.Elab
