/-
  Ix.Frontend.SccPass: Pass 2 & Pass 3 of the Ix Frontend —
  Binder-Aware Free Identifier Extraction and Tarjan SCC Dependency Scheduling.

  Enables order-free and `mutual`-free `.ix` source files:
  - Declarations may appear in any top-to-bottom order without forward-reference errors.
  - Mutual recursion (value-level or inductive) is inferred automatically via Tarjan's
    strongly connected components algorithm (`Ix.Compile.Canon.condensation`).
  - Typeclass `instance` declarations are automatically scheduled before declarations
    that mention their carrier types whenever doing so does not introduce a cycle.
-/
module

public import Ix.Frontend.Scope
public import Ix.Compile.Canon.Graph

@[expose] public section

namespace Ix.Frontend

open Ix.Frontend.Parser

/-! ## Pass 2: Binder-Aware Syntax Reference Extraction -/

/-- Dependency summary extracted for a single `ModuleDecl`. -/
structure DeclDepInfo where
  declIdx     : Nat
  sigRefs     : Array Nat := #[]
  bodyRefs    : Array Nat := #[]
  carrierRefs : Array Nat := #[]
  deriving Repr, Inhabited

/-- Insert a declaration index `dIdx` into an `Array Nat` if not already present. -/
def pushUniqueNat (arr : Array Nat) (x : Nat) : Array Nat :=
  if arr.toList.contains x then arr else arr.push x

/-- Extract the bound variable names from a single binder `Syntax` node
    (`explicitBinder`, `implicitBinder`, `strictImplicitBinder`, `instBinder`). -/
def extractBinderNames (binderStx : Ix.Syntax) : List Ix.Name :=
  let k := Syntax.getKind binderStx
  if k == SyntaxKind.explicitBinder || k == SyntaxKind.implicitBinder ||
     k == SyntaxKind.strictImplicitBinder || k == SyntaxKind.instBinder then
    let idsNode := Syntax.getArg binderStx 1
    (Syntax.getArgs idsNode).toList.filterMap fun idStx =>
      let id := Syntax.getId idStx
      if Name.isAnonymous id then none else some id
  else
    let id := Syntax.getId binderStx
    if Name.isAnonymous id then [] else [id]

/-- Extract the optional type `Syntax` from a single binder node. -/
def extractBinderType? (binderStx : Ix.Syntax) : Option Ix.Syntax :=
  let k := Syntax.getKind binderStx
  if k == SyntaxKind.explicitBinder || k == SyntaxKind.implicitBinder ||
     k == SyntaxKind.strictImplicitBinder || k == SyntaxKind.instBinder then
    let tyNode := Syntax.getArg binderStx 3
    if Syntax.isNone tyNode || Syntax.isMissing tyNode then none
    else some tyNode
  else
    none

/-- Extract pattern-bound variable names from a pattern `Syntax` tree, treating
    known module/external constructors as constants rather than pattern variables.
    Also records any constructor owner declaration indices into `accRefs`. -/
def scanPattern (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (isExtCtor : Ix.Name → Bool) :
    Nat → Ix.Syntax → NameSet × Array Nat → NameSet × Array Nat
  | 0, _, state => state
  | fuel + 1, pat, (bound, refs) =>
    match pat with
    | .missing | .atom _ _ => (bound, refs)
    | .ident _ _ id _ =>
      if Name.isAnonymous id then (bound, refs)
      else
        let resolved := resolveIdentInScope scope modIdx isExtConst id
        match modIdx.ctorToInd.get? resolved with
        | some (_, ownerIdx) =>
          (bound, pushUniqueNat refs ownerIdx)
        | none =>
          if isExtCtor resolved then
            (bound, refs)
          else
            -- Unqualified single-component identifier in pattern position binds a local variable
            match id with
            | .str (.anonymous _) _ _ => (bound.insert id, refs)
            | _ =>
              match modIdx.findOwnerIdx? resolved with
              | some ownerIdx => (bound, pushUniqueNat refs ownerIdx)
              | none => (bound, refs)
    | .node _ kind args =>
      if kind == SyntaxKind.numLit || kind == SyntaxKind.strLit ||
         kind == SyntaxKind.charLit || kind == SyntaxKind.holeTerm then
        (bound, refs)
      else if kind == SyntaxKind.appTerm then
        -- Head of pattern application is typically a constructor
        let fn := args.getD 0 .missing
        let arg := args.getD 1 .missing
        let (bound, refs) := match fn with
          | .ident _ _ fnId _ =>
            let resolved := resolveIdentInScope scope modIdx isExtConst fnId
            match modIdx.findOwnerIdx? resolved with
            | some ownerIdx => (bound, pushUniqueNat refs ownerIdx)
            | none => scanPattern scope modIdx isExtConst isExtCtor fuel fn (bound, refs)
          | _ => scanPattern scope modIdx isExtConst isExtCtor fuel fn (bound, refs)
        scanPattern scope modIdx isExtConst isExtCtor fuel arg (bound, refs)
      else
        args.foldl (fun st child => scanPattern scope modIdx isExtConst isExtCtor fuel child st)
          (bound, refs)

/-- Scan a sequence of binders left-to-right using `scanRec`, adding each binder's names to `locals`
    after scanning its domain type. -/
def scanBinderArray (scanRec : NameSet → Ix.Syntax → Array Nat → Array Nat)
    (locals : NameSet) (binders : Array Ix.Syntax) (refs : Array Nat) : NameSet × Array Nat :=
  binders.toList.foldl (fun (loc, r) b =>
    let r' := match extractBinderType? b with
      | some ty => scanRec loc ty r
      | none    => r
    let names := extractBinderNames b
    let loc' := names.foldl (fun s n => s.insert n) loc
    (loc', r')) (locals, refs)

/-- Scan a term/type/tactic `Syntax` tree with lexical `scope` and bound local variables `locals`,
    accumulating indices of referenced module declarations in `refs`.
    Structurally recursive on `fuel : Nat`. -/
def scanSyntaxRefs (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (isExtCtor : Ix.Name → Bool) :
    Nat → NameSet → Ix.Syntax → Array Nat → Array Nat
  | 0, _, _, refs => refs
  | fuel + 1, locals, stx, refs =>
    let scanRec := scanSyntaxRefs scope modIdx isExtConst isExtCtor fuel
    match stx with
    | .missing | .atom _ _ => refs
    | .ident _ _ id _ =>
      if Name.isAnonymous id || locals.contains id then
        refs
      else
        let resolved := resolveIdentInScope scope modIdx isExtConst id
        match modIdx.findOwnerIdx? resolved with
        | some ownerIdx => pushUniqueNat refs ownerIdx
        | none =>
          -- Also check if `id` is a hierarchical projection `<ModDecl>.<fieldOrCtor>`
          match id with
          | .str pre _ _ =>
            if !Name.isAnonymous pre && !locals.contains pre then
              let resPre := resolveIdentInScope scope modIdx isExtConst pre
              match modIdx.findOwnerIdx? resPre with
              | some ownerIdx => pushUniqueNat refs ownerIdx
              | none => refs
            else
              refs
          | _ => refs
    | .node _ kind args =>
      -- 1. `fun binders => body`
      if kind == SyntaxKind.funTerm then
        let binders := Syntax.getArgs (args.getD 1 .missing)
        let body := args.getD 3 .missing
        let (locals', refs') := scanBinderArray scanRec locals binders refs
        scanRec locals' body refs'
      -- 2. `forall binders, vPref body` or `(binders) → vPref body`
      else if kind == SyntaxKind.forallTerm then
        let isKwForall := match args[0]? with
          | some (.atom _ kw) => kw == "forall" || kw == "∀"
          | _ => false
        let binders := Syntax.getArgs (if isKwForall then args.getD 1 .missing else args.getD 0 .missing)
        let body := if isKwForall then args.getD 4 .missing else args.getD 3 .missing
        let (locals', refs') := scanBinderArray scanRec locals binders refs
        scanRec locals' body refs'
      -- 3. `let bPref id binders optType := val; body`
      else if kind == SyntaxKind.letTerm then
        let idStx := args.getD 2 .missing
        let binders := Syntax.getArgs (args.getD 3 .missing)
        let optTy := args.getD 4 .missing
        let val := args.getD 6 .missing
        let body := args.getD 8 .missing
        let (localsBind, refs) := scanBinderArray scanRec locals binders refs
        let refs := scanRec localsBind optTy refs
        let refs := scanRec localsBind val refs
        let letId := Syntax.getId idStx
        let localsBody := if Name.isAnonymous letId then locals else locals.insert letId
        scanRec localsBody body refs
      -- 4. `let borrow bPref id binders optType := val; body`
      else if kind == SyntaxKind.letBorrowTerm then
        let idStx := args.getD 3 .missing
        let binders := Syntax.getArgs (args.getD 4 .missing)
        let optTy := args.getD 5 .missing
        let val := args.getD 7 .missing
        let body := args.getD 9 .missing
        let (localsBind, refs) := scanBinderArray scanRec locals binders refs
        let refs := scanRec localsBind optTy refs
        let refs := scanRec localsBind val refs
        let letId := Syntax.getId idStx
        let localsBody := if Name.isAnonymous letId then locals else locals.insert letId
        scanRec localsBody body refs
      -- 5. `have id optType := val; body`
      else if kind == SyntaxKind.haveTerm then
        let idStx := args.getD 1 .missing
        let optTy := args.getD 2 .missing
        let val := args.getD 4 .missing
        let body := args.getD 6 .missing
        let refs := scanRec locals optTy refs
        let refs := scanRec locals val refs
        let haveId := Syntax.getId idStx
        let localsBody := if Name.isAnonymous haveId then locals else locals.insert haveId
        scanRec localsBody body refs
      -- 6. `if [h :] cond then t else e`
      else if kind == SyntaxKind.ifTerm then
        if args.size == 8 then
          let hId := Syntax.getId (args.getD 1 .missing)
          let cond := args.getD 3 .missing
          let thenBr := args.getD 5 .missing
          let elseBr := args.getD 7 .missing
          let refs := scanRec locals cond refs
          let locals' := if Name.isAnonymous hId then locals else locals.insert hId
          let refs := scanRec locals' thenBr refs
          scanRec locals' elseBr refs
        else
          let cond := args.getD 2 .missing
          let thenBr := args.getD 4 .missing
          let elseBr := args.getD 6 .missing
          let refs := scanRec locals cond refs
          let refs := scanRec locals thenBr refs
          scanRec locals elseBr refs
      -- 7. `| pat1, pat2 => rhs` (`matchAlt`)
      else if kind == SyntaxKind.matchAlt then
        let pats := Syntax.getArgs (args.getD 1 .missing)
        let rhs := args.getD 3 .missing
        let (locals', refs') := pats.foldl
          (fun st p => scanPattern scope modIdx isExtConst isExtCtor fuel p st)
          (locals, refs)
        scanRec locals' rhs refs'
      -- 8. Projection `base.field`: scan `base`, and also check if `field` is a known structure field
      else if kind == SyntaxKind.projTerm then
        let base := args.getD 0 .missing
        let fieldNode := args.getD 2 .missing
        let refs := scanRec locals base refs
        let fieldId := Syntax.getId fieldNode
        if Name.isAnonymous fieldId then refs
        else
          -- Check if base is an identifier prefix
          let refs := match base with
            | .ident _ _ bId _ =>
              if !locals.contains bId then
                let combined := Name.append bId fieldId
                let resCombined := resolveIdentInScope scope modIdx isExtConst combined
                match modIdx.findOwnerIdx? resCombined with
                | some ownerIdx => pushUniqueNat refs ownerIdx
                | none => refs
              else refs
            | _ => refs
          refs
      -- 9. Tactic sequence: handle `intro`, `have`, `let`, `cases`/`induction` alternatives
      else if kind == SyntaxKind.tacticSeq then
        let (_, refs') := args.foldl (fun (loc, r) tac =>
          let tk := Syntax.getKind tac
          if tk == SyntaxKind.tacticIntro then
            let ids := (Syntax.getArgs (Syntax.getArg tac 1)).toList.map Syntax.getId
            let loc' := ids.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) loc
            (loc', r)
          else if tk == SyntaxKind.tacticHave then
            let hId := Syntax.getId (Syntax.getArg tac 1)
            let ty := Syntax.getArg tac 3
            let val := Syntax.getArg tac 5
            let r := scanRec loc ty r
            let r := scanRec loc val r
            let loc' := if Name.isAnonymous hId then loc else loc.insert hId
            (loc', r)
          else if tk == SyntaxKind.tacticLet then
            let lId := Syntax.getId (Syntax.getArg tac 1)
            let optTy := Syntax.getArg tac 2
            let val := Syntax.getArg tac 4
            let r := scanRec loc optTy r
            let r := scanRec loc val r
            let loc' := if Name.isAnonymous lId then loc else loc.insert lId
            (loc', r)
          else
            (loc, scanRec loc tac r)
        ) (locals, refs)
        refs'
      else if kind == SyntaxKind.tacticAlt then
        -- `| tag x y => tacSeq`
        let boundIds := (Syntax.getArgs (args.getD 2 .missing)).toList.map Syntax.getId
        let locals' := boundIds.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) locals
        let seq := args.getD 4 .missing
        scanRec locals' seq refs
      else
        -- Default: scan all child syntax nodes with the same `locals`
        args.toList.foldl (fun acc child =>
          scanRec locals child acc) refs

/-- Extract `DeclDepInfo` (`sigRefs`, `bodyRefs`, `carrierRefs`) for a single `ModuleDecl`. -/
def extractDeclDeps (modIdx : ModuleIndex) (decl : ModuleDecl)
    (isExtConst : Ix.Name → Bool := fun _ => false)
    (isExtCtor : Ix.Name → Bool := fun _ => false)
    (fuel : Nat := 256) : DeclDepInfo :=
  let scope := decl.scope
  let cmd := decl.stx
  let k := Syntax.getKind cmd
  let scanRec := scanSyntaxRefs scope modIdx isExtConst isExtCtor fuel
  -- 1. Scan section `variable` binders into `sigRefs` and initial `locals`
  let (locals0, sigRefs0) :=
    scanBinderArray scanRec NameSet.empty scope.varBinders #[]
  if k == SyntaxKind.defDecl || k == SyntaxKind.abbrevDecl ||
     k == SyntaxKind.theoremDecl || k == SyntaxKind.opaqueDecl then
    let binders := Syntax.getArgs (Syntax.getArg cmd 4)
    let optType := Syntax.getArg cmd 6
    let (localsSig, sigRefs) :=
      scanBinderArray scanRec locals0 binders sigRefs0
    let sigRefs := scanRec localsSig optType sigRefs
    let bodyNode :=
      if Syntax.getNumArgs cmd == 9 then Syntax.getArg cmd 8
      else Syntax.getArg cmd 7
    let bodyRefs := scanRec localsSig bodyNode #[]
    { declIdx := decl.idx, sigRefs, bodyRefs }
  else if k == SyntaxKind.axiomDecl then
    let binders := Syntax.getArgs (Syntax.getArg cmd 4)
    let ty := Syntax.getArg cmd 6
    let (localsSig, sigRefs) :=
      scanBinderArray scanRec locals0 binders sigRefs0
    let sigRefs := scanRec localsSig ty sigRefs
    { declIdx := decl.idx, sigRefs, bodyRefs := #[] }
  else if k == SyntaxKind.instanceDecl then
    let binders := Syntax.getArgs (Syntax.getArg cmd 4)
    let ty := Syntax.getArg cmd 6
    let (localsSig, sigRefs) :=
      scanBinderArray scanRec locals0 binders sigRefs0
    let tyRefs := scanRec localsSig ty #[]
    let sigRefs := tyRefs.foldl pushUniqueNat sigRefs
    let bodyNode := Syntax.getArg cmd 8
    let bodyRefs := scanRec localsSig bodyNode #[]
    { declIdx := decl.idx, sigRefs, bodyRefs, carrierRefs := tyRefs }
  else if k == SyntaxKind.inductiveDecl then
    -- args: #[modifiers, "inductive", id, univParams, binders, vPref, optType, ctorsNull, derivingNull]
    let binders := Syntax.getArgs (Syntax.getArg cmd 4)
    let optType := Syntax.getArg cmd 6
    let ctorsNode := Syntax.getArg cmd 7
    let derivNode := Syntax.getArg cmd 8
    let (localsSig, sigRefs) :=
      scanBinderArray scanRec locals0 binders sigRefs0
    let sigRefs := scanRec localsSig optType sigRefs
    let bodyRefs := (Syntax.getArgs ctorsNode).foldl (fun acc ctorStx =>
      -- ctorDecl: #["|", id, binders, vPref, optType]
      let cBinders := Syntax.getArgs (Syntax.getArg ctorStx 2)
      let cOptType := Syntax.getArg ctorStx 4
      let (localsCtor, acc) :=
        scanBinderArray scanRec localsSig cBinders acc
      scanRec localsCtor cOptType acc) #[]
    let bodyRefs := scanRec localsSig derivNode bodyRefs
    { declIdx := decl.idx, sigRefs, bodyRefs }
  else if k == SyntaxKind.structureDecl || k == SyntaxKind.classDecl then
    -- args: #[modifiers, kw, id, univParams, binders, extendsNull, vPref, optType, customCtorOrNull, fieldsOrCtorsNull, derivingNull]
    let binders := Syntax.getArgs (Syntax.getArg cmd 4)
    let extendsNode := Syntax.getArg cmd 5
    let optType := Syntax.getArg cmd 7
    let fieldsOrCtorsNode := Syntax.getArg cmd 9
    let derivNode := Syntax.getArg cmd 10
    let (localsSig, sigRefs) :=
      scanBinderArray scanRec locals0 binders sigRefs0
    let sigRefs := scanRec localsSig extendsNode sigRefs
    let sigRefs := scanRec localsSig optType sigRefs
    -- Scan fields sequentially (each field name becomes bound for subsequent dependent fields!)
    let (_, bodyRefs) := (Syntax.getArgs fieldsOrCtorsNode).foldl (fun (loc, acc) item =>
      if Syntax.isOfKind item SyntaxKind.ctorDecl then
        let cBinders := Syntax.getArgs (Syntax.getArg item 2)
        let cOptType := Syntax.getArg item 4
        let (locCtor, acc) :=
          scanBinderArray scanRec loc cBinders acc
        (loc, scanRec locCtor cOptType acc)
      else if Syntax.isOfKind item SyntaxKind.fieldDecl then
        let fArgs := Syntax.getArgs item
        let isBracketed := match fArgs[0]? with
          | some (.atom _ "(") | some (.atom _ "{") => true
          | _ => false
        let idsNode := if isBracketed then Syntax.getArg item 2 else Syntax.getArg item 1
        let tyNode  := if isBracketed then Syntax.getArg item 5 else Syntax.getArg item 4
        let defNode := if isBracketed then Syntax.getArg item 6 else Syntax.getArg item 5
        let acc := scanRec loc tyNode acc
        let acc := scanRec loc defNode acc
        let fIds := (Syntax.getArgs idsNode).toList.map Syntax.getId
        let loc' := fIds.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) loc
        (loc', acc)
      else
        (loc, scanRec loc item acc)
    ) (localsSig, #[])
    let bodyRefs := scanRec localsSig derivNode bodyRefs
    { declIdx := decl.idx, sigRefs, bodyRefs }
  else
    { declIdx := decl.idx }

/-! ## Pass 3: Tarjan SCC Condensation & Intra-SCC Topological Ordering -/

/-- Check whether node `src` can reach `dst` in `adj` (fuel-bounded DFS). -/
def reachesNode (adj : Array (Array Nat)) (src dst : Nat) : Bool :=
  let rec dfs (fuel : Nat) (stack : List Nat) (visited : Array Bool) : Bool :=
    match fuel, stack with
    | 0, _ | _, [] => false
    | fuel + 1, u :: rest =>
      if u == dst then true
      else if visited.getD u false then
        dfs fuel rest visited
      else
        let visited' := if u < visited.size then visited.set! u true else visited
        let nbrs := (adj.getD u #[]).toList
        dfs fuel (nbrs ++ rest) visited'
  dfs (adj.size * adj.size + 16) [src] (Array.replicate adj.size false)

/-- Add cycle-safe scheduling edges `u -> instIdx` whenever declaration `u`
    references a carrier/class type in `inst.carrierRefs` and `instIdx` does not
    reach `u` in `adj`. Ensures `instance`s are elaborated before declarations
    that need them for typeclass synthesis without ever creating false mutual cycles. -/
def addInstanceSchedulingEdges (decls : Array ModuleDecl) (deps : Array DeclDepInfo)
    (adj : Array (Array Nat)) : Array (Array Nat) :=
  let instInfos := deps.toList.filter fun d =>
    match Syntax.listGet? decls.toList d.declIdx with
    | some decl => decl.kind == .inst && !d.carrierRefs.isEmpty
    | none      => false
  instInfos.foldl (fun curAdj inst =>
    let instIdx := inst.declIdx
    (List.range decls.size).foldl (fun accAdj u =>
      if u == instIdx then accAdj
      else
        let uDep := Syntax.listGetD deps.toList u { declIdx := u }
        let uAllRefs := uDep.sigRefs ++ uDep.bodyRefs
        let mentionsCarrier := inst.carrierRefs.toList.any fun c => uAllRefs.toList.contains c
        let curRow := Syntax.listGetD accAdj.toList u #[]
        if mentionsCarrier && !curRow.toList.contains instIdx &&
           !reachesNode accAdj instIdx u then
          accAdj.set! u (curRow.push instIdx)
        else
          accAdj) curAdj) adj

/-- Total, proof-free element lookup on `Array α` via `List` structural recursion
    (avoids `Array.getElem` proof obligations during kernel reduction). -/
def arrayGetD (xs : Array α) (i : Nat) (d : α) : α :=
  let rec go : List α → Nat → α
    | [], _            => d
    | x :: _, 0        => x
    | _ :: rest, k + 1 => go rest k
  go xs.toList i

/-- Total, proof-free in-bounds element update on `Array α` via `List` structural recursion. -/
def arraySetD (xs : Array α) (i : Nat) (v : α) : Array α :=
  let rec go : List α → Nat → List α
    | [], _            => []
    | _ :: rest, 0     => v :: rest
    | x :: rest, k + 1 => x :: go rest k
  Array.mk (go xs.toList i)

/-- Pure, total insertion sort on `Array α` (avoids `Array.qsort` and `Array.foldlM.loop`). -/
def sortArrayBy (xs : Array α) (lt : α → α → Bool) : Array α :=
  let rec insert (x : α) : List α → List α
    | []      => [x]
    | y :: ys => if lt y x then y :: insert x ys else x :: y :: ys
  Array.mk (xs.toList.foldl (fun acc x => insert x acc) [])

/-- Visit node `v` in `TarjanState` using pure `arraySetD`. -/
def tarjanVisit : Ix.Compile.Canon.TarjanState → Nat → Ix.Compile.Canon.TarjanState
  | { index, low, onStack, stack, calls, next, comps, roots, order, exhausted }, v =>
    { index := arraySetD index v next, low := arraySetD low v next,
      onStack := arraySetD onStack v true, stack := v :: stack, calls := (v, 0) :: calls,
      next := next + 1, comps, roots, order := order.push v, exhausted }

/-- Update `low[v] := x` in `TarjanState` using pure `arraySetD`. -/
def tarjanSetLow : Ix.Compile.Canon.TarjanState → Nat → Nat → Ix.Compile.Canon.TarjanState
  | { index, low, onStack, stack, calls, next, comps, roots, order, exhausted }, v, x =>
    { index, low := arraySetD low v x, onStack, stack, calls, next, comps, roots, order, exhausted }

/-- Pop a component rooted at `v` off `TarjanState` using pure `sortArrayBy` (no `Array.qsort`). -/
def tarjanPopComp : Ix.Compile.Canon.TarjanState → Nat → Ix.Compile.Canon.TarjanState
  | { index, low, onStack, stack, calls, next, comps, roots, order, exhausted }, v =>
    let rec go : List Nat → Array Nat → Array Bool → List Nat × Array Nat × Array Bool
      | [], comp, on => ([], comp, on)
      | w :: ws, comp, on =>
        let comp := comp.push w
        let on := arraySetD on w false
        if w == v then (ws, comp, on) else go ws comp on
    let (stack, comp, onStack) := go stack #[] onStack
    { index, low, onStack, stack, calls, next, comps := comps.push (sortArrayBy comp (· < ·)),
      roots := roots.push v, order, exhausted }

/-- Pure, structurally recursive Tarjan DFS loop without `Array.qsort` or `Array.getElem` proofs. -/
def tarjanDfsLoop (adj : Array (Array Nat)) : Nat → Ix.Compile.Canon.TarjanState → Ix.Compile.Canon.TarjanState
  | 0, st => if st.calls.isEmpty then st else { st with exhausted := true }
  | fuel + 1, st =>
    match st.calls with
    | [] => st
    | (v, i) :: rest =>
      let succs := arrayGetD adj v #[]
      if i < succs.size then
        let w := arrayGetD succs i 0
        let st := { st with calls := (v, i + 1) :: rest }
        let iw := arrayGetD st.index w 0
        if iw == 0 then
          tarjanDfsLoop adj fuel (tarjanVisit st w)
        else if arrayGetD st.onStack w false then
          let lv := arrayGetD st.low v 0
          tarjanDfsLoop adj fuel (tarjanSetLow st v (min lv iw))
        else tarjanDfsLoop adj fuel st
      else
        let lv := arrayGetD st.low v 0
        let iv := arrayGetD st.index v 0
        let st := { st with calls := rest }
        let st := if lv == iv then tarjanPopComp st v else st
        let st := match rest with
          | (u, _) :: _ =>
            let lu := arrayGetD st.low u 0
            tarjanSetLow st u (min lu lv)
          | [] => st
        tarjanDfsLoop adj fuel st

/-- Total Tarjan SCC condensation using pure `sortArrayBy` and `List` recursion. -/
def tarjanCondensation (adj : Array (Array Nat)) : Option Ix.Compile.Canon.Condensation :=
  let n := adj.size
  let adj := Array.mk (adj.toList.map (fun row => Array.mk (row.toList.filter (· < n))))
  let edges := adj.toList.foldl (init := 0) (· + ·.size)
  let init : Ix.Compile.Canon.TarjanState :=
    { index := Array.mk (List.replicate n 0), low := Array.mk (List.replicate n 0),
      onStack := Array.mk (List.replicate n false) }
  let (st, _) := (List.range n).foldl (init := (init, edges + n + 1))
    fun (st, fuel) r =>
      if st.exhausted || arrayGetD st.index r 0 != 0 then (st, fuel)
      else (tarjanDfsLoop adj fuel (tarjanVisit st r), fuel)
  if st.exhausted then none
  else some { comps := st.comps, roots := st.roots, order := st.order }

/-- Topologically order members of a single SCC `comp` by signature dependencies (`sigRefs`),
    breaking ties by original source declaration order (`u < v`). -/
def sortSccBySigRefs (comp : Array Nat) (deps : Array DeclDepInfo) : Array Nat :=
  if comp.size ≤ 1 then comp
  else
    let sortedComp := sortArrayBy comp (· < ·)
    let rec pickLoop (fuel : Nat) (remaining : List Nat) (placed : Array Nat) : Array Nat :=
      match fuel, remaining with
      | 0, rem => placed ++ rem.toArray
      | _, []  => placed
      | fuel + 1, rem =>
        -- Pick the first element in `rem` whose `sigRefs` inside `comp` are all already in `placed`
        let ready? := rem.find? fun u =>
          let sig := (deps.getD u { declIdx := u }).sigRefs
          sig.all fun v => v == u || !comp.contains v || placed.contains v
        let chosen := ready?.getD (rem.headD 0)
        let rem' := rem.filter (· != chosen)
        pickLoop fuel rem' (placed.push chosen)
    pickLoop (sortedComp.size + 1) sortedComp.toList #[]

/-- Classification of a scheduled Strongly Connected Component of top-level declarations. -/
inductive SccKind where
  | singleNonRec
  | singleRec
  | mutualInductive
  | mutualDef
  | mixedMutual
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A single scheduled SCC ready for elaboration. -/
structure ScheduledSCC where
  sccIdx   : Nat
  kind     : SccKind
  declIdxs : Array Nat
  deriving Repr, Inhabited

/-- Complete dependency and topological schedule for a parsed `.ix` module. -/
structure ModuleSchedule where
  modIdx      : ModuleIndex
  deps        : Array DeclDepInfo
  explicitAdj : Array (Array Nat)
  fullAdj     : Array (Array Nat)
  sccs        : Array ScheduledSCC
  deriving Repr, Inhabited

/-- Classify a strongly connected component `comp` given `modIdx` and `explicitAdj`. -/
def classifyScc (modIdx : ModuleIndex) (explicitAdj : Array (Array Nat))
    (comp : Array Nat) : SccKind :=
  if comp.size == 1 then
    let u := arrayGetD comp 0 0
    if (arrayGetD explicitAdj u #[]).toList.contains u then .singleRec else .singleNonRec
  else
    let allInd := comp.toList.all fun u =>
      match Syntax.listGet? modIdx.decls.toList u with
      | some d => d.kind == .ind || d.kind == .struct || d.kind == .cls
      | none   => false
    let allVal := comp.toList.all fun u =>
      match Syntax.listGet? modIdx.decls.toList u with
      | some d => d.kind == .defn || d.kind == .abbrev || d.kind == .thm || d.kind == .inst
      | none   => false
    if allInd then .mutualInductive
    else if allVal then .mutualDef
    else .mixedMutual

/-- Run Pass 2 and Pass 3 on `modIdx : ModuleIndex` to compute the Tarjan SCC elaboration schedule. -/
def scheduleModuleDecls (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool := fun _ => false)
    (isExtCtor : Ix.Name → Bool := fun _ => false) : Except String ModuleSchedule := do
  let n := modIdx.decls.size
  let deps := Array.mk (modIdx.decls.toList.map fun d => extractDeclDeps modIdx d isExtConst isExtCtor)
  -- Build explicit adjacency list `explicitAdj[u]` (including self-edges for `classifyScc`)
  let explicitAdj : Array (Array Nat) := Array.mk (deps.toList.map fun d =>
    let all := d.sigRefs.toList.foldl pushUniqueNat #[]
    d.bodyRefs.toList.foldl pushUniqueNat all)
  -- Build condensation adjacency list (without self-loops) + cycle-safe instance edges
  let baseAdj : Array (Array Nat) := Array.mk (explicitAdj.toList.zipIdx.map fun (nbrs, u) =>
    Array.mk (nbrs.toList.filter (· != u)))
  let fullAdj := addInstanceSchedulingEdges modIdx.decls deps baseAdj
  match tarjanCondensation fullAdj with
  | none =>
    throw "internal error: Tarjan SCC condensation failed"
  | some cond =>
    let sccs : Array ScheduledSCC := Array.mk (cond.comps.toList.zipIdx.map fun (rawComp, sccIdx) =>
      let orderedComp := sortSccBySigRefs rawComp deps
      let kind := classifyScc modIdx explicitAdj orderedComp
      { sccIdx, kind, declIdxs := orderedComp })
    let _ := n
    return { modIdx, deps, explicitAdj, fullAdj, sccs }

/-- End-to-end Pass 1 + Pass 2 + Pass 3: parse `.ix` module syntax into a `ModuleSchedule`. -/
def analyzeModuleSyntax (moduleStx : Ix.Syntax)
    (isExtConst : Ix.Name → Bool := fun _ => false)
    (isExtCtor : Ix.Name → Bool := fun _ => false) : Except String ModuleSchedule := do
  let modIdx ← buildModuleIndex moduleStx
  scheduleModuleDecls modIdx isExtConst isExtCtor

end Ix.Frontend
