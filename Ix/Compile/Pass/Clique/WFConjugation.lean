/-
  Ix.Compile.Pass.Clique.WFConjugation: the decoder-owned well-founded
  transport.

  The transport starts from the exact root of `f₀._mutual` (`decodeWFRoot`)
  and moves only what that root owns: its packing, codomain and measure, its
  refinement tree, the recursive binder and the recursive calls through it,
  the complete root obligations, and the decoded calls of the packed function
  and of its abstracted proofs elsewhere. User case leaves are opaque except
  for the exact recursive binder and definitionally equal complete root
  obligations. `transportWF` runs it over a whole clique: the packed
  function, its proofs, the members and the carried lemmas.
-/
module
public import Ix.Compile.Pass.Clique.WF
public import Ix.Compile.Pass.Clique.WFSchema
public import Ix.Compile.Pass.Clique.WFMatcher
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Expr Name)
open Ix.Compile.Canon (stripMdata mkAppN getAppFnArgs)
open Ix.Compile.Image (Local)

/-- Substitute only the decoder-established recursive binder. A call at a
decoded constructor reduces the explicit adapter directly. Other uses keep
the adapter, including copies threaded through arbitrary user functions. -/
def ownedWFCalls (L : WFLayout) (adapter : Expr) (fuel depth : Nat) (e : Expr) : TM Expr :=
  (visit fuel depth e).run' {}
where
  visit : Nat → Nat → Expr → TransportMemoM Expr
  | 0, _, _ => throw "WF ownership: body recursion bound"
  | fuel + 1, depth, e => memoTransport e (fuel + 1) depth do
    if L.sigma == idPerm L.n then return e
    let go := visit fuel depth
    if let .app .. := e then
      let (head, args) := getAppFnArgs e
      if alphaEqSkipMdata head (Expr.mkBVar depth) then
        let (some first, some second) := (args[0]?, args[1]?)
          | return mkAppN (liftLoose adapter depth) (← args.mapM go)
        let some (spine, index, payload) := decodeInj L.n first
          | return mkAppN (liftLoose adapter depth) (← args.mapM go)
        unless L.isClique spine do throw "WF ownership: foreign recursive injection"
        let payload ← go payload
        let some target := spine.permute L.sigma | throw "WF ownership: foreign recursive injection"
        let position ← TM.idx L.sigma index "WF ownership: recursive injection"
        let some argument := mkInj target position payload
          | throw "WF ownership: recursive injection reconstruction failed"
        let proof ← go second
        return mkAppN head (#[argument, proof] ++ (← (args.extract 2 args.size).mapM go))
    match e with
    | .bvar i _ =>
      if i == depth then return liftLoose adapter depth
      return e
    | .app f a _ => return Expr.mkApp (← go f) (← go a)
    | .lam n t b bi _ =>
      return Expr.mkLam n (← go t) (← visit fuel (depth + 1) b) bi
    | .forallE n t b bi _ =>
      return Expr.mkForallE n (← go t) (← visit fuel (depth + 1) b) bi
    | .letE n t v b nd _ =>
      return Expr.mkLetE n (← go t) (← go v) (← visit fuel (depth + 1) b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go x)
    | .mdata d x _ => return Expr.mkMData d (← go x)
    | _ => return e

/-- An inverse-input adapter for the exact decoded recursive binder. Splitting
the source argument into constructors makes the source and target decreasing
obligations definitionally equal in every branch; no arbitrary user relation
is rewritten. The result retains the source recursive function's type. -/
def ownedWFRecAdapter (L : WFLayout) (spine : Spine) (w : Ix.Level)
    (recursive : Local) : TM Expr := do
  let (arguments, result) ← openBinders false 1 recursive.type
  let some argument := arguments[0]? | throw "WF ownership: missing recursive argument"
  let spineType ← spine.typeM "WF ownership"
  unless alphaEqSkipMdata argument.type spineType do throw "WF ownership: wrong recursive argument domain"
  let mut leaves := #[]
  for j in [0:L.n] do
    let payloadName ← freshFVar
    let summand ← TM.idx spine.leaves j "WF ownership: recursive adapter summand"
    let payload : Local := {
      fvar := payloadName, userName := leanName `value, type := summand, bi := .default }
    let some source := mkInj spine j payload.expr
      | throw "WF ownership: recursive adapter injection failed"
    let atConstructor := instLocals (abstractFVars #[argument.fvar] result) #[source]
    let (proofs, _) ← openBinders false 1 atConstructor
    let some proof := proofs[0]? | throw "WF ownership: missing decreasing proof binder"
    let some target := spine.permute L.sigma
      | throw "WF ownership: recursive adapter domain does not take the permutation"
    let position ← TM.idx L.sigma j "WF ownership: recursive adapter"
    let some targetInj := mkInj target position payload.expr
      | throw "WF ownership: recursive adapter injection failed"
    let value := mkAppN recursive.expr #[targetInj, proof.expr]
    leaves := leaves.push (← liftE (closeBinders true #[payload, proof] value))
  let tree : Tree := {
    spine, w, motiveName := argument.userName,
    motiveBody := abstractFVars #[argument.fvar] result,
    major := argument.expr, leaves, extras := #[], altNames := #[] }
  let some body := tree.build | throw "WF ownership: inverse-input case tree failed"
  liftE (closeBinders true #[argument] body)

def substituteWFLocal (identity : Name) (value replacement : Expr) : Expr :=
  instLocals (abstractFVars #[identity] value) #[replacement]

/-- Follow an exact recursive argument through the standard PSigma eliminator
at the decoded payload. Its minor's third binder receives that argument by
the eliminator's declared semantics. All other user binders remain opaque to
ownership; general forwarding uses the typed inverse-input adapter. -/
def ownedWFBody (L : WFLayout) (schema : WFRootSchema) (w : Ix.Level)
    (const? : Name → Option Ix.ConstantInfo) :
    Nat → Local → Local → Expr → Expr → Expr → TM Expr
  | 0, _, _, _, _, _ => throw "WF ownership: payload refinement recursion bound"
  | fuel + 1, payload, recursive, sourcePoint, targetPoint, body => do
    if let some (name, levels, args) := constApp? body then
      if let #[pairType, pairFamily, motiveArg, major, minorArg, recursiveArg] := args then
        if name == leanName ``PSigma.casesOn &&
            alphaEqSkipMdata major payload.expr && alphaEqSkipMdata recursiveArg recursive.expr &&
            !mentionsFVar recursive.fvar motiveArg && !mentionsFVar recursive.fvar minorArg then
          let some (payloadName, payloadLevels, payloadArgs) := constApp? payload.type
            | throw "WF ownership: refined payload is not a dependent pair"
          let foreignPayload := "WF ownership: dependent-pair eliminator has a foreign payload type"
          let #[payloadα, payloadβ] := payloadArgs | throw foreignPayload
          unless payloadName == nPSigma && alphaEqSkipMdata payloadα pairType &&
              alphaEqSkipMdata payloadβ pairFamily do
            throw foreignPayload
          let (motiveLocals, motiveBody) ← openBinders true 1 motiveArg
          let #[motivePayload] := motiveLocals | throw "WF ownership: refinement motive has no payload binder"
          let (motiveBinders, motiveResult) ← openBinders false 1 motiveBody
          let #[motiveRecursive] := motiveBinders
            | throw "WF ownership: refinement motive has no recursive binder"
          if mentionsFVar motiveRecursive.fvar motiveResult then
            throw "WF ownership: refinement result depends on its recursive value"
          let motiveRecType ← ownedWFRecType schema
            (substituteWFLocal payload.fvar sourcePoint motivePayload.expr)
            (substituteWFLocal payload.fvar targetPoint motivePayload.expr) motiveRecursive.type
          let motiveBody ← liftE (closeBinders false #[{ motiveRecursive with type := motiveRecType }] motiveResult)
          let motive ← liftE (closeBinders true motiveLocals motiveBody)
          let (minorLocals, minorBody) ← openBinders true 3 minorArg
          let #[first, second, minorRecursive] := minorLocals
            | throw "WF ownership: refinement minor does not bind its components and recursive value"
          let pair := mkAppN (Expr.mkConst (leanName ``PSigma.mk) payloadLevels)
            #[payloadα, payloadβ, first.expr, second.expr]
          let sourcePoint := substituteWFLocal payload.fvar sourcePoint pair
          let targetPoint := substituteWFLocal payload.fvar targetPoint pair
          let recType ← ownedWFRecType schema sourcePoint targetPoint minorRecursive.type
          let minorBody ← ownedWFBody L schema w const? fuel second minorRecursive sourcePoint targetPoint minorBody
          let minor ← liftE (closeBinders true #[first, second, { minorRecursive with type := recType }] minorBody)
          return mkAppN (Expr.mkConst name levels) #[pairType, pairFamily, motive, major, minor, recursiveArg]
      if let #[motiveArg, major, zeroArg, succArg, recursiveArg] := args then
        if alphaEqSkipMdata major payload.expr && alphaEqSkipMdata recursiveArg recursive.expr &&
            !(args.extract 0 4).any (mentionsFVar recursive.fvar) then
          match (decodeWFNatMatcher const? name levels).run (← get) with
          | .error reason => trace s!"{reason}; retaining the faithful recursive-input adapter"
          | .ok (flow, state) =>
            set state
            let (motiveLocals, motiveBody) ← openBinders true 1 motiveArg
            let #[motivePayload] := motiveLocals | throw "WF matcher: motive has no payload binder"
            unless alphaEqSkipMdata motivePayload.type payload.type do
              throw "WF matcher: motive payload differs from owned input"
            let (motiveBinders, motiveResult) ← openBinders false 1 motiveBody
            let #[motiveRecursive] := motiveBinders | throw "WF matcher: motive has no recursive binder"
            if mentionsFVar motiveRecursive.fvar motiveResult then
              throw "WF matcher: result depends on the recursive value"
            let motiveRecType ← ownedWFRecType schema
              (substituteWFLocal payload.fvar sourcePoint motivePayload.expr)
              (substituteWFLocal payload.fvar targetPoint motivePayload.expr) motiveRecursive.type
            let motiveBody ← liftE (closeBinders false #[{ motiveRecursive with type := motiveRecType }] motiveResult)
            let motive ← liftE (closeBinders true motiveLocals motiveBody)
            let mut minors := #[]
            for (minorArg, index) in #[zeroArg, succArg].zipIdx do
              let (locals, minorBody) ← openBinders true 2 minorArg
              let #[branchArgument, minorRecursive] := locals
                | throw "WF matcher: minor does not bind its argument and recursive value"
              let point := if index == 0 then flow.zero else
                Expr.mkApp (Expr.mkConst (leanName ``Nat.succ) #[]) branchArgument.expr
              let sourcePoint := substituteWFLocal payload.fvar sourcePoint point
              let targetPoint := substituteWFLocal payload.fvar targetPoint point
              let recType ← ownedWFRecType schema sourcePoint targetPoint minorRecursive.type
              let minorBody ← ownedWFBody L schema w const? fuel branchArgument minorRecursive sourcePoint targetPoint minorBody
              minors := minors.push (← liftE (closeBinders true
                #[branchArgument, { minorRecursive with type := recType }] minorBody))
            let #[zeroMinor, succMinor] := minors | throw "WF matcher: minor reconstruction failed"
            return mkAppN (Expr.mkConst name levels) #[motive, major, zeroMinor, succMinor, recursiveArg]
    let body ← rewriteWFObligations schema L.sigma transportFuel body
    let adapter ← ownedWFRecAdapter L schema.sourceSpine w recursive
    let adapter := abstractFVars #[recursive.fvar] adapter
    let transformed ← ownedWFCalls L adapter transportFuel 0
      (abstractFVars #[recursive.fvar] body)
    return instLocals transformed #[recursive.expr]

/-- Decode the exact root relationship and preserve user syntax by transporting
only its owned entry, recursive argument flow and output positions. -/
def conjugateWFRoot (L : WFLayout) (value : Expr)
    (const? : Name → Option Ix.ConstantInfo := fun _ => none) : TM Expr := do
  let schema ← decodeWFRoot L value
  let some functional := schema.sourceArguments.back?
    | throw "WF ownership: missing root functional"
  let (locals, body) ← openBinders true 2 functional
  let #[x, recursive] := locals | throw "WF ownership: missing root functional"
  let sourceType ← schema.sourceSpine.typeM "WF ownership"
  let targetType ← schema.targetSpine.typeM "WF ownership"
  unless alphaEqSkipMdata x.type sourceType do
    throw "WF ownership: functional domain differs from root"
  let recursiveType ← ownedWFRecType schema x.expr x.expr recursive.type
  let some tree := decodeTree L.n body | throw "WF ownership: missing root refinement tree"
  let treeType ← tree.spine.typeM "WF ownership"
  let threadsRecursive := match tree.extras with
    | #[extra] => alphaEqSkipMdata extra recursive.expr
    | _ => false
  unless alphaEqSkipMdata treeType sourceType && alphaEqSkipMdata tree.major x.expr && threadsRecursive do
    throw "WF ownership: root refinement has foreign entry identities"
  let sourceTypeAt (point : Expr) := instLocals
    (abstractFVars #[x.fvar] recursive.type) #[point]
  let mut leaves := #[]
  for index in [0:L.n] do
    let leaf ← TM.idx tree.leaves index "WF ownership: refinement leaf"
    if mentionsFVar x.fvar leaf || mentionsFVar recursive.fvar leaf then
      throw "WF ownership: leaf captures an unthreaded root identity"
    let (entry, leafBody) ← openBinders true 2 leaf
    let #[payload, recursor] := entry | throw "WF ownership: leaf does not bind its payload and recursive value"
    let summand ← TM.idx schema.sourceSpine.leaves index "WF ownership: root summand"
    unless alphaEqSkipMdata payload.type summand do
      throw "WF ownership: leaf payload differs from root summand"
    let some sourcePoint := mkInj schema.sourceSpine index payload.expr
      | throw "WF ownership: leaf injection reconstruction failed"
    let position ← TM.idx L.sigma index "WF ownership: refinement leaf"
    let some targetPoint := mkInj schema.targetSpine position payload.expr
      | throw "WF ownership: leaf injection reconstruction failed"
    unless alphaEqSkipMdata recursor.type (sourceTypeAt sourcePoint) do
      throw "WF ownership: leaf recursive binder differs from root telescope"
    let recursorType ← ownedWFRecType schema sourcePoint targetPoint recursor.type
    let transformed ← ownedWFBody L schema tree.w const? transportFuel payload recursor sourcePoint targetPoint leafBody
    leaves := leaves.push (← liftE (closeBinders true
      #[payload, { recursor with type := recursorType }] transformed))
  let pointName ← freshFVar
  let point := Expr.mkFVar pointName
  let sourceMotive := mkForall #[{ recursive with type := sourceTypeAt point }]
    (applyWFCase schema.sourceCodomain point)
  unless alphaEqSkipMdata tree.motiveBody (abstractFVars #[pointName] sourceMotive) do
    throw "WF ownership: refinement motive differs from root telescope"
  let targetMotive := mkForall
    #[{ recursive with type := ← ownedWFRecType schema point point (sourceTypeAt point) }]
    (applyWFCase schema.targetCodomain point)
  let tree := { tree with leaves, motiveBody := abstractFVars #[pointName] targetMotive }
  let some body := (tree.permute L.sigma).bind Tree.build
    | throw "WF ownership: root refinement reconstruction failed"
  let functional ← liftE (closeBinders true
    #[{ x with type := targetType }, { recursive with type := recursiveType }] body)
  return mkAppN schema.head (schema.targetArguments.push functional)

def conjugateWFType (L : WFLayout) (type : Expr) : TM Expr := do
  let .forallE name domain body bi _ := stripMdata type
    | throw "WF schema: packed type has no input binder"
  let some spine := decodeSpine .psum L.n domain | throw "WF schema: packed type has no sum domain"
  unless L.isClique spine do throw "WF schema: packed type has a foreign domain"
  let transformed ← decodeWFCase spine L.sigma (Expr.mkLam name domain body bi)
  let .lam name domain body bi _ := transformed | throw "WF schema: transformed codomain has no binder"
  return Expr.mkForallE name domain body bi

def wfPackedDomain (L : WFLayout) (packed : Decl) (levels : Array Ix.Level)
    (fixed : Array Expr) : TM (Spine × Expr × Ix.Level) := do
  unless fixed.size == L.numFixed do throw "WF adapter: incomplete fixed arguments"
  let type := Ix.Compile.Canon.substLevels packed.levelParams levels packed.type
  let (_, result) := Ix.Compile.Canon.peelForalls L.numFixed type #[]
  let result := instLocals result fixed
  let .forallE _ domain codomain _ _ := stripMdata result
    | throw "WF adapter: packed type has no dependent input"
  let some spine := decodeSpine .psum L.n domain | throw "WF adapter: missing source sum domain"
  let value := Ix.Compile.Canon.substLevels packed.levelParams levels packed.value
  let (_, root) := peelLams L.numFixed value #[]
  let some (_, rootLevels, _) := constApp? (stripMdata root) | throw "WF adapter: missing fixpoint root"
  let some resultLevel := rootLevels[1]? | throw "WF adapter: missing result universe"
  return (spine, codomain, resultLevel)

/-- Dependent pullback of the target packed function. Case analysis on the
source input makes C'(inj' i p) and C(inj i p) definitionally equal at every
leaf; using a bare f'(post x) at an arbitrary x would not establish that. -/
def applyWFPackedAdapter (L : WFLayout) (packed : Decl) (levels : Array Ix.Level)
    (fixed : Array Expr) (argument : Expr) : TM Expr := do
  let (spine, codomain, resultLevel) ← wfPackedDomain L packed levels fixed
  let some target := spine.permute L.sigma
    | throw "WF adapter: packed domain does not take the permutation"
  let some targetFixed := reorder L.fixedPerm fixed | throw "WF adapter: incomplete fixed arguments"
  let call (index : Nat) (payload : Expr) : TM Expr := do
    let position ← TM.idx L.sigma index "WF adapter: packed input"
    let some input := mkInj target position payload
      | throw "WF adapter: target injection reconstruction failed"
    return mkAppN (Expr.mkConst L.newMutualName levels) (targetFixed.push input)
  if let some (actual, index, payload) := decodeInj L.n argument then
    let actualType ← actual.typeM "WF adapter"
    let spineType ← spine.typeM "WF adapter"
    unless alphaEqSkipMdata actualType spineType do throw "WF adapter: injected argument has a foreign type"
    return ← call index payload
  let mut leaves := #[]
  for index in [0:L.n] do
    let name ← freshFVar
    let summand ← TM.idx spine.leaves index "WF adapter: packed summand"
    let payload : Local := {
      fvar := name, userName := leanName `payload, type := summand, bi := .default }
    leaves := leaves.push (mkLambda #[payload] (← call index payload.expr))
  let tree : Tree := {
    spine, w := resultLevel, motiveName := leanName `input, motiveBody := codomain,
    major := argument, leaves, extras := #[], altNames := #[] }
  let some value := tree.build | throw "WF adapter: dependent input case reconstruction failed"
  return value

/-- Exact constant identities only: proof-prefix reordering and the decoded
member call into the packed root. No user types, binders or relations grant
entry to the encoding. General packed inputs use the dependent adapter;
an incomplete fixed-parameter prefix remains an explicit decline. -/
def rewriteOwnedWFUses (L : WFLayout) (packed : Decl) (fuel : Nat) (e : Expr) : TM Expr :=
  (visit fuel e).run' {}
where
  visit : Nat → Expr → TransportMemoM Expr
  | 0, _ => throw "WF ownership: constant-use recursion bound"
  | fuel + 1, e => memoTransport e (fuel + 1) 0 do
    let go := visit fuel
    let packedUse (levels : Array Ix.Level) (args : Array Expr) : TransportMemoM Expr := do
      unless args.size ≥ L.numFixed do throw "WF ownership: partial fixed prefix of packed root"
      let args ← args.mapM go
      let fixed := args.extract 0 L.numFixed
      let some packedArg := args[L.numFixed]? | do
        let (spine, _, _) ← wfPackedDomain L packed levels fixed
        let spineType ← spine.typeM "WF ownership"
        let identity ← freshFVar
        let argument : Local := {
          fvar := identity, userName := leanName `input, type := spineType, bi := .default }
        let value ← applyWFPackedAdapter L packed levels fixed argument.expr
        return mkLambda #[argument] value
      let value ← applyWFPackedAdapter L packed levels fixed packedArg
      return mkAppN value (args.extract (L.numFixed + 1) args.size)
    match e with
    | .app .. =>
      let (head, args) := getAppFnArgs e
      if let .const name levels _ := head then
        if name == L.mutualName then
          return ← packedUse levels args
        if let some permutation := L.proofPerm.get? name then
          unless args.size ≥ permutation.size do throw "WF ownership: partial proof use"
          let args ← args.mapM go
          let some fixedArgs := reorder permutation args | throw "WF ownership: partial proof use"
          return mkAppN head (fixedArgs ++ args.extract permutation.size args.size)
      return mkAppN (← go head) (← args.mapM go)
    | .const name levels _ =>
      if name == L.mutualName then return ← packedUse levels #[]
      if let some permutation := L.proofPerm.get? name then
        unless permutation.isEmpty do throw "WF ownership: bare proof use"
      return e
    | .lam n t b bi _ => return Expr.mkLam n (← go t) (← go b) bi
    | .forallE n t b bi _ => return Expr.mkForallE n (← go t) (← go b) bi
    | .letE n t v b nd _ => return Expr.mkLetE n (← go t) (← go v) (← go b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go x)
    | .mdata d x _ => return Expr.mkMData d (← go x)
    | _ => return e

/-- The packed equation keeps its source-domain indexing through a dependent
input adapter. At each decoded constructor, the target fix_eq is exactly the
required equation by beta/iota conversion. No arbitrary proof syntax is
transported, and no equality between arbitrary C'(post x) and C(x) is assumed. -/
def transportOwnedWFEqDef (L : WFLayout) (packed target : Decl) (equation : Decl)
    (newName : Name) : TM Decl := do
  let rewrite := rewriteOwnedWFUses L packed transportFuel
  let type ← withReorderedBinders2 false L.numFixed L.fixedPerm equation.type pure rewrite
  let (parameters, statement) ← openBinders false (L.numFixed + 1) type
  let point ← TM.idx parameters L.numFixed "WF equation: packed argument"
  let some inverse := invPerm L.fixedPerm
    | throw "WF equation: the fixed-parameter order is not a permutation"
  let sourceFixed ← (idPerm L.numFixed).mapM fun index => do
    let position ← TM.idx inverse index "WF equation: fixed-parameter order"
    let parameter ← TM.idx parameters position "WF equation: fixed parameter"
    pure parameter.expr
  let targetFixed := (parameters.extract 0 L.numFixed).map (·.expr)
  let sourceStep ← liftE (eqDefFixStep equation L.numFixed (sourceFixed.push point.expr))
  let (sourceBinders, sourceBody) := peelLams L.numFixed packed.value #[]
  let (targetBinders, targetBody) := peelLams L.numFixed target.value #[]
  unless sourceBinders.size == L.numFixed && targetBinders.size == L.numFixed do
    throw "WF equation: packed fixed telescope differs from its layout"
  let sourceRoot := instLocals sourceBody sourceFixed
  let targetRoot := instLocals targetBody targetFixed
  let some (rootName, rootLevels, sourceArgs) := constApp? sourceRoot
    | throw "WF equation: source root is not a fixpoint"
  let some (_, _, targetArgs) := constApp? targetRoot
    | throw "WF equation: target root is not a fixpoint"
  let some (stepName, stepLevels, stepArgs) := constApp? (stripId sourceStep)
    | throw "WF equation: source proof has no fix_eq step"
  let expectedStep := if rootName == leanName ``WellFounded.Nat.fix then leanName ``WellFounded.Nat.fix_eq
    else if rootName == leanName ``WellFounded.fix then leanName ``WellFounded.fix_eq else Ix.Name.mkAnon
  let foreignRoot := "WF equation: fix_eq does not refer to the exact decoded source root"
  unless stepName == expectedStep && stepLevels == rootLevels && stepArgs.size == sourceArgs.size + 1 &&
      ((stepArgs.extract 0 sourceArgs.size).zip sourceArgs).all (fun (a, b) => alphaEqSkipMdata a b) do
    throw foreignRoot
  let some stepPoint := stepArgs[sourceArgs.size]? | throw foreignRoot
  unless alphaEqSkipMdata stepPoint point.expr do
    throw "WF equation: fix_eq uses a foreign input identity"
  let some spine := decodeSpine .psum L.n point.type | throw "WF equation: source equation has no sum input"
  let spineType ← spine.typeM "WF equation"
  let some sourceDomain := sourceArgs[0]? | throw "WF equation: equation input differs from source root"
  unless alphaEqSkipMdata spineType sourceDomain do throw "WF equation: equation input differs from source root"
  let some targetSpine := spine.permute L.sigma
    | throw "WF equation: target domain differs from permutation"
  let targetType ← targetSpine.typeM "WF equation"
  let some targetDomain := targetArgs[0]? | throw "WF equation: target domain differs from permutation"
  unless alphaEqSkipMdata targetType targetDomain do throw "WF equation: target domain differs from permutation"
  let atPoint (argument : Expr) := substituteWFLocal point.fvar statement argument
  let mut leaves := #[]
  for index in [0:L.n] do
    let name ← freshFVar
    let summand ← TM.idx spine.leaves index "WF equation: summand"
    let payload : Local := {
      fvar := name, userName := leanName `payload, type := summand, bi := .default }
    let position ← TM.idx L.sigma index "WF equation: permutation"
    let sourceInput (value : Expr) : TM Expr := do
      let some input := mkInj spine index value | throw "WF equation: source injection reconstruction failed"
      return input
    let targetInput (value : Expr) : TM Expr := do
      let some input := mkInj targetSpine position value
        | throw "WF equation: target injection reconstruction failed"
      return input
    let body ← splitPSigma (fun value => do return atPoint (← sourceInput value))
      (fun value => do return mkAppN (Expr.mkConst stepName stepLevels) (targetArgs.push (← targetInput value)))
      wfDepth payload.type id payload.expr
    leaves := leaves.push (mkLambda #[payload] body)
  let tree : Tree := {
    spine, w := Ix.Level.mkZero, motiveName := point.userName,
    motiveBody := abstractFVars #[point.fvar] statement,
    major := point.expr, leaves, extras := #[], altNames := #[] }
  let some body := tree.build | throw "WF equation: source-domain case reconstruction failed"
  let value ← liftE (closeBinders true parameters body)
  return { equation with name := newName, type, value }

/-- Owned root, proof, member and equation transport of a well-founded
clique: the packed function `packed` (renamed `newName`), its abstracted
`proofs`, the `members` and the carried `lemmas` (each with its new name),
under the clique permutation `sigma`. The prologue (the proofs' fixed
prefixes) and the epilogue (the proofs' numbering and the renames) are the
ones `transportPF` shares (`fixedProofPerms`, `numberProofs`). -/
def transportWF (members : Array Decl) (packed : Decl) (proofs : Array Decl)
    (sigma : Array Nat) (newName : Name) (lemmas : Array (Decl × Name) := #[])
    (const? : Name → Option Ix.ConstantInfo := fun _ => none) : TM TransportOutput := do
  let initial ← liftE (wfLayout members packed sigma newName)
  let prologue ← fixedProofPerms proofs initial.numFixed initial.fixedPerm packed.value
  let fixed := prologue.fixed
  let body := prologue.body
  let uses := prologue.uses
  let isPackedLemma (name : Name) := match name with
    | .str parent _ _ => parent == packed.name
    | _ => false
  -- the packed function's own lemmas take its fixed parameters in the new order
  let proofPerm := lemmas.foldl (init := prologue.proofPerm) fun permutations (declaration, _) =>
    if isPackedLemma declaration.name then permutations.insert declaration.name initial.fixedPerm else permutations
  let L := { initial with proofPerm }
  let rewrite := rewriteOwnedWFUses L packed transportFuel
  let schema ← decodeWFRoot L body
  let mut wellFoundedProof : Option (Name × Expr × Expr) := none
  if let #[_, _, _, sourceWitness, _] := schema.sourceArguments then
    if let some (name, levels, arguments) := constApp? sourceWitness then
      if let some declaration := proofs.find? (·.name == name) then
        unless levels == declaration.levelParams.map Ix.Level.mkParam do
          throw "WF ownership: well-founded proof uses a nonidentity universe substitution"
        let mut parameters := #[]
        for argument in arguments do
          let .fvar identity _ := stripMdata argument
            | throw "WF ownership: well-founded proof argument is not a fixed parameter"
          let some parameter := fixed.find? (·.fvar == identity)
            | throw "WF ownership: well-founded proof uses a foreign parameter"
          parameters := parameters.push parameter
        let permutation := (proofPerm.get? name).getD #[]
        let prefixDiffers := "WF ownership: well-founded proof prefix differs from its decoded application"
        unless permutation.size == parameters.size do throw prefixDiffers
        let .const _ rootLevels _ := schema.head | throw "WF ownership: missing fixpoint universe"
        let some domainLevel := rootLevels[0]? | throw "WF ownership: missing domain universe"
        let #[_, _, targetRelation, targetWitness] := schema.targetArguments
          | throw "WF ownership: the decoded root has no well-founded witness"
        let targetType ← schema.targetSpine.typeM "WF ownership"
        let goal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[targetType, targetRelation]
        let witness := mkAppN (Expr.mkConst (leanName ``Lean.opaqueId) #[Ix.Level.mkZero])
          #[goal, targetWitness]
        let some reordered := reorder permutation parameters | throw prefixDiffers
        wellFoundedProof := some (name, ← liftE (closeBinders false reordered goal),
          ← liftE (closeBinders true reordered witness))
  let value ← withReorderedBinders2 true L.numFixed L.fixedPerm packed.value pure
    (fun value => do
      let transformed ← conjugateWFRoot L value const?
      let transformed ← match wellFoundedProof with
        | some _ => do
          -- the root keeps Lean's witness argument, an application of the
          -- abstracted proof (which is transported below)
          let (_, sourceArgs) := getAppFnArgs value
          let (head, targetArgs) := getAppFnArgs transformed
          let some sourceWitness := sourceArgs[3]?
            | throw "WF ownership: the fixpoint root has no well-founded witness argument"
          unless 3 < targetArgs.size do
            throw "WF ownership: the transported root has no well-founded witness argument"
          pure (mkAppN head (targetArgs.setIfInBounds 3 sourceWitness))
        | none => pure transformed
      rewrite transformed)
  let type ← withReorderedBinders2 false L.numFixed L.fixedPerm packed.type pure (conjugateWFType L)
  let mut output : Array Transported := #[{ decl := { packed with name := newName, type, value } }]
  for proof in proofs do
    if let some (name, type, value) := wellFoundedProof then
      if name == proof.name then
        output := output.push { decl := { proof with type, value } }
        continue
    let permutation := (proofPerm.get? proof.name).getD #[]
    let transform (isLam : Bool) (expression : Expr) : TM Expr := do
      let (parameters, body) ← openBinders isLam permutation.size expression
      let positions := (uses.get? proof.name).getD #[]
      unless positions.size == parameters.size do throw "WF obligation: proof prefix disagrees with its use"
      let mut arguments := fixed.map (·.expr)
      for (position, parameter) in positions.zip parameters do
        unless position < arguments.size do throw "WF obligation: fixed proof argument is out of scope"
        arguments := arguments.setIfInBounds position parameter.expr
      let instantiate (expression : Expr) := instLocals
        (abstractFVars (fixed.map (·.fvar)) expression) arguments
      let proofSchema := schema.mapExpressions instantiate
      let body ← rewriteWFObligations proofSchema L.sigma transportFuel body
      let body ← rewrite body
      let some reordered := reorder permutation parameters
        | throw "WF obligation: proof prefix disagrees with its use"
      liftE (closeBinders isLam reordered body)
    let type ← transform false proof.type
    let value ← transform true proof.value
    output := output.push { decl := { proof with type, value } }
  for member in members do
    output := output.push { decl := { member with type := ← rewrite member.type, value := ← rewrite member.value } }
  let packedTarget : Decl := { packed with name := newName, type, value }
  for (lemma, name) in lemmas do
    if lemma.name == Ix.Name.mkStr packed.name "eq_def" then
      let some functional := schema.sourceArguments.back? | throw "WF equation: missing functional"
      let (_, body) := peelLams 2 functional #[]
      let some tree := decodeTree L.n body | throw "WF equation: missing source refinement tree"
      unless tree.leaves.all (leafReduces wfDepth) do
        throw "WF equation: source matcher needs argument-pushing proof reconstruction"
      output := output.push { decl := ← transportOwnedWFEqDef L packed packedTarget lemma name }
    else if isPackedLemma lemma.name then
      let type ← withReorderedBinders2 false L.numFixed L.fixedPerm lemma.type pure rewrite
      let value ← withReorderedBinders2 true L.numFixed L.fixedPerm lemma.value pure rewrite
      output := output.push { decl := { lemma with name, type, value } }
    else
      output := output.push { decl := { lemma with name, type := ← rewrite lemma.type, value := ← rewrite lemma.value } }
  return numberProofs output packed.name newName proofs lemmas value

end Ix.Compile.Pass.Clique

end
