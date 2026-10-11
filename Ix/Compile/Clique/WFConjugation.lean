/- Decoder-owned WF transport. User case leaves are opaque except for the
exact recursive binder and definitionally equal complete root obligations. -/
module
public import Ix.Compile.Clique.WF
public import Ix.Compile.Clique.WFSchema
public import Ix.Compile.Clique.WFMatcher
public section

namespace Ix.Compile.Clique
open Ix (Expr Name)
open Ix.Compile.Canon (stripMdata mkAppN getAppFnArgs)

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
      if alphaEq head (Expr.mkBVar depth) then
        unless args.size ≥ 2 do return mkAppN (liftLoose adapter depth) (← args.mapM go)
        let some (spine, index, payload) := decodeInj L.n args[0]!
          | return mkAppN (liftLoose adapter depth) (← args.mapM go)
        unless L.isClique spine do throw "WF ownership: foreign recursive injection"
        let argument := mkInj (spine.permute L.sigma) L.sigma[index]! (← go payload)
        let proof ← go args[1]!
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
    (recursive : Ix.Compile.Image.Local) : TM Expr := do
  let (arguments, result) ← openBinders false 1 recursive.type
  let some argument := arguments[0]? | throw "WF ownership: missing recursive argument"
  unless alphaEq argument.type spine.type do throw "WF ownership: wrong recursive argument domain"
  let mut leaves := #[]
  for j in [0:L.n] do
    let payloadName ← freshFVar
    let payload : Ix.Compile.Image.Local := {
      fvar := payloadName, userName := leanName `value, type := spine.leaves[j]!, bi := .default }
    let atConstructor := Ix.Compile.Clique.instLocals
      (Ix.Compile.Clique.abstractFVars #[argument.fvar] result) #[mkInj spine j payload.expr]
    let (proofs, _) ← openBinders false 1 atConstructor
    let some proof := proofs[0]? | throw "WF ownership: missing decreasing proof binder"
    let value := mkAppN recursive.expr #[mkInj (spine.permute L.sigma) L.sigma[j]! payload.expr, proof.expr]
    leaves := leaves.push (← liftE (closeBinders true #[payload, proof] value))
  let tree : Tree := {
    spine, w, motiveName := argument.userName,
    motiveBody := Ix.Compile.Clique.abstractFVars #[argument.fvar] result,
    major := argument.expr, leaves, extras := #[], altNames := #[] }
  let some body := tree.build | throw "WF ownership: inverse-input case tree failed"
  liftE (closeBinders true #[argument] body)

def substituteWFLocal (identity : Name) (value replacement : Expr) : Expr :=
  Ix.Compile.Clique.instLocals (Ix.Compile.Clique.abstractFVars #[identity] value) #[replacement]

/-- Follow an exact recursive argument through the standard PSigma eliminator
at the decoded payload. Its minor's third binder receives that argument by
the eliminator's declared semantics. All other user binders remain opaque to
ownership; general forwarding uses the typed inverse-input adapter. -/
def ownedWFBody (L : WFLayout) (schema : WFRootSchema) (w : Ix.Level)
    (const? : Name → Option Ix.ConstantInfo) :
    Nat → Ix.Compile.Image.Local → Ix.Compile.Image.Local → Expr → Expr → Expr → TM Expr
  | 0, _, _, _, _, _ => throw "WF ownership: payload refinement recursion bound"
  | fuel + 1, payload, recursive, sourcePoint, targetPoint, body => do
    if let some (name, levels, args) := constApp? body then
      if name == leanName ``PSigma.casesOn && args.size == 6 &&
          alphaEq args[3]! payload.expr && alphaEq args[5]! recursive.expr &&
          !mentionsFVar recursive.fvar args[2]! && !mentionsFVar recursive.fvar args[4]! then
        let some (payloadName, payloadLevels, payloadArgs) := constApp? payload.type
          | throw "WF ownership: refined payload is not a dependent pair"
        unless payloadName == nPSigma && payloadArgs.size == 2 &&
            alphaEq payloadArgs[0]! args[0]! && alphaEq payloadArgs[1]! args[1]! do
          throw "WF ownership: dependent-pair eliminator has a foreign payload type"
        let (motiveLocals, motiveBody) ← openBinders true 1 args[2]!
        let motivePayload := motiveLocals[0]!
        let (motiveBinders, motiveResult) ← openBinders false 1 motiveBody
        let motiveRecursive := motiveBinders[0]!
        if mentionsFVar motiveRecursive.fvar motiveResult then
          throw "WF ownership: refinement result depends on its recursive value"
        let motiveRecType ← ownedWFRecType schema
          (substituteWFLocal payload.fvar sourcePoint motivePayload.expr)
          (substituteWFLocal payload.fvar targetPoint motivePayload.expr) motiveRecursive.type
        let motiveBody ← liftE (closeBinders false #[{ motiveRecursive with type := motiveRecType }] motiveResult)
        let motive ← liftE (closeBinders true motiveLocals motiveBody)
        let (minorLocals, minorBody) ← openBinders true 3 args[4]!
        let first := minorLocals[0]!
        let second := minorLocals[1]!
        let minorRecursive := minorLocals[2]!
        let pair := mkAppN (Expr.mkConst (leanName ``PSigma.mk) payloadLevels)
          #[payloadArgs[0]!, payloadArgs[1]!, first.expr, second.expr]
        let sourcePoint := substituteWFLocal payload.fvar sourcePoint pair
        let targetPoint := substituteWFLocal payload.fvar targetPoint pair
        let recType ← ownedWFRecType schema sourcePoint targetPoint minorRecursive.type
        let minorBody ← ownedWFBody L schema w const? fuel second minorRecursive sourcePoint targetPoint minorBody
        let minor ← liftE (closeBinders true #[first, second, { minorRecursive with type := recType }] minorBody)
        return mkAppN (Expr.mkConst name levels) #[args[0]!, args[1]!, motive, args[3]!, minor, args[5]!]
      if args.size == 5 && alphaEq args[1]! payload.expr && alphaEq args[4]! recursive.expr &&
          !(args.extract 0 4).any (mentionsFVar recursive.fvar) then
        match (decodeWFNatMatcher const? name levels).run (← get) with
        | .error reason => trace s!"{reason}; retaining the faithful recursive-input adapter"
        | .ok (flow, state) =>
          set state
          let (motiveLocals, motiveBody) ← openBinders true 1 args[0]!
          let motivePayload := motiveLocals[0]!
          unless alphaEq motivePayload.type payload.type do throw "WF matcher: motive payload differs from owned input"
          let (motiveBinders, motiveResult) ← openBinders false 1 motiveBody
          let motiveRecursive := motiveBinders[0]!
          if mentionsFVar motiveRecursive.fvar motiveResult then
            throw "WF matcher: result depends on the recursive value"
          let motiveRecType ← ownedWFRecType schema
            (substituteWFLocal payload.fvar sourcePoint motivePayload.expr)
            (substituteWFLocal payload.fvar targetPoint motivePayload.expr) motiveRecursive.type
          let motiveBody ← liftE (closeBinders false #[{ motiveRecursive with type := motiveRecType }] motiveResult)
          let motive ← liftE (closeBinders true motiveLocals motiveBody)
          let mut minors := #[]
          for index in [0:2] do
            let (locals, minorBody) ← openBinders true 2 args[index + 2]!
            let branchArgument := locals[0]!
            let minorRecursive := locals[1]!
            let point := if index == 0 then flow.zero else
              Expr.mkApp (Expr.mkConst (leanName ``Nat.succ) #[]) branchArgument.expr
            let sourcePoint := substituteWFLocal payload.fvar sourcePoint point
            let targetPoint := substituteWFLocal payload.fvar targetPoint point
            let recType ← ownedWFRecType schema sourcePoint targetPoint minorRecursive.type
            let minorBody ← ownedWFBody L schema w const? fuel branchArgument minorRecursive sourcePoint targetPoint minorBody
            minors := minors.push (← liftE (closeBinders true
              #[branchArgument, { minorRecursive with type := recType }] minorBody))
          return mkAppN (Expr.mkConst name levels) #[motive, args[1]!, minors[0]!, minors[1]!, args[4]!]
    let body ← rewriteWFObligations schema L.sigma defaultFuel body
    let adapter ← ownedWFRecAdapter L schema.sourceSpine w recursive
    let adapter := Ix.Compile.Clique.abstractFVars #[recursive.fvar] adapter
    let transformed ← ownedWFCalls L adapter defaultFuel 0
      (Ix.Compile.Clique.abstractFVars #[recursive.fvar] body)
    return Ix.Compile.Clique.instLocals transformed #[recursive.expr]

/-- Decode the exact root relationship and preserve user syntax by transporting
only its owned entry, recursive argument flow and output positions. -/
def conjugateWFRoot (L : WFLayout) (value : Expr)
    (const? : Name → Option Ix.ConstantInfo := fun _ => none) : TM Expr := do
  let schema ← decodeWFRoot L value
  let some functional := schema.sourceArguments.back?
    | throw "WF ownership: missing root functional"
  let (locals, body) ← openBinders true 2 functional
  let x := locals[0]!
  let recursive := locals[1]!
  unless alphaEq x.type schema.sourceSpine.type do
    throw "WF ownership: functional domain differs from root"
  let recursiveType ← ownedWFRecType schema x.expr x.expr recursive.type
  let some tree := decodeTree L.n body | throw "WF ownership: missing root refinement tree"
  unless alphaEq tree.spine.type schema.sourceSpine.type && alphaEq tree.major x.expr &&
      tree.extras.size == 1 && alphaEq tree.extras[0]! recursive.expr do
    throw "WF ownership: root refinement has foreign entry identities"
  let sourceTypeAt (point : Expr) := Ix.Compile.Clique.instLocals
    (Ix.Compile.Clique.abstractFVars #[x.fvar] recursive.type) #[point]
  let mut leaves := #[]
  for index in [0:L.n] do
    let leaf := tree.leaves[index]!
    if mentionsFVar x.fvar leaf || mentionsFVar recursive.fvar leaf then
      throw "WF ownership: leaf captures an unthreaded root identity"
    let (entry, leafBody) ← openBinders true 2 leaf
    let payload := entry[0]!
    let recursor := entry[1]!
    unless alphaEq payload.type schema.sourceSpine.leaves[index]! do
      throw "WF ownership: leaf payload differs from root summand"
    let sourcePoint := mkInj schema.sourceSpine index payload.expr
    let targetPoint := mkInj schema.targetSpine L.sigma[index]! payload.expr
    unless alphaEq recursor.type (sourceTypeAt sourcePoint) do
      throw "WF ownership: leaf recursive binder differs from root telescope"
    let targetType ← ownedWFRecType schema sourcePoint targetPoint recursor.type
    let transformed ← ownedWFBody L schema tree.w const? defaultFuel payload recursor sourcePoint targetPoint leafBody
    leaves := leaves.push (← liftE (closeBinders true
      #[payload, { recursor with type := targetType }] transformed))
  let pointName ← freshFVar
  let point := Expr.mkFVar pointName
  let sourceMotive := Ix.Compile.Clique.mkForall #[{ recursive with type := sourceTypeAt point }]
    (applyWFCase schema.sourceCodomain point)
  unless alphaEq tree.motiveBody (Ix.Compile.Clique.abstractFVars #[pointName] sourceMotive) do
    throw "WF ownership: refinement motive differs from root telescope"
  let targetMotive := Ix.Compile.Clique.mkForall
    #[{ recursive with type := ← ownedWFRecType schema point point (sourceTypeAt point) }]
    (applyWFCase schema.targetCodomain point)
  let tree := { tree with leaves, motiveBody := Ix.Compile.Clique.abstractFVars #[pointName] targetMotive }
  let some body := (tree.permute L.sigma).build | throw "WF ownership: root refinement reconstruction failed"
  let functional ← liftE (closeBinders true
    #[{ x with type := schema.targetSpine.type }, { recursive with type := recursiveType }] body)
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
  let result := Ix.Compile.Clique.instLocals result fixed
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
  let target := spine.permute L.sigma
  let call (index : Nat) (payload : Expr) := mkAppN (Expr.mkConst L.newMutualName levels)
    ((L.fixedPerm.map (fixed[·]!)).push (mkInj target L.sigma[index]! payload))
  if let some (actual, index, payload) := decodeInj L.n argument then
    unless alphaEq actual.type spine.type do throw "WF adapter: injected argument has a foreign type"
    return call index payload
  let mut leaves := #[]
  for index in [0:L.n] do
    let name ← freshFVar
    let payload : Ix.Compile.Image.Local := {
      fvar := name, userName := leanName `payload, type := spine.leaves[index]!, bi := .default }
    leaves := leaves.push (Ix.Compile.Clique.mkLambda #[payload] (call index payload.expr))
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
      if args.size == L.numFixed then
        let (spine, _, _) ← wfPackedDomain L packed levels fixed
        let identity ← freshFVar
        let argument : Ix.Compile.Image.Local := {
          fvar := identity, userName := leanName `input, type := spine.type, bi := .default }
        let value ← applyWFPackedAdapter L packed levels fixed argument.expr
        return Ix.Compile.Clique.mkLambda #[argument] value
      let value ← applyWFPackedAdapter L packed levels fixed args[L.numFixed]!
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
          return mkAppN head (permutation.map (args[·]!) ++ args.extract permutation.size args.size)
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
  let rewrite := rewriteOwnedWFUses L packed defaultFuel
  let type ← withReorderedBinders2 false L.numFixed L.fixedPerm equation.type pure rewrite
  let (parameters, statement) ← openBinders false (L.numFixed + 1) type
  let point := parameters[L.numFixed]!
  let inverse := invPerm L.fixedPerm
  let sourceFixed := (idPerm L.numFixed).map fun index => parameters[inverse[index]!]!.expr
  let targetFixed := (parameters.extract 0 L.numFixed).map (·.expr)
  let sourceStep ← liftE (eqDefFixStep equation L.numFixed (sourceFixed.push point.expr))
  let (sourceBinders, sourceBody) := peelLams L.numFixed packed.value #[]
  let (targetBinders, targetBody) := peelLams L.numFixed target.value #[]
  unless sourceBinders.size == L.numFixed && targetBinders.size == L.numFixed do
    throw "WF equation: packed fixed telescope differs from its layout"
  let sourceRoot := Ix.Compile.Clique.instLocals sourceBody sourceFixed
  let targetRoot := Ix.Compile.Clique.instLocals targetBody targetFixed
  let some (rootName, rootLevels, sourceArgs) := constApp? sourceRoot
    | throw "WF equation: source root is not a fixpoint"
  let some (_, _, targetArgs) := constApp? targetRoot
    | throw "WF equation: target root is not a fixpoint"
  let some (stepName, stepLevels, stepArgs) := constApp? (stripId sourceStep)
    | throw "WF equation: source proof has no fix_eq step"
  let expectedStep := if rootName == leanName ``WellFounded.Nat.fix then leanName ``WellFounded.Nat.fix_eq
    else if rootName == leanName ``WellFounded.fix then leanName ``WellFounded.fix_eq else Ix.Name.mkAnon
  unless stepName == expectedStep && stepLevels == rootLevels && stepArgs.size == sourceArgs.size + 1 &&
      ((stepArgs.extract 0 sourceArgs.size).zip sourceArgs).all (fun (a, b) => alphaEq a b) do
    throw "WF equation: fix_eq does not refer to the exact decoded source root"
  unless alphaEq stepArgs[sourceArgs.size]! point.expr do
    throw "WF equation: fix_eq uses a foreign input identity"
  let some spine := decodeSpine .psum L.n point.type | throw "WF equation: source equation has no sum input"
  unless alphaEq spine.type sourceArgs[0]! do throw "WF equation: equation input differs from source root"
  let targetSpine := spine.permute L.sigma
  unless alphaEq targetSpine.type targetArgs[0]! do throw "WF equation: target domain differs from permutation"
  let atPoint (argument : Expr) := substituteWFLocal point.fvar statement argument
  let mut leaves := #[]
  for index in [0:L.n] do
    let name ← freshFVar
    let payload : Ix.Compile.Image.Local := {
      fvar := name, userName := leanName `payload, type := spine.leaves[index]!, bi := .default }
    let sourceInput (value : Expr) := mkInj spine index value
    let targetInput (value : Expr) := mkInj targetSpine L.sigma[index]! value
    let body ← splitPSigma (fun value => atPoint (sourceInput value))
      (fun value => mkAppN (Expr.mkConst stepName stepLevels) (targetArgs.push (targetInput value)))
      64 payload.type id payload.expr
    leaves := leaves.push (Ix.Compile.Clique.mkLambda #[payload] body)
  let tree : Tree := {
    spine, w := Ix.Level.mkZero, motiveName := point.userName,
    motiveBody := Ix.Compile.Clique.abstractFVars #[point.fvar] statement,
    major := point.expr, leaves, extras := #[], altNames := #[] }
  let some body := tree.build | throw "WF equation: source-domain case reconstruction failed"
  let value ← liftE (closeBinders true parameters body)
  return { equation with name := newName, type, value }

/-- Owned root, proof, member and equation transport. -/
def transportWF (members : Array Decl) (packed : Decl) (proofs : Array Decl)
    (sigma : Array Nat) (newName : Name) (lemmas : Array (Decl × Name) := #[])
    (const? : Name → Option Ix.ConstantInfo := fun _ => none) : TM WFOutput := do
  let initial ← liftE (wfLayout members packed sigma newName)
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun names proof => names.insert proof.name
  let (fixed, body) ← openBinders true initial.numFixed packed.value
  let uses := scanProofs proofNames (fixed.map (·.fvar)) body {}
  let inverse := invPerm initial.fixedPerm
  let proofPerm : Std.HashMap Name (Array Nat) := uses.fold (init := {}) fun acc name positions =>
    acc.insert name ((idPerm positions.size).qsort fun i j => inverse[positions[i]!]! < inverse[positions[j]!]!)
  let isPackedLemma (name : Name) := match name with
    | .str parent _ _ => parent == packed.name
    | _ => false
  let proofPerm := lemmas.foldl (init := proofPerm) fun permutations (declaration, _) =>
    if isPackedLemma declaration.name then permutations.insert declaration.name initial.fixedPerm else permutations
  let L := { initial with proofPerm }
  let rewrite := rewriteOwnedWFUses L packed defaultFuel
  let schema ← decodeWFRoot L body
  let mut wellFoundedProof : Option (Name × Expr × Expr) := none
  if schema.sourceArguments.size == 5 then
    if let some (name, levels, arguments) := constApp? schema.sourceArguments[3]! then
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
        unless permutation.size == parameters.size do
          throw "WF ownership: well-founded proof prefix differs from its decoded application"
        let .const _ rootLevels _ := schema.head | throw "WF ownership: missing fixpoint universe"
        let some domainLevel := rootLevels[0]? | throw "WF ownership: missing domain universe"
        let goal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[schema.targetSpine.type, schema.targetArguments[2]!]
        let witness := mkAppN (Expr.mkConst (leanName ``Lean.opaqueId) #[Ix.Level.mkZero])
          #[goal, schema.targetArguments[3]!]
        let reordered := reorder permutation parameters
        wellFoundedProof := some (name, ← liftE (closeBinders false reordered goal),
          ← liftE (closeBinders true reordered witness))
  let value ← withReorderedBinders2 true L.numFixed L.fixedPerm packed.value pure
    (fun value => do
      let transformed ← conjugateWFRoot L value const?
      let transformed := match wellFoundedProof with
        | some _ =>
          let (_, sourceArgs) := getAppFnArgs value
          let (head, targetArgs) := getAppFnArgs transformed
          mkAppN head (targetArgs.set! 3 sourceArgs[3]!)
        | none => transformed
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
      for i in [0:positions.size] do
        unless positions[i]! < arguments.size do throw "WF obligation: fixed proof argument is out of scope"
        arguments := arguments.set! positions[i]! parameters[i]!.expr
      let instantiate (expression : Expr) := Ix.Compile.Clique.instLocals
        (Ix.Compile.Clique.abstractFVars (fixed.map (·.fvar)) expression) arguments
      let proofSchema := schema.mapExpressions instantiate
      let body ← rewriteWFObligations proofSchema L.sigma defaultFuel body
      let body ← rewrite body
      liftE (closeBinders isLam (reorder permutation parameters) body)
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
      unless tree.leaves.all (leafReduces 64) do
        throw "WF equation: source matcher needs argument-pushing proof reconstruction"
      output := output.push { decl := ← transportOwnedWFEqDef L packed packedTarget lemma name }
    else if isPackedLemma lemma.name then
      let type ← withReorderedBinders2 false L.numFixed L.fixedPerm lemma.type pure rewrite
      let value ← withReorderedBinders2 true L.numFixed L.fixedPerm lemma.value pure rewrite
      output := output.push { decl := { lemma with name, type, value } }
    else
      output := output.push { decl := { lemma with name, type := ← rewrite lemma.type, value := ← rewrite lemma.value } }
  let used := constOccurrences proofNames.contains value
  let rest := (proofs.map (·.name)).filter fun name => !used.contains name
  let numbered := (used ++ rest).zipIdx.map fun (name, index) =>
    (name, Ix.Name.mkStr newName s!"_proof_{index + 1}")
  let lemmaRenames := lemmas.filterMap fun (declaration, name) =>
    if declaration.name != name then some (declaration.name, name) else none
  let names : Std.HashMap Name Name := (numbered ++ lemmaRenames).foldl (init := {}) fun names (old, new) => names.insert old new
  let renamed := output.map fun item => { item with decl := { item.decl with
    name := (names.get? item.decl.name).getD item.decl.name
    type := renameConsts names.get? item.decl.type
    value := renameConsts names.get? item.decl.value } }
  return { decls := renamed, renames := #[(packed.name, newName)] ++ numbered ++ lemmaRenames }

end Ix.Compile.Clique
end
