/- Prototype: transport only the recursive binder and output tuple decoded
from Lean's partial-fixpoint functional. Inner user binders retain identity. -/
module
public import Ix.Compile.Clique.PartialFixpoint
public section

namespace Ix.Compile.Clique

open Ix (Expr Name ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata substLevels)

/-- Ordinary constructor projection reduction. No type-shape recognition and
no delta reduction: a projection reduces only when its actual operand is the
corresponding constructor, including constructors introduced by substitution. -/
def reduceConjugation : Expr → Expr
  | .app f a _ => reduceHead (Expr.mkApp (reduceConjugation f) (reduceConjugation a))
  | .proj s i x _ => reduceHead (Expr.mkProj s i (reduceConjugation x))
  | .lam n t b bi _ => Expr.mkLam n (reduceConjugation t) (reduceConjugation b) bi
  | .forallE n t b bi _ => Expr.mkForallE n (reduceConjugation t) (reduceConjugation b) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (reduceConjugation t) (reduceConjugation v) (reduceConjugation b) nd
  | .mdata d x _ => Expr.mkMData d (reduceConjugation x)
  | e => e
where
  reduceHead (e : Expr) : Expr := Id.run do
    let project (s : Ix.Name) (i : Nat) (base : Expr) : Option Expr := do
      let (c, _, args) ← constApp? (stripMdata base)
      unless ((s == nPProd && c == nPProdMk) || (s == nAnd && c == nAndIntro)) &&
          args.size == 4 && i < 2 do none
      args[2 + i]?
    match e with
    | .proj s i x _ => return (project s i x).getD e
    | _ =>
      let (h, args) := getAppFnArgs e
      if let .const c _ _ := h then
        if (c == nPProdFst || c == nPProdSnd) && args.size ≥ 3 then
          if let some value := project nPProd (if c == nPProdFst then 0 else 1) args[2]! then
            return mkAppN value (args.extract 3 args.size)
      return e

/-- Evaluate inverse-packing substitution at paths of the exact recursive
binder, retaining Lean's projection-vs-application spelling at each owned
site. This is constructor projection reduction of the explicit inverse
tuple, not a rewrite selected by a binder's type. Other binders are visited
only to adjust de Bruijn depth. A bare recursive value becomes the inverse
tuple itself. -/
def substitutePFInput (input : Spine) (sigma : Array Nat) (body : Expr) : Except String Expr :=
  go body 0
where
  go (e : Expr) (depth : Nat) : Except String Expr := do
    let source := { input with leaves := input.leaves.map (liftLoose · (depth + 1)) }
    let target := source.permute sigma
    if let some (spine, j, base) := decodePathApp input.size e then
      if alphaEq base (Expr.mkBVar depth) then
        unless alphaEq (normOrderAlias spine.type) (normOrderAlias source.type) do
          throw "PF conjugation: recursive path has a foreign type"
        return mkPathApp (spine.permute sigma) sigma[j]! base
    match e with
    | .proj .. =>
      let (steps, base) := projChain e
      if alphaEq base (Expr.mkBVar depth) then
        let some (j, used) := pathPrefix input.size steps
          | throw "PF conjugation: recursive projection is not a component path"
        unless stepsFit source j (steps.extract 0 used) do
          throw "PF conjugation: recursive projection has a foreign structure"
        return applyProjs (target.projSteps sigma[j]! ++ steps.extract used steps.size) base
    | _ => pure ()
    match e with
    | .bvar i _ =>
      if i == depth then
        return mkTuple source (sigma.map fun j => applyProjs (target.projSteps j) e)
      return e
    | .app f a _ => return Expr.mkApp (← go f depth) (← go a depth)
    | .proj s i x _ => return Expr.mkProj s i (← go x depth)
    | .lam n t b bi _ => return Expr.mkLam n (← go t depth) (← go b (depth + 1)) bi
    | .forallE n t b bi _ => return Expr.mkForallE n (← go t depth) (← go b (depth + 1)) bi
    | .letE n t v b nd _ =>
      return Expr.mkLetE n (← go t depth) (← go v depth) (← go b (depth + 1)) nd
    | .mdata d x _ => return Expr.mkMData d (← go x depth)
    | _ => return e

/-- `φ ∘ F ∘ φ⁻¹`, with the input binder and output tuple established by
decoding this functional. The inverse tuple replaces that exact binder by
de Bruijn identity; same-typed or shadowing user binders are never selected.
The existing `fix_iso` theorem supplies the semantic transport obligation. -/
def conjugatePF (n : Nat) (sigma : Array Nat) (functional : Expr) : Except String Expr := do
  unless n ≥ 2 && sigma.size == n && isPerm sigma do throw "PF conjugation: invalid permutation"
  let .lam name domain body bi _ := stripMdata functional
    | throw "PF conjugation: missing recursive binder"
  let some input := decodeSpine .pprod n domain
    | throw "PF conjugation: recursive binder is not a packed product"
  let some (output, components) := decodeTuple n (stripMdata body)
    | throw "PF conjugation: missing encoded result tuple"
  unless alphaEq (normOrderAlias output.type) (normOrderAlias (liftLoose input.type 1)) do
    throw "PF conjugation: input and output packing differ"
  let target := input.permute sigma
  let components ← components.mapM (substitutePFInput input sigma)
  return Expr.mkLam name target.type
    (mkTuple (output.permute sigma) (permute sigma components)) bi

/-- Precompose a decoded component functional with the inverse packing.
This is the function occurring in the existing composition proof fallback. -/
def conjugatePFInput (input : Spine) (sigma : Array Nat) (functional : Expr) : Except String Expr := do
  unless input.size ≥ 2 && sigma.size == input.size && isPerm sigma do
    throw "PF input conjugation: invalid permutation"
  let .lam name domain body bi _ := stripMdata functional
    | throw "PF input conjugation: missing recursive binder"
  unless alphaEq (normOrderAlias domain) (normOrderAlias input.type) do
    throw "PF input conjugation: wrong binder domain"
  let some actualInput := decodeSpine .pprod input.size domain
    | throw "PF input conjugation: missing functional packing"
  let target := actualInput.permute sigma
  return Expr.mkLam name target.type (← substitutePFInput actualInput sigma body) bi

/-- Transport a decoded monotonicity tree by the existing checked composition
construction, keeping every source per-component proof verbatim. This
prototype deliberately avoids recognizing user proof syntax by its types. -/
def conjugatePFMono (layout : PFLayout) (proof : Expr) : Except String Expr := do
  let some (data, fs, hs) := decodeMonoTree layout proof
    | throw "PF conjugation: monotonicity proof is not a decoded tuple tree"
  let target := data.permute layout.sigma
  let fs' ← fs.mapM (conjugatePFInput data.tspine layout.sigma)
  let hs' ← (List.range layout.n).toArray.mapM fun k =>
    mkComposeFallback layout.sigma data target k fs[k]! hs[k]! layout.composeLevels
  return mkMonoTree target (permute layout.sigma fs') (permute layout.sigma hs')

def nMonotone : Name := leanName ``Lean.Order.monotone

/-- A premise about the exact symbolic recursive-domain parameter. Opening
the theorem telescope before this test distinguishes parameters that merely
receive equal types at an application. Quantified user parameters stay user
parameters, even if their instantiated type is the packing. -/
def ownedMonoPremise (domain order : Name) : Expr → Bool
  | .forallE _ t b _ _ =>
    !mentionsFVar domain t && !mentionsFVar order t && ownedMonoPremise domain order b
  | e => match constApp? (stripMdata e) with
    | some (c, _, args) => c == nMonotone && args.size == 5 &&
      alphaEq args[0]! (Expr.mkFVar domain) && alphaEq args[1]! (Expr.mkFVar order)
    | none => false

/-- Transport a proof only through the argument roles of its applied
theorem's declared telescope. The domain/order are exact fresh identities
from its `monotone` conclusion, never inferred from a user's matching type.
Unknown dependent roles decline to the composition construction. -/
def transportOwnedMono (L : PFLayout) (const? : Name → Option ConstantInfo) :
    Nat → Expr → TM Expr
  | 0, _ => throw "PF proof ownership: recursion bound exhausted"
  | fuel + 1, e => do
    if let some (data, j) := decodePathProof L e then
      return (mkPathProof (data.permute L.sigma) L.sigma[j]!).1
    match e with
    | .lam n t b bi _ =>
      return Expr.mkLam n t (← transportOwnedMono L const? fuel b) bi
    | .mdata d x _ => return Expr.mkMData d (← transportOwnedMono L const? fuel x)
    | _ => pure ()
    let some (name, levels, args) := constApp? e
      | throw "PF proof ownership: expected an applied monotonicity theorem"
    let some info := const? name | throw s!"PF proof ownership: missing theorem {name}"
    let type := substLevels info.getCnst.levelParams levels info.getCnst.type
    let (parameters, conclusion) ← openBinders false args.size type
    let some (head, _, resultArgs) := constApp? conclusion
      | throw "PF proof ownership: theorem conclusion is not monotonicity"
    unless head == nMonotone && resultArgs.size == 5 do
      throw "PF proof ownership: theorem conclusion is not monotonicity"
    let .fvar domain _ := resultArgs[0]!
      | throw "PF proof ownership: domain is not a theorem parameter"
    let .fvar order _ := resultArgs[1]!
      | throw "PF proof ownership: order is not a theorem parameter"
    -- This transport precomposes the recursive input and leaves the output
    -- type/order alone. `monotone_id`, for example, has no function argument
    -- to inspect but changes *both* ends when its one type parameter changes.
    -- Such a theorem needs the separately checked path or composition route.
    unless !mentionsFVar domain resultArgs[2]! && !mentionsFVar order resultArgs[2]! &&
        !mentionsFVar domain resultArgs[3]! && !mentionsFVar order resultArgs[3]! do
      throw "PF proof ownership: conclusion output depends on the recursive-domain parameter"
    let some domainIndex := parameters.findIdx? (·.fvar == domain)
      | throw "PF proof ownership: missing domain parameter"
    let some orderIndex := parameters.findIdx? (·.fvar == order)
      | throw "PF proof ownership: missing order parameter"
    let some spine := decodeSpine .pprod L.n args[domainIndex]!
      | throw "PF proof ownership: recursive domain is not the decoded packing"
    let some data := decodeOrderData L args[orderIndex]!
      | throw "PF proof ownership: recursive order is not the decoded order"
    unless L.isClique spine && alphaEq (normOrderAlias spine.type) (normOrderAlias data.spine.type) do
      throw "PF proof ownership: domain/order mismatch"
    let target := ({ data with tspine := spine }).permute L.sigma
    let mut args' := args
    for i in [0:parameters.size] do
      let parameter := parameters[i]!
      if i == domainIndex then args' := args'.set! i target.tspine.type
      else if i == orderIndex then args' := args'.set! i target.packedPO
      else if mentionsFVar domain parameter.type || mentionsFVar order parameter.type then
        if ownedMonoPremise domain order parameter.type then
          args' := args'.set! i (← transportOwnedMono L const? fuel args[i]!)
        else
          let .forallE _ input output _ _ := stripMdata parameter.type
            | throw "PF proof ownership: unsupported dependent argument role"
          unless alphaEq input (Expr.mkFVar domain) &&
              !mentionsFVar domain output && !mentionsFVar order output &&
              looseAllAtLeast output 1 do
            throw "PF proof ownership: unsupported dependent functional role"
          args' := args'.set! i (← liftE (conjugatePFInput spine L.sigma args[i]!))
    return mkAppN (Expr.mkConst name levels) args'

/-- Regenerate recognized source proof syntax; keep each unknown component
proof verbatim inside checked composition. The functional arguments always
come from binder-identified precomposition, including the fallback branch. -/
def conjugatePFMonoChecked (L : PFLayout) (const? : Name → Option ConstantInfo)
    (proof : Expr) : TM Expr := do
  let some (data, fs, hs) := decodeMonoTree L proof
    | throw "PF conjugation: monotonicity proof is not a decoded tuple tree"
  let target := data.permute L.sigma
  let fs' ← liftE (fs.mapM (conjugatePFInput data.tspine L.sigma))
  let mut hs' := #[]
  for k in [0:L.n] do
    let state ← get
    match (transportOwnedMono L const? defaultFuel hs[k]!).run state with
    | .ok (h, state') => set state'; hs' := hs'.push h
    | .error reason =>
      hs' := hs'.push (← liftE (mkComposeFallback L.sigma data target k fs[k]! hs[k]! L.composeLevels))
      modify fun state => { state with fallbacks := state.fallbacks.push s!"monotonicity proof {k}: {reason}" }
  return mkMonoTree target (permute L.sigma fs') (permute L.sigma hs')

/-- The packed root is identified by its declaration and full fixed-argument
application. Replacing it by the inverse output tuple preserves its old type
and meaning everywhere in user syntax. Reducing surrounding projections
then yields canonical member paths without selecting user binders. -/
def rewritePFPackedUses (L : PFLayout) : Expr → Except String Expr := go defaultFuel
where
  go : Nat → Expr → Except String Expr
  | 0, _ => throw "PF ownership: packed-use recursion bound exhausted"
  | fuel + 1, e => do
    if let some (name, levels, args) := constApp? e then
      if name == L.packedName then
        unless args.size == L.numFixed do throw "PF ownership: partial/over-applied packed declaration"
        let args' ← args.mapM (go fuel)
        let source := { L.spine with leaves := L.spine.leaves.map fun t =>
          Ix.Compile.Clique.instantiateRev t args.reverse }
        let target := source.permute L.sigma
        let value := mkAppN (Expr.mkConst L.newPackedName levels) (L.fixedPerm.map (args'[·]!))
        return mkTuple source (L.sigma.map fun j => applyProjs (target.projSteps j) value)
    match e with
    | .app f a _ =>
      let f' ← go fuel f
      let a' ← go fuel a
      if f' == f && a' == a then return e
      return reduceConjugation.reduceHead (Expr.mkApp f' a')
    | .proj s i x _ =>
      let x' ← go fuel x
      if x' == x then return e
      return reduceConjugation.reduceHead (Expr.mkProj s i x')
    | .lam n t b bi _ => return Expr.mkLam n (← go fuel t) (← go fuel b) bi
    | .forallE n t b bi _ => return Expr.mkForallE n (← go fuel t) (← go fuel b) bi
    | .letE n t v b nd _ =>
      return Expr.mkLetE n (← go fuel t) (← go fuel v) (← go fuel b) nd
    | .mdata d x _ => return Expr.mkMData d (← go fuel x)
    | _ => return e

/-- Transform the exact monotonicity statement of an abstracted tuple proof.
Every modified position is supplied by the `monotone` application schema. -/
def conjugatePFStatement (L : PFLayout) (type : Expr) : Except String Expr := do
  let some (head, levels, args) := constApp? (stripMdata type)
    | throw "PF ownership: expected a monotonicity statement"
  unless head == nMonotone && args.size == 5 do throw "PF ownership: expected a monotonicity statement"
  let some input := decodeSpine .pprod L.n args[0]!
    | throw "PF ownership: statement has no input packing"
  let some output := decodeSpine .pprod L.n args[2]!
    | throw "PF ownership: statement has no output packing"
  let some data := decodeOrderData L args[1]!
    | throw "PF ownership: statement has no packed input order"
  let data := { data with tspine := output }
  unless L.isClique input && alphaEq (normOrderAlias input.type) (normOrderAlias output.type) &&
      alphaEq args[3]! (data.poTree 0) do
    throw "PF ownership: statement input/output orders differ"
  let target := data.permute L.sigma
  return mkAppN (Expr.mkConst head levels)
    #[(input.permute L.sigma).type, target.packedPO, target.tspine.type,
      target.poTree 0, ← conjugatePF L.n L.sigma args[4]!]

structure PFEquationStep where
  type : Expr
  left : Expr
  right : Expr
  proof : Expr

/-- Rebuild the equation proof from the owned fixpoint equation, its member
projection, and ordinary congruence applications. User expressions in the
component body are never traversed or recognized. -/
def conjugatePFEquationProof (L : PFLayout) (component : Nat) (sourceFix targetFix : Expr) :
    Nat → Expr → Except String PFEquationStep
  | 0, _ => throw "PF equation ownership: proof recursion bound exhausted"
  | fuel + 1, e => do
    let some (head, levels, args) := constApp? (stripMdata e)
      | throw "PF equation ownership: unsupported proof constructor"
    if head == leanName ``id && args.size == 2 then
      return ← conjugatePFEquationProof L component sourceFix targetFix fuel args[1]!
    if head == leanName ``Eq.trans && args.size == 6 then
      let some (last, _, lastArgs) := constApp? args[5]!
        | throw "PF equation ownership: non-reflexive final equation step"
      unless last == leanName ``Eq.refl && lastArgs.size == 2 do
        throw "PF equation ownership: non-reflexive final equation step"
      return ← conjugatePFEquationProof L component sourceFix targetFix fuel args[4]!
    if (head == leanName ``Lean.Order.fix_eq || head == leanName ``Lean.Order.lfp_monotone_fix) && args.size == 4 then
      let some (sourceHead, _, sourceArgs) := constApp? sourceFix
        | throw "PF equation ownership: missing source fixpoint"
      let some (_, _, targetArgs) := constApp? targetFix
        | throw "PF equation ownership: missing target fixpoint"
      let expected := if sourceHead == nOrderFix then leanName ``Lean.Order.fix_eq
        else leanName ``Lean.Order.lfp_monotone_fix
      unless head == expected && args.size == sourceArgs.size && targetArgs.size == 4 &&
          (args.zip sourceArgs).all (fun (a, b) => alphaEq a b) do
        throw "PF equation ownership: equation belongs to another fixpoint"
      return {
        type := targetArgs[0]!, left := targetFix
        right := Expr.mkApp targetArgs[2]! targetFix,
        proof := mkAppN (Expr.mkConst head levels) targetArgs }
    if head == leanName ``congrArg && args.size == 6 then
      let .lam binder domain body bi _ := stripMdata args[4]!
        | throw "PF equation ownership: congruence is not a member projection"
      let some source := decodeSpine .pprod L.n domain
        | throw "PF equation ownership: congruence has no packed binder"
      let (steps, base) := projChain body
      let some (index, used) := pathPrefix L.n steps
        | throw "PF equation ownership: congruence is not a complete member path"
      unless index == component && used == steps.size && alphaEq base (Expr.mkBVar 0) &&
          stepsFit source index steps do
        throw "PF equation ownership: congruence selects another binder/component"
      let previous ← conjugatePFEquationProof L component sourceFix targetFix fuel args[5]!
      let target := source.permute L.sigma
      let projection := Expr.mkLam binder target.type
        (applyProjs (target.projSteps L.sigma[component]!) (Expr.mkBVar 0)) bi
      return {
        type := args[1]!, left := Expr.mkApp projection previous.left
        right := Expr.mkApp projection previous.right,
        proof := mkAppN (Expr.mkConst head levels)
          #[target.type, args[1]!, previous.left, previous.right, projection, previous.proof] }
    if head == leanName ``congrFun && args.size == 6 then
      let previous ← conjugatePFEquationProof L component sourceFix targetFix fuel args[4]!
      return {
        type := Expr.mkApp args[1]! args[5]!, left := Expr.mkApp previous.left args[5]!
        right := Expr.mkApp previous.right args[5]!,
        proof := mkAppN (Expr.mkConst head levels)
          #[args[0]!, args[1]!, previous.left, previous.right, previous.proof, args[5]!] }
    throw s!"PF equation ownership: unsupported proof constructor {head}"

def conjugatePFEquation (L : PFLayout) (members : Array Decl) (sourcePacked targetPacked : Decl)
    (lemma : Decl) (newName : Name) : TM Decl := do
  let arity := Ix.Compile.Image.forallArity lemma.type
  let (parameters, statement) ← openBinders false arity lemma.type
  let some (eq, _, eqArgs) := constApp? statement
    | throw "PF equation ownership: statement is not an equality"
  unless eq == leanName ``Eq && eqArgs.size == 3 do throw "PF equation ownership: statement is not an equality"
  let some (memberName, _, memberArgs) := constApp? eqArgs[1]!
    | throw "PF equation ownership: equality does not start at a member application"
  let some component := members.findIdx? (·.name == memberName)
    | throw "PF equation ownership: equality concerns another declaration"
  let appliedMember := betaApp members[component]!.value memberArgs
  let (projection, _) := getAppFnArgs appliedMember
  let (_, base) := projChain projection
  let some (packedName, _, fixedArgs) := constApp? base
    | throw "PF equation ownership: member has no packed root"
  unless packedName == sourcePacked.name && fixedArgs.size == L.numFixed do
    throw "PF equation ownership: member uses another packed root"
  let sourceFix := betaApp sourcePacked.value fixedArgs
  let targetFix := betaApp targetPacked.value (L.fixedPerm.map (fixedArgs[·]!))
  let (binders, proofBody) := peelLams arity lemma.value #[]
  unless binders.size == arity do throw "PF equation ownership: proof telescope differs from its statement"
  let proofBody := Ix.Compile.Clique.instLocals proofBody (parameters.map (·.expr))
  let proof ← liftE (conjugatePFEquationProof L component sourceFix targetFix defaultFuel proofBody)
  let value ← liftE (closeBinders true parameters proof.proof)
  return { lemma with name := newName, value }

/-- Ownership-preserving PF transport. The packed declaration, its fixed
binders, fixpoint arguments and abstracted proof positions are decoded once.
User syntax is transported only by substitution of those exact identities.
Unsupported roles leave the entire clique to the caller's faithful baseline. -/
def transportPF (members : Array Decl) (packed : Decl) (proofs : Array Decl) (sigma : Array Nat)
    (newPackedName : Name) (const? : Name → Option ConstantInfo)
    (lemmas : Array (Decl × Name) := #[]) : TM WFOutput := do
  let initial ← liftE (pfLayout members packed sigma newPackedName)
  let composeLevels := match const? nMonoCompose with
    | some info => info.getCnst.levelParams
    | none => #[]
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun names proof => names.insert proof.name
  let (fixed, body) ← openBinders true initial.numFixed packed.value
  let uses := scanProofs proofNames (fixed.map (·.fvar)) body {}
  let inverseFixed := invPerm initial.fixedPerm
  let proofPerm : Std.HashMap Name (Array Nat) := uses.fold (init := {}) fun acc name indices =>
    acc.insert name ((idPerm indices.size).qsort fun a b => inverseFixed[indices[a]!]! < inverseFixed[indices[b]!]!)
  let L := { initial with composeLevels, proofPerm }
  let unchanged (e : Expr) : TM Expr := pure e
  let packedType (e : Expr) : TM Expr := do
    let some spine := decodeSpine .pprod L.n (stripMdata e)
      | throw "PF ownership: packed result type is not a product"
    unless L.isClique spine do throw "PF ownership: packed result type differs from the layout"
    return (spine.permute sigma).type
  let packedValue (e : Expr) : TM Expr := do
    let some (head, levels, args) := constApp? (stripMdata e)
      | throw "PF ownership: packed value is not a fixpoint application"
    unless (head == nOrderFix || head == leanName ``Lean.Order.lfp_monotone) && args.size == 4 do
      throw "PF ownership: unsupported fixpoint root"
    let some spine := decodeSpine .pprod L.n args[0]!
      | throw "PF ownership: fixpoint has no packed domain"
    let some (instanceName, instanceSpine, instances) := decodeInstTree L.n args[1]!
      | throw "PF ownership: fixpoint has no decoded instance tree"
    unless L.isClique spine && alphaEq (normOrderAlias spine.type) (normOrderAlias instanceSpine.type) do
      throw "PF ownership: fixpoint type/instance mismatch"
    let some (proofName, proofLevels, proofArgs) := constApp? args[3]!
      | throw "PF ownership: fixpoint proof is not an owned abstracted declaration"
    unless proofNames.contains proofName do
      throw "PF ownership: fixpoint proof is not among the owned declarations"
    let permutation := (proofPerm.get? proofName).getD #[]
    unless proofArgs.size == permutation.size do throw "PF ownership: proof fixed-argument arity mismatch"
    let proof := mkAppN (Expr.mkConst proofName proofLevels) (permutation.map (proofArgs[·]!))
    return mkAppN (Expr.mkConst head levels)
      #[(spine.permute sigma).type,
        mkInstTree instanceName (instanceSpine.permute sigma) (permute sigma instances),
        ← liftE (conjugatePF L.n sigma args[2]!), proof]
  let type ← withReorderedBinders2 false L.numFixed L.fixedPerm packed.type unchanged packedType
  let value ← withReorderedBinders2 true L.numFixed L.fixedPerm packed.value unchanged packedValue
  let mut out : Array Transported := #[{ decl := { packed with name := newPackedName, type, value } }]
  for proof in proofs do
    let permutation := (proofPerm.get? proof.name).getD #[]
    let type ← withReorderedBinders2 false permutation.size permutation proof.type unchanged
      (fun e => liftE (conjugatePFStatement L e))
    let before := (← get).fallbacks.size
    let value ← withReorderedBinders2 true permutation.size permutation proof.value unchanged
      (conjugatePFMonoChecked L const?)
    let causes := (← get).fallbacks.extract before (← get).fallbacks.size
    out := out.push {
      decl := { proof with type, value }
      fallback := if causes.isEmpty then none else some ("; ".intercalate causes.toList) }
  for member in members do
    out := out.push { decl := { member with
      type := ← liftE (rewritePFPackedUses L member.type),
      value := ← liftE (rewritePFPackedUses L member.value) } }
  for (lemma, name) in lemmas do
    let declaration ← conjugatePFEquation L members packed
      { packed with name := newPackedName, type, value } lemma name
    out := out.push { decl := declaration }
  let order := constOccurrences proofNames.contains value
  let rest := (proofs.map (·.name)).filter fun name => !order.contains name
  let numbered := (order ++ rest).zipIdx.map fun (name, i) =>
    (name, Ix.Name.mkStr newPackedName s!"_proof_{i + 1}")
  let lemmaRenames := lemmas.filterMap fun (lemma, name) => if lemma.name != name then some (lemma.name, name) else none
  let renames : Std.HashMap Name Name := (numbered ++ lemmaRenames).foldl (init := {}) fun names (a, b) => names.insert a b
  let renamed := out.map fun item => { item with decl := { item.decl with
    name := (renames.get? item.decl.name).getD item.decl.name,
    type := renameConsts renames.get? item.decl.type,
    value := renameConsts renames.get? item.decl.value } }
  return { decls := renamed, renames := #[(packed.name, newPackedName)] ++ numbered ++ lemmaRenames }

end Ix.Compile.Clique

end
