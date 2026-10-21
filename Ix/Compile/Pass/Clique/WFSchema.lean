/-
  Ix.Compile.Pass.Clique.WFSchema: the exact root of Lean's well-founded
  encoding and the positions it relates.

  `decodeWFRoot` decodes the `WellFounded.fix` / `WellFounded.Nat.fix`
  application at the root of `f₀._mutual` into a `WFRootSchema`: the sum
  packing, the codomain and measure case trees (permuted only where they are
  fed by their own input binder), the relation and the well-founded witness.
  The other functions transport exactly the positions that schema owns: the
  recursive binder's telescope (`ownedWFRecType`) and the complete decreasing
  obligations (`rewriteWFObligations`). User terms are never recognised by
  their type.
-/
module
public import Ix.Compile.Pass.Clique.WF
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Expr Name)
open Ix.Compile.Canon (stripMdata mkAppN getAppFnArgs)

def applyWFCase (function argument : Expr) : Expr :=
  match stripMdata function with
  | .lam _ _ body _ _ => instantiateRev body #[argument]
  | _ => Expr.mkApp function argument

/-- Permute only the case tree fed by this function's exact input binder.
The case alternatives and constant codomains/measures are user syntax.
In particular a constant codomain equal to the packing is NOT permuted. -/
def decodeWFCase (spine : Spine) (sigma : Array Nat) (function : Expr) : TM Expr := do
  let (locals, body) ← openBinders true 1 function
  let some argument := locals[0]? | throw "WF schema: missing case function argument"
  let spineType ← spine.typeM "WF schema"
  unless alphaEqSkipMdata argument.type spineType do throw "WF schema: case function has a foreign domain"
  let body' ← if !mentionsFVar argument.fvar body then pure body else do
    let some tree := decodeTree spine.size body | throw "WF schema: input-dependent function is not a case tree"
    let treeType ← tree.spine.typeM "WF schema"
    unless alphaEqSkipMdata treeType spineType && alphaEqSkipMdata tree.major argument.expr &&
        tree.extras.isEmpty do
      throw "WF schema: case function has foreign entry identities"
    if tree.leaves.any (mentionsFVar argument.fvar) || mentionsFVar argument.fvar tree.motiveBody then
      throw "WF schema: case function captures its input outside the decoded major"
    let some value := (tree.permute sigma).bind Tree.build | throw "WF schema: case function reconstruction failed"
    pure value
  let some target := spine.permute sigma | throw "WF schema: case function domain does not take the permutation"
  let targetType ← target.typeM "WF schema"
  liftE (closeBinders true #[{ argument with type := targetType }] body')

structure WFRootSchema where
  sourceSpine : Spine
  targetSpine : Spine
  sourceCodomain : Expr
  targetCodomain : Expr
  sourceMeasure : Expr
  targetMeasure : Expr
  head : Expr
  sourceArguments : Array Expr
  targetArguments : Array Expr
  sourceRelation : Option Expr := none
  targetRelation : Option Expr := none

def WFRootSchema.mapExpressions (schema : WFRootSchema) (transform : Expr → Expr) : WFRootSchema :=
  { schema with
    sourceSpine := { schema.sourceSpine with leaves := schema.sourceSpine.leaves.map transform }
    targetSpine := { schema.targetSpine with leaves := schema.targetSpine.leaves.map transform }
    sourceCodomain := transform schema.sourceCodomain
    targetCodomain := transform schema.targetCodomain
    sourceMeasure := transform schema.sourceMeasure
    targetMeasure := transform schema.targetMeasure
    sourceArguments := schema.sourceArguments.map transform
    targetArguments := schema.targetArguments.map transform
    sourceRelation := schema.sourceRelation.map transform
    targetRelation := schema.targetRelation.map transform }

/-- At corresponding decoded constructors, source and target measures reduce
to the SAME user leaf. Thus this whole-proposition rewrite is definitional
equality, even inside a user proof. It never rewrites a relation's underlying
user instance or arbitrary inputs merely because their types match. -/
def rewriteWFObligations (schema : WFRootSchema) (sigma : Array Nat) (fuel : Nat)
    (expression : Expr) : TM Expr := do
  let sourceType ← schema.sourceSpine.typeM "WF obligation"
  let targetType ← schema.targetSpine.typeM "WF obligation"
  (visit sourceType targetType fuel expression).run' {}
where
  visit (sourceType targetType : Expr) : Nat → Expr → TransportMemoM Expr
  | 0, _ => throw "WF obligation: recursion bound"
  | fuel + 1, expression => memoTransport expression (fuel + 1) 0 do
    let go := visit sourceType targetType fuel
    let (head, args) := getAppFnArgs expression
    let relation : Option (Expr × Expr × Expr) := Id.run do
      if let some source := schema.sourceRelation then
        if let some target := schema.targetRelation then
          if let #[first, second] := args then
            if alphaEqSkipMdata head source then return some (target, first, second)
      if let some (name, levels, #[domain, a₁, a₂, measure, first, second]) := constApp? expression then
        if name == nInvImage && alphaEqSkipMdata domain sourceType &&
            alphaEqSkipMdata measure schema.sourceMeasure then
          return some (mkAppN (Expr.mkConst name levels)
            #[targetType, a₁, a₂, schema.targetMeasure], first, second)
      return none
    if let some (relation, first, second) := relation then
      if let some (firstSpine, firstIndex, firstPayload) := decodeInj schema.sourceSpine.size first then
        if let some (secondSpine, secondIndex, secondPayload) := decodeInj schema.sourceSpine.size second then
          let firstType ← firstSpine.typeM "WF obligation"
          let secondType ← secondSpine.typeM "WF obligation"
          if alphaEqSkipMdata firstType sourceType && alphaEqSkipMdata secondType sourceType then
            let firstPayload ← go firstPayload
            let secondPayload ← go secondPayload
            let firstPosition ← TM.idx sigma firstIndex "WF obligation: permutation"
            let secondPosition ← TM.idx sigma secondIndex "WF obligation: permutation"
            let some firstInj := mkInj schema.targetSpine firstPosition firstPayload
              | throw "WF obligation: injection reconstruction failed"
            let some secondInj := mkInj schema.targetSpine secondPosition secondPayload
              | throw "WF obligation: injection reconstruction failed"
            return mkAppN relation #[firstInj, secondInj]
    match expression with
    | .app f a _ => return Expr.mkApp (← go f) (← go a)
    | .lam n t b bi _ => return Expr.mkLam n (← go t) (← go b) bi
    | .forallE n t b bi _ => return Expr.mkForallE n (← go t) (← go b) bi
    | .letE n t v b nd _ => return Expr.mkLetE n (← go t) (← go v) (← go b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go x)
    | .mdata d x _ => return Expr.mkMData d (← go x)
    | _ => return expression

/-- Decode the actual `Nat.fix` or `fix (invImage ...).rel` root. The
underlying measure codomain and relation instance are opaque user objects;
only invImage's declared source domain and measure argument may change. -/
def decodeWFRoot (L : WFLayout) (value : Expr) : TM WFRootSchema := do
  let some (name, levels, args) := constApp? (stripMdata value)
    | throw "WF schema: root is not a fixpoint application"
  let isNat := name == leanName ``WellFounded.Nat.fix
  let unsupported := "WF schema: unsupported fixpoint root"
  unless (isNat && args.size == 4) ||
      (name == leanName ``WellFounded.fix && args.size == 5) do
    throw unsupported
  let some domain := args[0]? | throw unsupported
  let some sourceCodomain := args[1]? | throw unsupported
  let some third := args[2]? | throw unsupported
  let some spine := decodeSpine .psum L.n domain
    | throw "WF schema: root has no sum packing"
  unless L.isClique spine do throw "WF schema: root has a foreign packing"
  let some targetSpine := spine.permute L.sigma
    | throw "WF schema: root packing does not take the permutation"
  let sourceType ← spine.typeM "WF schema"
  let targetType ← targetSpine.typeM "WF schema"
  let codomain ← decodeWFCase spine L.sigma sourceCodomain
  let (measure, targetArgs, relations) ← if isNat then do
    let measure ← decodeWFCase spine L.sigma third
    pure (third, #[targetType, codomain, measure], none)
  else do
    let .proj structureName field relation _ := stripMdata third
      | throw "WF schema: general relation is not the owned projection"
    unless structureName == nWFRelation && field == 0 do
      throw "WF schema: general relation projects another structure"
    let some (relName, relLevels, relArgs) := constApp? relation
      | throw "WF schema: general relation is not invImage"
    let foreignDomain := "WF schema: general relation has foreign invImage domain"
    unless relName == leanName ``invImage do throw foreignDomain
    let #[relDomain, relCodomain, relMeasure, relInstance] := relArgs | throw foreignDomain
    unless alphaEqSkipMdata relDomain sourceType do throw foreignDomain
    let measure ← decodeWFCase spine L.sigma relMeasure
    let targetRel := mkAppN (Expr.mkConst relName relLevels)
      #[targetType, relCodomain, measure, relInstance]
    let targetRelation := Expr.mkProj nWFRelation 0 targetRel
    -- Lean may abstract its opaqueId/projection into a separate proof
    -- declaration. Regenerate the well-founded witness from the SAME
    -- decoded relation record, instead of recognizing arbitrary proof syntax.
    -- The production declaration route can re-abstract this checked witness.
    let mut proof := Expr.mkProj nWFRelation 1 targetRel
    -- This wrapper belongs to the exact root witness, not a user proof
    -- discovered by its type. Preserve Lean's inline opaqueId convention
    -- only after checking its complete source proposition and projection.
    let some witness := args[3]? | throw unsupported
    if let some (wrapper, wrapperLevels, #[wrappedGoal, wrappedProof]) := constApp? witness then
      if wrapper == leanName ``Lean.opaqueId then
        let some domainLevel := levels[0]? | throw "WF schema: missing domain universe"
        let sourceGoal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[sourceType, third]
        unless alphaEqSkipMdata wrappedGoal sourceGoal &&
            alphaEqSkipMdata wrappedProof (Expr.mkProj nWFRelation 1 relation) do
          throw "WF schema: inline well-founded witness differs from the exact root relation"
        let targetGoal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[targetType, targetRelation]
        proof := mkAppN (Expr.mkConst wrapper wrapperLevels) #[targetGoal, proof]
    pure (relMeasure, #[targetType, codomain, targetRelation, proof], some (third, targetRelation))
  let targetMeasure ← decodeWFCase spine L.sigma measure
  return {
    sourceSpine := spine, targetSpine, sourceCodomain,
    targetCodomain := codomain, sourceMeasure := measure, targetMeasure,
    head := Expr.mkConst name levels, sourceArguments := args, targetArguments := targetArgs
    sourceRelation := relations.map (·.1)
    targetRelation := relations.map (·.2) }

/-- Rebuild only the two declared binders of a recursive telescope. Exact
source measure and point identities establish the decreasing relation; the
underlying relation and all its parameters stay unchanged. -/
def ownedWFRecType (schema : WFRootSchema) (sourcePoint targetPoint type : Expr) : TM Expr := do
  let (locals, result) ← openBinders false 2 type
  let #[argument, proof] := locals | throw "WF schema: incomplete recursive telescope"
  let sourceType ← schema.sourceSpine.typeM "WF schema"
  let targetType ← schema.targetSpine.typeM "WF schema"
  unless alphaEqSkipMdata argument.type sourceType do
    throw "WF schema: recursive argument has a foreign domain"
  let relation ← match schema.sourceRelation, schema.targetRelation with
    | some source, some target => do
      let (head, args) := getAppFnArgs proof.type
      let foreign := "WF schema: decreasing obligation has a foreign root relation or argument identity"
      let #[first, second] := args | throw foreign
      unless alphaEqSkipMdata head source && alphaEqSkipMdata first argument.expr &&
          alphaEqSkipMdata second sourcePoint do
        throw foreign
      pure (mkAppN target #[argument.expr, targetPoint])
    | _, _ => do
      let some (name, levels, args) := constApp? proof.type
        | throw "WF schema: decreasing obligation is not invImage"
      let foreign := "WF schema: decreasing obligation has foreign measure or argument identities"
      let #[domain, a₁, a₂, measure, first, second] := args | throw foreign
      unless name == nInvImage && alphaEqSkipMdata domain sourceType &&
          alphaEqSkipMdata measure schema.sourceMeasure &&
          alphaEqSkipMdata first argument.expr && alphaEqSkipMdata second sourcePoint do
        throw foreign
      pure (mkAppN (Expr.mkConst name levels)
        #[targetType, a₁, a₂, schema.targetMeasure, argument.expr, targetPoint])
  unless alphaEqSkipMdata result (applyWFCase schema.sourceCodomain argument.expr) do
    throw "WF schema: recursive result differs from the root codomain"
  liftE (closeBinders false #[{ argument with type := targetType },
    { proof with type := relation }] (applyWFCase schema.targetCodomain argument.expr))

end Ix.Compile.Pass.Clique

end
