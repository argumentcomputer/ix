/- Exact root and relationship positions of Lean's WF encoding. -/
module
public import Ix.Compile.Clique.WF
public section

namespace Ix.Compile.Clique
open Ix (Expr Name)
open Ix.Compile.Canon (stripMdata mkAppN getAppFnArgs instantiateRev)

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
  unless alphaEq argument.type spine.type do throw "WF schema: case function has a foreign domain"
  let body' ← if !mentionsFVar argument.fvar body then pure body else do
    let some tree := decodeTree spine.size body | throw "WF schema: input-dependent function is not a case tree"
    unless alphaEq tree.spine.type spine.type && alphaEq tree.major argument.expr && tree.extras.isEmpty do
      throw "WF schema: case function has foreign entry identities"
    if tree.leaves.any (mentionsFVar argument.fvar) || mentionsFVar argument.fvar tree.motiveBody then
      throw "WF schema: case function captures its input outside the decoded major"
    let some value := (tree.permute sigma).build | throw "WF schema: case function reconstruction failed"
    pure value
  liftE (closeBinders true #[{ argument with type := (spine.permute sigma).type }] body')

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
def rewriteWFObligations (schema : WFRootSchema) (sigma : Array Nat) : Nat → Expr → TM Expr
  | 0, _ => throw "WF obligation: recursion bound"
  | fuel + 1, expression => do
    let go := rewriteWFObligations schema sigma fuel
    let (head, args) := getAppFnArgs expression
    let relation : Option (Expr × Expr × Expr) := Id.run do
      if let some source := schema.sourceRelation then
        if let some target := schema.targetRelation then
          if alphaEq head source && args.size == 2 then return some (target, args[0]!, args[1]!)
      if let some (name, levels, args) := constApp? expression then
        if name == nInvImage && args.size == 6 && alphaEq args[0]! schema.sourceSpine.type &&
            alphaEq args[3]! schema.sourceMeasure then
          return some (mkAppN (Expr.mkConst name levels)
            #[schema.targetSpine.type, args[1]!, args[2]!, schema.targetMeasure], args[4]!, args[5]!)
      return none
    if let some (relation, first, second) := relation then
      if let some (firstSpine, firstIndex, firstPayload) := decodeInj schema.sourceSpine.size first then
        if let some (secondSpine, secondIndex, secondPayload) := decodeInj schema.sourceSpine.size second then
          if alphaEq firstSpine.type schema.sourceSpine.type && alphaEq secondSpine.type schema.sourceSpine.type then
            return mkAppN relation #[
              mkInj schema.targetSpine sigma[firstIndex]! (← go firstPayload),
              mkInj schema.targetSpine sigma[secondIndex]! (← go secondPayload)]
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
  unless (isNat && args.size == 4) ||
      (name == leanName ``WellFounded.fix && args.size == 5) do
    throw "WF schema: unsupported fixpoint root"
  let some spine := decodeSpine .psum L.n args[0]!
    | throw "WF schema: root has no sum packing"
  unless L.isClique spine do throw "WF schema: root has a foreign packing"
  let targetSpine := spine.permute L.sigma
  let codomain ← decodeWFCase spine L.sigma args[1]!
  let (measure, targetArgs) ← if isNat then do
    let measure ← decodeWFCase spine L.sigma args[2]!
    pure (args[2]!, #[targetSpine.type, codomain, measure])
  else do
    let .proj structureName field relation _ := stripMdata args[2]!
      | throw "WF schema: general relation is not the owned projection"
    unless structureName == nWFRelation && field == 0 do
      throw "WF schema: general relation projects another structure"
    let some (relName, relLevels, relArgs) := constApp? relation
      | throw "WF schema: general relation is not invImage"
    unless relName == leanName ``invImage && relArgs.size == 4 && alphaEq relArgs[0]! spine.type do
      throw "WF schema: general relation has foreign invImage domain"
    let measure ← decodeWFCase spine L.sigma relArgs[2]!
    let targetRel := mkAppN (Expr.mkConst relName relLevels)
      #[targetSpine.type, relArgs[1]!, measure, relArgs[3]!]
    let targetRelation := Expr.mkProj nWFRelation 0 targetRel
    -- Lean may abstract its opaqueId/projection into a separate proof
    -- declaration. Regenerate the well-founded witness from the SAME
    -- decoded relation record, instead of recognizing arbitrary proof syntax.
    -- The production declaration route can re-abstract this checked witness.
    let mut proof := Expr.mkProj nWFRelation 1 targetRel
    -- This wrapper belongs to the exact root witness, not a user proof
    -- discovered by its type. Preserve Lean's inline opaqueId convention
    -- only after checking its complete source proposition and projection.
    if let some (wrapper, wrapperLevels, wrapperArgs) := constApp? args[3]! then
      if wrapper == leanName ``Lean.opaqueId && wrapperArgs.size == 2 then
        let some domainLevel := levels[0]? | throw "WF schema: missing domain universe"
        let sourceGoal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[spine.type, args[2]!]
        unless alphaEq wrapperArgs[0]! sourceGoal &&
            alphaEq wrapperArgs[1]! (Expr.mkProj nWFRelation 1 relation) do
          throw "WF schema: inline well-founded witness differs from the exact root relation"
        let targetGoal := mkAppN (Expr.mkConst (leanName ``WellFounded) #[domainLevel])
          #[targetSpine.type, targetRelation]
        proof := mkAppN (Expr.mkConst wrapper wrapperLevels) #[targetGoal, proof]
    pure (relArgs[2]!, #[targetSpine.type, codomain, targetRelation, proof])
  let targetMeasure ← decodeWFCase spine L.sigma measure
  return {
    sourceSpine := spine, targetSpine, sourceCodomain := args[1]!,
    targetCodomain := codomain, sourceMeasure := measure, targetMeasure,
    head := Expr.mkConst name levels, sourceArguments := args, targetArguments := targetArgs
    sourceRelation := if isNat then none else some args[2]!
    targetRelation := if isNat then none else some targetArgs[2]! }

/-- Rebuild only the two declared binders of a recursive telescope. Exact
source measure and point identities establish the decreasing relation; the
underlying relation and all its parameters stay unchanged. -/
def ownedWFRecType (schema : WFRootSchema) (sourcePoint targetPoint type : Expr) : TM Expr := do
  let (locals, result) ← openBinders false 2 type
  unless locals.size == 2 do throw "WF schema: incomplete recursive telescope"
  let argument := locals[0]!
  let proof := locals[1]!
  unless alphaEq argument.type schema.sourceSpine.type do
    throw "WF schema: recursive argument has a foreign domain"
  let relation ← match schema.sourceRelation, schema.targetRelation with
    | some source, some target => do
      let (head, args) := getAppFnArgs proof.type
      unless alphaEq head source && args.size == 2 &&
          alphaEq args[0]! argument.expr && alphaEq args[1]! sourcePoint do
        throw "WF schema: decreasing obligation has a foreign root relation or argument identity"
      pure (mkAppN target #[argument.expr, targetPoint])
    | _, _ => do
      let some (name, levels, args) := constApp? proof.type
        | throw "WF schema: decreasing obligation is not invImage"
      unless name == nInvImage && args.size == 6 &&
          alphaEq args[0]! schema.sourceSpine.type && alphaEq args[3]! schema.sourceMeasure &&
          alphaEq args[4]! argument.expr && alphaEq args[5]! sourcePoint do
        throw "WF schema: decreasing obligation has foreign measure or argument identities"
      pure (mkAppN (Expr.mkConst name levels)
        #[schema.targetSpine.type, args[1]!, args[2]!, schema.targetMeasure, argument.expr, targetPoint])
  unless alphaEq result (applyWFCase schema.sourceCodomain argument.expr) do
    throw "WF schema: recursive result differs from the root codomain"
  liftE (closeBinders false #[{ argument with type := schema.targetSpine.type },
    { proof with type := relation }] (applyWFCase schema.targetCodomain argument.expr))

end Ix.Compile.Clique
end
