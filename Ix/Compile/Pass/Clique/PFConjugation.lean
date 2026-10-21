/-
  Ix.Compile.Pass.Clique.PFConjugation: the decoder-owned `partial_fixpoint`
  transport.

  Only the identities the decoders establish move: the recursive binder and
  the output tuple of Lean's root functional, the packed constant at its full
  fixed-argument application, the monotonicity proof's `monotone_mk` tree and
  the per-function proofs' applied theorems (through the argument roles of
  each theorem's declared telescope), and the equation proofs' fixpoint
  equation, member projection and congruences. Inner user binders keep their
  identity, even when their type is the packing. `transportPF` runs it over a
  whole clique: the packed fixpoint, its proofs, the members and the carried
  equation lemmas.

  The walks over shared proof terms are memoised: `transportOwnedMono` by
  `memoTransport` (its key carries the fuel; a visit that allocates fresh
  variables is never cached), `rewritePFPackedUses` by the subterm and the
  fuel, and a subterm without the packed constant is returned as it is (with
  the walk's own fuel check, `mentionHeights`). Neither changes a result, a
  refusal or the fresh-name stream; the equation proof walk is a chain and
  needs neither.
-/
module
public import Ix.Compile.Pass.Clique.PartialFixpoint
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Expr Name ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata substLevels)
open Ix.Compile.Image (forallArity)

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
          if let some base := args[2]? then
            if let some value := project nPProd (if c == nPProdFst then 0 else 1) base then
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
    -- the packing at this depth, and over the canonical order: pure, and
    -- built only at the sites of the recursive binder
    let source (_ : Unit) : Spine := { input with leaves := input.leaves.map (liftLoose · (depth + 1)) }
    let target? (_ : Unit) : Option Spine := (source ()).permute sigma
    let noTarget := "PF conjugation: the recursive packing does not permute"
    if let some (spine, j, base) := decodePathApp input.size e then
      if alphaEqSkipMdata base (Expr.mkBVar depth) then
        let spineType ← spine.typeE "PF conjugation"
        let sourceType ← (source ()).typeE "PF conjugation"
        unless alphaEqSkipMdata (normOrderAlias spineType) (normOrderAlias sourceType) do
          throw "PF conjugation: recursive path has a foreign type"
        let some permuted := spine.permute sigma | throw noTarget
        let some position := sigma[j]? | throw noTarget
        let some path := mkPathApp permuted position base
          | throw "PF conjugation: recursive path reconstruction failed"
        return path
    match e with
    | .proj .. =>
      let (steps, base) := projChain e
      if alphaEqSkipMdata base (Expr.mkBVar depth) then
        let some (j, used) := pathPrefix input.size steps
          | throw "PF conjugation: recursive projection is not a component path"
        unless stepsFit (source ()) j (steps.extract 0 used) do
          throw "PF conjugation: recursive projection has a foreign structure"
        let some target := target? () | throw noTarget
        let some position := sigma[j]? | throw noTarget
        let some canonical := target.projSteps position
          | throw "PF conjugation: recursive projection reconstruction failed"
        return applyProjs (canonical ++ steps.extract used steps.size) base
    | _ => pure ()
    match e with
    | .bvar i _ =>
      if i == depth then
        let some target := target? () | throw noTarget
        let some components := sigma.mapM fun j => do return applyProjs (← target.projSteps j) e
          | throw "PF conjugation: inverse tuple reconstruction failed"
        let some tuple := mkTuple (source ()) components
          | throw "PF conjugation: inverse tuple reconstruction failed"
        return tuple
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
(Semantically, `Lean.Order.fix` commutes with the re-association, an order
isomorphism; see the module docstring of `PartialFixpoint.lean`.) -/
def conjugatePF (n : Nat) (sigma : Array Nat) (functional : Expr) : Except String Expr := do
  unless n ≥ 2 && sigma.size == n && isPerm sigma do throw "PF conjugation: invalid permutation"
  let .lam name domain body bi _ := stripMdata functional
    | throw "PF conjugation: missing recursive binder"
  let some input := decodeSpine .pprod n domain
    | throw "PF conjugation: recursive binder is not a packed product"
  let some (output, components) := decodeTuple n (stripMdata body)
    | throw "PF conjugation: missing encoded result tuple"
  let outputType ← output.typeE "PF conjugation"
  let inputType ← input.typeE "PF conjugation"
  unless alphaEqSkipMdata (normOrderAlias outputType) (normOrderAlias (liftLoose inputType 1)) do
    throw "PF conjugation: input and output packing differ"
  let components ← components.mapM (substitutePFInput input sigma)
  let some target := input.permute sigma | throw "PF conjugation: invalid permutation"
  let some outputTarget := output.permute sigma | throw "PF conjugation: invalid permutation"
  let some permuted := permute sigma components | throw "PF conjugation: invalid permutation"
  let some tuple := mkTuple outputTarget permuted
    | throw "PF conjugation: result tuple reconstruction failed"
  return Expr.mkLam name (← target.typeE "PF conjugation") tuple bi

/-- Precompose a decoded component functional with the inverse packing.
This is the function occurring in the composition fallback. -/
def conjugatePFInput (input : Spine) (sigma : Array Nat) (functional : Expr) : Except String Expr := do
  unless input.size ≥ 2 && sigma.size == input.size && isPerm sigma do
    throw "PF input conjugation: invalid permutation"
  let .lam name domain body bi _ := stripMdata functional
    | throw "PF input conjugation: missing recursive binder"
  let inputType ← input.typeE "PF input conjugation"
  unless alphaEqSkipMdata (normOrderAlias domain) (normOrderAlias inputType) do
    throw "PF input conjugation: wrong binder domain"
  let some actualInput := decodeSpine .pprod input.size domain
    | throw "PF input conjugation: missing functional packing"
  let some target := actualInput.permute sigma | throw "PF input conjugation: invalid permutation"
  let targetType ← target.typeE "PF input conjugation"
  return Expr.mkLam name targetType (← substitutePFInput actualInput sigma body) bi

/-- Transport a decoded monotonicity tree by the composition construction
alone, keeping every source per-component proof verbatim (no user proof
syntax is recognised by its type). -/
def conjugatePFMono (layout : PFLayout) (proof : Expr) : Except String Expr := do
  let some (data, fs, hs) := decodeMonoTree layout proof
    | throw "PF conjugation: monotonicity proof is not a decoded tuple tree"
  let some target := data.permute layout.sigma
    | throw "PF conjugation: monotonicity proof packing does not permute"
  let fs' ← fs.mapM (conjugatePFInput data.tspine layout.sigma)
  let hs' ← (List.range layout.n).toArray.mapM fun k => do
    let some fk := fs[k]? | throw "PF conjugation: monotonicity proof has too few components"
    let some hk := hs[k]? | throw "PF conjugation: monotonicity proof has too few components"
    mkComposeFallback layout.sigma data target k fk hk layout.composeLevels
  let some fsP := permute layout.sigma fs' | throw "PF conjugation: invalid permutation"
  let some hsP := permute layout.sigma hs' | throw "PF conjugation: invalid permutation"
  let some tree := mkMonoTree target fsP hsP
    | throw "PF conjugation: monotonicity tree reconstruction failed"
  return tree

def nMonotone : Name := leanName ``Lean.Order.monotone

/-- A premise about the exact symbolic recursive-domain parameter. Opening
the theorem telescope before this test distinguishes parameters that merely
receive equal types at an application. Quantified user parameters stay user
parameters, even if their instantiated type is the packing. -/
def ownedMonoPremise (domain order : Name) : Expr → Bool
  | .forallE _ t b _ _ =>
    !mentionsFVar domain t && !mentionsFVar order t && ownedMonoPremise domain order b
  | e => match constApp? (stripMdata e) with
    | some (c, _, #[d, o, _, _, _]) => c == nMonotone &&
      alphaEqSkipMdata d (Expr.mkFVar domain) && alphaEqSkipMdata o (Expr.mkFVar order)
    | _ => false

/-- Transport a proof only through the argument roles of its applied
theorem's declared telescope. The domain/order are exact fresh identities
from its `monotone` conclusion, never inferred from a user's matching type.
Unknown dependent roles decline to the composition construction.

The walk is memoised (`memoTransport`, keyed by the subterm and the fuel):
a regenerated path proof shared by several theorem applications is decoded
once. A visit that opens a theorem's telescope allocates fresh variables and
is never cached, so the fresh-name stream is the unmemoised walk's. -/
def transportOwnedMono (L : PFLayout) (const? : Name → Option ConstantInfo) (fuel : Nat)
    (e : Expr) : TM Expr :=
  (visit fuel e).run' {}
where
  visit : Nat → Expr → TransportMemoM Expr
  | 0, _ => throw "PF proof ownership: recursion bound exhausted"
  | fuel + 1, e => memoTransport e (fuel + 1) 0 do
    if let some (data, j) := decodePathProof L e then
      let some target := data.permute L.sigma | throw "PF proof ownership: path packing does not permute"
      let position ← TM.idx L.sigma j "PF proof ownership: path component"
      let some (proof, _) := mkPathProof target position
        | throw "PF proof ownership: path proof reconstruction failed"
      return proof
    match e with
    | .lam n t b bi _ => return Expr.mkLam n t (← visit fuel b) bi
    | .mdata d x _ => return Expr.mkMData d (← visit fuel x)
    | _ => pure ()
    let some (name, levels, args) := constApp? e
      | throw "PF proof ownership: expected an applied monotonicity theorem"
    let some info := const? name | throw s!"PF proof ownership: missing theorem {name}"
    let type := substLevels info.getCnst.levelParams levels info.getCnst.type
    let (parameters, conclusion) ← openBinders false args.size type
    let notMonotone := "PF proof ownership: theorem conclusion is not monotonicity"
    let some (head, _, resultArgs) := constApp? conclusion | throw notMonotone
    unless head == nMonotone do throw notMonotone
    let #[domainArg, orderArg, outputType, outputOrder, _] := resultArgs | throw notMonotone
    let .fvar domain _ := domainArg
      | throw "PF proof ownership: domain is not a theorem parameter"
    let .fvar order _ := orderArg
      | throw "PF proof ownership: order is not a theorem parameter"
    -- This transport precomposes the recursive input and leaves the output
    -- type/order alone. `monotone_id`, for example, has no function argument
    -- to inspect but changes *both* ends when its one type parameter changes.
    -- Such a theorem needs the separately checked path or composition route.
    unless !mentionsFVar domain outputType && !mentionsFVar order outputType &&
        !mentionsFVar domain outputOrder && !mentionsFVar order outputOrder do
      throw "PF proof ownership: conclusion output depends on the recursive-domain parameter"
    let some domainIndex := parameters.findIdx? (·.fvar == domain)
      | throw "PF proof ownership: missing domain parameter"
    let some orderIndex := parameters.findIdx? (·.fvar == order)
      | throw "PF proof ownership: missing order parameter"
    let domainValue ← TM.idx args domainIndex "PF proof ownership: domain argument"
    let orderValue ← TM.idx args orderIndex "PF proof ownership: order argument"
    let some spine := decodeSpine .pprod L.n domainValue
      | throw "PF proof ownership: recursive domain is not the decoded packing"
    let some data := decodeOrderData L orderValue
      | throw "PF proof ownership: recursive order is not the decoded order"
    let spineType ← spine.typeM "PF proof ownership"
    let dataType ← data.spine.typeM "PF proof ownership"
    unless L.isClique spine &&
        alphaEqSkipMdata (normOrderAlias spineType) (normOrderAlias dataType) do
      throw "PF proof ownership: domain/order mismatch"
    let some target := ({ data with tspine := spine }).permute L.sigma
      | throw "PF proof ownership: recursive packing does not permute"
    let targetType ← target.tspine.typeM "PF proof ownership"
    let some targetOrder := target.packedPO
      | throw "PF proof ownership: recursive order reconstruction failed"
    let mut args' := #[]
    for (parameter, i) in parameters.zipIdx do
      let arg ← TM.idx args i "PF proof ownership: theorem argument"
      if i == domainIndex then args' := args'.push targetType
      else if i == orderIndex then args' := args'.push targetOrder
      else if mentionsFVar domain parameter.type || mentionsFVar order parameter.type then
        if ownedMonoPremise domain order parameter.type then
          args' := args'.push (← visit fuel arg)
        else
          let .forallE _ input output _ _ := stripMdata parameter.type
            | throw "PF proof ownership: unsupported dependent argument role"
          unless alphaEqSkipMdata input (Expr.mkFVar domain) &&
              !mentionsFVar domain output && !mentionsFVar order output &&
              looseAllAtLeast output 1 do
            throw "PF proof ownership: unsupported dependent functional role"
          args' := args'.push (← liftE (conjugatePFInput spine L.sigma arg))
      else args' := args'.push arg
    -- (`openBinders` opened one binder per argument: nothing is left over)
    return mkAppN (Expr.mkConst name levels) (args' ++ args.extract parameters.size args.size)

/-- Regenerate recognized source proof syntax; keep each unknown component
proof verbatim inside the composition construction. The functional arguments
always come from binder-identified precomposition, including the fallback
branch. A component that takes the fallback leaves the transport state as it
was before its attempt and records why in `fallbacks`. -/
def conjugatePFMonoChecked (L : PFLayout) (const? : Name → Option ConstantInfo)
    (proof : Expr) : TM Expr := do
  let some (data, fs, hs) := decodeMonoTree L proof
    | throw "PF conjugation: monotonicity proof is not a decoded tuple tree"
  let some target := data.permute L.sigma
    | throw "PF conjugation: monotonicity proof packing does not permute"
  let fs' ← liftE (fs.mapM (conjugatePFInput data.tspine L.sigma))
  let mut hs' := #[]
  for k in [0:L.n] do
    let fk ← TM.idx fs k "PF conjugation: monotonicity functional"
    let hk ← TM.idx hs k "PF conjugation: monotonicity proof"
    let state ← get
    match (transportOwnedMono L const? transportFuel hk).run state with
    | .ok (h, state') => set state'; hs' := hs'.push h
    | .error reason =>
      hs' := hs'.push (← liftE (mkComposeFallback L.sigma data target k fk hk L.composeLevels))
      modify fun state => { state with fallbacks := state.fallbacks.push s!"monotonicity proof {k}: {reason}" }
  let some fsP := permute L.sigma fs' | throw "PF conjugation: invalid permutation"
  let some hsP := permute L.sigma hs' | throw "PF conjugation: invalid permutation"
  let some tree := mkMonoTree target fsP hsP
    | throw "PF conjugation: monotonicity tree reconstruction failed"
  return tree

/-- For every distinct subterm of `e`: whether it mentions the constant `c`,
and its height (`0` for a leaf, one more than its highest child otherwise,
binder domains and `mdata` included). A walk that rebuilds every node of a
subterm without `c` from the same parts returns it unchanged, and succeeds
exactly when its fuel exceeds the height; `rewritePFPackedUses` uses this to
return such a subterm at once. -/
def mentionHeights (c : Name) (e : Expr) : Std.HashMap Expr (Bool × Nat) := ((go e).run {}).2
where
  go : Expr → StateM (Std.HashMap Expr (Bool × Nat)) (Bool × Nat)
    | e@(.const n _ _) => cached e (pure (n == c, 0))
    | e@(.app f a _) => cached e do
      let (mf, hf) ← go f
      let (ma, ha) ← go a
      pure (mf || ma, Nat.max hf ha + 1)
    | e@(.lam _ t b _ _) => cached e do
      let (mt, ht) ← go t
      let (mb, hb) ← go b
      pure (mt || mb, Nat.max ht hb + 1)
    | e@(.forallE _ t b _ _) => cached e do
      let (mt, ht) ← go t
      let (mb, hb) ← go b
      pure (mt || mb, Nat.max ht hb + 1)
    | e@(.letE _ t v b _ _) => cached e do
      let (mt, ht) ← go t
      let (mv, hv) ← go v
      let (mb, hb) ← go b
      pure (mt || mv || mb, Nat.max (Nat.max ht hv) hb + 1)
    | e@(.proj _ _ x _) => cached e do
      let (m, h) ← go x
      pure (m, h + 1)
    | e@(.mdata _ x _) => cached e do
      let (m, h) ← go x
      pure (m, h + 1)
    | e => cached e (pure (false, 0))
  cached (e : Expr) (k : StateM (Std.HashMap Expr (Bool × Nat)) (Bool × Nat)) :
      StateM (Std.HashMap Expr (Bool × Nat)) (Bool × Nat) := do
    if let some r := (← get).get? e then return r
    let r ← k
    modify (·.insert e r)
    return r

/-- The packed root is identified by its declaration and full fixed-argument
application. Replacing it by the inverse output tuple preserves its old type
and meaning everywhere in user syntax. Reducing surrounding projections
then yields canonical member paths without selecting user binders.

The walk is a function of the subterm and the fuel, memoised by both. A
subterm without the packed constant is rebuilt unchanged by the walk (which
then succeeds exactly when the fuel exceeds its height, `mentionHeights`), so
it is returned as it is, or the bound's refusal raised, without descending. -/
def rewritePFPackedUses (L : PFLayout) (e : Expr) : Except String Expr :=
  (go (mentionHeights L.packedName e) transportFuel e).run' {}
where
  /-- The memo of one call: the result at a subterm and fuel. -/
  memo (e : Expr) (fuel : Nat) (act : StateT (Std.HashMap (Expr × Nat) Expr) (Except String) Expr) :
      StateT (Std.HashMap (Expr × Nat) Expr) (Except String) Expr := do
    if let some out := (← get).get? (e, fuel) then return out
    let out ← act
    modify (·.insert (e, fuel) out)
    return out
  go (table : Std.HashMap Expr (Bool × Nat)) :
      Nat → Expr → StateT (Std.HashMap (Expr × Nat) Expr) (Except String) Expr
  | 0, _ => throw "PF ownership: packed-use recursion bound exhausted"
  | fuel + 1, e => do
    -- a subterm without the packed constant: the walk below would rebuild it
    -- unchanged, and run out of fuel exactly when its height reaches the fuel
    if let some (false, height) := table.get? e then
      if height ≤ fuel then return e
      throw "PF ownership: packed-use recursion bound exhausted"
    memo e (fuel + 1) do
      if let some (name, levels, args) := constApp? e then
        if name == L.packedName then
          unless args.size == L.numFixed do throw "PF ownership: partial/over-applied packed declaration"
          let args' ← args.mapM (go table fuel)
          let source := { L.spine with leaves := L.spine.leaves.map fun t => instantiateRev t args.reverse }
          let some target := source.permute L.sigma | throw "PF ownership: the packing does not permute"
          let some fixed := reorder L.fixedPerm args'
            | throw "PF ownership: the fixed-parameter order indexes past the packed arguments"
          let value := mkAppN (Expr.mkConst L.newPackedName levels) fixed
          let some components := L.sigma.mapM fun j => do return applyProjs (← target.projSteps j) value
            | throw "PF ownership: inverse tuple reconstruction failed"
          let some tuple := mkTuple source components
            | throw "PF ownership: inverse tuple reconstruction failed"
          return tuple
      match e with
      | .app f a _ =>
        let f' ← go table fuel f
        let a' ← go table fuel a
        if f' == f && a' == a then return e
        return reduceConjugation.reduceHead (Expr.mkApp f' a')
      | .proj s i x _ =>
        let x' ← go table fuel x
        if x' == x then return e
        return reduceConjugation.reduceHead (Expr.mkProj s i x')
      | .lam n t b bi _ => return Expr.mkLam n (← go table fuel t) (← go table fuel b) bi
      | .forallE n t b bi _ => return Expr.mkForallE n (← go table fuel t) (← go table fuel b) bi
      | .letE n t v b nd _ =>
        return Expr.mkLetE n (← go table fuel t) (← go table fuel v) (← go table fuel b) nd
      | .mdata d x _ => return Expr.mkMData d (← go table fuel x)
      | _ => return e

/-- Transform the exact monotonicity statement of an abstracted tuple proof.
Every modified position is supplied by the `monotone` application schema. -/
def conjugatePFStatement (L : PFLayout) (type : Expr) : Except String Expr := do
  let notStatement := "PF ownership: expected a monotonicity statement"
  let some (head, levels, args) := constApp? (stripMdata type) | throw notStatement
  unless head == nMonotone do throw notStatement
  let #[inputType, inputOrder, outputType, outputOrder, functional] := args | throw notStatement
  let some input := decodeSpine .pprod L.n inputType
    | throw "PF ownership: statement has no input packing"
  let some output := decodeSpine .pprod L.n outputType
    | throw "PF ownership: statement has no output packing"
  let some data := decodeOrderData L inputOrder
    | throw "PF ownership: statement has no packed input order"
  let data := { data with tspine := output }
  let inputSpineType ← input.typeE "PF ownership"
  let outputSpineType ← output.typeE "PF ownership"
  unless L.isClique input &&
      alphaEqSkipMdata (normOrderAlias inputSpineType) (normOrderAlias outputSpineType) &&
      (data.poTree 0).any (alphaEqSkipMdata outputOrder ·) do
    throw "PF ownership: statement input/output orders differ"
  let functional' ← conjugatePF L.n L.sigma functional
  let rebuild := "PF ownership: monotonicity statement reconstruction failed"
  let some target := data.permute L.sigma | throw rebuild
  let some inputTarget := input.permute L.sigma | throw rebuild
  let some packedOrder := target.packedPO | throw rebuild
  let some outputOrder' := target.poTree 0 | throw rebuild
  return mkAppN (Expr.mkConst head levels)
    #[← inputTarget.typeE "PF ownership", packedOrder, ← target.tspine.typeE "PF ownership",
      outputOrder', functional']

structure PFEquationStep where
  type : Expr
  left : Expr
  right : Expr
  proof : Expr

/-- Rebuild the equation proof from the owned fixpoint equation, its member
projection, and ordinary congruence applications. User expressions in the
component body are never traversed or recognized.

The walk is a chain (each accepted node has exactly one recursive child, and
every accepted node is rebuilt over the target fixpoint), so it has neither a
memo nor an unchanged-subterm shortcut. -/
def conjugatePFEquationProof (L : PFLayout) (component : Nat) (sourceFix targetFix : Expr) :
    Nat → Expr → Except String PFEquationStep
  | 0, _ => throw "PF equation ownership: proof recursion bound exhausted"
  | fuel + 1, e => do
    let some (head, levels, args) := constApp? (stripMdata e)
      | throw "PF equation ownership: unsupported proof constructor"
    if head == leanName ``id then
      if let #[_, proof] := args then
        return ← conjugatePFEquationProof L component sourceFix targetFix fuel proof
    if head == leanName ``Eq.trans then
      if let #[_, _, _, _, step, last] := args then
        let some (lastHead, _, lastArgs) := constApp? last
          | throw "PF equation ownership: non-reflexive final equation step"
        unless lastHead == leanName ``Eq.refl && lastArgs.size == 2 do
          throw "PF equation ownership: non-reflexive final equation step"
        return ← conjugatePFEquationProof L component sourceFix targetFix fuel step
    if (head == leanName ``Lean.Order.fix_eq || head == leanName ``Lean.Order.lfp_monotone_fix) &&
        args.size == 4 then
      let some (sourceHead, _, sourceArgs) := constApp? sourceFix
        | throw "PF equation ownership: missing source fixpoint"
      let some (_, _, targetArgs) := constApp? targetFix
        | throw "PF equation ownership: missing target fixpoint"
      let expected := if sourceHead == nOrderFix then leanName ``Lean.Order.fix_eq
        else leanName ``Lean.Order.lfp_monotone_fix
      let foreign := "PF equation ownership: equation belongs to another fixpoint"
      unless head == expected && args.size == sourceArgs.size && targetArgs.size == 4 &&
          (args.zip sourceArgs).all (fun (a, b) => alphaEqSkipMdata a b) do
        throw foreign
      let #[targetType, _, targetFunctional, _] := targetArgs | throw foreign
      return {
        type := targetType, left := targetFix
        right := Expr.mkApp targetFunctional targetFix,
        proof := mkAppN (Expr.mkConst head levels) targetArgs }
    if head == leanName ``congrArg then
      if let #[_, resultType, _, _, function, proof] := args then
        let .lam binder domain body bi _ := stripMdata function
          | throw "PF equation ownership: congruence is not a member projection"
        let some source := decodeSpine .pprod L.n domain
          | throw "PF equation ownership: congruence has no packed binder"
        let (steps, base) := projChain body
        let some (index, used) := pathPrefix L.n steps
          | throw "PF equation ownership: congruence is not a complete member path"
        unless index == component && used == steps.size && alphaEqSkipMdata base (Expr.mkBVar 0) &&
            stepsFit source index steps do
          throw "PF equation ownership: congruence selects another binder/component"
        let previous ← conjugatePFEquationProof L component sourceFix targetFix fuel proof
        let rebuild := "PF equation ownership: member projection reconstruction failed"
        let some target := source.permute L.sigma | throw rebuild
        let targetType ← target.typeE "PF equation ownership"
        let some position := L.sigma[component]? | throw rebuild
        let some steps' := target.projSteps position | throw rebuild
        let projection := Expr.mkLam binder targetType (applyProjs steps' (Expr.mkBVar 0)) bi
        return {
          type := resultType, left := Expr.mkApp projection previous.left
          right := Expr.mkApp projection previous.right,
          proof := mkAppN (Expr.mkConst head levels)
            #[targetType, resultType, previous.left, previous.right, projection, previous.proof] }
    if head == leanName ``congrFun then
      if let #[domainType, resultType, _, _, proof, argument] := args then
        let previous ← conjugatePFEquationProof L component sourceFix targetFix fuel proof
        return {
          type := Expr.mkApp resultType argument, left := Expr.mkApp previous.left argument
          right := Expr.mkApp previous.right argument,
          proof := mkAppN (Expr.mkConst head levels)
            #[domainType, resultType, previous.left, previous.right, previous.proof, argument] }
    throw s!"PF equation ownership: unsupported proof constructor {head}"

/-- The carried equation lemma `lemma` of a member, renamed `newName`: its
statement is kept, its proof rebuilt over the transported fixpoint
`targetPacked` (`conjugatePFEquationProof`). -/
def conjugatePFEquation (L : PFLayout) (members : Array Decl) (sourcePacked targetPacked : Decl)
    (lemma : Decl) (newName : Name) : TM Decl := do
  let arity := forallArity lemma.type
  let (parameters, statement) ← openBinders false arity lemma.type
  let notEquality := "PF equation ownership: statement is not an equality"
  let some (eq, _, eqArgs) := constApp? statement | throw notEquality
  unless eq == leanName ``Eq do throw notEquality
  let #[_, lhs, _] := eqArgs | throw notEquality
  let some (memberName, _, memberArgs) := constApp? lhs
    | throw "PF equation ownership: equality does not start at a member application"
  let some component := members.findIdx? (·.name == memberName)
    | throw "PF equation ownership: equality concerns another declaration"
  let member ← TM.idx members component "PF equation ownership: member"
  let appliedMember := betaApp member.value memberArgs
  let (projection, _) := getAppFnArgs appliedMember
  let (_, base) := projChain projection
  let some (packedName, _, fixedArgs) := constApp? base
    | throw "PF equation ownership: member has no packed root"
  unless packedName == sourcePacked.name && fixedArgs.size == L.numFixed do
    throw "PF equation ownership: member uses another packed root"
  let sourceFix := betaApp sourcePacked.value fixedArgs
  let some targetFixed := reorder L.fixedPerm fixedArgs
    | throw "PF equation ownership: the fixed-parameter order indexes past the packed arguments"
  let targetFix := betaApp targetPacked.value targetFixed
  let (binders, proofBody) := peelLams arity lemma.value #[]
  unless binders.size == arity do throw "PF equation ownership: proof telescope differs from its statement"
  let proofBody := instLocals proofBody (parameters.map (·.expr))
  let proof ← liftE (conjugatePFEquationProof L component sourceFix targetFix transportFuel proofBody)
  let value ← liftE (closeBinders true parameters proof.proof)
  return { lemma with name := newName, value }

/-- Ownership-preserving transport of a `partial_fixpoint` clique: the packed
fixpoint `packed` (renamed `newPackedName`), its abstracted `proofs`, the
`members` and the carried equation `lemmas` (each with its new name), under
the clique permutation `sigma`. The packed declaration, its fixed binders,
fixpoint arguments and abstracted proof positions are decoded once; user
syntax is transported only by substitution of those exact identities.
Unsupported roles leave the entire clique to the caller's faithful baseline.
The prologue (the proofs' fixed prefixes) and the epilogue (the proofs'
numbering and the renames) are the ones `transportWF` shares
(`fixedProofPerms`, `numberProofs`). -/
def transportPF (members : Array Decl) (packed : Decl) (proofs : Array Decl) (sigma : Array Nat)
    (newPackedName : Name) (const? : Name → Option ConstantInfo)
    (lemmas : Array (Decl × Name) := #[]) : TM TransportOutput := do
  let initial ← liftE (pfLayout members packed sigma newPackedName)
  let composeLevels := match const? nMonoCompose with
    | some info => info.getCnst.levelParams
    | none => #[]
  let prologue ← fixedProofPerms proofs initial.numFixed initial.fixedPerm packed.value
  let proofNames := prologue.proofNames
  let proofPerm := prologue.proofPerm
  let L := { initial with composeLevels, proofPerm }
  let unchanged (e : Expr) : TM Expr := pure e
  let packedType (e : Expr) : TM Expr := do
    let some spine := decodeSpine .pprod L.n (stripMdata e)
      | throw "PF ownership: packed result type is not a product"
    unless L.isClique spine do throw "PF ownership: packed result type differs from the layout"
    let some target := spine.permute sigma | throw "PF ownership: packed result type does not permute"
    target.typeM "PF ownership"
  let packedValue (e : Expr) : TM Expr := do
    let some (head, levels, args) := constApp? (stripMdata e)
      | throw "PF ownership: packed value is not a fixpoint application"
    let unsupported := "PF ownership: unsupported fixpoint root"
    unless head == nOrderFix || head == leanName ``Lean.Order.lfp_monotone do throw unsupported
    let #[domain, instances, functional, proofArg] := args | throw unsupported
    let some spine := decodeSpine .pprod L.n domain
      | throw "PF ownership: fixpoint has no packed domain"
    let some (instanceName, instanceSpine, leafInstances) := decodeInstTree L.n instances
      | throw "PF ownership: fixpoint has no decoded instance tree"
    let spineType ← spine.typeM "PF ownership"
    let instanceType ← instanceSpine.typeM "PF ownership"
    unless L.isClique spine && alphaEqSkipMdata (normOrderAlias spineType) (normOrderAlias instanceType) do
      throw "PF ownership: fixpoint type/instance mismatch"
    let some (proofName, proofLevels, proofArgs) := constApp? proofArg
      | throw "PF ownership: fixpoint proof is not an owned abstracted declaration"
    unless proofNames.contains proofName do
      throw "PF ownership: fixpoint proof is not among the owned declarations"
    let permutation := (proofPerm.get? proofName).getD #[]
    unless proofArgs.size == permutation.size do throw "PF ownership: proof fixed-argument arity mismatch"
    let some reordered := reorder permutation proofArgs
      | throw "PF ownership: proof fixed-argument arity mismatch"
    let proof := mkAppN (Expr.mkConst proofName proofLevels) reordered
    let functional' ← liftE (conjugatePF L.n sigma functional)
    let rebuild := "PF ownership: fixpoint root reconstruction failed"
    let some target := spine.permute sigma | throw rebuild
    let some instanceTarget := instanceSpine.permute sigma | throw rebuild
    let some leafInstances' := permute sigma leafInstances | throw rebuild
    let some instances' := mkInstTree instanceName instanceTarget leafInstances' | throw rebuild
    return mkAppN (Expr.mkConst head levels)
      #[← target.typeM "PF ownership", instances', functional', proof]
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
  return numberProofs out packed.name newPackedName proofs lemmas value

end Ix.Compile.Pass.Clique

end
