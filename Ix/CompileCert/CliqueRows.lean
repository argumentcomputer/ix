import Ix.CompileCert.Changed
import Ix.Cli.CliqueValues

/-! # Value rows for transported clique members (package V; untrusted)

A member `c` of a transported definition clique (`docs/compiler-passes.md` §11.2
case 7) holds the transported value `Φ_σ(v)` under Lean's name; Lean's value
`v` unfolds Lean's encoding (`f₀._mutual`, …), whose constants are in the
artifact in Lean's form (case 7c). W+ matched such a member by Lean's own
`c.eq_def` (`EqDefEquation`), trusting that Lean's lemma is `c`'s unfolding
equation. This module builds instead a **value row**: a theorem
`@Eq T c v_lean_export`, the very statement of the member's `rfl` row
(`RflEquation`, `HasRflRow`), with a proof the certifier generates; the
certified fold checks it like any support row, and `model_equations` reads it
(`c = v` in every strong model of the folded environment). Nothing here is
trusted: a wrong proof is refused by the fold and the member keeps the
`eq_def` route (or its Unsupported class).

**How the proof is made.** The member and the canonical constants it reaches
(`g._ix._mutual`, its `_proof_k`, …) are decompiled from the artifact's own
bytes with the compiled terms (`IxCliqueValues.compiledClosure`, the
`validate-lean` phase 9 reader) and added to Lean's environment, the members
under scratch names `m._ix_value` (`IxCliqueValues.addCompiled`, Lean's kernel
checks them). In that environment `proveWF` builds a proof of
`m._ix_value = v` (Lean's value, never Lean's constant `m`, which denotes the
transported value in the artifact) by one term construction per encoding
(`docs/compiler-certification.md` §1.3). **Well-founded** (`proveWF`):

* `funext` over the member's parameters, then **well-founded induction on
  Lean's relation** (read off Lean's functional's recursion binder) with the
  motive `M x`, the `PSum.casesOn` tree of the members' equations
  `B (inj'_{σ j} w) = A (inj_j w)` (`A`, `B` Lean's and the canonical fixpoint
  at their fixed arguments);
* each step: `B xI = F' xI gB` and `A xL = F xL gA` (`WellFounded.fix_eq` or
  `WellFounded.Nat.fix_eq`), `F' xI gB = F xL gBφ` by `Eq.refl` (one unfolding
  of either side is the same body: the conjugation), and
  `F xL gBφ = F xL gA` by `congrArg` and `funext` from the induction
  hypothesis (`gBφ y := casesOn y (λ w. B (inj'_{σ k} w))`).

σ is read off the members' own values. **Structural** (`proveStructural`):
induction on the major premise with the block's recursor, each case by
unfolding both sides and congruence with the induction hypotheses (see its
section). `partial_fixpoint` cliques get no proof. The proof is exported with
`exportExprWith`: Lean's constants through the map (`ExportContext.name`), the
scratch members through their own map entries (the Ix constant under Lean's
name holds the transported value), the canonical constants through their
records (`Kernel.Reader.resolve`, the reader's name). -/

namespace IxValueRows

open Lean Meta

/-! ## The well-founded generator -/

def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

/-- Instantiate the leading lambdas of `v` with `args` (metadata stripped). -/
def betaStrip (v : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := stripMData v
  for a in args do
    match e with
    | .lam _ _ b _ => e := stripMData (b.instantiate1 a)
    | _ => e := mkApp e a
  return e

/-- The body under the leading lambdas (loose bound variables kept), metadata stripped. -/
def lambdaBody : Expr → Expr
  | .lam _ _ b _ => lambdaBody b
  | .mdata _ e => lambdaBody e
  | e => e

/-- δ of a constant application (value instantiated, β, metadata stripped). -/
def unfoldApp (e : Expr) : MetaM Expr := do
  let .const c us := e.getAppFn | throwError "not a constant application: {e}"
  let some ci := (← getEnv).find? c | throwError "unknown constant {c}"
  let some v := ci.value? (allowOpaque := true) | throwError "{c} has no value"
  return betaStrip (v.instantiateLevelParams ci.levelParams us) e.getAppArgs

/-- The summand index of an injection into a right-nested `PSum` of `n` summands. -/
def readInj (n : Nat) (x : Expr) : Option Nat :=
  go n 0 (stripMData x)
where
  go : Nat → Nat → Expr → Option Nat
    | 0, _, _ => none
    | fuel + 1, k, x =>
      if k + 1 == n then some k
      else if x.isAppOfArity ``PSum.inl 3 then some k
      else if x.isAppOfArity ``PSum.inr 3 then go fuel (k + 1) (stripMData x.appArg!)
      else none

/-- The `n` summands of a right-nested `PSum`. -/
def summands (n : Nat) (ty : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  let mut t := ty
  for _ in [0:n - 1] do
    let t' ← whnfR t
    unless t'.isAppOfArity ``PSum 2 do throwError "not a PSum packing of {n}: {ty}"
    out := out.push t'.appFn!.appArg!
    t := t'.appArg!
  return out.push t

/-- `inj_k v` into the right-nested `α` of `n` summands. -/
def mkInj (α : Expr) (n k : Nat) (v : Expr) : MetaM Expr := do
  let mut tys : Array Expr := #[]
  let mut t := α
  for _ in [0:k] do
    let t' ← whnfR t
    unless t'.isAppOfArity ``PSum 2 do throwError "not a PSum packing: {α}"
    tys := tys.push t'
    t := t'.appArg!
  let t' ← whnfR t
  let mut out ← if k + 1 < n then do
      unless t'.isAppOfArity ``PSum 2 do throwError "not a PSum packing: {α}"
      mkAppOptM ``PSum.inl #[t'.appFn!.appArg!, t'.appArg!, v]
    else pure v
  for q in (List.range k).reverse do
    let tq := tys[q]!
    out ← mkAppOptM ``PSum.inr #[tq.appFn!.appArg!, tq.appArg!, out]
  return out

/-- `PSum.casesOn y` over the right-nested `α`, motive `C` (a function on `α`),
one branch function per summand. -/
partial def mkCases (α C : Expr) (fs : List Expr) (y : Expr) : MetaM Expr := do
  match fs with
  | [] => throwError "empty packing"
  | [f] => pure (mkApp f y).headBeta
  | f :: rest =>
    let α ← whnfR α
    unless α.isAppOfArity ``PSum 2 do throwError "not a PSum: {α}"
    let a := α.appFn!.appArg!
    let b := α.appArg!
    let mot ← withLocalDeclD `t α fun t => do mkLambdaFVars #[t] (mkApp C t).headBeta
    let Cb ← withLocalDeclD `z b fun z => do
      mkLambdaFVars #[z] (mkApp C (← mkAppOptM ``PSum.inr #[a, b, z])).headBeta
    let inrFn ← withLocalDeclD `r b fun r => do mkLambdaFVars #[r] (← mkCases b Cb rest r)
    mkAppOptM ``PSum.casesOn #[a, b, mot, y, f, inrFn]

/-- A well-founded fixpoint `fix … F` without its argument: Lean's
`WellFounded.fix α C r hwf F` or `WellFounded.Nat.fix α C h F`. -/
structure Fix where
  nat : Bool
  α : Expr
  C : Expr
  /-- `WellFounded.fix`: the well-foundedness proof; `WellFounded.Nat.fix`: the measure. -/
  h : Expr
  F : Expr

def readFix (e : Expr) : MetaM Fix := do
  let e := stripMData e
  if e.isAppOfArity ``WellFounded.fix 5 then
    let a := e.getAppArgs
    return { nat := false, α := a[0]!, C := a[1]!, h := a[3]!, F := a[4]! }
  else if e.isAppOfArity ``WellFounded.Nat.fix 4 then
    let a := e.getAppArgs
    return { nat := true, α := a[0]!, C := a[1]!, h := a[2]!, F := a[3]! }
  else throwError "not a well-founded fixpoint: {e.getAppFn}"

/-- `fix … x = F x (λ y _. fix … y)`. -/
def Fix.eq (fx : Fix) (x : Expr) : MetaM Expr :=
  if fx.nat then mkAppM ``WellFounded.Nat.fix_eq #[fx.h, fx.F, x]
  else mkAppM ``WellFounded.fix_eq #[fx.h, fx.F, x]

/-- The relation `λ y x. R y x` guarding the functional's recursion binder. -/
def Fix.rel (fx : Fix) : MetaM Expr := do
  forallBoundedTelescope (← inferType fx.F) (some 1) fun xs body => do
    let some x := xs[0]? | throwError "functional without its argument"
    let .forallE _ A _ _ := body | throwError "functional type: {body}"
    forallBoundedTelescope A (some 2) fun ys _ => do
      let (some y, some hy) := (ys[0]?, ys[1]?) | throwError "recursion binder: {A}"
      mkLambdaFVars #[y, x] (← inferType hy)

/-- A proof that `R` is well-founded. -/
def Fix.wf (fx : Fix) (R : Expr) : MetaM Expr := do
  let ty ← mkAppM ``WellFounded #[R]
  if fx.nat then
    let wfNat ← mkAppOptM ``WellFoundedRelation.wf #[none, some (mkConst ``Nat.lt_wfRel)]
    mkExpectedTypeHint (← mkAppM ``InvImage.wf #[fx.h, wfNat]) ty
  else mkExpectedTypeHint fx.h ty

/-- `λ y (_ : R y x). g y`. -/
def guarded (α R x : Expr) (g : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `y α fun y => do
    withLocalDeclD `hy (mkApp2 R y x).headBeta fun hy => do
      mkLambdaFVars #[y, hy] (← g y)

/-- `funext` over the free variables `ps` (innermost last) of a proof of `l = r`. -/
def funextOver (ps : Array Expr) (proof : Expr) : MetaM Expr := do
  let mut p := proof
  for x in ps.reverse do
    p ← mkAppM ``funext #[← mkLambdaFVars #[x] p]
  return p

/-- **The value equation of a well-founded clique member** `i`: per member,
the Ix constant (its value the transported one) and Lean's value; a proof of
`ix_i = leanValue_i` (`ix_i` at the level parameters of `leanValue_i`). -/
def proveWF (members : Array (Expr × Expr)) (i : Nat) : MetaM Expr := do
  let n := members.size
  let some (ixC, leanV) := members[i]? | throwError "no member {i}"
  -- σ: Lean summand ↦ Ix summand, read off every member's two values
  let mut sigma : Array Nat := Array.replicate n n
  for (c, v) in members do
    let some j := readInj n ((lambdaBody v).getAppArgs.back?.getD default)
      | throwError "Lean's value of a member is not an injection into the packing"
    let iv ← unfoldApp c
    let some k := readInj n ((lambdaBody iv).getAppArgs.back?.getD default)
      | throwError "the compiled value of a member is not an injection into the packing"
    unless j < n && k < n && sigma[j]! == n do throwError "the members' injections are not a permutation"
    sigma := sigma.set! j k
  let ixV ← unfoldApp ixC
  lambdaTelescope leanV fun ps bodyL => do
    let bodyL := stripMData bodyL
    let bodyI := betaStrip ixV ps
    let argsL := bodyL.getAppArgs
    let argsI := bodyI.getAppArgs
    let some xL := argsL.back? | throwError "Lean's value is not an application"
    unless argsI.size > 0 do throwError "the compiled value is not an application"
    let AL := mkAppN bodyL.getAppFn argsL.pop
    let BI := mkAppN bodyI.getAppFn argsI.pop
    let fxL ← readFix (← unfoldApp AL)
    let fxI ← readFix (← unfoldApp BI)
    let DL ← summands n fxL.α
    let RL ← fxL.rel
    let RI ← fxI.rel
    let hwf ← fxL.wf RL
    let injL (j : Nat) (w : Expr) := mkInj fxL.α n j w
    let injI (k : Nat) (w : Expr) := mkInj fxI.α n k w
    -- M x: the equation of x's summand
    let branchesM ← (List.range n).mapM fun j => withLocalDeclD `w DL[j]! fun w => do
      mkLambdaFVars #[w] (← mkEq (mkApp BI (← injI sigma[j]! w)) (mkApp AL (← injL j w)))
    let propMotive ← withLocalDeclD `x fxL.α fun x => mkLambdaFVars #[x] (mkSort Level.zero)
    let M ← withLocalDeclD `x fxL.α fun x => do mkLambdaFVars #[x] (← mkCases fxL.α propMotive branchesM x)
    -- Bφ y: the canonical fixpoint at the canonical summand of y's
    let branchesB ← (List.range n).mapM fun k => withLocalDeclD `w DL[k]! fun w => do
      mkLambdaFVars #[w] (mkApp BI (← injI sigma[k]! w))
    let Bφ (y : Expr) : MetaM Expr := mkCases fxL.α fxL.C branchesB y
    let ihTy (x : Expr) : MetaM Expr := withLocalDeclD `y fxL.α fun y => do
      withLocalDeclD `hy (mkApp2 RL y x).headBeta fun hy => do
        mkForallFVars #[y, hy] (mkApp M y).headBeta
    let branch (j : Nat) : MetaM Expr := withLocalDeclD `w DL[j]! fun w => do
      let xLj ← injL j w
      let xIj ← injI sigma[j]! w
      withLocalDeclD `ih (← ihTy xLj) fun ih => do
        let gA ← guarded fxL.α RL xLj fun y => pure (mkApp AL y)
        let gB ← guarded fxI.α RI xIj fun y => pure (mkApp BI y)
        let gBφ ← guarded fxL.α RL xLj Bφ
        let eA ← mkExpectedTypeHint (← fxL.eq xLj) (← mkEq (mkApp AL xLj) (mkApp2 fxL.F xLj gA))
        let eB ← mkExpectedTypeHint (← fxI.eq xIj) (← mkEq (mkApp BI xIj) (mkApp2 fxI.F xIj gB))
        let H ← mkExpectedTypeHint (← mkEqRefl (mkApp2 fxI.F xIj gB))
          (← mkEq (mkApp2 fxI.F xIj gB) (mkApp2 fxL.F xLj gBφ))
        -- K : gBφ = gA, from the induction hypothesis
        let kMotive ← withLocalDeclD `y fxL.α fun y => do
          mkLambdaFVars #[y] (← mkArrow (mkApp M y).headBeta (← mkEq (← Bφ y) (mkApp AL y)))
        let kBranches ← (List.range n).mapM fun k => withLocalDeclD `w DL[k]! fun w => do
          let xk ← injL k w
          withLocalDeclD `m (mkApp M xk).headBeta fun m => do
            mkLambdaFVars #[w, m] (← mkExpectedTypeHint m (← mkEq (← Bφ xk) (mkApp AL xk)))
        let K ← withLocalDeclD `y fxL.α fun y => do
          withLocalDeclD `hy (mkApp2 RL y xLj).headBeta fun hy => do
            let k ← mkCases fxL.α kMotive kBranches y
            let inner ← mkAppM ``funext #[← mkLambdaFVars #[hy] (mkApp k (mkApp2 ih y hy))]
            mkLambdaFVars #[y] inner
        let K ← mkExpectedTypeHint (← mkAppM ``funext #[K]) (← mkEq gBφ gA)
        let congr ← mkCongrArg (mkApp fxL.F xLj) K
        let chain ← mkEqTrans eB (← mkEqTrans H (← mkEqTrans congr (← mkEqSymm eA)))
        mkLambdaFVars #[w, ih] chain
    let branches ← (List.range n).mapM branch
    let stepMotive ← withLocalDeclD `x fxL.α fun x => do
      mkLambdaFVars #[x] (← mkArrow (← ihTy x) (mkApp M x).headBeta)
    let step ← withLocalDeclD `x fxL.α fun x => do
      withLocalDeclD `ih (← ihTy x) fun ih => do
        mkLambdaFVars #[x, ih] (mkApp (← mkCases fxL.α stepMotive branches x) ih)
    let ind ← mkAppOptM ``WellFounded.induction #[fxL.α, RL, hwf, M, xL, step]
    let ind ← mkExpectedTypeHint ind (← mkEq bodyI bodyL)
    let pf ← funextOver ps ind
    mkExpectedTypeHint pf (← mkEq ixC leanV)

/-! ## The structural generator

The construction for structural cliques: induction on the major
premise with the block's recursor (all its motives: mutual and nested types),
each motive the conjunction of the equations `ix_j args = lean_j args` of the
members recursing on that type (fixed parameters shared, the others
quantified), each minor premise proved by unfolding both sides to the user's
body (the members, the encoding constants: `brecOn`, `brecOn.go`, `_f`, the
matchers, `PProd`'s projections) and congruence, with the induction
hypotheses as the leaves: a recursive result on either side is, by
conversion, the member applied to the field (smart unfolding off, so that the
checker's conversion is the one `isDefEq` follows). A match on another argument than the major premise (a
second match, a `match h : x` threading the dictionary) is split by `cases` on
that variable, the induction hypotheses that mention it following. -/

/-- Is `c` a constant to unfold while exposing a member's body: a member (the
predicate), an encoding constant, a `brecOn`/`brecOn.go`/`brecOn_k`, a
matcher, `PProd`'s projections, `PProdN` helpers. -/
def encodingConst (isMember : Name → Bool) (env : Environment) (c : Name) : Bool :=
  isMember c ||
  (match c with
    | .str _ s => s == "brecOn" || s.startsWith "brecOn_" || s == "go" || s == "_f" ||
        s.startsWith "match_" || s == "binductionOn" || s.startsWith "_sparseCasesOn"
    | _ => false) ||
  (Lean.Meta.Match.Extension.getMatcherInfo? env c).isSome ||
  [``PProd.fst, ``PProd.snd, ``And.left, ``And.right].contains c ||
  (`Lean.PProdN).isPrefixOf c ||
  (c.components.any fun x => match x with
    | .str _ s => s.startsWith "_ix"
    | _ => false)

/-- Head-unfold `e`: β, ι, projections (`whnfCore`) and δ of the encoding constants. -/
partial def unfoldHead (isMember : Name → Bool) (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel == 0 then return e
  let e ← whnfCore e
  match e.getAppFn with
  | .const c _ =>
    if encodingConst isMember (← getEnv) c then
      match (← getEnv).find? c with
      | some ci =>
        match ci.value? (allowOpaque := false) with
        | some _ => unfoldHead isMember (← unfoldApp e) (fuel - 1)
        | none => return e
      | none => return e
    else return e
  | _ => return e

/-- Facts: proofs of `∀ xs, a = b`, from hypotheses whose types are
conjunctions (under binders) of such. -/
partial def splitFacts (pf : Expr) : MetaM (Array Expr) := do
  let ty ← inferType pf
  forallTelescopeReducing ty fun xs body => do
    let body ← whnfR body
    if body.isAppOfArity ``And 2 then
      let l ← mkLambdaFVars xs (← mkAppM ``And.left #[mkAppN pf xs])
      let r ← mkLambdaFVars xs (← mkAppM ``And.right #[mkAppN pf xs])
      return (← splitFacts l) ++ (← splitFacts r)
    else if body.isAppOfArity ``Eq 3 then return #[pf]
    else return #[]

/-- The free-variable major premise of a stuck `casesOn` or recursor application. -/
def stuckMajor? (e : Expr) : MetaM (Option Expr) := do
  let .const c _ := e.getAppFn | return none
  let env ← getEnv
  let major? : Option Nat := match env.find? c with
    | some (.recInfo rv) => some rv.getMajorIdx
    | _ =>
      if isCasesOnRecursor env c then
        match env.find? c.getPrefix with
        | some (.inductInfo iv) => some (iv.numParams + 1 + iv.numIndices)
        | _ => none
      else none
  let some k := major? | return none
  let some a := e.getAppArgs[k]? | return none
  return if a.isFVar then some a else none

/-- Is `ty` an equation under binders (a fact)? -/
def isEqTelescope (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => return (← whnfR b).isAppOfArity ``Eq 3

/-- A proof of `lhs = rhs` by definitional unfolding, congruence and the facts. -/
partial def proveEq (isMember : Name → Bool) (facts : Array Expr) (lhs rhs : Expr) (depth : Nat := 0) :
    MetaM Expr := do
  if depth > 200 then throwError "congruence: too deep"
  -- a fact
  for f in facts do
    let s ← saveState
    let (ms, _, eq) ← forallMetaTelescopeReducing (← inferType f)
    if eq.isAppOfArity ``Eq 3 then
      if (← isDefEq lhs eq.appFn!.appArg!) && (← isDefEq rhs eq.appArg!) then
        return ← instantiateMVars (mkAppN f ms)
    s.restore
  let lhs' ← unfoldHead isMember lhs
  let rhs' ← unfoldHead isMember rhs
  -- syntactic agreement after unfolding (no further unfolding)
  if lhs' == rhs' then return ← mkEqRefl lhs'
  -- a match on a variable other than the major premise: split it (the facts that mention the
  -- variable are reverted and reintroduced by `cases`)
  if let some y ← stuckMajor? lhs' then
    if (← stuckMajor? rhs') == some y then
      let s ← saveState
      try
        let g ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs' rhs')
        let hyps ← facts.mapIdxM fun i f => do
          pure ({ userName := Name.mkSimple s!"_fact{i}", type := ← inferType f, value := f } : Hypothesis)
        let (_, g1) ← g.mvarId!.assertHypotheses hyps
        let subgoals ← g1.cases y.fvarId!
        for sg in subgoals do
          sg.mvarId.withContext do
            let tgt ← instantiateMVars (← sg.mvarId.getType)
            let some (_, a, b) := tgt.eq? | throwError "case split: not an equation"
            let mut fs : Array Expr := #[]
            for d in (← getLCtx) do
              unless d.isImplementationDetail do
                if ← isEqTelescope (← instantiateMVars d.type) then fs := fs.push d.toExpr
            let p ← proveEq isMember fs a b (depth + 1)
            sg.mvarId.assign p
        return ← instantiateMVars g
      catch _ => s.restore
  match lhs', rhs' with
  | .lam n t b bi, .lam _ t' b' _ =>
    unless ← isDefEq t t' do throwError "congruence: binder types differ"
    withLocalDecl n bi t fun x => do
      let p ← proveEq isMember facts (b.instantiate1 x) (b'.instantiate1 x) (depth + 1)
      mkAppM ``funext #[← mkLambdaFVars #[x] p]
  | _, _ =>
    let f := lhs'.getAppFn
    let g := rhs'.getAppFn
    let as := lhs'.getAppArgs
    let bs := rhs'.getAppArgs
    unless as.size == bs.size && (f.isConst || f.isFVar) && f == g do
      if ← withTransparency .reducible (isDefEq lhs' rhs') then return ← mkEqRefl lhs'
      throwError "congruence: heads differ: {f} vs {g}"
    let mut pf ← mkEqRefl f
    let mut cur := f
    let mut cur' := f
    for i in [0:as.size] do
      let a := as[i]!
      let b := bs[i]!
      if (← isDefEq a b) then
        pf ← mkCongrFun pf a
      else
        let h ← proveEq isMember facts a b (depth + 1)
        pf ← mkCongr pf h
      cur := mkApp cur a
      cur' := mkApp cur' b
    return pf

/-- The type of member `j`'s major premise, its fixed parameters instantiated with `fv`. -/
partial def majorType (fv : Array Expr) (perm : Lean.Elab.FixedParamPerm) (recPos : Nat) (ty : Expr) (p : Nat) :
    MetaM Expr := do
  match ← whnf ty with
  | .forallE nm d b bi =>
    if let some (some k) := perm[p]? then majorType fv perm recPos (b.instantiate1 fv[k]!) (p + 1)
    else if p == recPos then return d
    else withLocalDecl nm bi d fun z => do
      let r ← majorType fv perm recPos (b.instantiate1 z) (p + 1)
      if r.containsFVar z.fvarId! then throwError "the major premise's type depends on a varying parameter"
      return r
  | _ => throwError "no major premise"

/-- `∀ zs, ix args = lean args` for member `j` at the major `t`: fixed parameters
`fv`, the major `t`, the others quantified. -/
partial def eqAtGo (ixj vj : Expr) (fv : Array Expr) (perm : Lean.Elab.FixedParamPerm) (recPos : Nat) (t : Expr)
    (ty : Expr) (p : Nat) (args quant : Array Expr) : MetaM Expr := do
  match ← whnf ty with
  | .forallE nm d b bi =>
    if let some (some k) := perm[p]? then
      eqAtGo ixj vj fv perm recPos t (b.instantiate1 fv[k]!) (p + 1) (args.push fv[k]!) quant
    else if p == recPos then eqAtGo ixj vj fv perm recPos t (b.instantiate1 t) (p + 1) (args.push t) quant
    else withLocalDecl nm bi d fun z =>
      eqAtGo ixj vj fv perm recPos t (b.instantiate1 z) (p + 1) (args.push z) (quant.push z)
  | _ =>
    let eq ← mkEq (mkAppN ixj args) (mkAppN vj args).headBeta
    mkForallFVars quant eq

/-- Prove a conjunction of the members' equations. -/
partial def proveConj (isMember : Name → Bool) (facts : Array Expr) (g : Expr) : MetaM Expr := do
  let g ← whnfR g
  if g.isAppOfArity ``And 2 then
    mkAppM ``And.intro #[← proveConj isMember facts g.appFn!.appArg!, ← proveConj isMember facts g.appArg!]
  else if g.isConstOf ``True then return mkConst ``True.intro
  else forallTelescopeReducing g fun zs eq => do
    let eq ← whnfR eq
    unless eq.isAppOfArity ``Eq 3 do throwError "not an equation: {eq}"
    let p ← proveEq isMember facts eq.appFn!.appArg! eq.appArg!
    mkLambdaFVars zs (← mkExpectedTypeHint p eq)

/-- The recursor's universe arguments for a Prop motive. -/
def recLevels (rv : RecursorVal) (us : List Level) : List Level :=
  if rv.levelParams.length == us.length + 1 then Level.zero :: us else us

/-- Structural: per member, the Ix constant and Lean's value (and Lean's name);
the proof of member `i`'s value equation. -/
def proveStructural (members : Array (Expr × Expr)) (leanNames : Array Name) (i : Nat) : MetaM Expr :=
  withOptions (fun o => o.setBool `smartUnfolding false) do
  let env ← getEnv
  let n := members.size
  let infos ← leanNames.mapM fun m => do
    let some info := Lean.Elab.Structural.eqnInfoExt.find? env m | throwError "{m}: no structural EqnInfo"
    pure info
  let permOf (j : Nat) : Lean.Elab.FixedParamPerm :=
    let k := infos[j]!.declNames.idxOf leanNames[j]!
    infos[j]!.fixedParamPerms.perms[k]!
  let isMember : Name → Bool := fun c => members.any fun (ix, _) => ix.constName? == some c
  let (ixC, leanV) := members[i]!
  lambdaTelescope leanV fun ps _ => do
    let infoI := infos[i]!
    let permI := permOf i
    let mut fv : Array Expr := Array.replicate infoI.fixedParamPerms.numFixed default
    for p in [0:permI.size] do
      if let some k := permI[p]! then fv := fv.set! k ps[p]!
    let major := ps[infoI.recArgPos]!
    -- the block: the first member's major type whose block's recursor has a motive for every
    -- member's major type (a nested member's major type is a container, e.g. `List Rose`)
    let tys ← (List.range n).toArray.mapM fun j => do
      let (_, vj) := members[j]!
      whnf (← majorType fv (permOf j) infos[j]!.recArgPos (← inferType vj) 0)
    let mut blockTy? : Option Expr := none
    for tyj in tys do
      if blockTy?.isNone then
        if let .const H hus := tyj.getAppFn then
          if let some (.inductInfo hv) := env.find? H then
            if let some (.recInfo rh) := env.find? (hv.all.head!.str "rec") then
              if rh.numIndices == 0 then
                let rty ← instantiateForall (rh.type.instantiateLevelParams rh.levelParams (recLevels rh hus))
                  (tyj.getAppArgs.extract 0 rh.numParams)
                let covers ← forallBoundedTelescope rty (some rh.numMotives) fun mvs _ => do
                  let mtys ← mvs.mapM fun mv => do
                    forallTelescopeReducing (← inferType mv) fun xs _ => inferType xs.back!
                  tys.allM fun tk => mtys.anyM fun mt => do isDefEq tk (← whnf mt)
                if covers then blockTy? := some tyj
    let some majorTy := blockTy? | throwError "no block whose recursor covers the members' major premises"
    let .const T us := majorTy.getAppFn | throwError "major premise type {majorTy}"
    let some (.inductInfo iv) := env.find? T | throwError "{T}: not an inductive"
    let some T0 := iv.all.head? | throwError "empty block"
    let some (.inductInfo iv0) := env.find? T0 | throwError "{T0}"
    let recs : Array Name := (iv0.all.map (·.str "rec")).toArray ++
      ((List.range iv0.numNested).map fun k => T0.str s!"rec_{k + 1}").toArray
    let some (.recInfo r0) := env.find? (T0.str "rec") | throwError "no recursor"
    unless r0.numIndices == 0 do throwError "an indexed family: not handled"
    let params := majorTy.getAppArgs.extract 0 r0.numParams
    let recTy ← instantiateForall (r0.type.instantiateLevelParams r0.levelParams (recLevels r0 us)) params
    forallBoundedTelescope recTy (some r0.numMotives) fun motVars _ => do
      let motTys ← motVars.mapM fun mv => do
        forallTelescopeReducing (← inferType mv) fun xs _ => inferType xs.back!
      let mut ms : Array Nat := #[]
      for j in [0:n] do
        let (_, vj) := members[j]!
        let tyj ← whnf (← majorType fv (permOf j) infos[j]!.recArgPos (← inferType vj) 0)
        let mut found : Option Nat := none
        for m in [0:motTys.size] do
          if found.isNone then
            if ← isDefEq tyj (← whnf motTys[m]!) then found := some m
        let some m := found | throwError "member {j}: no motive for its major type {tyj}"
        ms := ms.push m
      let motives ← (List.range motVars.size).toArray.mapM fun m => do
        forallTelescopeReducing (← inferType motVars[m]!) fun xs _ => do
          let t := xs.back!
          let js := (List.range n).filter (ms[·]! == m)
          let eqs ← js.mapM fun j => do
            let (ixj, vj) := members[j]!
            eqAtGo ixj vj fv (permOf j) infos[j]!.recArgPos t (← inferType vj) 0 #[] #[]
          let body ← match eqs.reverse with
            | [] => pure (mkConst ``True)
            | e :: rest => rest.foldlM (fun acc x => mkAppM ``And #[x, acc]) e
          mkLambdaFVars xs body
      let mut recName := recs[0]!
      for rn in recs do
        let some (.recInfo rv) := env.find? rn | continue
        let rty ← instantiateForall (rv.type.instantiateLevelParams rv.levelParams (recLevels rv us)) params
        let ok ← forallBoundedTelescope rty (some (rv.numMotives + rv.numMinors + rv.numIndices + 1)) fun xs body => do
          return body.getAppFn == xs[ms[i]!]!
        if ok then recName := rn
      let some (.recInfo rv) := env.find? recName | throwError "recursor"
      let recApp := mkAppN (mkConst recName (recLevels rv us)) (params ++ motives)
      let minors ← forallBoundedTelescope (← inferType recApp) (some rv.numMinors) fun mins _ => do
        mins.mapM fun mn => do
          forallTelescopeReducing (← inferType mn) fun xs goal => do
            let mut facts : Array Expr := #[]
            for x in xs do
              facts := facts ++ (← splitFacts x)
            mkLambdaFVars xs (← proveConj isMember facts goal)
      let ind := mkApp (mkAppN recApp minors) major
      let js := (List.range n).filter (ms[·]! == ms[i]!)
      let some pos := js.idxOf? i | throwError "member not in its group"
      let mut pfm := ind
      for _ in [0:pos] do pfm ← mkAppM ``And.right #[pfm]
      if pos + 1 < js.length then pfm ← mkAppM ``And.left #[pfm]
      let rest := (List.range ps.size).filter fun p => permI[p]!.isNone && p != infoI.recArgPos
      let applied := mkAppN pfm (rest.toArray.map (ps[·]!))
      let goal ← mkEq (mkAppN ixC ps) (mkAppN leanV ps).headBeta
      let hinted ← mkExpectedTypeHint applied goal
      let whole ← funextOver ps hinted
      mkExpectedTypeHint whole (← mkEq ixC leanV)


/-! ## A clique's proofs, on the Lean side -/

/-- One member's generated proof (Lean side), or why there is none. -/
structure MemberProof where
  name : Name
  /-- `m._ix_value = v` over the member's universe parameters. -/
  proof : Except String Expr

/-- What the generator found for one clique. -/
structure CliqueProofs where
  all : Array Name
  encoding : String
  members : Array MemberProof

/-- The heartbeat limit (thousands) of one member's proof. -/
def heartbeatLimit : Nat := 200000

/-- Decompile the clique's compiled constants, add them to Lean's environment
and generate each member's value equation. A generator failure leaves that
member without a proof (its reason recorded); nothing here is trusted. -/
def proveClique (env : Lean.Environment) (produced : Ixon.Env) (all : Array Name) : IO CliqueProofs := do
  let fail (enc : String) (why : String) : CliqueProofs :=
    { all, encoding := enc, members := all.map fun m => { name := m, proof := .error why } }
  match IxCliqueValues.compiledClosure produced all with
  | .error e => return fail "?" s!"decompile of the compiled clique: {e}"
  | .ok cs =>
    let enc := ((IxCliqueValues.sideCar? cs).map (·.1)).getD "?"
    let body : MetaM CliqueProofs := do
      if let some p ← IxCliqueValues.addCompiled all cs then
        return fail enc s!"the compiled clique in Lean's environment: {p.take 300}"
      let mut members : Array (Expr × Expr) := #[]
      for m in all do
        let some (.defnInfo d) := (← getEnv).find? m
          | return fail enc s!"{m}: not a definition in Lean's environment"
        let us := d.levelParams.map Level.param
        members := members.push (mkConst (IxCliqueValues.scratchName m) us, d.value)
      let mut out : Array MemberProof := #[]
      for i in [0:all.size] do
        let m := all[i]!
        unless enc == "well-founded" || enc == "structural" do
          out := out.push { name := m, proof := .error s!"encoding {enc}: no value-row generator" }
          continue
        let attempt : MetaM Expr := withCurrHeartbeats do
          let pf ← if enc == "structural" then proveStructural members all i else proveWF members i
          let pf ← instantiateMVars pf
          if pf.hasMVar then throwError "the proof has metavariables"
          let some (.defnInfo d) := (← getEnv).find? m | throwError "{m}: not a definition"
          -- Lean's kernel on the proof (a diagnostic; the certified fold decides)
          let ty ← instantiateMVars (← inferType pf)
          addDecl (.thmDecl { name := m.str "_ix_value_row", levelParams := d.levelParams, type := ty, value := pf })
          return pf
        let guarded : MetaM (Except String Expr) := do
          try
            let pf ← attempt
            return Except.ok pf
          catch e => return Except.error (← e.toMessageData.toString)
        let r : Except String Expr ← tryCatchRuntimeEx
          (withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeatLimit * 1000 }) guarded)
          fun e => do return Except.error s!"resource limit: {(← e.toMessageData.toString).take 200}"
        out := out.push { name := m, proof := Except.mapError (fun s => (s.take 400).toString) r }
      return { all, encoding := enc, members := out }
    let ctx : Core.Context := { fileName := "<compile-certify value rows>", fileMap := default, maxHeartbeats := 0 }
    try
      let (r, _) ← (body.run' {} {}).toIO ctx { env }
      return r
    catch e => return fail enc s!"generator: {e}"

end IxValueRows

/-! ## Export -/

namespace Ix.CompileCert.CliqueRows

/-- Export a member's proof: Lean's constants through `nameOfLean` (the map),
the scratch members through their own Lean names, the canonical (`_ix`)
constants through their records' reader names. -/
def exportProof (produced : Ixon.Env) (reader : Kernel.Reader.Ctx) (all : Array Lean.Name)
    (nameOfLean : Lean.Name → ExportM Kernel.Name) (levelOf : Lean.Level → ExportM Kernel.Level)
    (proof : Lean.Expr) : ExportM Kernel.Expr := do
  let scratch : Std.HashMap Lean.Name Lean.Name :=
    all.foldl (fun m a => m.insert (IxCliqueValues.scratchName a) a) {}
  let mut memo : Std.HashMap Lean.Name Kernel.Name := {}
  for c in proof.getUsedConstants do
    let k ← match scratch[c]? with
      | some m => nameOfLean m
      | none =>
        if IxCliqueValues.isReservedName c then
          match produced.named.get? (Ix.Name.fromLeanName c) with
          | none => throw s!"canonical constant {c} not in the artifact"
          | some named =>
            match Kernel.Reader.resolve reader.store named.addr with
            | some r => pure (reader.nameOf r)
            | none => throw s!"canonical constant {c}: its record does not resolve"
        else nameOfLean c
    memo := memo.insert c k
  exportExprWith levelOf (fun c => match memo[c]? with
    | some k => .ok k
    | none => .error s!"unexported constant {c}") proof

end Ix.CompileCert.CliqueRows
