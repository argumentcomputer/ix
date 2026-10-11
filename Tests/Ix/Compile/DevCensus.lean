/-
  dev-census (M7 X1; risk R6 of the L2a scoping note): what the development
  (`Ix.Compile.Image.Develop`, hereditary substitution, design document §4.3)
  substitutes, on the `pass3` fixtures and on Init+Std.

  Per compile unit (the `pass3` suite's units, compiled in-process by the Lean
  pipeline under Pass 3, the default), every call of the development the
  compiler makes is reconstructed and measured:

  * **P3a** (the image construction, `Ix.Compile.Image.imageOf`): a copy of
    `buildRecApp`/`imageOf` records the inputs of its three developments (the
    canonical minor types with the motives substituted, the rule right-hand
    sides at the opened telescope, the rule types at the constructor);
  * **P3b** (the call-site rewrite, `Ix.Compile.Pass.Translate.rw`): a copy of
    `rw` records the inputs of every inline (`instantiateWith`), with the same
    expansions, definitional passes and argument rewrites as the compiler.

  For each development: the executable's result, the memo-free core's
  (`Ix.CompileCert.Conv.instantiateP`/`hinstP`) compared with it, the fuel the
  core needs (its recursion depth, computed with a per-node table of heights,
  so it is the memo-free depth at linear cost), the hereditary level (how many
  β-redexes deep the substituted values go), the kinds of the substituted
  values per level (inert, first-order λ, higher-order λ, pair), and whether
  the input is simply typable in the erased system of `Ix.CompileCert.Conv`
  (the totality domain), by first-order unification.

  Run with: `lake test -- --ignored dev-census` (`DEV_CENSUS_ONLY` restricts
  the units: comma-separated stems, `twins`, `corpus`, `initstd`).
-/
import Tests.Ix.Compile.Pass3
import Ix.CompileCert.Conv.Core

open Lean (Environment)

namespace Tests.Ix.Compile.DevCensus

open _root_.Ix (Name Level Expr ConstantInfo)
open _root_.Ix.Compile.Image
open _root_.Ix.Compile.Canon (getAppFnArgs mkAppN substLevels normalizeLevel)

/-! ## Inputs of the development -/

inductive DevRec where
  | subst (what : String) (xs : Array Name) (vs : Array Expr) (e : Expr)
  | inst (what : String) (f : Expr) (args : Array Expr)

def DevRec.what : DevRec → String
  | .subst w .. | .inst w .. => w

/-! ## The image construction, recording its developments (copy of `Build.lean`) -/

abbrev CM := StateT (Array DevRec) GenM

def recSubst (what : String) (xs : Array Name) (vs : Array Expr) (e : Expr) : CM Expr := do
  modify (·.push (.subst what xs vs e))
  liftM (_root_.Ix.Compile.Image.liftExcept (substFVars xs vs e) : GenM Expr)

def recInst (what : String) (f : Expr) (args : Array Expr) : CM Expr := do
  modify (·.push (.inst what f args))
  liftM (_root_.Ix.Compile.Image.liftExcept (instantiate f args) : GenM Expr)

def buildRecAppC : Nat → LCtx → Nat → Array Expr → Expr → CM Expr
  | 0, _, t, _, _ => throw s!"image: relocation bound exhausted at Lean motive {t}"
  | fuel + 1, c, t, idx, major => do
    let e ← findElim c t
    let rv ← _root_.Ix.Compile.Image.liftExcept (recOf c.const? e.recName)
    let mts ← elimMotiveTypes c.const? e.ind e.indLevels e.params
    let classes : Array (Array Nat) := mts.map fun mt =>
      (c.motiveTys.zipIdx.filter fun (ty, _) => alphaEq ty mt).map (·.2)
    for (cl, i) in classes.zipIdx do
      if cl.isEmpty then
        throw s!"image: eliminator {e.recName.pretty}: slot {i} has no Lean motive"
    let anyTuple := classes.any (·.size > 1)
    let luZero := isAlwaysZero c.lu
    let L : Level := if anyTuple && !luZero then normalizeLevel (Level.mkMax lvlOne c.lu) else c.lu
    let packs : Array Pack := classes.map fun cl =>
      if cl.size > 1 then .tuple cl.size
      else if anyTuple && !luZero && !c.opts.noLift then .lift else .single
    if !e.hasElimLevel && !isAlwaysZero L then
      throw s!"image: eliminator {e.recName.pretty} is small but the Lean motives are not"
    let us := (if e.hasElimLevel then #[L] else #[]) ++ e.indLevels
    let recC := Expr.mkConst e.recName us
    let rty ← _root_.Ix.Compile.Image.liftExcept (instForall (substLevels rv.cnst.levelParams us rv.cnst.type) e.params)
    let (xs, _) ← telescope rty (rv.numMotives + rv.numMinors)
    let msC := xs.extract 0 rv.numMotives
    let minsC := xs.extract rv.numMotives xs.size
    let mut motives : Array Expr := #[]
    for h : i in [0:msC.size] do
      let (isy, _) ← telescope msC[i].type
      let apps ← (← GenM.idx classes i "slot class").mapM fun j => do
        pure (mkAppN (← GenM.idx c.ms j "Lean motive").expr (isy.map (·.expr)))
      motives := motives.push (etaReduce (mkLambda isy (← _root_.Ix.Compile.Image.liftExcept (wrapTy (← GenM.idx packs i "slot pack") c.lu apps))))
    let mut minors : Array Expr := #[]
    for minC in minsC do
      let (mi, ctor, nf, ihFields) ← analyzeCanonMinor c.const? msC minC.type
      let mty ← recSubst "P3a minor type" (msC.map (·.fvar)) motives minC.type
      let (bs, _) ← telescope mty
      let flds := bs.extract 0 nf
      let ihsC := bs.extract nf bs.size
      let mut comps : Array (Expr × Expr) := #[]
      for j in (← GenM.idx classes mi "minor slot class") do
        let some lmi := c.minors.findIdx? (fun lm => lm.motive == j && lm.ctor == ctor)
          | throw s!"image: no Lean minor for motive {j} and constructor {ctor.pretty}"
        let lm ← GenM.idx c.mins lmi "Lean minor"
        let mut lty ← _root_.Ix.Compile.Image.liftExcept (instForall lm.type (flds.map (·.expr)))
        let mut ihVals : Array Expr := #[]
        for _ in [0:forallArity lty] do
          match _root_.Ix.Compile.Canon.stripMdata lty with
          | .forallE _ bt body _ _ =>
            let (ys, cc) ← telescope bt
            let some t' := fvarIdx? c.ms (getAppFn cc) | throw "image: Lean hypothesis head"
            let some arg := appArg? cc | throw "image: Lean hypothesis major"
            let idx' := (getAppArgs cc).pop
            let some f := fvarIdx? flds (getAppFn arg) | throw "image: Lean hypothesis field"
            let v ← match ihFields.findIdx? (·.1 == f) with
              | some q => do
                let mq := (← GenM.idx ihFields q "hypothesis field").2
                let some pos := (← GenM.idx classes mq "hypothesis slot class").idxOf? t'
                  | throw s!"image: hypothesis motive {t'} not in its slot's class"
                pure (mkLambda ys (unwrap (← GenM.idx packs mq "hypothesis slot pack") luZero pos
                  (mkAppN (← GenM.idx ihsC q "canonical hypothesis").expr (ys.map (·.expr)))))
              | none => do
                let v ← buildRecAppC fuel c t' idx' arg
                pure (mkLambda ys v)
            ihVals := ihVals.push v
            lty := instLocals body #[v]
          | _ => throw "image: Lean minor arity"
        comps := comps.push (mkAppN lm.expr (flds.map (·.expr) ++ ihVals), lty)
      minors := minors.push (etaReduce (mkLambda bs (← _root_.Ix.Compile.Image.liftExcept (wrapVal (← GenM.idx packs mi "minor slot pack") c.lu comps))))
    let app := mkAppN recC (e.params ++ motives ++ minors ++ idx ++ #[major])
    let some pos := (← GenM.idx classes e.k "eliminated slot class").idxOf? t | throw "image: eliminated motive not in its class"
    return unwrap (← GenM.idx packs e.k "eliminated slot pack") luZero pos app

/-- `imageOf`, recording its developments (the image value is not needed here). -/
def imageDevs (const? : Name → Option ConstantInfo) (spec : ImageSpec) (r : Name) :
    Except String (Array DevRec) := GenM.run' do
  let ((), recs) ← (go : CM Unit).run #[]
  return recs
where
  go : CM Unit := do
    let rv ← _root_.Ix.Compile.Image.liftExcept (recOf const? r)
    let ty := spec.tr rv.cnst.type
    let (xs, body) ← telescope ty
    let np := rv.numParams
    let nm := rv.numMotives
    let nmin := rv.numMinors
    let ps := xs.extract 0 np
    let ms := xs.extract np (np + nm)
    let mins := xs.extract (np + nm) (np + nm + nmin)
    let is := xs.extract (np + nm + nmin) (xs.size - 1)
    let some x := xs.back? | throw "image: recursor without a major"
    let some m0 := ms[0]? | throw "image: recursor without motives"
    let minors ← mins.mapM fun m => analyzeLeanMinor ms m.type
    let some a0 := rv.all[0]? | throw "image: empty block"
    let ind ← _root_.Ix.Compile.Image.liftExcept (indOf const? a0)
    let c : LCtx := {
      const?, spec, opts := {}, ps, ms, mins
      motiveTys := ms.map fun m => stripSort m.type
      minors
      lu := motiveLevel m0.type
      indLevels := ind.cnst.levelParams.map Level.mkParam }
    let some t := fvarIdx? ms (getAppFn body) | throw "image: recursor's conclusion"
    discard <| buildRecAppC (nm + 1) c t (is.map (·.expr)) x.expr
    let pmm := xs.extract 0 (np + nm + nmin)
    let T := x.type
    let some (_, tLvls) := headConst? T | throw "image: major type's head"
    let recMap : Std.HashMap Name Name := (blockRecursors const? ind).foldl
      (fun m r => m.insert r (spec.naming.img r)) {}
    let trRule := fun (e : Expr) => _root_.Ix.Compile.Canon.canonicalizeConstNames recMap (spec.tr e)
    for rule in rv.rules do
      let cv ← _root_.Ix.Compile.Image.liftExcept (ctorOf const? rule.ctor)
      let cParams := (getAppArgs T).extract 0 cv.numParams
      let ctorC := Expr.mkConst (spec.trName rule.ctor) tLvls
      let cty ← _root_.Ix.Compile.Image.liftExcept (instForall
        (substLevels cv.cnst.levelParams tLvls (spec.tr cv.cnst.type)) cParams)
      let (flds, cres) ← telescope cty
      let idx := (getAppArgs cres).extract cv.numParams (getAppArgs cres).size
      let major := mkAppN ctorC (cParams ++ flds.map (·.expr))
      discard <| recInst "P3a rule rhs" (trRule rule.rhs) (pmm.map (·.expr) ++ flds.map (·.expr))
      discard <| recSubst "P3a rule type" ((is.push x).map (·.fvar)) (idx.push major) body

/-! ## The call-site rewrite, recording its developments (copy of `Translate.lean`) -/

open _root_.Ix.Compile.Pass (Expansion RwState rewriteFuel inlineKey)

abbrev RwC := StateT RwState (StateT (Array DevRec) (Except String))

section
variable (expansion? : Name → Except String (Option Expansion))

mutual
def expansionOfC : Nat → Name → RwC (Option Expansion)
  | 0, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, n => do
    if let some x := (← get).exps.get? n then return some x
    match ← liftM (expansion? n) with
    | none => return none
    | some x =>
      let x ← if x.needsRewrite then do
          let site := (← get).site
          modify fun st => { st with site := none }
          let v ← rwC fuel false x.value
          modify fun st => { st with site }
          pure { x with value := v, needsRewrite := false }
        else pure x
      modify fun st => { st with exps := st.exps.insert n x }
      return some x

def rwC : Nat → Bool → Expr → RwC Expr
  | 0, _, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, record, e => do
    let site := (← get).site
    if let some r := (← get).cache.get? (e, record, site) then return r
    let r ← match e with
      | .app .. | .const .. => do
        let (h, args) := getAppFnArgs e
        match h with
        | .const n us _ =>
          match ← expansionOfC fuel n with
          | some x =>
            let mut args' : Array Expr := #[]
            for a in args do args' := args'.push (← rwC fuel false a)
            if args.size < x.arity then
              return mkAppN (Expr.mkConst n us) args'
            let st ← get
            let res ← match st.opt? site n us args' with
              | some (e, cs, none) => pure (some (e, cs))
              | some (e, cs, some _) =>
                if st.inPlace then pure (some (e, cs))
                else pure ((st.opt? none n us args').map fun (e, cs, _) => (e, cs))
              | none => pure none
            let body ← match res with
              | some (e, _) => pure e
              | none => do
                let f := substLevels x.levelParams us x.value
                modifyThe (Array DevRec) (·.push (.inst "P3b inline" f args'))
                liftM (instantiate f args')
            if record then
              let st ← get
              let k := st.base + st.sources.size
              set { st with sources := st.sources.push e }
              pure (Expr.mkMData #[(inlineKey, .ofNat k)] body)
            else pure body
          | none =>
            let mut args' : Array Expr := #[]
            for a in args do args' := args'.push (← rwC fuel record a)
            pure (mkAppN h args')
        | _ =>
          let h' ← rwC fuel record h
          let mut args' : Array Expr := #[]
          for a in args do args' := args'.push (← rwC fuel record a)
          pure (mkAppN h' args')
      | .lam n t b bi _ => do
        pure (Expr.mkLam n (← rwC fuel record t) (← rwC fuel record b) bi)
      | .forallE n t b bi _ => do
        pure (Expr.mkForallE n (← rwC fuel record t) (← rwC fuel record b) bi)
      | .letE n t v b nd _ => do
        pure (Expr.mkLetE n (← rwC fuel record t) (← rwC fuel record v) (← rwC fuel record b) nd)
      | .proj s i x _ => do pure (Expr.mkProj s i (← rwC fuel record x))
      | .mdata md x _ => do pure (Expr.mkMData md (← rwC fuel record x))
      | e => pure e
    modify fun st => { st with cache := st.cache.insert (e, record, site) r }
    return r
end
end

/-- The developments of the rewrite of one constant. -/
def constDevs (expansion? : Name → Except String (Option Expansion))
    (opt? : Option Name → Name → Array Level → Array Expr →
      Option (Expr × Array ConstantInfo × Option String)) (ci : ConstantInfo) :
    Except String (Array DevRec) := do
  let go := rwC expansion? rewriteFuel true
  let m : RwC Unit := do
    discard <| go ci.getCnst.type
    match ci with
    | .defnInfo v =>
      modify fun st => { st with site := some v.cnst.name }
      discard <| go v.value
      modify fun st => { st with site := none }
    | .thmInfo v => discard <| go v.value
    | .opaqueInfo v => discard <| go v.value
    | .recInfo v => for r in v.rules do discard <| go r.rhs
    | _ => pure ()
  let ((_, _), recs) ← (m.run { base := 0, opt? }).run #[]
  return recs

/-! ## Measuring one development -/

/-- The kind of a substituted value: `inert` (not a λ and not a pair
constructor: no redex can form), `fo` (a λ whose binders never occur at a head
position, so substituting into it forms no redex), `ho` (another λ), `pair`. -/
partial def headOcc (j : Nat) : Expr → Bool
  | e@(.app ..) =>
    let (h, args) := getAppFnArgs e
    (match h with | .bvar i _ => i == j | _ => false) || headOcc j h || args.any (headOcc j)
  | .proj _ _ x _ =>
    (match (getAppFnArgs x).1 with | .bvar i _ => i == j | _ => false) || headOcc j x
  | .lam _ t b _ _ | .forallE _ t b _ _ => headOcc j t || headOcc (j + 1) b
  | .letE _ t v b _ _ => headOcc j t || headOcc j v || headOcc (j + 1) b
  | .mdata _ x _ => headOcc j x
  | _ => false

def kindOf (v : Expr) : String :=
  match v with
  | .lam .. =>
    -- the leading binders, then the body (on the head path when it is a variable)
    let rec peel : Expr → Nat → Bool
      | .lam _ t b _ _, d => !headOcc 0 t && peel b (d + 1)
      | b, d => (List.range d).all fun j => !headOcc j b &&
          (match (getAppFnArgs b).1 with | .bvar i _ => i != j | _ => true)
    if peel v 0 then "fo" else "ho"
  | _ =>
    match (getAppFnArgs v).1 with
    | .const c _ _ => if c == nPProdMk || c == nAndIntro then "pair" else "inert"
    | _ => "inert"

structure Stats where
  /-- Distinct `(v, e, k)` developments computed. -/
  nodes : Nat := 0
  betas : Nat := 0
  projs : Nat := 0
  etas : Nat := 0
  /-- `(level, kind)` ↦ count of hereditary substitutions. -/
  kinds : Std.HashMap (Nat × String) Nat := {}
  /-- `(v, e, k)` ↦ result, flag, height (calls nested below, the call included), max level. -/
  memo : Std.HashMap (Expr × Expr × Nat) (Expr × Created × Nat × Nat) := {}

abbrev SM := StateT Stats (Except String)

mutual
/-- `hinstP` measured: the result, its flag, the height of its call tree and the
deepest hereditary level below it. Tabled by `(v, e, k)`: the height of a
tabled node is its memo-free height, so the root's height is the fuel the
memo-free core needs. -/
partial def hinstM (lvl : Nat) (v : Expr) (k : Nat) (e : Expr) : SM (Expr × Created × Nat × Nat) := do
  if _root_.Ix.CompileCert.Conv.looseRangeP e ≤ k then return (e, .no, 1, lvl)
  if let some r := (← get).memo.get? (v, e, k) then return r
  let r ← match e with
    | .bvar i _ =>
      if i == k then pure (_root_.Ix.CompileCert.Conv.liftP v k 0, .direct, 1, lvl)
      else if i > k then pure (Expr.mkBVar (i - 1), .no, 1, lvl)
      else pure (e, .no, 1, lvl)
    | .app .. => do
      let (h, args) := getAppFnArgs e
      let mut args' : Array Expr := #[]
      let mut ht := 0
      let mut lv := lvl
      for a in args do
        let (a', _, ha, la) ← hinstM lvl v k a
        args' := args'.push a'
        ht := max ht ha
        lv := max lv la
      let (h', c, hh, lh) ← hinstM lvl v k h
      ht := max ht hh
      lv := max lv lh
      match c, h' with
      | .no, _ => pure (mkAppN h' args', .no, ht + 1, lv)
      | _, .lam .. => do
        modify fun s => { s with betas := s.betas + 1 }
        let (r, hr, lr) ← happM (lvl + 1) h' args'.toList
        pure (r, .reduced, max ht hr + 1, max lv lr)
      | c, _ => pure (mkAppN h' args', c, ht + 1, lv)
    | .proj s i x _ => do
      let (x', c, hx, lx) ← hinstM lvl v k x
      match c with
      | .no => pure (Expr.mkProj s i x', .no, hx + 1, lx)
      | _ =>
        match projCtor? s i x' with
        | some f =>
          modify fun s => { s with projs := s.projs + 1 }
          pure (f, .reduced, hx + 1, lx)
        | none => pure (Expr.mkProj s i x', .no, hx + 1, lx)
    | .lam n t b bi _ => do
      let (t', _, ht, lt) ← hinstM lvl v k t
      let (b', c, hb, lb) ← hinstM lvl v (k + 1) b
      let hh := max ht hb + 1
      match c, b' with
      | .direct, .app f (.bvar 0 _) _ =>
        if !(_root_.Ix.CompileCert.Conv.occursP f 0) then
          modify fun s => { s with etas := s.etas + 1 }
          pure (_root_.Ix.CompileCert.Conv.lowerP f 1 0, .direct, hh, max lt lb)
        else pure (Expr.mkLam n t' b' bi, .no, hh, max lt lb)
      | _, _ => pure (Expr.mkLam n t' b' bi, .no, hh, max lt lb)
    | .forallE n t b bi _ => do
      let (t', _, ht, lt) ← hinstM lvl v k t
      let (b', _, hb, lb) ← hinstM lvl v (k + 1) b
      pure (Expr.mkForallE n t' b' bi, .no, max ht hb + 1, max lt lb)
    | .letE n t x b nd _ => do
      let (t', _, ht, lt) ← hinstM lvl v k t
      let (x', _, hx, lx) ← hinstM lvl v k x
      let (b', _, hb, lb) ← hinstM lvl v (k + 1) b
      pure (Expr.mkLetE n t' x' b' nd, .no, max (max ht hx) hb + 1, max (max lt lx) lb)
    | .mdata md x _ => do
      let (x', c, hx, lx) ← hinstM lvl v k x
      pure (Expr.mkMData md x', c, hx + 1, lx)
    | _ => pure (e, .no, 1, lvl)
  modify fun s => { s with nodes := s.nodes + 1, memo := s.memo.insert (v, e, k) r }
  return r

/-- `happP` measured: the result, the height of its call tree, the deepest level. -/
partial def happM (lvl : Nat) (f : Expr) (args : List Expr) : SM (Expr × Nat × Nat) := do
  match f, args with
  | .lam _ _ b _ _, a :: rest =>
    let key := (lvl, kindOf a)
    modify fun (s : Stats) => { s with kinds := s.kinds.insert key (s.kinds.getD key 0 + 1) }
    let (b', _, hb, lb) ← hinstM lvl a 0 b
    let (r, hr, lr) ← happM lvl b' rest
    pure (r, max hb hr + 1, max lb lr)
  | f, args => pure (mkAppN f args.toArray, 1, lvl)
end

/-! ## Simple types of the erased terms (the totality domain), by unification -/

inductive STy where
  | var (n : Nat)
  | arr (a b : STy)
  | pairP (a b : STy)
  | pairA (a b : STy)
  deriving Inhabited

structure InfState where
  next : Nat := 0
  sub : Std.HashMap Nat STy := {}
  steps : Nat := 0
  /-- The types of the loose variables (the call site's context), by index outside the term:
  one type per variable, as in a typing context. -/
  loose : Std.HashMap Nat STy := {}

abbrev InfM := StateT InfState (Except String)

def fresh : InfM STy := modifyGet fun s => (.var s.next, { s with next := s.next + 1 })

partial def resolve (s : Std.HashMap Nat STy) : STy → STy
  | .var n => match s.get? n with
    | some t => resolve s t
    | none => .var n
  | t => t

partial def occursIn (s : Std.HashMap Nat STy) (n : Nat) (t : STy) : Bool :=
  match resolve s t with
  | .var m => m == n
  | .arr a b | .pairP a b | .pairA a b => occursIn s n a || occursIn s n b

partial def unify (a b : STy) : InfM Unit := do
  let s := (← get).sub
  match resolve s a, resolve s b with
  | .var n, .var m => if n == m then pure () else modify fun st => { st with sub := st.sub.insert n (.var m) }
  | .var n, t | t, .var n =>
    if occursIn s n t then throw "occurs check" else modify fun st => { st with sub := st.sub.insert n t }
  | .arr a1 b1, .arr a2 b2 => do unify a1 a2; unify b1 b2
  | .pairP a1 b1, .pairP a2 b2 => do unify a1 a2; unify b1 b2
  | .pairA a1 b1, .pairA a2 b2 => do unify a1 a2; unify b1 b2
  | _, _ => throw "constructor clash"

def pairKind (s : Name) : Option Bool :=
  if s == nPProd then some true else if s == nAnd then some false else none

def ctorKind (c : Name) : Option Bool :=
  if c == nPProdMk then some true else if c == nAndIntro then some false else none

def mkPair (k : Bool) (a b : STy) : STy := if k then .pairP a b else .pairA a b

/-- The simple type of `e` in the context `ctx` (the erasure's typing: opaque
leaves and constants at any type, pairs typed, binder annotations typable). -/
partial def infer (ctx : List STy) (e : Expr) : InfM STy := do
  modify fun s => { s with steps := s.steps + 1 }
  if (← get).steps > 4000000 then throw "budget"
  match e with
  | .bvar i _ => match ctx[i]? with
    | some t => pure t
    | none => do
      let j := i - ctx.length
      match (← get).loose.get? j with
      | some t => pure t
      | none => do
        let t ← fresh
        modify fun s => { s with loose := s.loose.insert j t }
        pure t
  | .fvar .. | .mvar .. | .sort .. | .lit .. => fresh
  | .const c _ _ =>
    match ctorKind c with
    | some k => do
      let a ← fresh; let b ← fresh; let x ← fresh; let y ← fresh
      pure (.arr a (.arr b (.arr x (.arr y (mkPair k x y)))))
    | none => fresh
  | .app f a _ => do
    let tf ← infer ctx f
    let ta ← infer ctx a
    let r ← fresh
    unify tf (.arr ta r)
    pure r
  | .lam _ t b _ _ => do
    discard <| infer ctx t
    let x ← fresh
    let tb ← infer (x :: ctx) b
    pure (.arr x tb)
  | .forallE _ t b _ _ => do
    discard <| infer ctx t
    let x ← fresh
    discard <| infer (x :: ctx) b
    fresh
  | .letE _ t v b _ _ => do
    discard <| infer ctx t
    let tv ← infer ctx v
    infer (tv :: ctx) b
  | .mdata _ x _ => infer ctx x
  | .proj s i x _ => do
    let tx ← infer ctx x
    match pairKind s with
    | some k =>
      if i < 2 then do
        let a ← fresh; let b ← fresh
        unify tx (mkPair k a b)
        pure (if i == 0 then a else b)
      else fresh
    | none => fresh

/-- Typability of a development's input: the application `f args`, or the
abstracted term with the values at its leading variables. -/
def typable (r : DevRec) : Except String Unit := do
  match r with
  | .inst _ f args =>
    let m : InfM Unit := do discard <| infer [] (mkAppN f args)
    discard <| m.run {}
  | .subst _ xs vs e =>
    let m : InfM Unit := do
      let n := xs.size
      let mut ctx : List STy := []
      for _ in [0:n] do ctx := (← fresh) :: ctx
      discard <| infer ctx (abstractFVars xs e)
      for i in [0:n] do
        if h : i < vs.size then
          let tv ← infer [] vs[i]
          if let some t := ctx[n - 1 - i]? then unify t tv
    discard <| m.run {}

/-! ## Heights (tabled by node) -/

partial def heightT (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some h := (← get).get? e then return h
  let h ← match e with
    | .app f a _ => do pure (max (← heightT f) (← heightT a) + 1)
    | .lam _ t b _ _ | .forallE _ t b _ _ => do pure (max (← heightT t) (← heightT b) + 1)
    | .letE _ t v b _ _ => do pure (max (max (← heightT t) (← heightT v)) (← heightT b) + 1)
    | .proj _ _ x _ | .mdata _ x _ => do pure ((← heightT x) + 1)
    | _ => pure 1
  modify (·.insert e h)
  return h

def height (e : Expr) : Nat := (heightT e).run' {}

/-! ## One record -/

structure Row where
  what : String
  ok : Bool := true
  coreEq : Option Bool := none
  depth : Nat := 0
  level : Nat := 0
  betas : Nat := 0
  projs : Nat := 0
  etas : Nat := 0
  kinds : Array ((Nat × String) × Nat) := #[]
  typable : Option Bool := none
  /-- The height of the whole input (`f args`, or the abstracted term and the values). -/
  inputHeight : Nat := 0
  nodes : Nat := 0

def measure (r : DevRec) : Row := Id.run do
  let mut row : Row := { what := r.what }
  -- the executable, the core, the measured copy
  let (exec, core, meas, ih) := match r with
    | .inst _ f args =>
      let m : SM (Expr × Nat × Nat) := happM 1 f args.toList
      (instantiate f args, _root_.Ix.CompileCert.Conv.instantiateP f args, m.run {},
        height (mkAppN f args))
    | .subst _ xs vs e =>
      let m : SM (Expr × Nat × Nat) := do
        let mut acc := abstractFVars xs e
        let mut ht := 0
        let mut lv := 1
        for v in vs.reverse do
          let key := (1, kindOf v)
          modify fun (s : Stats) => { s with kinds := s.kinds.insert key (s.kinds.getD key 0 + 1) }
          let (a, _, h, l) ← hinstM 1 v 0 acc
          acc := a
          ht := max ht h
          lv := max lv l
        pure (acc, ht, lv)
      (substFVars xs vs e, _root_.Ix.CompileCert.Conv.substFVarsP xs vs e, m.run {},
        vs.foldl (fun acc v => max acc (height v)) (height (abstractFVars xs e)) + 1)
  row := { row with inputHeight := ih }
  match exec, meas with
  | .ok x, .ok ((y, d, l), st) =>
    row := { row with ok := true, depth := d, level := l, betas := st.betas, projs := st.projs,
                      etas := st.etas, nodes := st.nodes, kinds := st.kinds.toArray }
    if !(x == y) then row := { row with ok := false }
    -- the memo-free core itself only where it is cheap (no table)
    if st.nodes < 20000 then
      row := { row with coreEq := some (match core with | .ok z => z == x | .error _ => false) }
  | _, _ => row := { row with ok := false }
  row := { row with typable := some ((typable r).isOk) }
  return row

/-! ## Units -/

def changedRecursors (cenv : _root_.Ix.CompileM.CompileEnv) (blockAll : Array Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for n in blockAll do
    if let some (.inductInfo iv) := cenv.env.get? n then
      for r in blockRecursors cenv.env.get? iv do
        if !out.contains r then out := out.push r
  return out

structure UnitResult where
  rows : Array Row := #[]
  problems : Array String := #[]
  /-- Images and rewrites the census could not rebuild for names the compile itself refused
  (`CompileEnv.ungrounded`: A0's refusal of a block, `REFUSED-SIBLING` in the pass3 record). -/
  refused : Nat := 0
  blocks : Nat := 0
  heads : Nat := 0

def runCompiled (cenv : _root_.Ix.CompileM.CompileEnv) : UnitResult := Id.run do
  let mut res : UnitResult := { blocks := cenv.p3Blocks.size, heads := cenv.p3Heads.size }
  if cenv.p3Heads.isEmpty then return res
  -- every changed block's view
  let mut views : Std.HashMap Name _root_.Ix.Compile.Pass.BlockView := {}
  let inp := _root_.Ix.Compile.Pass.viewInput cenv
  -- every changed block's view, built afresh over the whole compile (as the `pass3` suite's
  -- `ruleEnv` does): the canonical form with every component compiled
  for (key, all) in cenv.p3Blocks do
    match _root_.Ix.Compile.Pass.buildView inp all with
    | .ok v => views := views.insert key v
    | .error e => res := { res with problems := res.problems.push s!"view {key.pretty}: {e}" }
  -- P3a
  for (key, v) in views do
    for r in (_root_.Ix.Compile.Pass.imageKinds inp.const? ((cenv.p3Blocks.get? key).getD #[key])).filter
        (fun r => match inp.const? r with | some (.recInfo _) => true | _ => false) do
      match imageDevs (v.const? inp) v.spec r with
      | .ok recs => res := { res with rows := res.rows ++ recs.map measure }
      | .error e =>
        if cenv.ungrounded.contains r then res := { res with refused := res.refused + 1 }
        else res := { res with problems := res.problems.push s!"image {r.pretty}: {e}" }
  -- P3b: every constant that mentions a head
  let table := _root_.Ix.Compile.Pass.expansionTable cenv views
  let lookup := _root_.Ix.Compile.Pass.expansionLookupIn table cenv views
  let opt := _root_.Ix.Compile.Pass.optLookup cenv (_root_.Ix.Compile.Pass.optBlocks cenv views)
  for (n, ci) in cenv.env.consts do
    if (_root_.Ix.Compile.Pass.headsIn cenv.p3Heads ci).isEmpty then continue
    match constDevs lookup opt ci with
    | .ok recs => res := { res with rows := res.rows ++ recs.map measure }
    | .error e =>
      if cenv.ungrounded.contains n then res := { res with refused := res.refused + 1 }
      else res := { res with problems := res.problems.push s!"rewrite {n.pretty}: {e}" }
  return res

def summary (name : String) (r : UnitResult) : Array String := Id.run do
  let mut out : Array String := #[]
  let byWhat := ["P3a minor type", "P3a rule rhs", "P3a rule type", "P3b inline"]
  let mut parts : Array String := #[]
  for w in byWhat do
    let rs := r.rows.filter (·.what == w)
    if rs.isEmpty then continue
    let d := rs.foldl (fun a x => max a x.depth) 0
    let l := rs.foldl (fun a x => max a x.level) 0
    let ih := rs.foldl (fun a x => max a x.inputHeight) 0
    let ratio := rs.foldl (fun a x => max a (if x.inputHeight == 0 then 0 else (x.depth * 100) / x.inputHeight)) 0
    let bad := rs.filter (!·.ok)
    let un := rs.filter (·.typable == some false)
    let ce := rs.filter (·.coreEq == some false)
    let cc := rs.filter (·.coreEq.isSome)
    let b := rs.foldl (· + ·.betas) 0
    let p := rs.foldl (· + ·.projs) 0
    let e := rs.foldl (· + ·.etas) 0
    parts := parts.push s!"{w}: n={rs.size} maxDepth={d} maxLevel={l} maxInputHeight={ih} maxDepth/inputHeight={ratio}% β={b} proj={p} η={e} execMismatch={bad.size} coreChecked={cc.size} coreMismatch={ce.size} untypable={un.size}"
  out := out.push s!"{name}: changed blocks={r.blocks} heads={r.heads} developments={r.rows.size} refused-by-the-compile={r.refused}"
  for p in parts do out := out.push s!"{name}:   {p}"
  -- kinds per level
  let mut kinds : Std.HashMap (Nat × String) Nat := {}
  for row in r.rows do
    for (k, c) in row.kinds do kinds := kinds.insert k (kinds.getD k 0 + c)
  let ks := kinds.toArray.qsort (fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2))
  if !ks.isEmpty then
    out := out.push s!"{name}:   substituted values (level, kind) ↦ count: {ks.toList.map fun ((l, k), c) => s!"({l},{k})={c}"}"
  for p in r.problems do out := out.push s!"{name}: PROBLEM {p}"
  return out

/-- Controls of the typability check: `(λx. x x) (λx. x x)` is refused (it has no simple type,
and its development does not terminate), `(λx. x) c` accepted. -/
def typingControls : Bool × Bool :=
  let x := Expr.mkBVar 0
  let ty := Expr.mkSort lvlZero
  let nm := _root_.Ix.Name.mkAnon
  let self := Expr.mkLam nm ty (Expr.mkApp x x) .default
  let omega : DevRec := .inst "control" self #[self]
  let idApp : DevRec := .inst "control" (Expr.mkLam nm ty x .default) #[Expr.mkConst nm #[]]
  ((typable omega).isOk, (typable idApp).isOk)

def run (env : Environment) : IO UInt32 := do
  let (omegaOk, idOk) := typingControls
  IO.println s!"[dev-census] typing controls: (λx. x x) (λx. x x) typable={omegaOk} (expected false), (λx. x) c typable={idOk} (expected true)"
  let only := ((← IO.getEnv "DEV_CENSUS_ONLY").map (·.splitOn ",")).getD []
  let want := fun (s : String) => only.isEmpty || only.contains s
  let mut all : UnitResult := {}
  let mut units := 0
  let files := Tests.Ix.Compile.Pass3.auxCertFiles ++ Tests.Ix.Compile.Pass3.protoFiles ++
    Tests.Ix.Compile.Pass3.passFiles ++ Tests.Ix.Compile.Pass3.pjPassFiles
  let mut work : Array (String × IO Tests.Ix.Compile.Pass3.CUnit) := #[]
  for p in files do
    let stem := (System.FilePath.mk p).fileStem.getD p
    if want stem && !Tests.Ix.Compile.Pass3.leanRejects.contains stem then
      work := work.push (stem, Tests.Ix.Compile.Pass3.unitOfFile p)
  if want "twins" then
    work := work.push ("twins", do
      let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
      pure { name := "twins", env, seeds, closure := Tests.Ix.Compile.Pass3.closureOf env seeds.toList })
  if want "corpus" then
    work := work.push ("corpus", do
      let closure := Tests.Ix.Compile.Pass3.closureOf env ((validateAuxClosure env).map (·.1))
      pure { name := "corpus", env, seeds := (closure.map (·.1)).toArray, closure })
  for (stem, mk) in work do
    try
      let u ← mk
      let on ← Tests.Ix.Compile.Pass3.compileUnit u
      let r := runCompiled on.cenv
      units := units + 1
      for l in summary stem r do IO.println s!"[dev-census] {l}"
      all := { rows := all.rows ++ r.rows, problems := all.problems ++ r.problems.map (s!"{stem}: " ++ ·),
               blocks := all.blocks + r.blocks, heads := all.heads + r.heads,
               refused := all.refused + r.refused }
    catch e =>
      IO.println s!"[dev-census] {stem}: compile refused ({(toString e).take 160})"
  if want "initstd" then
    let ienv ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
    let whole := ienv.constants.toList
    let input ← IO.ofExcept ((_root_.Ix.Compile.compileInputFromEnv ienv whole).mapError toString)
    match ← _root_.Ix.CompileM.compileLeanInput input (numWorkers := 32) with
    | .ok o =>
      let r := runCompiled o.cenv
      units := units + 1
      IO.println s!"[dev-census] initstd: {whole.length} constants"
      for l in summary "initstd" r do IO.println s!"[dev-census] {l}"
      all := { rows := all.rows ++ r.rows, problems := all.problems ++ r.problems,
               blocks := all.blocks + r.blocks, heads := all.heads + r.heads }
    | .error e => IO.println s!"[dev-census] initstd: compile failed: {e}"
  for l in summary "TOTAL" all do IO.println s!"[dev-census] {l}"
  IO.println s!"[dev-census] {units} units, {all.rows.size} developments, {all.problems.size} problem(s)"
  let bad := all.rows.filter fun r => !r.ok || r.coreEq == some false
  return if bad.isEmpty && all.problems.isEmpty && !omegaOk && idOk then 0 else 1

end Tests.Ix.Compile.DevCensus
