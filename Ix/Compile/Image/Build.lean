/-
  Ix.Compile.Image.Build: the image of a Lean recursor over the canonical
  recursors (design document §4.1-§4.4, Def 3.3-3.4), its computation-rule
  statements, and its call-site forms (§4.5, Q11).

  Input: a lookup `const?` holding the Lean block (its recursors, inductives
  and constructors), the canonical blocks' inductives, constructors and
  recursors (Pass 2's output; their types are the specification's `recTy`),
  and the external inductives the types mention; and the block's
  `ImageSpec` (Pass 1's canonical form with placeholder names).

  Output, per Lean recursor `r`: `img(r)`, a closed term with type
  `tr_N(type r)` built from the canonical recursors' *types* only, already
  developed (§4.3, P3a), and one statement per computation rule of `r`,
  `∀ ps ms mins fs, img(r) ps ms mins is (c fs) = tr_N(rhs) ps ms mins fs`,
  with its proof `Eq.refl` (it holds by `rfl`: the tests check every one in
  Lean's kernel).

  The construction follows the prototype's `buildTransport`
  (`exp-prototype/CertProto/Lib.lean:136-357`) step by step; the differences
  are the term representation (`Ix.Expr`, locally nameless, no `MetaM`), the
  development (hereditary substitution while building instead of
  `Core.betaReduce` afterwards; the same result on these terms, since the
  only redexes are the motives substituted into the canonical minor types),
  the relocation bound (below) and the levels of the `PProd` packing
  (`normalizeLevel`, which is what Lean's `instantiateLevelParams` yields
  for the packings that occur).

  Relocation (`buildRecApp` calling itself for a field without a canonical
  hypothesis) is bounded by the number of Lean motives plus one: along one
  chain of relocations the eliminators are pairwise distinct (a field whose
  type is a motive type of the current eliminator has a hypothesis there),
  and each is `elim(t)` for a distinct Lean motive `t`. Exhausting the bound
  is an error naming the motive, never a silent result.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Image.Expr
public import Ix.Compile.Image.Develop
public import Ix.Compile.Image.Spec
public section

namespace Ix.Compile.Image

open Ix (Name Level Expr ConstantInfo InductiveVal ConstructorVal RecursorVal)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels normalizeLevel)

/-- Ablations, for the tests' negative controls only (the prototype's
`naive_elim` and `no_lift` variants). Both off is the construction. -/
structure GenOptions where
  /-- Try the type's head recursor first (violates the container rule). -/
  naiveElim : Bool := false
  /-- Do not lift singleton slots next to a tuple (violates the mixed-class
  rule). -/
  noLift : Bool := false
  deriving Inhabited

/-! ## Lookups -/

def recOf (const? : Name → Option ConstantInfo) (n : Name) : Except String RecursorVal :=
  match const? n with
  | some (.recInfo v) => pure v
  | some c => throw s!"image: {n.pretty} is not a recursor ({c.getCnst.name.pretty})"
  | none => throw s!"image: no recursor {n.pretty}"

def ctorOf (const? : Name → Option ConstantInfo) (n : Name) : Except String ConstructorVal :=
  match const? n with
  | some (.ctorInfo v) => pure v
  | _ => throw s!"image: {n.pretty} is not a constructor"

def mkRecName (n : Name) : Name := Ix.Name.mkStr n "rec"

/-- The recursor of motive slot `k` of the block `all` (member recursors,
then `all₀.rec_j` for the nested auxiliaries). -/
def recNameFor (all : Array Name) (k : Nat) : Name :=
  if h : k < all.size then mkRecName all[k]
  else match all[0]? with
    | some a => Ix.Name.mkStr a s!"rec_{k - all.size + 1}"
    | none => Ix.Name.mkAnon

/-- Lean's recursors of a block: the members' `rec`, then `all₀.rec_j`. -/
def blockRecursors (const? : Name → Option ConstantInfo) (iv : InductiveVal) : Array Name :=
  let mem := iv.all.map mkRecName
  let aux := match iv.all[0]? with
    | some a => (List.range iv.numNested).toArray.map fun i => Ix.Name.mkStr a s!"rec_{i + 1}"
    | none => #[]
  (mem ++ aux).filter fun r => (const? r).isSome

def getAppFn (e : Expr) : Expr := (getAppFnArgs e).1
def getAppArgs (e : Expr) : Array Expr := (getAppFnArgs e).2

/-! ## The Lean side -/

/-- A Lean minor: its motive and its constructor (renamed). -/
structure LeanMinor where
  motive : Nat
  ctor : Name
  deriving Inhabited

/-- The Lean recursor, opened: `tr_N(type r)`'s telescope and what the
construction reads from it. -/
structure LCtx where
  const? : Name → Option ConstantInfo
  spec : ImageSpec
  opts : GenOptions
  ps : Array Local
  ms : Array Local
  mins : Array Local
  /-- Motive types up to their sort. -/
  motiveTys : Array Expr
  minors : Array LeanMinor
  /-- The universe of Lean's motives. -/
  lu : Level
  /-- The Lean block's universe parameters, as levels. -/
  indLevels : Array Level

def analyzeLeanMinor (ms : Array Local) (ty : Expr) : GenM LeanMinor := do
  let (_, concl) ← telescope ty
  let some m := fvarIdx? ms (getAppFn concl) | throw "image: Lean minor's conclusion is not a motive"
  let some a := appArg? concl | throw "image: Lean minor's conclusion has no major"
  let some (c, _) := headConst? a | throw "image: Lean minor's conclusion is not a constructor"
  return { motive := m, ctor := c }

/-! ## Eliminator choice (§4.1, Def 3.3) -/

structure Elim where
  recName : Name
  ind : InductiveVal
  indLevels : Array Level
  params : Array Expr
  /-- The slot of the eliminated type among the eliminator's motives. -/
  k : Nat
  hasElimLevel : Bool

/-- The motive types (up to sort) of the block of `ind` at levels `lvls`
and parameters `ps`. -/
def elimMotiveTypes (const? : Name → Option ConstantInfo) (ind : InductiveVal)
    (lvls : Array Level) (ps : Array Expr) : GenM (Array Expr) := do
  let some a := ind.all[0]? | throw "image: empty block"
  let rv ← liftExcept (recOf const? (mkRecName a))
  let hasU := rv.cnst.levelParams.size > ind.cnst.levelParams.size
  let us := (if hasU then #[lvlZero] else #[]) ++ lvls
  let ty ← liftExcept (instForall (substLevels rv.cnst.levelParams us rv.cnst.type) ps)
  let (msC, _) ← telescope ty rv.numMotives
  return msC.map fun m => stripSort m.type

def isInductive (const? : Name → Option ConstantInfo) (n : Name) : Bool :=
  match const? n with
  | some (.inductInfo _) => true
  | _ => false

/-- `elim(t)`: the first recursor whose motive types contain Lean motive
`t`'s type, from (1) the canonical blocks occurring in it, (2) the other
inductives occurring strictly inside it, in `usedConstants` order at the
parameters of their first occurrence, (3) its head. -/
def findElim (c : LCtx) (t : Nat) : GenM Elim := do
  let some m := c.ms[t]? | throw "image: motive index"
  let target ← GenM.idx c.motiveTys t "findElim: motive type"
  let (xs, _) ← telescope m.type
  let some x := xs.back? | throw "image: motive without a major"
  let T := x.type
  let some (H, hLvls) := headConst? T | throw "image: major type's head is not a constant"
  let used := (usedConstants T).filter (isInductive c.const?)
  let occ := fun (i : Name) (np : Nat) =>
    (findSub? (fun e => match headConst? e with
      | some (h, _) => h == i && (getAppArgs e).size ≥ np
      | none => false) T).map fun e =>
        ((getAppArgs e).extract 0 np, (headConst? e).map (·.2) |>.getD #[])
  let mut cands : Array (Name × Array Expr × Array Level) := #[]
  for i in used do
    if c.spec.canonInds.contains i then cands := cands.push (i, c.ps.map (·.expr), c.indLevels)
  for i in used do
    if !c.spec.canonInds.contains i && i != H then
      let iv ← liftExcept (indOf c.const? i)
      if let some (ps, lv) := occ i iv.numParams then cands := cands.push (i, ps, lv)
  let hInfo ← liftExcept (indOf c.const? H)
  cands := cands.push (H, (getAppArgs T).extract 0 hInfo.numParams, hLvls)
  if c.opts.naiveElim then
    if let some b := cands.back? then cands := #[b] ++ cands.pop
  for (i, ps, lv) in cands do
    let ind ← liftExcept (indOf c.const? i)
    if ps.size != ind.numParams then continue
    let mts ← elimMotiveTypes c.const? ind lv ps
    if let some k := mts.findIdx? (alphaEq · target) then
      let rn := recNameFor ind.all k
      let rv ← liftExcept (recOf c.const? rn)
      return { recName := rn, ind, indLevels := lv, params := ps, k,
               hasElimLevel := rv.cnst.levelParams.size > ind.cnst.levelParams.size }
  throw s!"image: no eliminator for Lean motive {t}"

/-! ## Packing (§4.2, step 3) -/

/-- How a slot packs its class: one motive, one motive lifted next to a
tuple (`PProd m True`), or a tuple of `n`. -/
inductive Pack where
  | single
  | lift
  | tuple (n : Nat)
  deriving Inhabited, BEq, Repr

/-- `a ×' b` or `a ∧ b` (Lean's `mkPProd`), with the levels of `a` and `b`;
returns the pair and its level. -/
def mkPProdTy (a : Expr × Level) (b : Expr × Level) : Expr × Level :=
  if isAlwaysZero a.2 && isAlwaysZero b.2 then
    (mkAppN (Expr.mkConst nAnd #[]) #[a.1, b.1], lvlZero)
  else
    (mkAppN (Expr.mkConst nPProd #[a.2, b.2]) #[a.1, b.1],
     normalizeLevel (Level.mkMax (Level.mkMax lvlOne a.2) b.2))

/-- `⟨a, b⟩` (Lean's `mkPProdMk`): value, type, level of each side; returns
the pair's value, type and level. -/
def mkPProdVal (a : Expr × Expr × Level) (b : Expr × Expr × Level) : Expr × Expr × Level :=
  let (ty, l) := mkPProdTy (a.2.1, a.2.2) (b.2.1, b.2.2)
  if isAlwaysZero a.2.2 && isAlwaysZero b.2.2 then
    (mkAppN (Expr.mkConst nAndIntro #[]) #[a.2.1, b.2.1, a.1, b.1], ty, l)
  else
    (mkAppN (Expr.mkConst nPProdMk #[a.2.2, b.2.2]) #[a.2.1, b.2.1, a.1, b.1], ty, l)

/-- Right-nested fold of a non-empty array (`PProdN.genMk`). -/
def foldr1 {α} (f : α → α → α) (xs : Array α) (d : α) : α :=
  match xs.back? with
  | none => d
  | some last => xs.pop.foldr f last

/-- The packed motive body of a slot from its class's motive applications
(all at level `lu`). -/
def wrapTy (p : Pack) (lu : Level) (tys : Array Expr) : Except String Expr :=
  match p, tys[0]? with
  | .single, some t => pure t
  | .lift, some t => pure (mkAppN (Expr.mkConst nPProd #[lu, lvlZero]) #[t, Expr.mkConst nTrue #[]])
  | .tuple _, _ => pure (foldr1 mkPProdTy (tys.map (·, lu)) (default, lu)).1
  | _, none => throw "image: wrapTy: empty slot class"

/-- The packed minor body from the class members' values and their types. -/
def wrapVal (p : Pack) (lu : Level) (vs : Array (Expr × Expr)) : Except String Expr :=
  match p, vs[0]? with
  | .single, some v => pure v.1
  | .lift, some v =>
    pure (mkAppN (Expr.mkConst nPProdMk #[lu, lvlZero])
      #[v.2, Expr.mkConst nTrue #[], v.1, Expr.mkConst nTrueIntro #[]])
  | .tuple _, _ => pure (foldr1 mkPProdVal (vs.map fun (v, t) => (v, t, lu)) (default, default, lu)).1
  | _, none => throw "image: wrapVal: empty slot class"

/-- Component `pos` of a packed slot (`PProdN.proj` with primitive
projections; `.1` of a lift). -/
def unwrap (p : Pack) (luZero : Bool) (pos : Nat) (v : Expr) : Expr :=
  match p with
  | .single => v
  | .lift => Expr.mkProj nPProd 0 v
  | .tuple n =>
    let s := if luZero then nAnd else nPProd
    let v := (List.range pos).foldl (fun v _ => Expr.mkProj s 1 v) v
    if pos + 1 < n then Expr.mkProj s 0 v else v

/-! ## The construction (§4.2, steps 1-5) -/

/-- A canonical minor's shape: its slot, constructor, field count, and the
fields that have a hypothesis with the hypothesis's slot. -/
def analyzeCanonMinor (const? : Name → Option ConstantInfo) (msC : Array Local) (ty : Expr) :
    GenM (Nat × Name × Nat × Array (Nat × Nat)) := do
  let (bs, concl) ← telescope ty
  let some mi := fvarIdx? msC (getAppFn concl) | throw "image: canonical minor's conclusion"
  let some a := appArg? concl | throw "image: canonical minor's major"
  let some (ctor, _) := headConst? a | throw "image: canonical minor's constructor"
  let nf := (← liftExcept (ctorOf const? ctor)).numFields
  let flds := bs.extract 0 nf
  let mut ihFields : Array (Nat × Nat) := #[]
  for ih in bs.extract nf bs.size do
    let (_, cc) ← telescope ih.type
    let some m := fvarIdx? msC (getAppFn cc) | throw "image: canonical hypothesis head"
    let some fa := appArg? cc | throw "image: canonical hypothesis major"
    let some f := fvarIdx? flds (getAppFn fa) | throw "image: canonical hypothesis field"
    ihFields := ihFields.push (f, m)
  return (mi, ctor, nf, ihFields)

/-- `ρ.{ℓ} params motives′ minors′ idx major`, unwrapped at Lean motive `t`:
the image body for the type of motive `t` at indices `idx` and major
`major`. -/
def buildRecApp : Nat → LCtx → Nat → Array Expr → Expr → GenM Expr
  | 0, _, t, _, _ => throw s!"image: relocation bound exhausted at Lean motive {t}"
  | fuel + 1, c, t, idx, major => do
    let e ← findElim c t
    let rv ← liftExcept (recOf c.const? e.recName)
    let mts ← elimMotiveTypes c.const? e.ind e.indLevels e.params
    -- step 1: slot classes
    let classes : Array (Array Nat) := mts.map fun mt =>
      (c.motiveTys.zipIdx.filter fun (ty, _) => alphaEq ty mt).map (·.2)
    for (cl, i) in classes.zipIdx do
      if cl.isEmpty then
        throw s!"image: eliminator {e.recName.pretty}: slot {i} has no Lean motive"
    -- step 2: the level
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
    let rty ← liftExcept (instForall (substLevels rv.cnst.levelParams us rv.cnst.type) e.params)
    GenM.trace s!"elim for Lean motive {t}: {e.recName.pretty} classes={classes} packs={reprStr packs}"
    let (xs, _) ← telescope rty (rv.numMotives + rv.numMinors)
    let msC := xs.extract 0 rv.numMotives
    let minsC := xs.extract rv.numMotives xs.size
    -- step 3: motives
    let mut motives : Array Expr := #[]
    for h : i in [0:msC.size] do
      let (isy, _) ← telescope msC[i].type
      let apps ← (← GenM.idx classes i "buildRecApp: slot class").mapM fun j => do
        pure (mkAppN (← GenM.idx c.ms j "buildRecApp: Lean motive").expr (isy.map (·.expr)))
      motives := motives.push (etaReduce (mkLambda isy (← liftExcept (wrapTy (← GenM.idx packs i "buildRecApp: slot pack") c.lu apps))))
    -- step 4: minors
    let mut minors : Array Expr := #[]
    for minC in minsC do
      let (mi, ctor, nf, ihFields) ← analyzeCanonMinor c.const? msC minC.type
      let mty ← liftExcept (substFVars (msC.map (·.fvar)) motives minC.type)
      let (bs, _) ← telescope mty
      let flds := bs.extract 0 nf
      let ihsC := bs.extract nf bs.size
      let mut comps : Array (Expr × Expr) := #[]
      for j in (← GenM.idx classes mi "buildRecApp: minor slot class") do
        let some lmi := c.minors.findIdx? (fun lm => lm.motive == j && lm.ctor == ctor)
          | throw s!"image: no Lean minor for motive {j} and constructor {ctor.pretty}"
        let lm ← GenM.idx c.mins lmi "buildRecApp: Lean minor"
        let mut lty ← liftExcept (instForall lm.type (flds.map (·.expr)))
        let mut ihVals : Array Expr := #[]
        for _ in [0:forallArity lty] do
          match Ix.Compile.Canon.stripMdata lty with
          | .forallE _ bt body _ _ =>
            let (ys, cc) ← telescope bt
            let some t' := fvarIdx? c.ms (getAppFn cc) | throw "image: Lean hypothesis head"
            let some arg := appArg? cc | throw "image: Lean hypothesis major"
            let idx' := (getAppArgs cc).pop
            let some f := fvarIdx? flds (getAppFn arg) | throw "image: Lean hypothesis field"
            let v ← match ihFields.findIdx? (·.1 == f) with
              | some q => do
                let mq := (← GenM.idx ihFields q "buildRecApp: hypothesis field").2
                let some pos := (← GenM.idx classes mq "buildRecApp: hypothesis slot class").idxOf? t'
                  | throw s!"image: hypothesis motive {t'} not in its slot's class"
                pure (mkLambda ys (unwrap (← GenM.idx packs mq "buildRecApp: hypothesis slot pack") luZero pos
                  (mkAppN (← GenM.idx ihsC q "buildRecApp: canonical hypothesis").expr (ys.map (·.expr)))))
              | none => do
                -- a relocated hypothesis: the image construction for the field's type
                let v ← buildRecApp fuel c t' idx' arg
                pure (mkLambda ys v)
            ihVals := ihVals.push v
            lty := instLocals body #[v]
          | _ => throw "image: Lean minor arity"
        comps := comps.push (mkAppN lm.expr (flds.map (·.expr) ++ ihVals), lty)
      minors := minors.push (etaReduce (mkLambda bs (← liftExcept (wrapVal (← GenM.idx packs mi "buildRecApp: minor slot pack") c.lu comps))))
    -- step 5
    let app := mkAppN recC (e.params ++ motives ++ minors ++ idx ++ #[major])
    let some pos := (← GenM.idx classes e.k "buildRecApp: eliminated slot class").idxOf? t | throw "image: eliminated motive not in its class"
    return unwrap (← GenM.idx packs e.k "buildRecApp: eliminated slot pack") luZero pos app

/-! ## Images and their computation rules -/

/-- One computation rule of `r`, stated over `img(r)`. -/
structure RuleStmt where
  /-- The Lean constructor of the rule. -/
  ctor : Name
  /-- `img(r).iota_<ctor>`. -/
  name : Name
  levelParams : Array Name
  /-- `∀ ps ms mins fs, img(r) ps ms mins is (c fs) = rhs`. -/
  type : Expr
  /-- `λ ps ms mins fs, Eq.refl _`. -/
  proof : Expr
  deriving Inhabited

/-- The image of a Lean recursor. -/
structure Image where
  leanRec : Name
  /-- The image constant (placeholder name). -/
  name : Name
  levelParams : Array Name
  /-- `tr_N(type r)`. -/
  type : Expr
  /-- A λ over Lean's telescope: the image constant's value, and the eta
  adapter of bare and partial occurrences (Q11). -/
  value : Expr
  numParams : Nat
  numMotives : Nat
  numMinors : Nat
  numIndices : Nat
  rules : Array RuleStmt
  /-- The eliminator choices made (one line per `buildRecApp`). -/
  log : Array String
  deriving Inhabited

/-- Arguments of a full application: parameters, motives, minors, indices
and the major. -/
def Image.arity (img : Image) : Nat :=
  img.numParams + img.numMotives + img.numMinors + img.numIndices + 1

/-- The developed body of `img us args` at a full application
(`args.size ≥ arity`; later arguments stay applied), or `none` for a bare or
partial one. -/
def Image.inline (img : Image) (us : Array Level) (args : Array Expr) :
    Except String (Option Expr) :=
  if args.size < img.arity then pure none
  else some <$> instantiate (substLevels img.levelParams us img.value) args

/-- A bare or partial occurrence: the image constant itself is the eta
adapter (Q11). -/
def Image.adapter (img : Image) (us : Array Level) (args : Array Expr) : Expr :=
  mkAppN (Expr.mkConst img.name us) args

/-- The rewrite of an occurrence `r.{us} args`: inline at full application,
the image constant otherwise. -/
def Image.rewrite (img : Image) (us : Array Level) (args : Array Expr) : Except String Expr := do
  match ← img.inline us args with
  | some e => pure e
  | none => pure (img.adapter us args)

def lastStr : Name → String
  | .str _ s _ => s
  | _ => ""

/-- The image of Lean recursor `r` of the block of `spec`. -/
def imageOf (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec)
    (r : Name) : Except String Image := GenM.run' do
  let rv ← liftExcept (recOf const? r)
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
  let ind ← liftExcept (indOf const? a0)
  let c : LCtx := {
    const?, spec, opts, ps, ms, mins
    motiveTys := ms.map fun m => stripSort m.type
    minors
    lu := motiveLevel m0.type
    indLevels := ind.cnst.levelParams.map Level.mkParam }
  let some t := fvarIdx? ms (getAppFn body) | throw "image: recursor's conclusion"
  let v ← buildRecApp (nm + 1) c t (is.map (·.expr)) x.expr
  let value := mkLambda xs v
  let name := spec.naming.img r
  -- computation rules
  let lps := rv.cnst.levelParams
  let imgC := Expr.mkConst name (lps.map Level.mkParam)
  let pmm := xs.extract 0 (np + nm + nmin)
  let T := x.type
  let some (_, tLvls) := headConst? T | throw "image: major type's head"
  -- the right-hand sides call the block's recursors: those are their images (Def 3.5)
  let recMap : Std.HashMap Name Name := (blockRecursors const? ind).foldl
    (fun m r => m.insert r (spec.naming.img r)) {}
  let trRule := fun (e : Expr) => Ix.Compile.Canon.canonicalizeConstNames recMap (spec.tr e)
  let mut rules : Array RuleStmt := #[]
  for rule in rv.rules do
    let cv ← liftExcept (ctorOf const? rule.ctor)
    let cParams := (getAppArgs T).extract 0 cv.numParams
    let ctorC := Expr.mkConst (spec.trName rule.ctor) tLvls
    let cty ← liftExcept (instForall
      (substLevels cv.cnst.levelParams tLvls (spec.tr cv.cnst.type)) cParams)
    let (flds, cres) ← telescope cty
    let idx := (getAppArgs cres).extract cv.numParams (getAppArgs cres).size
    let major := mkAppN ctorC (cParams ++ flds.map (·.expr))
    let lhs := mkAppN imgC (pmm.map (·.expr) ++ idx ++ #[major])
    let rhs ← liftExcept (instantiate (trRule rule.rhs) (pmm.map (·.expr) ++ flds.map (·.expr)))
    let α ← liftExcept (substFVars ((is.push x).map (·.fvar)) (idx.push major) body)
    let eq := mkAppN (Expr.mkConst nEq #[c.lu]) #[α, lhs, rhs]
    let refl := mkAppN (Expr.mkConst nEqRefl #[c.lu]) #[α, lhs]
    rules := rules.push {
      ctor := rule.ctor
      name := Ix.Name.mkStr name s!"iota_{lastStr rule.ctor}"
      levelParams := lps
      type := mkForall (pmm ++ flds) eq
      proof := mkLambda (pmm ++ flds) refl }
  let log := (← get).log
  return { leanRec := r, name, levelParams := lps, type := ty, value
           numParams := np, numMotives := nm, numMinors := nmin, numIndices := rv.numIndices
           rules, log }

/-- The images of every Lean recursor of the block containing `member`. -/
def imagesOfBlock (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec)
    (member : Name) : Except String (Array Image) := do
  let iv ← indOf const? member
  (blockRecursors const? iv).mapM (imageOf opts const? spec)

end Ix.Compile.Image

end
