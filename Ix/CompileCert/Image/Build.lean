import Ix.CompileCert.Image.Fuel

/-!
# M7 L2a-syn: the image construction with its developments as a parameter

`Ix/Compile/Image/Build.lean` builds the image of a Lean recursor (`imageOf`, `buildRecApp`) in
`GenM` and calls the development twice: `substFVars` (the motive wrappers into the canonical minor
types; the indices and major into the rule types) and `instantiate` (the rule right-hand sides at
the opened telescope). Both are the hash-tabled executables of `Ix/Compile/Image/Develop.lean`.

Here the two functions that call the development are restated clause by clause with the
development as a parameter `D : DevOps`; everything else (`findElim`, `elimMotiveTypes`,
`analyzeCanonMinor`, the packing) is the compiler's own function, called as it is.

* `imageOf_eq`, `buildRecApp_eq`: **the executable is the instance at the executables**
  (`execDev`), by `rfl`: the restatement is the code;
* `imageOfP := imageOfW coreDev`: the instance at X1's table-free core (`substFVarsP`,
  `instantiateP`), the function every theorem of this package is about. The two instances agree
  wherever the tabled development agrees with the core on the calls made: that is X1's refactor
  R-1, the pending agreement between the tabled development and its table-free core, not proved
  here; the census (`dev-census`)
  found them equal on every P3a development of the `pass3` fixtures, and `l2a-syn` (tests)
  compares `imageOfP` with `imageOf` image by image.

Hash-free: the construction compares names with `==` (`Ix.Name`'s hash equality) in `alphaEq`,
`fvarIdx?`, `findIdx?`, `idxOf?` and `contains`; the theorems take the hypotheses under which
`==` is equality on the names involved (the reserved fresh names pairwise distinct, `NamesOK`;
L1's distinctness of the block's names), as L1 does.
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels normalizeLevel)
open Ix.Compile.Image

/-- The two development calls of the image construction. -/
structure DevOps where
  subst : Array Name → Array Expr → Expr → Except String Expr
  inst : Expr → Array Expr → Except String Expr

/-- The executables (`Ix/Compile/Image/Develop.lean`, hash-tabled). -/
def execDev : DevOps := ⟨substFVars, instantiate⟩

/-- X1's table-free core. -/
def coreDev : DevOps := ⟨Ix.CompileCert.Conv.substFVarsP, Ix.CompileCert.Conv.instantiateP⟩

/-- `Ix.Compile.Image.buildRecApp` with the development `D`. -/
def buildRecAppW (D : DevOps) : Nat → LCtx → Nat → Array Expr → Expr → GenM Expr
  | 0, _, t, _, _ => throw s!"image: relocation bound exhausted at Lean motive {t}"
  | fuel + 1, c, t, idx, major => do
    let e ← findElim c t
    let rv ← Ix.Compile.Image.liftExcept (recOf c.const? e.recName)
    let mts ← elimMotiveTypes c.const? e.ind e.indLevels e.params
    -- step 1: slot classes
    let classes := c.slotClasses mts
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
    let rty ← Ix.Compile.Image.liftExcept (instForall (substLevels rv.cnst.levelParams us rv.cnst.type) e.params)
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
      motives := motives.push (etaReduce (mkLambda isy (← Ix.Compile.Image.liftExcept (wrapTy (← GenM.idx packs i "buildRecApp: slot pack") c.lu apps))))
    -- step 4: minors
    let mut minors : Array Expr := #[]
    for minC in minsC do
      let (mi, ctor, nf, ihFields) ← analyzeCanonMinor c.const? msC minC.type
      let mty ← Ix.Compile.Image.liftExcept (D.subst (msC.map (·.fvar)) motives minC.type)
      let (bs, _) ← telescope mty
      let flds := bs.extract 0 nf
      let ihsC := bs.extract nf bs.size
      let mut comps : Array (Expr × Expr) := #[]
      for j in (← GenM.idx classes mi "buildRecApp: minor slot class") do
        let some lmi := c.minors.findIdx? (fun lm => lm.motive == j && lm.ctor == ctor)
          | throw s!"image: no Lean minor for motive {j} and constructor {ctor.pretty}"
        let lm ← GenM.idx c.mins lmi "buildRecApp: Lean minor"
        let mut lty ← Ix.Compile.Image.liftExcept (instForall lm.type (flds.map (·.expr)))
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
                let v ← buildRecAppW D fuel c t' idx' arg
                pure (mkLambda ys v)
            ihVals := ihVals.push v
            lty := instLocals body #[v]
          | _ => throw "image: Lean minor arity"
        comps := comps.push (mkAppN lm.expr (flds.map (·.expr) ++ ihVals), lty)
      minors := minors.push (etaReduce (mkLambda bs (← Ix.Compile.Image.liftExcept (wrapVal (← GenM.idx packs mi "buildRecApp: minor slot pack") c.lu comps))))
    -- step 5
    let app := mkAppN recC (e.params ++ motives ++ minors ++ idx ++ #[major])
    let some pos := (← GenM.idx classes e.k "buildRecApp: eliminated slot class").idxOf? t | throw "image: eliminated motive not in its class"
    return unwrap (← GenM.idx packs e.k "buildRecApp: eliminated slot pack") luZero pos app

/-- The program of `Ix.Compile.Image.imageOf` with the development `D`, before it is run from the
initial state. -/
def imageProgW (D : DevOps) (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec)
    (r : Name) : GenM Image := do
  let rv ← Ix.Compile.Image.liftExcept (recOf const? r)
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
  let ind ← Ix.Compile.Image.liftExcept (indOf const? a0)
  let c : LCtx := {
    const?, spec, opts, ps, ms, mins
    motiveTys := ms.map fun m => stripSort m.type
    minors
    lu := motiveLevel m0.type
    indLevels := ind.cnst.levelParams.map Level.mkParam }
  let some t := fvarIdx? ms (getAppFn body) | throw "image: recursor's conclusion"
  let v ← buildRecAppW D (nm + 1) c t (is.map (·.expr)) x.expr
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
    let cv ← Ix.Compile.Image.liftExcept (ctorOf const? rule.ctor)
    let cParams := (getAppArgs T).extract 0 cv.numParams
    let ctorC := Expr.mkConst (spec.trName rule.ctor) tLvls
    let cty ← Ix.Compile.Image.liftExcept (instForall
      (substLevels cv.cnst.levelParams tLvls (spec.tr cv.cnst.type)) cParams)
    let (flds, cres) ← telescope cty
    let idx := (getAppArgs cres).extract cv.numParams (getAppArgs cres).size
    let major := mkAppN ctorC (cParams ++ flds.map (·.expr))
    let lhs := mkAppN imgC (pmm.map (·.expr) ++ idx ++ #[major])
    let rhs ← Ix.Compile.Image.liftExcept (D.inst (trRule rule.rhs) (pmm.map (·.expr) ++ flds.map (·.expr)))
    let α ← Ix.Compile.Image.liftExcept (D.subst ((is.push x).map (·.fvar)) (idx.push major) body)
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

/-- `Ix.Compile.Image.imageOf` with the development `D`. -/
def imageOfW (D : DevOps) (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec)
    (r : Name) : Except String Image := GenM.run' (imageProgW D opts const? spec r)

/-- **The executable relocation step is the restatement at the executables.** -/
theorem buildRecApp_eq : ∀ (fuel : Nat) (c : LCtx) (t : Nat) (idx : Array Expr) (major : Expr),
    buildRecApp fuel c t idx major = buildRecAppW execDev fuel c t idx major
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, t, idx, major => by
    unfold buildRecApp buildRecAppW
    simp only [buildRecApp_eq fuel]
    rfl

/-- **The executable image construction is the restatement at the executables.** -/
theorem imageOf_eq (opts : GenOptions) (const? : Name → Option ConstantInfo) (spec : ImageSpec)
    (r : Name) : imageOf opts const? spec r = imageOfW execDev opts const? spec r := by
  unfold imageOf imageOfW imageProgW
  simp only [buildRecApp_eq]
  rfl

/-- The image construction at X1's table-free development: what this package proves things of. -/
def imageOfP : GenOptions → (Name → Option ConstantInfo) → ImageSpec → Name → Except String Image :=
  imageOfW coreDev

def buildRecAppP : Nat → LCtx → Nat → Array Expr → Expr → GenM Expr := buildRecAppW coreDev

end Ix.CompileCert.Img
