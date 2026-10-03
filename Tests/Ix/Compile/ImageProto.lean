/-
  The prototype's generic machinery (`plans/review/auxgen-certify/exp-prototype/CertProto/Lib.lean`,
  Lean-view prototype, PRO), kept verbatim apart from the result log and the deprecated `levelZero`/`levelOne` spellings (rows go to `rowsRef` and the
  per-case log to `logRef` instead of `out/results.tsv`), so that the image-gen test can

  * compare the pure generator's images with the prototype's hand-built transports
    (`buildTransport`, `iotaStatements`), and
  * build the Lean view over the generated images exactly as the prototype did (`copyAll`, `nf`).

  This is test code: it uses `MetaM` and `partial`, which the generator (`Ix.Compile.Image`) does not.
-/
import Lean
open Lean Meta Elab Command

namespace Tests.Ix.Compile.ImageProto

structure Spec where
  caseName : String
  srcNs : Name
  viewNs : Name
  canNs : Name
  tyMap : Array (Name × Name)
  ctorMap : Array (Name × Name)
  users : Array Name      -- short names (relative to srcNs) of user declarations
  /-- ablations: "naive_elim" (eliminate every Lean type by its head inductive's recursor first),
  "no_lift" (do not lift singleton classes when a tuple raises the eliminator level) -/
  variant : String := ""
  deriving Inhabited

def Spec.trName (s : Spec) (n : Name) : Name :=
  match s.tyMap.find? (·.1 == n) with
  | some (_, m) => m
  | none => match s.ctorMap.find? (·.1 == n) with
    | some (_, m) => m
    | none =>
      let u := (privateToUserName? n).getD n
      if s.srcNs.isPrefixOf u then u.replacePrefix s.srcNs s.viewNs else n

def Spec.trExpr (s : Spec) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (s.trName n) ls)
    | _ => none

def Spec.isUser (s : Spec) (n : Name) : Bool :=
  s.users.any fun u => n == s.srcNs ++ u || n == s.viewNs ++ u || n == s.canNs ++ u

/-! ## result log -/

/-- One verdict: case, tag, name, verdict, message. -/
structure Row where
  case : String
  tag : String
  name : String
  verdict : String
  msg : String

initialize rowsRef : IO.Ref (Array Row) ← IO.mkRef #[]
initialize logRef : IO.Ref (Array (String × String)) ← IO.mkRef #[]

def oneLine (s : String) : String :=
  let s := s.replace "\n" " " |>.replace "\t" " "
  if s.length > 1500 then (s.take 1500).toString ++ "…" else s

def record (case tag name verdict msg : String) : CoreM Unit := do
  rowsRef.modify (·.push { case, tag, name, verdict, msg := oneLine msg })

def appendLog (case : String) (msg : String) : CoreM Unit := do
  logRef.modify (·.push (case, msg))

/-- constants of `ns` that are fallback axioms (= a rejected declaration) in the closure of `n`. -/
partial def rejectedDeps (ns : Name) (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let rec go (todo : List Name) (seen : NameSet) (acc : Array Name) : Array Name :=
    match todo with
    | [] => acc
    | c :: rest =>
      if seen.contains c then go rest seen acc else
      let seen := seen.insert c
      match env.find? c with
      | none => go rest seen acc
      | some ci =>
        let acc := if c != n && ns.isPrefixOf c && ci matches .axiomInfo _ then acc.push c else acc
        let deps := (ci.getUsedConstantsAsSet.toList.filter fun d => ns.isPrefixOf d)
        go (deps ++ rest) seen acc
  return go [n] {} #[]

/-- Add through the kernel; returns `none` on acceptance, the kernel message on rejection.
(Lean's `addDecl` then adds a fallback axiom so that later declarations can still be tried.) -/
def kernelAdd (decl : Declaration) : CoreM (Option String) := do
  try
    withOptions (fun o => o.setBool `Elab.async false) do addDecl decl
    return none
  catch e =>
    return some (← e.toMessageData.toString)

def addAndRecord (s : Spec) (tag : String) (decl : Declaration) (name : Name) : CoreM Bool := do
  match ← kernelAdd decl with
  | none =>
    let deps ← rejectedDeps s.viewNs name
    if deps.isEmpty then
      record s.caseName tag name.toString "ACCEPT" ""
    else
      record s.caseName tag name.toString "ACCEPT*" s!"(depends on rejected {deps})"
    return true
  | some msg =>
    let deps ← rejectedDeps s.viewNs name
    record s.caseName tag name.toString "REJECT" (msg ++ (if deps.isEmpty then "" else s!" (depends on rejected {deps})"))
    return false

def lastStr : Name → String
  | .str _ s => s
  | _ => ""

/-! ## motive types up to their sort -/

partial def stripSort : Expr → Expr
  | .forallE n t b bi => .forallE n t (stripSort b) bi
  | .sort _ => .sort 0
  | e => e

/-- sort level at the end of a motive type -/
partial def motiveLevel : Expr → Level
  | .forallE _ _ b _ => motiveLevel b
  | .sort l => l
  | _ => Level.zero

/-! ## the transport builder -/

structure LeanMinor where
  motive : Nat
  ctor : Name
  deriving Inhabited

structure LCtx where
  spec : Spec
  ps : Array Expr
  ms : Array Expr
  mins : Array Expr
  motiveTys : Array Expr       -- stripped
  minors : Array LeanMinor
  lu : Level                   -- Lean motive universe
  indLevels : List Level       -- Lean inductive universe levels (as params)
  log : IO.Ref (Array String)

def analyzeMinor (ms : Array Expr) (ty : Expr) : MetaM LeanMinor :=
  forallTelescope ty fun _ concl => do
    let some m := ms.idxOf? concl.getAppFn | throwError "minor conclusion head is not a motive: {concl}"
    let some c := concl.appArg!.getAppFn.constName? | throwError "minor conclusion is not a ctor app: {concl}"
    return { motive := m, ctor := c }

structure Elim where
  recName : Name
  indInfo : InductiveVal
  indLevels : List Level
  params : Array Expr
  k : Nat           -- motive index of the eliminated type in this eliminator
  hasElimLevel : Bool
  deriving Inhabited

def recNameFor (all : List Name) (k : Nat) : Name :=
  if h : k < all.length then mkRecName all[k] else
    (mkRecName all[0]!).appendIndexAfter (k - all.length + 1)

/-- motive types (stripped) of the recursor of `ind`'s block at params `ps` -/
def elimMotiveTypes (ind : InductiveVal) (lvls : List Level) (ps : Array Expr) : MetaM (Array Expr) := do
  let rv ← getConstInfoRec (mkRecName ind.all[0]!)
  let hasU := rv.levelParams.length > ind.levelParams.length
  let us := (if hasU then [Level.zero] else []) ++ lvls
  let ty ← instantiateForall (rv.type.instantiateLevelParams rv.levelParams us) ps
  forallBoundedTelescope ty rv.numMotives fun msC _ => msC.mapM fun m => return stripSort (← inferType m)

/-- find the eliminator for Lean motive `t`.  Candidates, in order: canonical blocks occurring in
the renamed type (their nested auxiliaries included); other containers occurring strictly inside
it (so `List (Rose B)` is eliminated by `Rose.rec_1`, consistently with `Rose.rec`); the head. -/
def findElim (c : LCtx) (t : Nat) : MetaM Elim := do
  let mty := (← inferType c.ms[t]!)
  let target := c.motiveTys[t]!
  let T ← forallTelescope mty fun xs _ => inferType xs.back!
  let some H := T.getAppFn.constName? | throwError "major type head not a constant: {T}"
  let canonInds := (c.spec.tyMap.map (·.2)).toList
  let env ← getEnv
  let used := T.getUsedConstants.filter fun n => env.find? n matches some (.inductInfo _)
  let occ (i : Name) (np : Nat) : Option (Array Expr × List Level) :=
    (T.find? fun e => e.getAppFn.isConstOf i && e.getAppNumArgs ≥ np).map fun e =>
      (e.getAppArgs[:np].toArray, e.getAppFn.constLevels!)
  let mut cands : Array (Name × Array Expr × List Level) := #[]
  for i in used do
    if canonInds.contains i then cands := cands.push (i, c.ps, c.indLevels)
  for i in used do
    if !canonInds.contains i && i != H then
      let iv ← getConstInfoInduct i
      if let some (ps, lv) := occ i iv.numParams then cands := cands.push (i, ps, lv)
  let hInfo ← getConstInfoInduct H
  cands := cands.push (H, T.getAppArgs[:hInfo.numParams].toArray, T.getAppFn.constLevels!)
  if c.spec.variant == "naive_elim" then cands := #[cands.back!] ++ cands.pop
  for (i, ps, lv) in cands do
    let ind ← getConstInfoInduct i
    if ps.size != ind.numParams then continue
    let mts ← elimMotiveTypes ind lv ps
    if let some k := mts.idxOf? target then
      let rn := recNameFor ind.all k
      let rv ← getConstInfoRec rn
      return { recName := rn, indInfo := ind, indLevels := lv, params := ps, k,
               hasElimLevel := rv.levelParams.length > ind.levelParams.length }
  throwError "no eliminator found for Lean motive {t}: {target}"

/-- wrap/unwrap conventions of a class: `single` (one Lean motive), `lift` (one Lean motive in an
eliminator whose level had to be raised for a tuple elsewhere: `PProd m True`), `tuple` -/
inductive Pack | single | lift | tuple (n : Nat)
  deriving Inhabited

def unwrap (p : Pack) (pos : Nat) (v : Expr) : MetaM Expr := do
  match p with
  | .single => return v
  | .lift => return .proj ``PProd 0 v
  | .tuple n => return PProdN.proj n pos (← whnf (← inferType v)) v

def wrapTy (p : Pack) (lvl : Level) (lu : Level) (tys : Array Expr) : MetaM Expr := do
  let _ := lu
  match p with
  | .single => return tys[0]!
  | .lift => return mkApp2 (.const ``PProd [lu, Level.zero]) tys[0]! (.const ``True [])
  | .tuple _ => PProdN.pack lvl tys

def wrapVal (p : Pack) (lvl : Level) (lu : Level) (vs : Array Expr) : MetaM Expr := do
  match p with
  | .single => return vs[0]!
  | .lift => return mkApp4 (.const ``PProd.mk [lu, Level.zero]) (← inferType vs[0]!) (.const ``True []) vs[0]! (.const ``True.intro [])
  | .tuple _ => PProdN.mk lvl vs

partial def buildRecApp (c : LCtx) (fuel : Nat) (t : Nat) (idx : Array Expr) (major : Expr) : MetaM Expr := do
  if fuel == 0 then throwError "transport builder: out of fuel"
  let e ← findElim c t
  let rv ← getConstInfoRec e.recName
  let mts ← elimMotiveTypes e.indInfo e.indLevels e.params
  let classes : Array (Array Nat) := mts.map fun mt =>
    (List.range c.ms.size).toArray.filter fun j => c.motiveTys[j]! == mt
  for i in [:classes.size] do
    if classes[i]!.isEmpty then throwError "eliminator {e.recName}: canonical motive {i} has no Lean preimage"
  let anyTuple := classes.any (·.size > 1)
  let luZero := c.lu.isAlwaysZero
  let L : Level := if anyTuple && !luZero then (mkLevelMax Level.one c.lu).normalize else c.lu
  let packs : Array Pack := classes.map fun cl =>
    if cl.size > 1 then .tuple cl.size
    else if anyTuple && !luZero && c.spec.variant != "no_lift" then .lift else .single
  if !e.hasElimLevel && !L.isAlwaysZero then
    throwError "eliminator {e.recName} is small but Lean motive level is {c.lu}"
  let us := (if e.hasElimLevel then [L] else []) ++ e.indLevels
  let recC := Expr.const e.recName us
  let rty ← instantiateForall ((← inferType recC)) e.params
  c.log.modify (·.push s!"  elim for Lean motive {t}: {e.recName} classes={classes} level={L}")
  forallBoundedTelescope rty (rv.numMotives + rv.numMinors) fun xs _ => do
    let msC := xs[:rv.numMotives].toArray
    let minsC := xs[rv.numMotives:].toArray
    -- canonical motives
    let mut motives : Array Expr := #[]
    for i in [:msC.size] do
      let mty ← inferType msC[i]!
      let mot ← forallTelescope mty fun isy _ => do
        let apps := classes[i]!.map fun j => mkAppN c.ms[j]! isy
        mkLambdaFVars isy (← wrapTy packs[i]! L c.lu apps)
      motives := motives.push mot.eta
    -- canonical minors
    let mut minors : Array Expr := #[]
    for minC in minsC do
      let mtyRaw ← inferType minC
      -- structure from the uninstantiated minor type
      let (mi, ctor, nf, ihFields) ← forallTelescope mtyRaw fun bs concl => do
        let some mi := msC.idxOf? concl.getAppFn | throwError "canonical minor conclusion: {concl}"
        let some ctor := concl.appArg!.getAppFn.constName? | throwError "canonical minor ctor: {concl}"
        let ctorArgs := concl.appArg!.getAppArgs
        let nf := (← getConstInfoCtor ctor).numFields
        let flds := bs[:nf].toArray
        let _ := ctorArgs
        let mut ihFields : Array (Nat × Nat) := #[]   -- (field idx, canonical motive idx)
        for ih in bs[nf:] do
          let r ← forallTelescope (← inferType ih) fun _ cc => do
            let some m := msC.idxOf? cc.getAppFn | throwError "IH head {cc}"
            let some f := flds.idxOf? cc.appArg!.getAppFn | throwError "IH field {cc}"
            return (f, m)
          ihFields := ihFields.push r
        return (mi, ctor, nf, ihFields)
      let mty := mtyRaw.replaceFVars msC motives
      let minor ← forallTelescope mty fun bs _ => do
        let flds := bs[:nf].toArray
        let ihsC := bs[nf:].toArray
        let mut comps : Array Expr := #[]
        for j in classes[mi]! do
          let some lmi := c.minors.findIdx? (fun lm => lm.motive == j && lm.ctor == ctor)
            | throwError "no Lean minor for motive {j} ctor {ctor}"
          let lm := c.mins[lmi]!
          let mut lty ← instantiateForall (← inferType lm) flds
          let mut ihVals : Array Expr := #[]
          while lty.isForall do
            let bt := lty.bindingDomain!
            let v ← forallTelescope bt fun ys cc => do
              let some t' := c.ms.idxOf? cc.getAppFn | throwError "Lean IH head {cc}"
              let arg := cc.appArg!
              let idx' := cc.getAppArgs.pop
              let some f := flds.idxOf? arg.getAppFn | throwError "Lean IH field {cc}"
              match ihFields.findIdx? (·.1 == f) with
              | some q =>
                let mq := ihFields[q]!.2
                let some pos := classes[mq]!.idxOf? t' | throwError "IH motive {t'} not in class {classes[mq]!}"
                let v ← unwrap packs[mq]! pos (mkAppN ihsC[q]! ys)
                mkLambdaFVars ys v
              | none =>
                let v ← buildRecApp c (fuel - 1) t' idx' arg
                mkLambdaFVars ys v
            ihVals := ihVals.push v
            lty := lty.bindingBody!.instantiate1 v
          comps := comps.push (mkAppN lm (flds ++ ihVals))
        let body ← wrapVal packs[mi]! L c.lu comps
        mkLambdaFVars bs body
      minors := minors.push minor.eta
    let app := mkAppN recC (e.params ++ motives ++ minors ++ idx ++ #[major])
    let some pos := classes[e.k]!.idxOf? t | throwError "eliminated motive {t} not in its class"
    unwrap packs[e.k]! pos app

/-- Telescope `tr(type of r)` and run `k ps ms mins is x c` -/
def withLeanRec {α} (s : Spec) (r : Name) (k : LCtx → Array Expr → Expr → Nat → MetaM α) : MetaM α := do
  let rv ← getConstInfoRec r
  let ty := s.trExpr rv.type
  forallTelescope ty fun xs body => do
    let np := rv.numParams; let nm := rv.numMotives; let nmin := rv.numMinors
    let ps := xs[:np].toArray
    let ms := xs[np:np+nm].toArray
    let mins := xs[np+nm:np+nm+nmin].toArray
    let is := xs[np+nm+nmin:xs.size-1].toArray
    let x := xs.back!
    let mtys ← ms.mapM fun m => return stripSort (← inferType m)
    let minors ← mins.mapM fun m => do analyzeMinor ms (← inferType m)
    let lu := motiveLevel (← inferType ms[0]!)
    let ind ← getConstInfoInduct rv.all[0]!
    let indLevels := ind.levelParams.map mkLevelParam
    let some t := ms.idxOf? body.getAppFn | throwError "rec body head"
    let log ← IO.mkRef #[]
    let c : LCtx := { spec := s, ps, ms, mins, motiveTys := mtys, minors, lu, indLevels, log }
    let _ := is
    k c xs x t

def buildTransport (s : Spec) (r : Name) : MetaM (Expr × Array String) := do
  withLeanRec s r fun c xs x t => do
    let rv ← getConstInfoRec r
    let is := xs[rv.numParams + rv.numMotives + rv.numMinors : xs.size - 1].toArray
    let body ← buildRecApp c 64 t is x
    let v ← mkLambdaFVars xs body
    let v ← Core.betaReduce v
    return (v, ← c.log.get)

/-- iota statements for recursor `r` (renamed): ∀ ps ms mins fields, r^L … (c fields) = tr(rhs) -/
def iotaStatements (s : Spec) (r : Name) : MetaM (Array (Name × Expr × Expr)) := do
  let rv ← getConstInfoRec r
  let rL := Expr.const (s.trName r) (rv.levelParams.map mkLevelParam)
  withLeanRec s r fun _ xs x _ => do
    let np := rv.numParams; let nm := rv.numMotives; let nmin := rv.numMinors
    let pmm := xs[:np+nm+nmin].toArray
    let T ← inferType x
    let mut out := #[]
    for rule in rv.rules do
      let cv ← getConstInfoCtor rule.ctor
      let cParams := T.getAppArgs[:cv.numParams].toArray
      let ctorC := Expr.const (s.trName rule.ctor) T.getAppFn.constLevels!
      let cty ← instantiateForall (← inferType ctorC) cParams
      let res ← forallTelescope cty fun flds cres => do
        let idx := cres.getAppArgs[cv.numParams:].toArray
        let lhs := mkAppN rL (pmm ++ idx ++ #[mkAppN ctorC (cParams ++ flds)])
        let rhs := (s.trExpr rule.rhs).beta (pmm ++ flds)
        let rhs ← Core.betaReduce rhs
        let eq ← mkEq lhs rhs
        let prf ← mkEqRefl lhs
        return (← mkForallFVars (pmm ++ flds) eq, ← mkLambdaFVars (pmm ++ flds) prf)
      out := out.push ((s.trName r).str s!"iota_{lastStr rule.ctor}", res.1, res.2)
    return out

/-! ## copying -/

def blockRecursors (ind : InductiveVal) : List Name :=
  ind.all.map mkRecName ++ (List.range ind.numNested).map fun i => (mkRecName ind.all[0]!).appendIndexAfter (i+1)

def valueOf : ConstantInfo → Expr
  | .defnInfo d => d.value | .thmInfo t => t.value | .opaqueInfo o => o.value | _ => default

def kindStr : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "ax" | .quotInfo _ => "quot"

def copyDecl (s : Spec) (ci : ConstantInfo) : CoreM Unit := do
  let tag := if s.isUser ci.name then "L" else "V"
  let tr := s.trExpr
  let n := s.trName ci.name
  let env ← getEnv
  let decl? : Option Declaration := match ci with
    | .defnInfo d =>
      let d' : DefinitionVal := { d with name := n, type := tr d.type, value := tr d.value, all := d.all.map s.trName }
      if d.safety != .safe then
        -- partial/unsafe (`_unsafe_rec`) groups are added together
        let ds := d.all.filterMap fun m => match env.find? m with
          | some (.defnInfo dm) => some { dm with name := s.trName m, type := tr dm.type, value := tr dm.value, all := d.all.map s.trName : DefinitionVal }
          | _ => none
        some (.mutualDefnDecl ds)
      else some (.defnDecl d')
    | .thmInfo d => some <| .thmDecl { d with name := n, type := tr d.type, value := tr d.value, all := d.all.map s.trName }
    | .opaqueInfo d => some <| .opaqueDecl { d with name := n, type := tr d.type, value := tr d.value, all := d.all.map s.trName }
    | .axiomInfo d => some <| .axiomDecl { d with name := n, type := tr d.type }
    | _ => none
  match decl? with
  | some decl => discard <| addAndRecord s s!"{tag}:{kindStr ci}" decl n
  | none =>
    match ci with
    | .inductInfo iv =>
      let env ← getEnv
      let types ← iv.all.mapM fun m => do
        let some (.inductInfo mv) := env.find? m | throwError "ind {m}"
        let ctors ← mv.ctors.mapM fun cn => do
          let cv ← getConstInfoCtor cn
          return { name := s.trName cn, type := tr cv.type : Constructor }
        return { name := s.trName m, type := tr mv.type, ctors : InductiveType }
      let decl := Declaration.inductDecl iv.levelParams iv.numParams types iv.isUnsafe
      discard <| addAndRecord s s!"{tag}:ind" decl (s.trName iv.name)
    | _ => pure ()

partial def copyAll (s : Spec) : CoreM Unit := do
  let env ← getEnv
  -- exclusions: changed inductives, their ctors and recursors
  let mut excl : NameSet := {}
  for (src, _) in s.tyMap do
    let iv ← getConstInfoInduct src
    for m in iv.all do
      excl := excl.insert m
      let some (.inductInfo mv) := env.find? m | pure ()
      for c in mv.ctors do excl := excl.insert c
    for r in blockRecursors iv do excl := excl.insert r
  let srcConsts := env.constants.toList.filter fun (n, _) =>
    s.srcNs.isPrefixOf ((privateToUserName? n).getD n) && !excl.contains n
  let srcConsts := srcConsts.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  let done ← IO.mkRef excl
  let rec visit (n : Name) : CoreM Unit := do
    if (← done.get).contains n then return
    let some ci := (← getEnv).find? n | return
    -- ctors / recursors of a copied inductive: visit the inductive
    match ci with
    | .ctorInfo cv => visit cv.induct; return
    | .recInfo rv => visit rv.getMajorInduct; done.modify (·.insert n); return
    | _ => pure ()
    let group : List Name := match ci with
      | .inductInfo iv => iv.all
      | .defnInfo d => if d.safety != .safe then d.all else [n]
      | _ => [n]
    for g in group do done.modify (·.insert g)
    let mut deps : NameSet := {}
    for g in group do
      let some gi := (← getEnv).find? g | continue
      deps := deps.append gi.getUsedConstantsAsSet
      if let .inductInfo gv := gi then
        for cn in gv.ctors do
          done.modify (·.insert cn)
          deps := deps.append (← getConstInfo cn).getUsedConstantsAsSet
    for d in deps.toList do
      if s.srcNs.isPrefixOf ((privateToUserName? d).getD d) then visit d
    copyDecl s ci
    -- the kernel generated the recursor of a copied inductive
    if let .inductInfo iv := ci then
      for m in iv.all do done.modify (·.insert (mkRecName m))
  for (n, _) in srcConsts do visit n

/-! ## normal form -/

def unfoldable (s : Spec) (env : Environment) (n : Name) : Bool :=
  if s.isUser n then false else
  match env.find? n with
  | some (.defnInfo _) =>
    s.viewNs.isPrefixOf n || s.canNs.isPrefixOf n || isAuxRecursor env n || Meta.isMatcherCore env n
      || lastStr n == "go" || lastStr n.getPrefix == "brecOn"
  | _ => false

def nf (s : Spec) (e : Expr) : CoreM Expr := do
  let env ← getEnv
  Core.transform e (post := fun e => do
    let f := e.getAppFn
    if f.isLambda && e.isApp then return .visit e.headBeta
    if let .const n ls := f then
      if unfoldable s env n then
        let some ci := env.find? n | return .done e
        let v := ci.instantiateValueLevelParams! ls
        return .visit (v.beta e.getAppArgs)
      -- projection functions applied to constructor applications
      if let some pinfo := env.getProjectionFnInfo? n then
        let args := e.getAppArgs
        if args.size > pinfo.numParams then
          let st := args[pinfo.numParams]!
          if let some (.ctorInfo cv) := env.find? (st.getAppFn.constName?.getD .anonymous) then
            let sargs := st.getAppArgs
            if sargs.size == cv.numParams + cv.numFields then
              return .visit (mkAppN sargs[cv.numParams + pinfo.i]! args[pinfo.numParams+1:].toArray)
    if let .proj _ i st := e then
      if let some (.ctorInfo cv) := env.find? (st.getAppFn.constName?.getD .anonymous) then
        let sargs := st.getAppArgs
        if sargs.size == cv.numParams + cv.numFields then
          return .visit sargs[cv.numParams + i]!
    if let .mdata _ b := e then return .visit b
    if e.isLambda then
      let e' := e.eta
      if e' != e then return .visit e'
    return .done e)

end Tests.Ix.Compile.ImageProto
