import Ix.Meta
import Ix.CanonM
import Ix.Compile.Clique.WF
import Ix.Compile.Clique.PartialFixpoint
import Ix.Compile.Clique.PFConjugation
import Ix.Compile.Clique.Recover
import Tests.Ix.Compile.Twins.Cliques
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Lean Meta

namespace Tests.Ix.Compile.Recognition

def userPair : PProd Nat Nat := ⟨17, 29⟩
def userFirst (p : PProd Nat Nat) : Nat := p.fst
def sideRank : PSum Nat Nat → Nat
  | .inl _ => 0
  | .inr _ => 1
set_option warn.classDefReducibility false in
def userWF (α : Type) (rank : α → Nat) : WellFoundedRelation α :=
  invImage rank (inferInstance : WellFoundedRelation Nat)

abbrev UserFn := Nat → Option Nat
def userFns : PProd (Nat → Option Nat) (Nat → Option Nat) :=
  ⟨fun _ => some 17, fun _ => some 29⟩
def applyUserProjection (q : PProd (Nat → Option Nat) (Nat → Option Nat))
    (select : PProd (Nat → Option Nat) (Nat → Option Nat) → (Nat → Option Nat))
    (n : Nat) : Option Nat := select q n

mutual
def actualFirst (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecond q (n - 1)
partial_fixpoint
def actualSecond (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else actualFirst q (n - 1)
partial_fixpoint
end

example (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) :
    actualFirst q n =
      (if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecond q (n - 1)) :=
  actualFirst.eq_def q n

example (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) :
    actualSecond q n = (if n = 0 then some 31 else actualFirst q (n - 1)) :=
  actualSecond.eq_def q n

mutual
def actualSecondTwin (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else actualFirstTwin q (n - 1)
partial_fixpoint
def actualFirstTwin (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecondTwin q (n - 1)
partial_fixpoint
end

def ignoreRecursive (_ : Nat → Option Nat) (q : PProd (Nat → Option Nat) (Nat → Option Nat))
    (select : PProd (Nat → Option Nat) (Nat → Option Nat) → Nat → Option Nat) : Nat → Option Nat := select q

/-- The user projection shares an application with the actual recursive
binder and shadows its printed name. Neither fact grants ownership. -/
def binderMentionControl (r : PProd (Nat → Option Nat) (Nat → Option Nat)) :
    PProd (Nat → Option Nat) (Nat → Option Nat) :=
  ⟨ignoreRecursive r.fst userFns (fun r => r.fst), fun _ => some 31⟩

def userTag {α : Type} (_ : α) : Nat := 17

namespace FixedP0
mutual
def first (α : Type) (a : α) (b n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b) else second b α a (n - 1)
partial_fixpoint
def second (b : Nat) (α : Type) (a : α) (n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b + 1) else first α a b (n - 1)
partial_fixpoint
end
end FixedP0

namespace FixedP1
mutual
def second (b : Nat) (α : Type) (a : α) (n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b + 1) else first α a b (n - 1)
partial_fixpoint
def first (α : Type) (a : α) (b n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b) else second b α a (n - 1)
partial_fixpoint
end
end FixedP1

mutual
def actualWFFirst (n : Nat) : Prop :=
  if n = 0 then
    (userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)
  else actualWFSecond (n - 1)
termination_by n
def actualWFSecond (n : Nat) : Prop :=
  if n = 0 then True else actualWFFirst (n - 1)
termination_by n
end

example : actualWFFirst 0 := by
  rw [actualWFFirst]
  exact (show (0 : Nat) < 1 by decide)

private def canon (e : Expr) : Ix.Expr := (Ix.CanonM.canonExpr e).run' {}
private def uncanon (e : Ix.Expr) : Expr := (Ix.CanonM.uncanonExpr e).run' {}
private def ixName (n : Name) : Ix.Name := Ix.Name.fromLeanName n
private def leanName : Ix.Name → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (leanName p) s
  | .num p i _ => .num (leanName p) i

private def firstDifference (path : String) (a b : Ix.Expr) : Option (String × Ix.Expr × Ix.Expr) :=
  if Ix.Compile.Clique.alphaEq a b then none else
  match a, b with
  | .app f x _, .app g y _ =>
    firstDifference (path ++ ".fn") f g <|> firstDifference (path ++ ".arg") x y
  | .lam _ t x _ _, .lam _ u y _ _ | .forallE _ t x _ _, .forallE _ u y _ _ =>
    firstDifference (path ++ ".dom") t u <|> firstDifference (path ++ ".body") x y
  | .proj s i x _, .proj s' i' y _ =>
    if s == s' && i == i' then firstDifference (path ++ ".proj") x y else some (path, a, b)
  | _, _ => some (path, a, b)

def actualWFProbe (env : Environment) : IO Unit := runMeta (do
  let declOf (n : Name) := (env.find? n).bind fun c =>
    Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst c).run' {})
  let some first := declOf ``actualWFFirst | throwError "missing WF first"
  let some second := declOf ``actualWFSecond | throwError "missing WF second"
  let packedName := ``actualWFFirst ++ `_mutual
  let some packed := declOf packedName | throwError "missing WF packed"
  let proofNames := env.constants.fold (init := #[]) fun names name _ =>
    match name with
    | .str parent suffix => if parent == packedName && suffix.startsWith "_proof_" then names.push name else names
    | _ => names
  let proofs ← proofNames.mapM fun name => do
    let some d := declOf name | throwError "missing WF proof"
    pure d
  let out ← match (Ix.Compile.Clique.transportWF #[first, second] packed proofs #[1, 0]
      (ixName `RecognitionWFScratch.packed)).run' with
    | .ok value => pure value
    | .error why => throwError "actual WF transport declined: {why}"
  let userPredicate (value : Expr) := value.find? fun candidate =>
    match candidate.getAppFn with
    | .proj ``WellFoundedRelation 0 record =>
      candidate.getAppNumArgs == 2 && record.getAppFn.constName? == some ``userWF
    | .const ``WellFoundedRelation.rel _ =>
      let args := candidate.getAppArgs
      args.size == 4 && args[1]!.getAppFn.constName? == some ``userWF
    | _ => false
  let some source := userPredicate (uncanon packed.value) | throwError "missing actual WF user predicate"
  let some target := userPredicate (uncanon out.decls[0]!.decl.value) | throwError "missing target WF user predicate"
  let expected := mkApp2 (mkConst ``Nat.lt) (mkNatLit 0) (mkNatLit 1)
  let wrong := mkApp2 (mkConst ``Nat.lt) (mkNatLit 1) (mkNatLit 0)
  unless ← isDefEq source expected do throwError "actual WF source predicate differs"
  let same ← isDefEq target expected
  let reversed ← isDefEq target wrong
  IO.println s!"ACTUAL WF: source=0<1, target01={same}, target10={reversed}; source actualWFFirst 0 is proved in Lean"
  unless !same && reversed do throwError "preserved actual WF negative stopped reproducing"
  ) env

def positiveProbes (env : Environment) : IO Unit := runMeta (do
  let declOf (n : Name) := (env.find? n).bind fun c =>
    Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst c).run' {})
  let const? (name : Ix.Name) := (env.find? (leanName name)).map fun c => (Ix.CanonM.canonConst c).run' {}
  let cases : Array (String × Array String × Array Nat × Nat) := #[
    ("PF", #["pa", "pb", "pc"], #[1, 2, 0], 1),
    ("PF", #["pa", "pb", "pc"], #[1, 0, 2], 2),
    ("LI", #["la", "lb", "lc"], #[1, 2, 0], 1),
    ("LI", #["la", "lb", "lc"], #[1, 0, 2], 2),
    ("LC", #["ca", "cb"], #[1, 0], 1),
    ("PU", #["ua", "ub"], #[1, 0], 1),
    ("Fixed", #["first", "second"], #[1, 0], 1)]
  for (family, memberNames, _orderHint, presentation) in cases do
    let familyPrefix := Name.str `Tests.Ix.Compile.Twins.Cliques family
    let sourcePrefix := if family == "Fixed" then `Tests.Ix.Compile.Recognition.FixedP0 else Name.str familyPrefix "P0"
    let targetPrefix := if family == "Fixed" then `Tests.Ix.Compile.Recognition.FixedP1 else Name.str familyPrefix s!"P{presentation}"
    let members ← memberNames.mapM fun name => do
      let some d := declOf (Name.str sourcePrefix name) | throwError "missing {family} member {name}"
      pure d
    let sigma ← memberNames.mapM fun name => do
      let some target := declOf (Name.str targetPrefix name) | throwError "missing target member"
      let (_, value) := Ix.Compile.Clique.peelLams (Ix.Compile.Clique.lamArity target.value) target.value #[]
      let (head, _) := Ix.Compile.Canon.getAppFnArgs value
      let (steps, _) := Ix.Compile.Clique.projChain head
      let some (index, used) := Ix.Compile.Clique.pathPrefix memberNames.size steps
        | throwError "target member has no packed component"
      unless used == steps.size do throwError "target member has an extra projection"
      pure index
    let packedName := Name.str (leanName members[0]!.name) "mutual"
    let some packed := declOf packedName | throwError "missing {family} packed declaration"
    let proofNames := env.constants.fold (init := #[]) fun names name _ =>
      match name with
      | .str parent suffix =>
        if parent == packedName && suffix.startsWith "_proof_" then names.push name else names
      | _ => names
    IO.println s!"POSITIVE {family}/P{presentation}: source proof declarations={proofNames}"
    let proofs ← proofNames.mapM fun name => do
      let some d := declOf name | throwError "missing {family} proof"
      pure d
    let first := (Ix.Compile.Clique.invPerm sigma)[0]!
    let newPacked := Name.str (Name.str sourcePrefix memberNames[first]!) "mutual"
    let (out, state) ← match (Ix.Compile.Clique.transportPF members packed proofs sigma (ixName newPacked) const?).run {} with
      | .ok value => pure value
      | .error why => throwError "{family}/P{presentation} declined: {why}"
    let normalize (name : Ix.Name) := ixName ((leanName name).replacePrefix targetPrefix sourcePrefix)
    let mut exact := 0
    let names := out.decls.map (·.decl.name)
    let scratch := Name.str `RecognitionPositive s!"{family}{presentation}"
    let scratchName (name : Ix.Name) : Option Ix.Name :=
      if names.contains name then some (ixName (scratch ++ (leanName name).replacePrefix sourcePrefix .anonymous)) else none
    let order := (List.range proofs.size).toArray.map (· + 1) ++ #[0] ++
      ((List.range members.size).toArray.map (· + 1 + proofs.size))
    for index in order do
      let item := out.decls[index]!
      let targetName := (leanName item.decl.name).replacePrefix sourcePrefix targetPrefix
      let some target := declOf targetName | throwError "missing positive counterpart {targetName}"
      let equalSyntax := Ix.Compile.Clique.eqUpTo normalize item.decl.type target.type &&
        Ix.Compile.Clique.eqUpTo normalize item.decl.value target.value
      if equalSyntax then exact := exact + 1
      else unless family == "PU" && item.fallback.isSome do
        let normalized := Ix.Compile.Clique.renameConsts (fun name => some (normalize name)) target.value
        if let some (path, a, b) := firstDifference "value" item.decl.value normalized then
          IO.println s!"DIFFERENCE {path}: actual {← ppExpr (uncanon a)}; expected {← ppExpr (uncanon b)}"
        IO.println s!"FALLBACKS {state.fallbacks}"
        throwError "{family}/P{presentation}: noncanonical {leanName item.decl.name}"
      let name := leanName ((scratchName item.decl.name).getD item.decl.name)
      let type := uncanon (Ix.Compile.Clique.renameConsts scratchName item.decl.type)
      let value := uncanon (Ix.Compile.Clique.renameConsts scratchName item.decl.value)
      let levels := item.decl.levelParams.toList.map leanName
      if item.decl.isThm then
        addDecl (.thmDecl { name := name, levelParams := levels, type := type, value := value })
      else
        addDecl (.defnDecl {
          name := name, levelParams := levels, type := type, value := value
          hints := .opaque, safety := .safe })
    unless family == "PU" || state.fallbacks.isEmpty do throwError "{family}: unexpected fallback {state.fallbacks}"
    IO.println s!"POSITIVE {family}/P{presentation}: exact={exact}/{out.decls.size}, kernel={out.decls.size}/{out.decls.size}, fallbacks={state.fallbacks.size}"
  ) env

def actualProbe (env : Environment) : IO Unit := runMeta (do
  let declOf (n : Name) := (env.find? n).bind fun c =>
    Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst c).run' {})
  let some first := declOf ``actualFirst | throwError "missing first"
  let some second := declOf ``actualSecond | throwError "missing second"
  let some packed := declOf ``actualFirst.mutual | throwError "missing packed"
  let layout ← match Ix.Compile.Clique.pfLayout #[first, second] packed #[1, 0] packed.name with
    | .ok l => pure l
    | .error e => throwError "actual layout: {e}"
  IO.println s!"ACTUAL layout fixed={layout.numFixed}, leaves={layout.leaves.size}"
  IO.println s!"ACTUAL source packed: {← ppExpr (uncanon packed.value)}"
  let target ← match (Ix.Compile.Clique.transportPFShape #[first, second] packed #[] #[1, 0]
      packed.name (fun n => (env.find? (leanName n)).map fun c => (Ix.CanonM.canonConst c).run' {})).run' with
    | .ok out => pure out.decls[0]!.decl
    | .error e => throwError "actual transport: {e}"
  IO.println s!"ACTUAL target packed: {← ppExpr (uncanon target.value)}"
  let evaluate (value : Ix.Expr) (component : Nat) : MetaM Expr := do
    let body := (mkApp (uncanon value) (mkConst ``userFns)).headBeta
    let some functional := body.getAppArgs.find? Expr.isLambda
      | throwError "actual packed body has no functional lambda"
    return mkApp (mkProj ``PProd component (mkApp functional (mkConst ``userFns))) (mkNatLit 0)
  let source ← evaluate packed.value 0
  let changed ← evaluate target.value 1
  let expected := mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)
  let expected := mkApp expected (mkNatLit 17)
  let wrong := mkApp (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)) (mkNatLit 29)
  unless ← isDefEq source expected do throwError "actual source functional does not return some 17"
  let same ← isDefEq changed expected
  let swapped ← isDefEq changed wrong
  IO.println s!"ACTUAL functional at n=0: source=some17, target17={same}, target29={swapped}"
  let body := (mkApp (uncanon packed.value) (mkConst ``userFns)).headBeta
  IO.println s!"FIX HEAD {body.getAppFn.constName?} ARITY {body.getAppArgs.size}"
  for arg in body.getAppArgs do IO.println s!"FIX ARG {← ppExpr arg}"
  for (n, ci) in env.constants.toList do
    if n.getPrefix == ``actualFirst.mutual then
      IO.println s!"PROOF {n}: {← ppExpr ci.type}"
      if let .thmInfo info := ci then IO.println s!"PROOF VALUE {← ppExpr info.value}"
  let some functional := body.getAppArgs.find? Expr.isLambda
    | throwError "actual functional missing"
  let conjugated ← match Ix.Compile.Clique.conjugatePF 2 #[1, 0] (canon functional) with
    | .ok e => pure (uncanon e)
    | .error e => throwError "conjugation declined: {e}"
  let conjugatedValue := mkApp (mkProj ``PProd 1 (mkApp conjugated (mkConst ``userFns))) (mkNatLit 0)
  unless ← isDefEq conjugatedValue expected do throwError "conjugation changed the user value"
  IO.println s!"CONJUGATED actual functional: value=some17; {← ppExpr conjugated}"
  let some twin := declOf ``actualSecondTwin.mutual | throwError "missing twin"
  let twinBody := (mkApp (uncanon twin.value) (mkConst ``userFns)).headBeta
  let some twinFunctional := twinBody.getAppArgs.find? Expr.isLambda
    | throwError "missing twin functional"
  unless ← isDefEq conjugated twinFunctional do throwError "conjugation disagrees with the canonical source twin"
  IO.println "CONJUGATED canonical source twin: definitionally equal"
  let some control := (env.find? ``binderMentionControl).bind ConstantInfo.value?
    | throwError "missing binder-mention control"
  let control' ← match Ix.Compile.Clique.conjugatePF 2 #[1, 0] (canon control) with
    | .ok e => pure (uncanon e)
    | .error e => throwError "control conjugation: {e}"
  let controlValue := mkApp (mkProj ``PProd 1 (mkApp control' (mkConst ``userFns))) (mkNatLit 0)
  unless ← isDefEq controlValue expected do throwError "binder mention or shadowing changed a user value"
  IO.println "CONJUGATED recursive-binder mention + shadowing control: some17"
  let some sourceProof := declOf (``actualFirst.mutual ++ `_proof_1)
    | throwError "missing monotonicity proof body"
  let proofBody := (mkApp (uncanon sourceProof.value) (mkConst ``userFns)).headBeta
  let composeInfo ← getConstInfo ``Lean.Order.monotone_compose
  let layout := { layout with composeLevels := composeInfo.levelParams.toArray.map ixName }
  let mono ← match Ix.Compile.Clique.conjugatePFMono layout (canon proofBody) with
    | .ok e => pure (uncanon e)
    | .error e => throwError "proof conjugation declined: {e}"
  let fixArgs := body.getAppArgs
  let whole := mkAppN body.getAppFn #[fixArgs[0]!, fixArgs[1]!, conjugated, mono]
  addDecl (.defnDecl {
    name := `RecognitionScratch.conjugated, levelParams := [], type := fixArgs[0]!,
    value := whole, hints := .opaque, safety := .safe })
  IO.println "CONJUGATED packed fixpoint + composed monotonicity proof: Lean kernel accepted"
  let const? (name : Ix.Name) := (env.find? (leanName name)).map fun c => (Ix.CanonM.canonConst c).run' {}
  let (checkedMono, checkedState) ← match
      (Ix.Compile.Clique.conjugatePFMonoChecked layout const? (canon proofBody)).run {} with
    | .ok result => pure result
    | .error reason => throwError "owned proof transport: {reason}"
  let checkedWhole := mkAppN body.getAppFn #[fixArgs[0]!, fixArgs[1]!, conjugated, uncanon checkedMono]
  addDecl (.defnDecl {
    name := `RecognitionScratch.ownedProof, levelParams := [], type := fixArgs[0]!,
    value := checkedWhole, hints := .opaque, safety := .safe })
  let some twinProof := declOf (``actualSecondTwin.mutual ++ `_proof_1)
    | throwError "missing twin proof"
  let twinProofBody := (mkApp (uncanon twinProof.value) (mkConst ``userFns)).headBeta
  IO.println s!"OWNED proof: kernel accepted; fallbacks={checkedState.fallbacks}; exact twin={Ix.Compile.Clique.alphaEq checkedMono (canon twinProofBody)}"
  unless checkedState.fallbacks.isEmpty do throwError "ordinary generated proof fell back"
  unless Ix.Compile.Clique.alphaEq checkedMono (canon twinProofBody) do
    throwError "owned proof transport changed canonical generated syntax"
  let firstEquationName ← realizeGlobalConstNoOverloadCore (``actualFirst ++ `eq_def)
  let secondEquationName ← realizeGlobalConstNoOverloadCore (``actualSecond ++ `eq_def)
  let equationEnv ← getEnv
  let equationOf (name : Name) := (equationEnv.find? name).bind fun c =>
    Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst c).run' {})
  let some firstEquation := equationOf firstEquationName | throwError "missing first equation"
  let some secondEquation := equationOf secondEquationName | throwError "missing second equation"
  let equations := #[(firstEquation, firstEquation.name), (secondEquation, secondEquation.name)]
  let repaired ← match (Ix.Compile.Clique.transportPF #[first, second] packed #[sourceProof]
      #[1, 0] (ixName `RecognitionScratch.packed) const? equations).run {} with
    | .ok (out, state) =>
      unless state.fallbacks.isEmpty do throwError "production repair unexpectedly fell back"
      pure out
    | .error reason => throwError "production PF routing: {reason}"
  let repairedValue ← evaluate repaired.decls[0]!.decl.value 1
  unless ← isDefEq repairedValue expected do throwError "production PF routing changed the user's value"
  let renamed (name : Ix.Name) : Option Ix.Name := do
    let index ← repaired.decls.findIdx? (·.decl.name == name)
    if index < 2 then some name else some (ixName (Name.str `RecognitionScratch s!"decl{index}"))
  for index in #[1, 0, 2, 3, 4, 5] do
    let declaration := repaired.decls[index]!.decl
    let name := leanName ((renamed declaration.name).getD declaration.name)
    let type := uncanon (Ix.Compile.Clique.renameConsts renamed declaration.type)
    let value := uncanon (Ix.Compile.Clique.renameConsts renamed declaration.value)
    if declaration.isThm then
      addDecl (.thmDecl { name, levelParams := declaration.levelParams.toList.map leanName, type, value })
    else
      addDecl (.defnDecl {
        name, levelParams := declaration.levelParams.toList.map leanName
        type := type, value := value, hints := .opaque, safety := .safe })
  IO.println "PRODUCTION PF routing: source value preserved; all six declarations including equation lemmas kernel accepted"
  match Ix.Compile.Clique.recoverPF #[first, second] packed with
  | .ok (components, _) =>
    unless components.size == 2 do throwError "PF recovery lost a component"
  | .error reason => throwError "PF recovery rejected the decoded source: {reason}"
  let foreignRoot := Ix.Compile.Clique.renameConsts
    (fun name => if name == Ix.Compile.Clique.nOrderFix then some (ixName `Unowned.fix) else none)
    packed.value
  match Ix.Compile.Clique.recoverPF #[first, second] { packed with value := foreignRoot } with
  | .error _ => pure ()
  | .ok _ => throwError "PF recovery accepted a functional under an unowned root"
  IO.println "PF recovery: decoded root accepted; unowned root rejected"
  unless !same && swapped do throwError "preserved baseline negative stopped reproducing"
  ) env

/-- Baseline audit probe: both source and transformed values are checked by
Lean; equality of their types alone must not establish transport correctness. -/
def probe (env : Environment) : IO Unit := runMeta (do
  let nat := mkConst ``Nat
  let natIx := canon nat
  let spine : Ix.Compile.Clique.Spine :=
    { kind := .pprod, leaves := #[natIx, natIx], lvls := #[Ix.Level.mkSucc Ix.Level.mkZero, Ix.Level.mkSucc Ix.Level.mkZero] }
  let pf : Ix.Compile.Clique.PFLayout := {
    n := 2, sigma := #[1, 0], packedName := ixName `encodingOnly,
    newPackedName := ixName `encodingOnly, numFixed := 0, fixedPerm := #[],
    leaves := #[natIx, natIx], spine }
  let some first := (env.find? ``userFirst).bind ConstantInfo.value?
    | throwError "missing userFirst body"
  let source := mkApp first (mkConst ``userPair)
  let transported ← match (Ix.Compile.Clique.phiPF pf #[] (canon source)).run' with
    | .ok value => pure (uncanon value)
    | .error error => throwError "PF transport declined: {error}"
  unless ← isDefEq (← inferType source) nat do throwError "PF source is not Nat"
  unless ← isDefEq (← inferType transported) nat do throwError "PF target is not Nat"
  unless ← isDefEq source (mkNatLit 17) do throwError "PF source does not compute to 17"
  let unchanged ← isDefEq transported (mkNatLit 17)
  let swapped ← isDefEq transported (mkNatLit 29)
  IO.println s!"PF user binder: source=17, target17={unchanged}, target29={swapped}; target={← ppExpr transported}"

  let sum := mkApp2 (mkConst ``PSum [Level.one, Level.one]) nat nat
  let left := mkApp3 (mkConst ``PSum.inl [Level.one, Level.one]) nat nat (mkNatLit 0)
  let right := mkApp3 (mkConst ``PSum.inr [Level.one, Level.one]) nat nat (mkNatLit 0)
  let relation := mkApp2 (mkConst ``userWF) sum (mkConst ``sideRank)
  let predicate := mkApp2 (mkProj ``WellFoundedRelation 0 relation) left right
  let wf : Ix.Compile.Clique.WFLayout := {
    n := 2, sigma := #[1, 0], mutualName := ixName `encodingOnly,
    newMutualName := ixName `encodingOnly, numFixed := 0, fixedPerm := #[],
    leaves := #[natIx, natIx] }
  let changed ← match (Ix.Compile.Clique.phiWF wf false (canon predicate)).run' with
    | .ok value => pure (uncanon value)
    | .error error => throwError "WF transport declined: {error}"
  unless ← isProp predicate do throwError "WF source is not Prop"
  unless ← isProp changed do throwError "WF target is not Prop"
  let expected := mkApp2 (mkConst ``Nat.lt) (mkNatLit 0) (mkNatLit 1)
  let wrong := mkApp2 (mkConst ``Nat.lt) (mkNatLit 1) (mkNatLit 0)
  unless ← isDefEq predicate expected do throwError "WF source is not 0 < 1"
  let same ← isDefEq changed expected
  let reversed ← isDefEq changed wrong
  IO.println s!"WF unrelated relation: recognised={wf.isRelApp (canon predicate)}, source=0<1, target01={same}, target10={reversed}; target={← ppExpr changed}"
  if !unchanged || !same then throwError "recognition changed a user's value or predicate"
  ) env

def run : IO UInt32 := do
  let env ← get_env!
  actualProbe env
  positiveProbes env
  actualWFProbe env
  return 0

end Tests.Ix.Compile.Recognition
