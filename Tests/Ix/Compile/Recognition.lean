import Ix.Meta
import Ix.CanonM
import Ix.Compile.Clique.WF
import Ix.Compile.Clique.PartialFixpoint
import Ix.Compile.Clique.PFConjugation
import Ix.Compile.Clique.Recover
import Ix.Compile.Clique.WFConjugation
import Tests.Ix.Compile.Twins.Cliques
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Lean Meta

namespace Tests.Ix.Compile.Recognition

def userPair : PProd Nat Nat := ⟨17, 29⟩
def userFirst (p : PProd Nat Nat) : Nat := p.fst
def repeatedPFPacked (a b : Nat) : PProd Nat Nat := ⟨a, b⟩
def repeatedPFFirst (a : Nat) : Nat := (repeatedPFPacked a a).fst
def repeatedPFSecond (a : Nat) : Nat := (repeatedPFPacked a a).snd
def repeatedWFPacked (a b : Nat) : PSum Nat Nat → Nat
  | .inl n => a + n
  | .inr n => b + n
def repeatedWFFirst (a n : Nat) : Nat := repeatedWFPacked a a (.inl n)
def repeatedWFSecond (a n : Nat) : Nat := repeatedWFPacked a a (.inr n)

namespace RepeatedStructural
mutual
def first (a b : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => second a b n
def second (a b : Nat) : Nat → Nat
  | 0 => b
  | n + 1 => first a b n
end
end RepeatedStructural
def sideRank : PSum Nat Nat → Nat
  | .inl _ => 0
  | .inr _ => 1
set_option warn.classDefReducibility false in
def userWF (α : Type) (rank : α → Nat) : WellFoundedRelation α :=
  invImage rank (inferInstance : WellFoundedRelation Nat)

def wgLeft : PSum (PSigma fun _ : Nat => Nat) (PSigma fun _ : Nat => Nat) :=
  .inl ⟨7, 11⟩
def wgRight : PSum (PSigma fun _ : Nat => Nat) (PSigma fun _ : Nat => Nat) :=
  .inr ⟨7, 11⟩

private def userNatDispatch (_motive : Nat → Type) (_n : Nat)
    (_zero : Unit → Nat) (_succ : Nat → Nat) : Nat := 17

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

/-! Frozen outputs of the deleted shape routes (`transportWFShape`,
`transportPFShape`, deleted by the commit that introduced these definitions;
recorded by running them on `4907a048`, design document §5 and
`plans/review2/FIX-pfwf.md` §1.2–1.3). Each is the user-facing part of the old
route's output on the clique above with `σ = [1, 0]`, kept so that the
negative controls still show what the shape-based recognition did, without
keeping the code that did it:

* WF (`actualWFFirst`/`actualWFSecond`): the user's predicate
  `(userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)` (`0 < 1`)
  came out with its injections swapped (`1 < 0`);
* PF (`actualFirst`/`actualSecond`): the user's selector `fun p => p.fst`
  passed to `applyUserProjection` came out as `fun p => p.snd` (`some 17`
  became `some 29`). -/
def frozenOldWFPredicate : Prop := (userWF (PSum Nat Nat) sideRank).rel (PSum.inr 0) (PSum.inl 0)
def frozenOldPFSelector : PProd (Nat → Option Nat) (Nat → Option Nat) → (Nat → Option Nat) :=
  fun p => p.snd

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
  let userPredicate (value : Expr) := value.find? fun candidate =>
    match candidate.getAppFn with
    | .proj ``WellFoundedRelation 0 record =>
      candidate.getAppNumArgs == 2 && record.getAppFn.constName? == some ``userWF
    | .const ``WellFoundedRelation.rel _ =>
      let args := candidate.getAppArgs
      args.size == 4 && args[1]!.getAppFn.constName? == some ``userWF
    | _ => false
  let some source := userPredicate (uncanon packed.value) | throwError "missing actual WF user predicate"
  -- the deleted shape route's output on this clique (frozen data, see
  -- `frozenOldWFPredicate`)
  let some target := (env.find? ``frozenOldWFPredicate).bind ConstantInfo.value?
    | throwError "missing frozen WF predicate"
  let expected := mkApp2 (mkConst ``Nat.lt) (mkNatLit 0) (mkNatLit 1)
  let wrong := mkApp2 (mkConst ``Nat.lt) (mkNatLit 1) (mkNatLit 0)
  unless ← isDefEq source expected do throwError "actual WF source predicate differs"
  let same ← isDefEq target expected
  let reversed ← isDefEq target wrong
  IO.println s!"FROZEN OLD WF ROUTE: source=0<1, old target01={same}, old target10={reversed}; source actualWFFirst 0 is proved in Lean"
  unless !same && reversed do throwError "the frozen old-route WF output no longer means 1<0"
  let layout ← match Ix.Compile.Clique.wfLayout #[first, second] packed #[1, 0]
      (ixName `RecognitionWFScratch.owned) with
    | .ok value => pure value
    | .error reason => throwError "owned WF layout: {reason}"
  let (head, args) := Ix.Compile.Canon.getAppFnArgs packed.value
  unless args.size == 4 do throwError "owned WF test requires specialized Nat root"
  let owned ← match (do
      let value ← Ix.Compile.Clique.conjugateWFRoot layout packed.value
      let type ← Ix.Compile.Clique.conjugateWFType layout packed.type
      pure (type, value)).run' with
    | .ok value => pure value
    | .error reason => throwError "owned WF prototype: {reason}"
  let some preserved := userPredicate (uncanon owned.2)
    | throwError "owned WF lost user predicate"
  unless ← isDefEq preserved expected do throwError "owned WF changed user relation"
  addDecl (.defnDecl {
    name := `RecognitionWFScratch.owned,
    levelParams := packed.levelParams.toList.map leanName,
    type := uncanon owned.1, value := uncanon owned.2, hints := .opaque, safety := .safe })
  IO.println "OWNED WF: source user relation remains0<1; complete packed fixpoint kernel accepted"
  let .lam xn xt (.lam rn rt tree rbi _) xbi _ := args[3]!
    | throwError "WF control: missing exact functional binders"
  let some decoded := Ix.Compile.Clique.decodeTree 2 tree
    | throwError "WF control: missing exact case tree"
  let .lam pn pt (.lam an recursiveType leaf abi _) pbi _ := decoded.leaves[0]!
    | throwError "WF control: missing exact leaf binders"
  let shadow := Ix.Expr.mkLam an (Ix.Compile.Canon.liftLoose recursiveType 1)
    (Ix.Compile.Canon.liftLoose leaf 1) abi
  let leaf' := Ix.Expr.mkApp shadow (Ix.Expr.mkBVar 0)
  let newLeaf := Ix.Expr.mkLam pn pt (Ix.Expr.mkLam an recursiveType leaf' abi) pbi
  let decoded := { decoded with leaves := decoded.leaves.set! 0 newLeaf }
  let some tree' := decoded.build | throwError "WF control: failed to rebuild case tree"
  let functional := Ix.Expr.mkLam xn xt (Ix.Expr.mkLam rn rt tree' rbi) xbi
  addDecl (.defnDecl {
    name := `RecognitionWFScratch.sourceBinderMention,
    levelParams := packed.levelParams.toList.map leanName,
    type := uncanon packed.type,
    value := uncanon (Ix.Compile.Canon.mkAppN head (args.set! 3 functional)),
    hints := .opaque, safety := .safe })
  let changed ← match (Ix.Compile.Clique.conjugateWFRoot layout
      (Ix.Compile.Canon.mkAppN head (args.set! 3 functional))).run' with
    | .ok value => pure value
    | .error reason => throwError "WF binder-mention control: {reason}"
  let value := changed
  addDecl (.defnDecl {
    name := `RecognitionWFScratch.binderMention,
    levelParams := packed.levelParams.toList.map leanName,
    type := uncanon owned.1, value := uncanon value, hints := .opaque, safety := .safe })
  let some preserved := userPredicate (uncanon value) | throwError "WF control lost user relation"
  unless ← isDefEq preserved expected do throwError "WF binder mention changed user relation"
  IO.println "OWNED WF: exact recursive-binder argument and same-typed shadowing preserve0<1; kernel accepted"
  let recovered ← match (Ix.Compile.Clique.recoverWF #[first, second] packed).run' with
    | .ok value => pure value
    | .error reason => throwError "owned WF recovery: {reason}"
  let some recoveredPredicate := userPredicate (uncanon recovered[0]!)
    | throwError "WF recovery erased the user's relation"
  unless ← isDefEq recoveredPredicate expected do throwError "WF recovery changed the user predicate"
  IO.println "OWNED WF RECOVERY: source user relation retained as0<1; re-encoding passed"
  let equationNames ← #[packedName ++ `eq_def, ``actualWFFirst ++ `eq_def,
      ``actualWFSecond ++ `eq_def].mapM fun name => do realizeGlobalConstNoOverloadCore name
  let equationEnv ← getEnv
  let equations ← equationNames.mapIdxM fun index name => do
    let some declaration := (equationEnv.find? name).bind fun info =>
        Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst info).run' {})
      | throwError "missing WF equation {name}"
    let targetName := if index == 0 then `RecognitionWFEquation.packed.eq_def
      else Name.str `RecognitionWFEquation s!"equation{index}"
    pure (declaration, ixName targetName)
  let equationOutput ← match (Ix.Compile.Clique.transportWF #[first, second] packed proofs
      #[1, 0] (ixName `RecognitionWFEquation.packed) equations).run' with
    | .ok result => pure result
    | .error reason => throwError "WF carried equations: {reason}"
  let rename (name : Ix.Name) : Option Ix.Name :=
    if name == first.name then some (ixName `RecognitionWFEquation.first)
    else if name == second.name then some (ixName `RecognitionWFEquation.second) else none
  let order := ((List.range proofs.size).toArray.map (· + 1)).push 0 ++
    (List.range (equationOutput.decls.size - proofs.size - 1)).toArray.map (· + proofs.size + 1)
  for index in order do
    let declaration := equationOutput.decls[index]!.decl
    let name := leanName ((rename declaration.name).getD declaration.name)
    let type := uncanon (Ix.Compile.Clique.renameConsts rename declaration.type)
    let value := uncanon (Ix.Compile.Clique.renameConsts rename declaration.value)
    if declaration.isThm then
      addDecl (.thmDecl { name, levelParams := declaration.levelParams.toList.map leanName, type, value })
    else
      addDecl (.defnDecl {
        name, levelParams := declaration.levelParams.toList.map leanName,
        type, value, hints := .opaque, safety := .safe })
  IO.println s!"WF CARRIED EQUATIONS: all {equationOutput.decls.size} declarations including3 equations kernel accepted"
  ) env

/-- The existing GuessLex comparison policy, kept identical to
`Tests.Ix.Compile.Transport.maskMeasures`: docs/compiler-passes.md §5.7.
Used only after checking the exact WG differing-object set below. -/
private partial def maskWGMeasures (e : Ix.Expr) : Ix.Expr :=
  match e with
  | .app .. =>
    let (head, args) := Ix.Compile.Canon.getAppFnArgs e
    let args := args.map maskWGMeasures
    let placeholder := Ix.Expr.mkConst (ixName `_measure) #[]
    let args := match head with
      | .const name _ _ =>
        if (name == ixName ``invImage || name == ixName ``WellFounded.Nat.fix) && args.size ≥ 3 then
          args.set! 2 placeholder
        else if name == ixName ``InvImage && args.size ≥ 4 then args.set! 3 placeholder
        else args
      | _ => args
    Ix.Compile.Canon.mkAppN (maskWGMeasures head) args
  | .lam n t b bi _ => Ix.Expr.mkLam n (maskWGMeasures t) (maskWGMeasures b) bi
  | .forallE n t b bi _ => Ix.Expr.mkForallE n (maskWGMeasures t) (maskWGMeasures b) bi
  | .letE n t v b nd _ => Ix.Expr.mkLetE n (maskWGMeasures t) (maskWGMeasures v) (maskWGMeasures b) nd
  | .proj s i x _ => Ix.Expr.mkProj s i (maskWGMeasures x)
  | .mdata d x _ => Ix.Expr.mkMData d (maskWGMeasures x)
  | e => e

def wfMatcherControls (env : Environment) : IO Unit := runMeta (do
  let const? (name : Ix.Name) := (env.find? (leanName name)).map fun info => (Ix.CanonM.canonConst info).run' {}
  let matcher := ixName `Tests.Ix.Compile.Twins.Cliques.TS.P0.evT.match_1
  match (Ix.Compile.Clique.decodeWFNatMatcher const? matcher #[]).run' with
  | .ok _ => pure ()
  | .error reason => throwError "real source matcher declined: {reason}"
  let expectDecline (lookup : Ix.Name → Option Ix.ConstantInfo) (name : Ix.Name)
      (reason : String) : MetaM Unit := do
    match (Ix.Compile.Clique.decodeWFNatMatcher lookup name #[]).run' with
    | .ok _ => throwError "matcher ownership accepted a negative control"
    | .error actual => unless actual.contains reason do throwError "matcher declined for another reason: {actual}"
  expectDecline (fun _ => none) matcher "unavailable"
  expectDecline (fun _ => const? matcher) (ixName `Another.sourceIdentity) "another source declaration identity"
  expectDecline const? (ixName ``userNatDispatch) "zero minor does not return its motive"
  let nat := mkConst ``Nat
  let userCall := mkAppN (mkConst ``userNatDispatch) #[
    mkLambda `n .default nat nat, mkNatLit 0,
    mkLambda `unit .default (mkConst ``Unit) (mkNatLit 29),
    mkLambda `n .default nat (mkNatLit 31)]
  unless ← isDefEq userCall (mkNatLit 17) do throwError "user dispatch value control is not17"
  let spine : Ix.Compile.Clique.Spine := {
    kind := .psum, leaves := #[canon nat, canon (mkConst ``Bool)],
    lvls := #[Ix.Level.mkSucc Ix.Level.mkZero, Ix.Level.mkSucc Ix.Level.mkZero] }
  let constantCodomain := Ix.Expr.mkLam (ixName `input) spine.type spine.type .default
  let moved ← match (Ix.Compile.Clique.decodeWFCase spine #[1, 0] constantCodomain).run' with
    | .ok value => pure value
    | .error reason => throwError "constant-codomain control: {reason}"
  let expected := Ix.Expr.mkLam (ixName `input) (spine.permute #[1, 0]).type spine.type .default
  unless Ix.Compile.Clique.alphaEq moved expected do throwError "same-typed user codomain was permuted"
  IO.println "WF MATCHER OWNERSHIP: exact source dispatch accepted; absent/aliased/private user declarations rejected; user17 retained; constant packing-valued codomain unchanged"
  ) env

def structuralIdentityControl (env : Environment) : IO Unit := runMeta (do
  let const? (name : Ix.Name) := (env.find? (leanName name)).map fun info => (Ix.CanonM.canonConst info).run' {}
  let members ← #[``RepeatedStructural.first, ``RepeatedStructural.second].mapM fun name => do
    let some declaration := (const? (ixName name)).bind Ix.Compile.Clique.Decl.ofConstantInfo?
      | throwError "missing structural identity fixture"
    pure declaration
  let layout ← match Ix.Compile.Clique.structLayout members #[] #[1, 0] const? with
    | .ok value => pure value
    | .error reason => throwError "ordinary structural identity fixture declined: {reason}"
  unless layout.numFixed == 2 do throwError "structural identity fixture lost its two fixed slots"
  let rec aliasSecond : Nat → Ix.Expr → Ix.Expr
    | 0, expression => expression
    | fuel + 1, expression =>
      let go := aliasSecond fuel
      match expression with
      | .app .. =>
        let (head, args) := Ix.Compile.Canon.getAppFnArgs expression
        let args := args.map go
        let args := match head with
          | .const name _ _ => if layout.fNames.contains name && args.size ≥ 2 then args.set! 1 args[0]! else args
          | _ => args
        Ix.Compile.Canon.mkAppN head args
      | .lam n t b bi _ => Ix.Expr.mkLam n (go t) (go b) bi
      | .forallE n t b bi _ => Ix.Expr.mkForallE n (go t) (go b) bi
      | .letE n t v b nd _ => Ix.Expr.mkLetE n (go t) (go v) (go b) nd
      | .proj s i x _ => Ix.Expr.mkProj s i (go x)
      | .mdata d x _ => Ix.Expr.mkMData d (go x)
      | e => e
  let altered := members.map fun declaration => { declaration with value := aliasSecond 1000 declaration.value }
  for (declaration, index) in altered.zipIdx do
    addDecl (.defnDecl {
      name := Name.str `RecognitionStructuralAlias s!"member{index}",
      levelParams := declaration.levelParams.toList.map leanName,
      type := uncanon declaration.type, value := uncanon declaration.value,
      hints := .opaque, safety := .safe })
  IO.println "Structural repeated fixed-slot control: both altered source declarations kernel accepted"
  match Ix.Compile.Clique.structLayout altered #[] #[1, 0] const? with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throwError "structural alias control declined for another reason: {reason}"
  | .ok layout => throwError "structural layout accepted aliased source binder identities: {repr layout.memberFixed}"
  ) env

def wfPositiveProbes (env : Environment) : IO Unit := runMeta (do
  let const? (name : Ix.Name) := (env.find? (leanName name)).map fun info => (Ix.CanonM.canonConst info).run' {}
  let declOf (name : Name) := (env.find? name).bind fun info =>
    Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst info).run' {})
  let cases : Array (String × Array String) := #[
    ("WD", #["wa", "wb"]), ("W3", #["ga", "gb", "gc"]),
    ("WG", #["ga", "gb"]), ("WT", #["ta", "tb"]), ("WB", #["ba", "bb"]),
    ("WP", #["ha", "hb"]), ("WA", #["ta", "tb", "tc"]),
    ("WH", #["ha", "hb"]), ("WU", #["wx", "wy"]),
    ("TW", #["wa", "wb"]), ("TQ", #["qa", "qb"]), ("TS", #["evT", "odT"])]
  let mut failures : Array String := #[]
  for (family, names) in cases do
    let familyPrefix := Name.str `Tests.Ix.Compile.Twins.Cliques family
    let readMembers (presentation : String) := names.mapM fun name => do
      let some declaration := declOf (Name.str (Name.str familyPrefix presentation) name)
        | throwError "missing WF {family}/{presentation}/{name}"
      pure declaration
    let sourceMembers ← readMembers "P0"
    let targetMembers ← readMembers "P1"
    let unpack (declaration : Ix.Compile.Clique.Decl) := do
      let (_, body) := Ix.Compile.Clique.peelLams
        (Ix.Compile.Clique.lamArity declaration.value) declaration.value #[]
      let (head, _, args) ← Ix.Compile.Clique.constApp? body
      let argument ← args.back?
      let (_, index, _) ← Ix.Compile.Clique.decodeInj names.size argument
      some (head, index)
    let sourceData ← sourceMembers.mapM fun declaration =>
      match unpack declaration with
      | some value => pure value
      | none => throwError "missing WF source injection {family}"
    let targetData ← targetMembers.mapM fun declaration =>
      match unpack declaration with
      | some value => pure value
      | none => throwError "missing WF target injection {family}"
    let order := ((List.range names.size).toArray).qsort fun i j => sourceData[i]!.2 < sourceData[j]!.2
    let members := order.map (sourceMembers[·]!)
    let sigma := order.map fun i => targetData[i]!.2
    let some packed := declOf (leanName sourceData[0]!.1) | throwError "missing WF packed {family}"
    let some twin := declOf (leanName targetData[0]!.1) | throwError "missing WF twin {family}"
    if family == "WG" || family == "W3" then
      let sourceArgs := (uncanon packed.value).getAppArgs
      IO.println s!"{family} ROOT: {(uncanon packed.value).getAppFn}; source relation={← ppExpr sourceArgs[2]!}; wf={← ppExpr sourceArgs[3]!}"
      let targetArgs := (uncanon twin.value).getAppArgs
      IO.println s!"{family} TARGET RELATION: {← ppExpr targetArgs[2]!}"
    let result := (do
      let layout ← Ix.Compile.Clique.liftE (Ix.Compile.Clique.wfLayout members packed sigma packed.name)
      let value ← Ix.Compile.Clique.withReorderedBinders2 true layout.numFixed layout.fixedPerm
        packed.value pure (fun value => Ix.Compile.Clique.conjugateWFRoot layout value const?)
      let type ← Ix.Compile.Clique.withReorderedBinders2 false layout.numFixed layout.fixedPerm
        packed.type pure (Ix.Compile.Clique.conjugateWFType layout)
      pure (type, value)).run'
    match result with
    | .error reason =>
      IO.println s!"WF POSITIVE {family}: DECLINED {reason}"
      failures := failures.push s!"{family}: {reason}"
    | .ok (type, value) =>
      try
        addDecl (.defnDecl {
          name := Name.str `RecognitionWFPositive family,
          levelParams := packed.levelParams.toList.map leanName,
          type := uncanon type, value := uncanon value, hints := .opaque, safety := .safe })
        let equivalent ← isDefEq (uncanon value) (uncanon twin.value)
        IO.println s!"WF POSITIVE {family}: kernel accepted; twin defeq={equivalent}"
        let proofNames := env.constants.fold (init := #[]) fun names name _ =>
          match name with
          | .str parent suffix =>
            if parent == leanName packed.name && suffix.startsWith "_proof_" then names.push name else names
          | _ => names
        let proofs ← proofNames.mapM fun name =>
          match declOf name with
          | some declaration => pure declaration
          | none => throwError "missing WF declaration proof {name}"
        let transported ← match (Ix.Compile.Clique.transportWF members packed proofs sigma
            (ixName (Name.str `RecognitionWFRoute family)) #[] const?).run' with
          | .ok result => pure result
          | .error reason => throwError "WF production candidate {family}: {reason}"
        let rename (name : Ix.Name) : Option Ix.Name := do
          let index ← members.findIdx? (·.name == name)
          some (ixName (Name.str (Name.str `RecognitionWFMembers family) s!"member{index}"))
        let order := ((List.range proofs.size).toArray.map (· + 1)).push 0 ++
          (List.range members.size).toArray.map (· + proofs.size + 1)
        for index in order do
          let declaration := transported.decls[index]!.decl
          let name := leanName ((rename declaration.name).getD declaration.name)
          let type := uncanon (Ix.Compile.Clique.renameConsts rename declaration.type)
          let value := uncanon (Ix.Compile.Clique.renameConsts rename declaration.value)
          if declaration.isThm then
            addDecl (.thmDecl { name, levelParams := declaration.levelParams.toList.map leanName, type, value })
          else
            addDecl (.defnDecl {
              name, levelParams := declaration.levelParams.toList.map leanName,
              type, value, hints := .opaque, safety := .safe })
        IO.println s!"WF PRODUCTION {family}: all {transported.decls.size} declarations kernel accepted"
        let targetRoot := twin.name
        let counterpart (name : Ix.Name) : Option Ix.Name :=
          if name == ixName (Name.str `RecognitionWFRoute family) then some targetRoot else
          match sourceMembers.findIdx? (·.name == name) with
          | some index => some targetMembers[index]!.name
          | none => match name with
            | .str parent suffix _ =>
              if parent == ixName (Name.str `RecognitionWFRoute family) && suffix.startsWith "_proof_" then
                some (Ix.Name.mkStr targetRoot suffix)
              else none
            | _ => none
        let mut exact := 0
        let mut differences : Array Ix.Name := #[]
        for item in transported.decls do
          let some name := counterpart item.decl.name | throwError "no WF target counterpart {item.decl.name}"
          let some expected := declOf (leanName name) | throwError "missing WF target declaration {name}"
          let typeEqual := Ix.Compile.Clique.alphaEq
            (Ix.Compile.Clique.renameConsts counterpart item.decl.type) expected.type
          let valueEqual := Ix.Compile.Clique.alphaEq
            (Ix.Compile.Clique.renameConsts counterpart item.decl.value) expected.value
          if typeEqual && valueEqual then exact := exact + 1
          else
            differences := differences.push name
            IO.println s!"WF EXACT DIFFERENCE {family}/{name}: type={typeEqual}, value={valueEqual}"
            if family == "WG" then
              let maskedType := Ix.Compile.Clique.alphaEq
                (maskWGMeasures (Ix.Compile.Clique.renameConsts counterpart item.decl.type))
                (maskWGMeasures expected.type)
              let maskedValue := Ix.Compile.Clique.alphaEq
                (maskWGMeasures (Ix.Compile.Clique.renameConsts counterpart item.decl.value))
                (maskWGMeasures expected.value)
              -- A decreasing proof's body depends on its measure; the existing
              -- policy compares its statement. Every literal proof checks above.
              let isProof := name == Ix.Name.mkStr targetRoot "_proof_1" ||
                name == Ix.Name.mkStr targetRoot "_proof_2"
              unless maskedType && (isProof || maskedValue) do
                throwError "WG has a difference outside the established measure policy: {name}"
        IO.println s!"WF EXACT {family}: {exact}/{transported.decls.size}"
        if family == "WG" then
          let expected := #[targetRoot, Ix.Name.mkStr targetRoot "_proof_1", Ix.Name.mkStr targetRoot "_proof_2"]
          unless differences.size == expected.size && expected.all differences.contains && exact == 2 do
            throwError "WG enlarged or changed its documented differing-object set: {differences}"
          IO.println "WG POLICY: exactly packed root + two decreasing proofs; all masked obligations match; both members exact"
        else if family == "WH" then
          unless differences == #[targetRoot] && exact == 4 do
            throwError "WH changed its documented TACTIC-ASYM object set: {differences}"
        else unless differences.isEmpty do
          throwError "unexplained WF differences in {family}: {differences}"
        unless packed.isThm do
          let equationNames := (#[leanName packed.name] ++ members.map (leanName ∘ (·.name))).map (· ++ `eq_def)
          let equationNames ← equationNames.mapM fun name => do realizeGlobalConstNoOverloadCore name
          let equationEnvironment ← getEnv
          let equations ← equationNames.mapIdxM fun index name => do
            let some declaration := (equationEnvironment.find? name).bind fun info =>
                Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst info).run' {})
              | throwError "missing carried {family} equation {name}"
            let target := if index == 0 then
              Name.str (Name.str `RecognitionWFRoute family) "eq_def"
              else Name.str (Name.str (Name.str `RecognitionWFMembers family) s!"member{index - 1}") "eq_def"
            pure (declaration, ixName target)
          let withEquations ← match (Ix.Compile.Clique.transportWF members packed proofs sigma
              (ixName (Name.str `RecognitionWFRoute family)) equations const?).run' with
            | .ok result => pure result
            | .error reason => throwError "WF carried {family}: {reason}"
          for index in [0:transported.decls.size] do
            unless Ix.Compile.Clique.alphaEq transported.decls[index]!.decl.type withEquations.decls[index]!.decl.type &&
                Ix.Compile.Clique.alphaEq transported.decls[index]!.decl.value withEquations.decls[index]!.decl.value do
              throwError "WF equations changed an already-checked root/proof/member in {family}"
          for item in withEquations.decls.extract transported.decls.size withEquations.decls.size do
            let declaration := item.decl
            addDecl (.thmDecl {
              name := leanName declaration.name,
              levelParams := declaration.levelParams.toList.map leanName,
              type := uncanon (Ix.Compile.Clique.renameConsts rename declaration.type),
              value := uncanon (Ix.Compile.Clique.renameConsts rename declaration.value) })
          if family == "WG" then
            for index in [1:equations.size] do
              let sourceEquation := equations[index]!.1
              let carried := withEquations.decls[transported.decls.size + index]!.decl
              unless Ix.Compile.Clique.alphaEq sourceEquation.type carried.type do
                throwError "WG changed the source-domain member equation statement at {index}"
            IO.println "WG SOURCE EQUATIONS: both carried member statements exactly preserve source-domain equations"
          IO.println s!"WF EQUATIONS {family}: {equations.size}/{equations.size} kernel accepted"
        if family == "TW" || family == "TQ" then
          match (Ix.Compile.Clique.recoverWF members packed).run' with
          | .ok recovered => IO.println s!"WF RECOVERY {family}: {recovered.size} source leaves re-encoded"
          | .error reason =>
            IO.println s!"WF RECOVERY {family}: DECLINED {reason}"
            failures := failures.push s!"{family} recovery: {reason}"
        unless equivalent do
          let (_, ownArgs) := Ix.Compile.Canon.getAppFnArgs value
          let (_, twinArgs) := Ix.Compile.Canon.getAppFnArgs twin.value
          if family == "WG" && ownArgs.size == 4 && twinArgs.size == 4 then
            let measureEqual ← isDefEq (uncanon ownArgs[2]!) (uncanon twinArgs[2]!)
            IO.println s!"WG MEASURE: equal={measureEqual}; transformed={← ppExpr (uncanon ownArgs[2]!)}; twin={← ppExpr (uncanon twinArgs[2]!)}"
            let (_, sourceArgs) := Ix.Compile.Canon.getAppFnArgs packed.value
            unless sourceArgs.size == 4 && !measureEqual do throwError "WG measure premise changed"
            -- Independently inspected member injection paths: source ga=inl,
            -- gb=inr; target ga=inr, gb=inl. These witnesses use unequal fields.
            for (sourceInput, targetInput, pinned, guessed) in
                #[( ``wgLeft, ``wgRight, 7, 11), (``wgRight, ``wgLeft, 11, 7)] do
              let sourceMeasure := mkApp (uncanon sourceArgs[2]!) (mkConst sourceInput)
              let movedMeasure := mkApp (uncanon ownArgs[2]!) (mkConst targetInput)
              let twinMeasure := mkApp (uncanon twinArgs[2]!) (mkConst targetInput)
              unless (← isDefEq sourceMeasure (mkNatLit pinned)) &&
                  (← isDefEq movedMeasure (mkNatLit pinned)) &&
                  (← isDefEq twinMeasure (mkNatLit guessed)) do
                throwError "WG failed its independent source-to-target measure witness"
              IO.println s!"WG MEASURE WITNESS: source={pinned}, transported={pinned}, independently guessed twin={guessed}"
          else failures := failures.push s!"{family}: canonical twin differs"
      catch error =>
        let reason ← error.toMessageData.toString
        IO.println s!"WF POSITIVE {family}: ERROR {reason}"
        failures := failures.push s!"{family}: {reason}"
  unless failures.isEmpty do throwError "WF positive failures: {failures}"
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
  let evaluate (value : Ix.Expr) (component : Nat) : MetaM Expr := do
    let body := (mkApp (uncanon value) (mkConst ``userFns)).headBeta
    let some functional := body.getAppArgs.find? Expr.isLambda
      | throwError "actual packed body has no functional lambda"
    return mkApp (mkProj ``PProd component (mkApp functional (mkConst ``userFns))) (mkNatLit 0)
  let source ← evaluate packed.value 0
  -- the deleted shape route's output on this clique: the user's selector
  -- became `fun p => p.snd` (frozen data, see `frozenOldPFSelector`)
  let some frozenSel := (env.find? ``frozenOldPFSelector).bind ConstantInfo.value?
    | throwError "missing frozen PF selector"
  let changed := mkApp3 (mkConst ``applyUserProjection) (mkConst ``userFns) frozenSel (mkNatLit 0)
  let expected := mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)
  let expected := mkApp expected (mkNatLit 17)
  let wrong := mkApp (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)) (mkNatLit 29)
  unless ← isDefEq source expected do throwError "actual source functional does not return some 17"
  let same ← isDefEq changed expected
  let swapped ← isDefEq changed wrong
  IO.println s!"FROZEN OLD PF ROUTE: functional at n=0: source=some17, old target17={same}, old target29={swapped}"
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
  unless !same && swapped do throwError "the frozen old-route PF output no longer means some 29"
  ) env

def run : IO UInt32 := do
  let env ← get_env!
  let declOf (name : Name) : IO Ix.Compile.Clique.Decl := do
    let some declaration := (env.find? name).bind fun info =>
        Ix.Compile.Clique.Decl.ofConstantInfo? ((Ix.CanonM.canonConst info).run' {})
      | throw (IO.userError s!"missing repeated-parameter control {name}")
    pure declaration
  let pfPacked ← declOf ``repeatedPFPacked
  let wfPacked ← declOf ``repeatedWFPacked
  let pfMembers ← #[``repeatedPFFirst, ``repeatedPFSecond].mapM declOf
  -- The elaborator's generated members use primitive projections, whereas
  -- these ordinary source definitions elaborate through PProd.fst/snd.
  let pfMembers := pfMembers.mapIdx fun index declaration =>
    { declaration with value := canon (mkLambda `a .default (mkConst ``Nat)
      (mkProj ``PProd index (mkApp2 (mkConst ``repeatedPFPacked) (mkBVar 0) (mkBVar 0)))) }
  let wfMembers ← #[``repeatedWFFirst, ``repeatedWFSecond].mapM declOf
  for invalid in #[#[], #[0], #[0, 0], #[0, 2]] do
    let input : Ix.Compile.Clique.Input := {
      encoding := .wellFounded, members := wfMembers, aux := #[wfPacked],
      sigma := invalid, newEncName := wfPacked.name }
    let rejected := Ix.Compile.Clique.transport input
    let originals := input.aux ++ input.members
    unless rejected.baseline && rejected.decls.size == originals.size &&
        rejected.causes.size == originals.size &&
        rejected.causes.all (fun (_, cause, reason) => cause == .shape && reason.contains "bad permutation") &&
        (rejected.decls.zip originals).all (fun (actual, expected) =>
          actual.name == expected.name && Ix.Compile.Clique.alphaEq actual.type expected.type &&
          Ix.Compile.Clique.alphaEq actual.value expected.value) do
      throw (IO.userError s!"public transport accepted or lost source input for invalid permutation {invalid}")
  IO.println "Public transport rejects empty/truncated/duplicate/out-of-range permutations before identity shortcut"
  match Ix.Compile.Clique.pfLayout pfMembers pfPacked #[1, 0] pfPacked.name with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throw (IO.userError s!"PF repeated-parameter control failed for another reason: {reason}")
  | .ok _ => throw (IO.userError "PF layout accepted two fixed slots sharing one source binder")
  match Ix.Compile.Clique.wfLayout wfMembers wfPacked #[1, 0] wfPacked.name with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throw (IO.userError s!"WF repeated-parameter control failed for another reason: {reason}")
  | .ok _ => throw (IO.userError "WF layout accepted two fixed slots sharing one source binder")
  IO.println "Repeated same-typed fixed arguments: PF and WF both rejected"
  actualProbe env
  positiveProbes env
  wfMatcherControls env
  structuralIdentityControl env
  actualWFProbe env
  wfPositiveProbes env
  return 0

end Tests.Ix.Compile.Recognition
