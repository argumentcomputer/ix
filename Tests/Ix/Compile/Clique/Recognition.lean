/-
  clique-recognition: the clique library's recognisers
  (`Ix.Compile.Pass.Clique`) on Lean's own encodings, with their negative
  controls. The library is not wired into the compiler, so this suite and
  `clique-transport` are its only coverage.

  The fixtures are the twin families (`Tests/Ix/Compile/Twins/Cliques.lean`)
  and the library's own (`Tests/Ix/Compile/Clique/Fixtures.lean`), loaded at
  run time (`Common.fixturesEnv`); every transported constant this suite
  builds is added to a scratch copy of that environment with Lean's kernel.

  * repeated fixed arguments and invalid permutations: refused;
  * `partial_fixpoint` (`actualProbe`, `positiveProbes`): a user projection of
    the packing type survives (the frozen old shape route changed it), the
    conjugated functional and monotonicity proof are definitionally equal to
    the canonical twin's and kernel-accepted, the owned proof transport is
    exact, the carried equation lemmas are kernel-accepted, recovery accepts
    the decoded root and refuses an unowned one; the PF/LI/LC/PU families
    and a fixed-parameter permutation are transported exactly (PU's fallback
    excepted);
  * well-founded (`actualWFProbe`, `wfPositiveProbes`, `wfMatcherControls`): a
    user relation on the packing type survives (the frozen old shape route
    swapped it), so do a recursive-binder mention and same-typed shadowing;
    the `Nat` dispatcher is accepted only from its source declaration; every
    WF twin family is transported, kernel-accepted and exact, except the
    documented GuessLex (`WG`) and TACTIC-ASYM (`WH`) object sets;
  * structural (`structuralIdentityControl`): aliased fixed slots refused;
  * adversarial negatives (`adversarialNegatives`): user declarations named
    like encoding constants, and encoding constants' names on other bodies,
    are refused or treated as ordinary constants, as the library's
    recognition by declaration and by the authenticated family promises: a
    user `match_1` and a matcher-shaped `match_1` whose body applies a user
    function (beside Lean's below matchers of `IP` too), Lean's own below
    matcher on such a body, `below`/`brecOn` of a non-recursive structure,
    an altered `Nat.brecOn`, and decoy `m._f`s beside the functionals the
    members pass (at the recovery, the order, the transport and the plan).
    No decoy plan may transport constants the kernel rejects
    (`knownDecoyPlanGaps` records exceptions; it is empty).

  The suite may use `MetaM`/`CoreM` (it reads Lean's equation lemmas,
  converts terms and calls the kernel); the library may not and does not.

  Invoked as `lake test -- clique-recognition`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Canon
import Ix.Compile.Pass.Clique
import Ix.AuxGen.SourceFamily
import Tests.Ix.Compile.Clique.Common
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Lean Meta

namespace Tests.Ix.Compile.Clique.Recognition

open Tests.Ix.Compile.Clique.Common
open _root_.Ix.Compile.Pass.Clique (Decl Input Spine Transported alphaEqSkipMdata renameConsts)

private def say (s : String) : IO Unit := IO.println s!"[clique-recognition] {s}"

private def getDecl (env : Environment) (n : Name) : MetaM Decl := do
  let some d := declOf env n | throwError "missing fixture {n}"
  pure d

private def ofExcept {α : Type} (what : String) : Except String α → MetaM α
  | .ok a => pure a
  | .error e => throwError "{what}: {e}"

private def firstDifference (path : String) (a b : IxExpr) : Option (String × IxExpr × IxExpr) :=
  if alphaEqSkipMdata a b then none else
  match a, b with
  | .app f x _, .app g y _ =>
    firstDifference (path ++ ".fn") f g <|> firstDifference (path ++ ".arg") x y
  | .lam _ t x _ _, .lam _ u y _ _ | .forallE _ t x _ _, .forallE _ u y _ _ =>
    firstDifference (path ++ ".dom") t u <|> firstDifference (path ++ ".body") x y
  | .proj s i x _, .proj s' i' y _ =>
    if s == s' && i == i' then firstDifference (path ++ ".proj") x y else some (path, a, b)
  | _, _ => some (path, a, b)

/-- The abstracted proofs `packed._proof_k` of `env`. -/
private def proofNamesOf (env : Environment) (packedName : Name) : Array Name :=
  env.constants.fold (init := #[]) fun names name _ =>
    match name with
    | .str parent suffix => if parent == packedName && suffix.startsWith "_proof_" then names.push name else names
    | _ => names

/-! ## Well-founded recursion -/

def actualWFProbe (env : Environment) : IO Unit := _root_.runMeta (do
  let first ← getDecl env (fx "actualWFFirst")
  let second ← getDecl env (fx "actualWFSecond")
  let packedName := fx "actualWFFirst" ++ `_mutual
  let packed ← getDecl env packedName
  let proofs ← (proofNamesOf env packedName).mapM (getDecl env)
  let userWF := fx "userWF"
  let userPredicate (value : Expr) := value.find? fun candidate =>
    match candidate.getAppFn with
    | .proj ``WellFoundedRelation 0 record =>
      candidate.getAppNumArgs == 2 && record.getAppFn.constName? == some userWF
    | .const ``WellFoundedRelation.rel _ =>
      let args := candidate.getAppArgs
      args.size == 4 && args[1]!.getAppFn.constName? == some userWF
    | _ => false
  let some source := userPredicate (toLeanExpr packed.value) | throwError "missing actual WF user predicate"
  -- the deleted shape route's output on this clique (frozen data, see
  -- `frozenOldWFPredicate`)
  let some target := (env.find? (fx "frozenOldWFPredicate")).bind (·.value?)
    | throwError "missing frozen WF predicate"
  let expected := mkApp2 (mkConst ``Nat.lt) (mkNatLit 0) (mkNatLit 1)
  let wrong := mkApp2 (mkConst ``Nat.lt) (mkNatLit 1) (mkNatLit 0)
  unless ← isDefEq source expected do throwError "actual WF source predicate differs"
  let same ← isDefEq target expected
  let reversed ← isDefEq target wrong
  say s!"FROZEN OLD WF ROUTE: source=0<1, old target01={same}, old target10={reversed}; source actualWFFirst 0 is proved in Lean"
  unless !same && reversed do throwError "the frozen old-route WF output no longer means 1<0"
  let layout ← ofExcept "owned WF layout" (_root_.Ix.Compile.Pass.Clique.wfLayout #[first, second]
    packed #[1, 0] (ixName `RecognitionWFScratch.owned))
  let (head, args) := _root_.Ix.Compile.Canon.getAppFnArgs packed.value
  unless args.size == 4 do throwError "owned WF test requires specialized Nat root"
  let owned ← ofExcept "owned WF prototype" (do
      let value ← _root_.Ix.Compile.Pass.Clique.conjugateWFRoot layout packed.value
      let type ← _root_.Ix.Compile.Pass.Clique.conjugateWFType layout packed.type
      pure (type, value)).run'
  let some preserved := userPredicate (toLeanExpr owned.2)
    | throwError "owned WF lost user predicate"
  unless ← isDefEq preserved expected do throwError "owned WF changed user relation"
  kernelAddOrThrow (.defnDecl {
    name := `RecognitionWFScratch.owned,
    levelParams := packed.levelParams.toList.map toLeanName,
    type := toLeanExpr owned.1, value := toLeanExpr owned.2, hints := .opaque, safety := .safe })
  say "OWNED WF: source user relation remains 0<1; complete packed fixpoint kernel accepted"
  let .lam xn xt (.lam rn rt tree rbi _) xbi _ := args[3]!
    | throwError "WF control: missing exact functional binders"
  let some decoded := _root_.Ix.Compile.Pass.Clique.decodeTree 2 tree
    | throwError "WF control: missing exact case tree"
  let .lam pn pt (.lam an recursiveType leaf abi _) pbi _ := decoded.leaves[0]!
    | throwError "WF control: missing exact leaf binders"
  let shadow := _root_.Ix.Expr.mkLam an (_root_.Ix.Compile.Canon.liftLoose recursiveType 1)
    (_root_.Ix.Compile.Canon.liftLoose leaf 1) abi
  let leaf' := _root_.Ix.Expr.mkApp shadow (_root_.Ix.Expr.mkBVar 0)
  let newLeaf := _root_.Ix.Expr.mkLam pn pt (_root_.Ix.Expr.mkLam an recursiveType leaf' abi) pbi
  let decoded := { decoded with leaves := decoded.leaves.set! 0 newLeaf }
  let some tree' := decoded.build | throwError "WF control: failed to rebuild case tree"
  let functional := _root_.Ix.Expr.mkLam xn xt (_root_.Ix.Expr.mkLam rn rt tree' rbi) xbi
  kernelAddOrThrow (.defnDecl {
    name := `RecognitionWFScratch.sourceBinderMention,
    levelParams := packed.levelParams.toList.map toLeanName,
    type := toLeanExpr packed.type,
    value := toLeanExpr (_root_.Ix.Compile.Canon.mkAppN head (args.set! 3 functional)),
    hints := .opaque, safety := .safe })
  let value ← ofExcept "WF binder-mention control" (_root_.Ix.Compile.Pass.Clique.conjugateWFRoot layout
      (_root_.Ix.Compile.Canon.mkAppN head (args.set! 3 functional))).run'
  kernelAddOrThrow (.defnDecl {
    name := `RecognitionWFScratch.binderMention,
    levelParams := packed.levelParams.toList.map toLeanName,
    type := toLeanExpr owned.1, value := toLeanExpr value, hints := .opaque, safety := .safe })
  let some preserved := userPredicate (toLeanExpr value) | throwError "WF control lost user relation"
  unless ← isDefEq preserved expected do throwError "WF binder mention changed user relation"
  say "OWNED WF: exact recursive-binder argument and same-typed shadowing preserve 0<1; kernel accepted"
  let recovered ← ofExcept "owned WF recovery"
    (_root_.Ix.Compile.Pass.Clique.recoverWF #[first, second] packed).run'
  let some recoveredPredicate := userPredicate (toLeanExpr recovered[0]!)
    | throwError "WF recovery erased the user's relation"
  unless ← isDefEq recoveredPredicate expected do throwError "WF recovery changed the user predicate"
  say "OWNED WF RECOVERY: source user relation retained as 0<1; re-encoding passed"
  let equationNames ← #[packedName ++ `eq_def, fx "actualWFFirst" ++ `eq_def,
      fx "actualWFSecond" ++ `eq_def].mapM fun name => do realizeGlobalConstNoOverloadCore name
  let equationEnv ← getEnv
  let equations ← equationNames.mapIdxM fun index name => do
    let some declaration := (equationEnv.find? name).bind fun info =>
        Decl.ofConstantInfo? (toIxConst info)
      | throwError "missing WF equation {name}"
    let targetName := if index == 0 then `RecognitionWFEquation.packed.eq_def
      else Name.str `RecognitionWFEquation s!"equation{index}"
    pure (declaration, ixName targetName)
  let equationOutput ← ofExcept "WF carried equations"
    (_root_.Ix.Compile.Pass.Clique.transportWF #[first, second] packed proofs
      #[1, 0] (ixName `RecognitionWFEquation.packed) equations).run'
  let rename (name : IxName) : Option IxName :=
    if name == first.name then some (ixName `RecognitionWFEquation.first)
    else if name == second.name then some (ixName `RecognitionWFEquation.second) else none
  let order := ((List.range proofs.size).toArray.map (· + 1)).push 0 ++
    (List.range (equationOutput.decls.size - proofs.size - 1)).toArray.map (· + proofs.size + 1)
  for index in order do
    kernelAddOrThrow (kernelOfDecl equationOutput.decls[index]!.decl rename)
  say s!"WF CARRIED EQUATIONS: all {equationOutput.decls.size} declarations including 3 equations kernel accepted"
  ) env

def wfMatcherControls (env : Environment) : IO Unit := _root_.runMeta (do
  let const? := constOf env
  let matcher := ixName `Tests.Ix.Compile.Twins.Cliques.TS.P0.evT.match_1
  discard <| ofExcept "real source matcher declined"
    (_root_.Ix.Compile.Pass.Clique.decodeWFNatMatcher const? matcher #[]).run'
  let expectDecline (lookup : IxName → Option IxConst) (name : IxName)
      (reason : String) : MetaM Unit := do
    match (_root_.Ix.Compile.Pass.Clique.decodeWFNatMatcher lookup name #[]).run' with
    | .ok _ => throwError "matcher ownership accepted a negative control"
    | .error actual => unless actual.contains reason do throwError "matcher declined for another reason: {actual}"
  let some dispatch := privateNamed? env (fx "userNatDispatch")
    | throwError "missing the private user dispatcher"
  expectDecline (fun _ => none) matcher "unavailable"
  expectDecline (fun _ => const? matcher) (ixName `Another.sourceIdentity) "another source declaration identity"
  expectDecline const? (ixName dispatch) "zero minor does not return its motive"
  let nat := mkConst ``Nat
  let userCall := mkAppN (mkConst dispatch) #[
    mkLambda `n .default nat nat, mkNatLit 0,
    mkLambda `unit .default (mkConst ``Unit) (mkNatLit 29),
    mkLambda `n .default nat (mkNatLit 31)]
  unless ← isDefEq userCall (mkNatLit 17) do throwError "user dispatch value control is not 17"
  let spine : Spine := {
    kind := .psum, leaves := #[toIxExpr nat, toIxExpr (mkConst ``Bool)],
    lvls := #[_root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero, _root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero] }
  let some spineType := spine.type? | throwError "the control packing has no type"
  let some permutedType := (spine.permute #[1, 0]).bind (·.type?)
    | throwError "the permuted control packing has no type"
  let constantCodomain := _root_.Ix.Expr.mkLam (ixName `input) spineType spineType .default
  let moved ← ofExcept "constant-codomain control"
    (_root_.Ix.Compile.Pass.Clique.decodeWFCase spine #[1, 0] constantCodomain).run'
  let expected := _root_.Ix.Expr.mkLam (ixName `input) permutedType spineType .default
  unless alphaEqSkipMdata moved expected do throwError "same-typed user codomain was permuted"
  say "WF MATCHER OWNERSHIP: exact source dispatch accepted; absent/aliased/private user declarations rejected; user 17 retained; constant packing-valued codomain unchanged"
  ) env

def wfPositiveProbes (env : Environment) : IO Unit := _root_.runMeta (do
  let const? := constOf env
  let cases : Array (String × Array String) := #[
    ("WD", #["wa", "wb"]), ("W3", #["ga", "gb", "gc"]),
    ("WG", #["ga", "gb"]), ("WT", #["ta", "tb"]), ("WB", #["ba", "bb"]),
    ("WP", #["ha", "hb"]), ("WA", #["ta", "tb", "tc"]),
    ("WH", #["ha", "hb"]), ("WU", #["wx", "wy"]),
    ("TW", #["wa", "wb"]), ("TQ", #["qa", "qb"]), ("TS", #["evT", "odT"])]
  let mut failures : Array String := #[]
  for (family, names) in cases do
    let familyPrefix := Name.str `Tests.Ix.Compile.Twins.Cliques family
    let readMembers (presentation : String) := names.mapM fun name =>
      getDecl env (Name.str (Name.str familyPrefix presentation) name)
    let sourceMembers ← readMembers "P0"
    let targetMembers ← readMembers "P1"
    let unpack (declaration : Decl) := do
      let (_, body) := _root_.Ix.Compile.Pass.Clique.peelLams
        (_root_.Ix.Compile.Pass.Clique.lamArity declaration.value) declaration.value #[]
      let (head, _, args) ← _root_.Ix.Compile.Pass.Clique.constApp? body
      let argument ← args.back?
      let (_, index, _) ← _root_.Ix.Compile.Pass.Clique.decodeInj names.size argument
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
    let packed ← getDecl env (toLeanName sourceData[0]!.1)
    let twin ← getDecl env (toLeanName targetData[0]!.1)
    if family == "WG" || family == "W3" then
      let sourceArgs := (toLeanExpr packed.value).getAppArgs
      say s!"{family} ROOT: {(toLeanExpr packed.value).getAppFn}; source relation={← ppExpr sourceArgs[2]!}; wf={← ppExpr sourceArgs[3]!}"
      let targetArgs := (toLeanExpr twin.value).getAppArgs
      say s!"{family} TARGET RELATION: {← ppExpr targetArgs[2]!}"
    let result := (do
      let layout ← _root_.Ix.Compile.Pass.Clique.liftE
        (_root_.Ix.Compile.Pass.Clique.wfLayout members packed sigma packed.name)
      let value ← _root_.Ix.Compile.Pass.Clique.withReorderedBinders2 true layout.numFixed layout.fixedPerm
        packed.value pure (fun value => _root_.Ix.Compile.Pass.Clique.conjugateWFRoot layout value const?)
      let type ← _root_.Ix.Compile.Pass.Clique.withReorderedBinders2 false layout.numFixed layout.fixedPerm
        packed.type pure (_root_.Ix.Compile.Pass.Clique.conjugateWFType layout)
      pure (type, value)).run'
    match result with
    | .error reason =>
      say s!"WF POSITIVE {family}: DECLINED {reason}"
      failures := failures.push s!"{family}: {reason}"
    | .ok (type, value) =>
      try
        kernelAddOrThrow (.defnDecl {
          name := Name.str `RecognitionWFPositive family,
          levelParams := packed.levelParams.toList.map toLeanName,
          type := toLeanExpr type, value := toLeanExpr value, hints := .opaque, safety := .safe })
        let equivalent ← isDefEq (toLeanExpr value) (toLeanExpr twin.value)
        say s!"WF POSITIVE {family}: kernel accepted; twin defeq={equivalent}"
        let proofs ← (proofNamesOf env (toLeanName packed.name)).mapM (getDecl env)
        let transported ← ofExcept s!"WF production candidate {family}"
          (_root_.Ix.Compile.Pass.Clique.transportWF members packed proofs sigma
            (ixName (Name.str `RecognitionWFRoute family)) #[] const?).run'
        let rename (name : IxName) : Option IxName := do
          let index ← members.findIdx? (·.name == name)
          some (ixName (Name.str (Name.str `RecognitionWFMembers family) s!"member{index}"))
        let order := ((List.range proofs.size).toArray.map (· + 1)).push 0 ++
          (List.range members.size).toArray.map (· + proofs.size + 1)
        for index in order do
          kernelAddOrThrow (kernelOfDecl transported.decls[index]!.decl rename)
        say s!"WF PRODUCTION {family}: all {transported.decls.size} declarations kernel accepted"
        let targetRoot := twin.name
        let counterpart (name : IxName) : Option IxName :=
          if name == ixName (Name.str `RecognitionWFRoute family) then some targetRoot else
          match sourceMembers.findIdx? (·.name == name) with
          | some index => some targetMembers[index]!.name
          | none => match name with
            | .str parent suffix _ =>
              if parent == ixName (Name.str `RecognitionWFRoute family) && suffix.startsWith "_proof_" then
                some (_root_.Ix.Name.mkStr targetRoot suffix)
              else none
            | _ => none
        let mut exact := 0
        let mut differences : Array IxName := #[]
        for item in transported.decls do
          let some name := counterpart item.decl.name | throwError "no WF target counterpart {item.decl.name}"
          let expected ← getDecl env (toLeanName name)
          let typeEqual := alphaEqSkipMdata (renameConsts counterpart item.decl.type) expected.type
          let valueEqual := alphaEqSkipMdata (renameConsts counterpart item.decl.value) expected.value
          if typeEqual && valueEqual then exact := exact + 1
          else
            differences := differences.push name
            say s!"WF EXACT DIFFERENCE {family}/{name}: type={typeEqual}, value={valueEqual}"
            if family == "WG" then
              let maskedType := alphaEqSkipMdata
                (maskMeasures (renameConsts counterpart item.decl.type)) (maskMeasures expected.type)
              let maskedValue := alphaEqSkipMdata
                (maskMeasures (renameConsts counterpart item.decl.value)) (maskMeasures expected.value)
              -- A decreasing proof's body depends on its measure; the existing
              -- policy compares its statement. Every literal proof checks above.
              let isProof := name == _root_.Ix.Name.mkStr targetRoot "_proof_1" ||
                name == _root_.Ix.Name.mkStr targetRoot "_proof_2"
              unless maskedType && (isProof || maskedValue) do
                throwError "WG has a difference outside the established measure policy: {name}"
        say s!"WF EXACT {family}: {exact}/{transported.decls.size}"
        if family == "WG" then
          let expected := #[targetRoot, _root_.Ix.Name.mkStr targetRoot "_proof_1",
            _root_.Ix.Name.mkStr targetRoot "_proof_2"]
          unless differences.size == expected.size && expected.all differences.contains && exact == 2 do
            throwError "WG enlarged or changed its documented differing-object set: {differences}"
          say "WG POLICY: exactly packed root + two decreasing proofs; all masked obligations match; both members exact"
        else if family == "WH" then
          unless differences == #[targetRoot] && exact == 4 do
            throwError "WH changed its documented TACTIC-ASYM object set: {differences}"
        else unless differences.isEmpty do
          throwError "unexplained WF differences in {family}: {differences}"
        unless packed.isThm do
          let equationNames := (#[toLeanName packed.name] ++ members.map (toLeanName ∘ (·.name))).map (· ++ `eq_def)
          let equationNames ← equationNames.mapM fun name => do realizeGlobalConstNoOverloadCore name
          let equationEnvironment ← getEnv
          let equations ← equationNames.mapIdxM fun index name => do
            let some declaration := (equationEnvironment.find? name).bind fun info =>
                Decl.ofConstantInfo? (toIxConst info)
              | throwError "missing carried {family} equation {name}"
            let target := if index == 0 then
              Name.str (Name.str `RecognitionWFRoute family) "eq_def"
              else Name.str (Name.str (Name.str `RecognitionWFMembers family) s!"member{index - 1}") "eq_def"
            pure (declaration, ixName target)
          let withEquations ← ofExcept s!"WF carried {family}"
            (_root_.Ix.Compile.Pass.Clique.transportWF members packed proofs sigma
              (ixName (Name.str `RecognitionWFRoute family)) equations const?).run'
          for index in [0:transported.decls.size] do
            unless alphaEqSkipMdata transported.decls[index]!.decl.type withEquations.decls[index]!.decl.type &&
                alphaEqSkipMdata transported.decls[index]!.decl.value withEquations.decls[index]!.decl.value do
              throwError "WF equations changed an already-checked root/proof/member in {family}"
          for item in withEquations.decls.extract transported.decls.size withEquations.decls.size do
            let declaration := item.decl
            kernelAddOrThrow (.thmDecl {
              name := toLeanName declaration.name,
              levelParams := declaration.levelParams.toList.map toLeanName,
              type := toLeanExpr (renameConsts rename declaration.type),
              value := toLeanExpr (renameConsts rename declaration.value) })
          if family == "WG" then
            for index in [1:equations.size] do
              let sourceEquation := equations[index]!.1
              let carried := withEquations.decls[transported.decls.size + index]!.decl
              unless alphaEqSkipMdata sourceEquation.type carried.type do
                throwError "WG changed the source-domain member equation statement at {index}"
            say "WG SOURCE EQUATIONS: both carried member statements exactly preserve source-domain equations"
          say s!"WF EQUATIONS {family}: {equations.size}/{equations.size} kernel accepted"
        if family == "TW" || family == "TQ" then
          match (_root_.Ix.Compile.Pass.Clique.recoverWF members packed).run' with
          | .ok recovered => say s!"WF RECOVERY {family}: {recovered.size} source leaves re-encoded"
          | .error reason =>
            say s!"WF RECOVERY {family}: DECLINED {reason}"
            failures := failures.push s!"{family} recovery: {reason}"
        unless equivalent do
          let (_, ownArgs) := _root_.Ix.Compile.Canon.getAppFnArgs value
          let (_, twinArgs) := _root_.Ix.Compile.Canon.getAppFnArgs twin.value
          if family == "WG" && ownArgs.size == 4 && twinArgs.size == 4 then
            let measureEqual ← isDefEq (toLeanExpr ownArgs[2]!) (toLeanExpr twinArgs[2]!)
            say s!"WG MEASURE: equal={measureEqual}; transformed={← ppExpr (toLeanExpr ownArgs[2]!)}; twin={← ppExpr (toLeanExpr twinArgs[2]!)}"
            let (_, sourceArgs) := _root_.Ix.Compile.Canon.getAppFnArgs packed.value
            unless sourceArgs.size == 4 && !measureEqual do throwError "WG measure premise changed"
            -- Independently inspected member injection paths: source ga=inl,
            -- gb=inr; target ga=inr, gb=inl. These witnesses use unequal fields.
            for (sourceInput, targetInput, pinned, guessed) in
                #[(fx "wgLeft", fx "wgRight", 7, 11), (fx "wgRight", fx "wgLeft", 11, 7)] do
              let sourceMeasure := mkApp (toLeanExpr sourceArgs[2]!) (mkConst sourceInput)
              let movedMeasure := mkApp (toLeanExpr ownArgs[2]!) (mkConst targetInput)
              let twinMeasure := mkApp (toLeanExpr twinArgs[2]!) (mkConst targetInput)
              unless (← isDefEq sourceMeasure (mkNatLit pinned)) &&
                  (← isDefEq movedMeasure (mkNatLit pinned)) &&
                  (← isDefEq twinMeasure (mkNatLit guessed)) do
                throwError "WG failed its independent source-to-target measure witness"
              say s!"WG MEASURE WITNESS: source={pinned}, transported={pinned}, independently guessed twin={guessed}"
          else failures := failures.push s!"{family}: canonical twin differs"
      catch error =>
        let reason ← error.toMessageData.toString
        say s!"WF POSITIVE {family}: ERROR {reason}"
        failures := failures.push s!"{family}: {reason}"
  unless failures.isEmpty do throwError "WF positive failures: {failures}"
  ) env

/-! ## Structural recursion -/

def structuralIdentityControl (env : Environment) : IO Unit := _root_.runMeta (do
  let const? := constOf env
  let members ← #[fx "RepeatedStructural.first", fx "RepeatedStructural.second"].mapM (getDecl env)
  -- the authenticated `below`/`brecOn` family of the block (`Input.family`):
  -- the structural layout refuses without it
  let family ← ofExcept "structural identity family"
    (_root_.Ix.Compile.Pass.Clique.authenticatedFamily (ixEnvOf env) members)
  let layout ← ofExcept "ordinary structural identity fixture declined"
    (_root_.Ix.Compile.Pass.Clique.structLayout members #[] #[1, 0] const? family)
  unless layout.numFixed == 2 do throwError "structural identity fixture lost its two fixed slots"
  let rec aliasSecond : Nat → IxExpr → IxExpr
    | 0, expression => expression
    | fuel + 1, expression =>
      let go := aliasSecond fuel
      match expression with
      | .app .. =>
        let (head, args) := _root_.Ix.Compile.Canon.getAppFnArgs expression
        let args := args.map go
        let args := match head with
          | .const name _ _ => if layout.fNames.contains name && args.size ≥ 2 then args.set! 1 args[0]! else args
          | _ => args
        _root_.Ix.Compile.Canon.mkAppN head args
      | .lam n t b bi _ => _root_.Ix.Expr.mkLam n (go t) (go b) bi
      | .forallE n t b bi _ => _root_.Ix.Expr.mkForallE n (go t) (go b) bi
      | .letE n t v b nd _ => _root_.Ix.Expr.mkLetE n (go t) (go v) (go b) nd
      | .proj s i x _ => _root_.Ix.Expr.mkProj s i (go x)
      | .mdata d x _ => _root_.Ix.Expr.mkMData d (go x)
      | e => e
  let altered := members.map fun declaration => { declaration with value := aliasSecond 1000 declaration.value }
  for (declaration, index) in altered.zipIdx do
    kernelAddOrThrow (.defnDecl {
      name := Name.str `RecognitionStructuralAlias s!"member{index}",
      levelParams := declaration.levelParams.toList.map toLeanName,
      type := toLeanExpr declaration.type, value := toLeanExpr declaration.value,
      hints := .opaque, safety := .safe })
  say "Structural repeated fixed-slot control: both altered source declarations kernel accepted"
  match _root_.Ix.Compile.Pass.Clique.structLayout altered #[] #[1, 0] const? family with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throwError "structural alias control declined for another reason: {reason}"
  | .ok layout => throwError "structural layout accepted aliased source binder identities: {repr layout.memberFixed}"
  ) env

/-! ## `partial_fixpoint` -/

def positiveProbes (env : Environment) : IO Unit := _root_.runMeta (do
  let const? := constOf env
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
    let sourcePrefix := if family == "Fixed" then fx "FixedP0" else Name.str familyPrefix "P0"
    let targetPrefix := if family == "Fixed" then fx "FixedP1" else Name.str familyPrefix s!"P{presentation}"
    let members ← memberNames.mapM fun name => getDecl env (Name.str sourcePrefix name)
    let sigma ← memberNames.mapM fun name => do
      let target ← getDecl env (Name.str targetPrefix name)
      let (_, value) := _root_.Ix.Compile.Pass.Clique.peelLams
        (_root_.Ix.Compile.Pass.Clique.lamArity target.value) target.value #[]
      let (head, _) := _root_.Ix.Compile.Canon.getAppFnArgs value
      let (steps, _) := _root_.Ix.Compile.Pass.Clique.projChain head
      let some (index, used) := _root_.Ix.Compile.Pass.Clique.pathPrefix memberNames.size steps
        | throwError "target member has no packed component"
      unless used == steps.size do throwError "target member has an extra projection"
      pure index
    let packedName := Name.str (toLeanName members[0]!.name) "mutual"
    let packed ← getDecl env packedName
    let proofNames := proofNamesOf env packedName
    say s!"POSITIVE {family}/P{presentation}: source proof declarations={proofNames}"
    let proofs ← proofNames.mapM (getDecl env)
    let some inverse := _root_.Ix.Compile.Pass.Clique.invPerm sigma
      | throwError "{family}: the target order is not a permutation"
    let newPacked := Name.str (Name.str sourcePrefix memberNames[inverse[0]!]!) "mutual"
    let (out, state) ← ofExcept s!"{family}/P{presentation} declined"
      ((_root_.Ix.Compile.Pass.Clique.transportPF members packed proofs sigma (ixName newPacked) const?).run {})
    let normalize (name : IxName) := ixName ((toLeanName name).replacePrefix targetPrefix sourcePrefix)
    let mut exact := 0
    let names := out.decls.map (·.decl.name)
    let scratch := Name.str `RecognitionPositive s!"{family}{presentation}"
    let scratchName (name : IxName) : Option IxName :=
      if names.contains name then some (ixName (scratch ++ (toLeanName name).replacePrefix sourcePrefix .anonymous)) else none
    let order := (List.range proofs.size).toArray.map (· + 1) ++ #[0] ++
      ((List.range members.size).toArray.map (· + 1 + proofs.size))
    for index in order do
      let item := out.decls[index]!
      let targetName := (toLeanName item.decl.name).replacePrefix sourcePrefix targetPrefix
      let target ← getDecl env targetName
      let equalSyntax := eqUpTo normalize item.decl.type target.type &&
        eqUpTo normalize item.decl.value target.value
      if equalSyntax then exact := exact + 1
      else unless family == "PU" && item.fallback.isSome do
        let normalized := renameConsts (fun name => some (normalize name)) target.value
        if let some (path, a, b) := firstDifference "value" item.decl.value normalized then
          say s!"DIFFERENCE {path}: actual {← ppExpr (toLeanExpr a)}; expected {← ppExpr (toLeanExpr b)}"
        say s!"FALLBACKS {state.fallbacks}"
        throwError "{family}/P{presentation}: noncanonical {toLeanName item.decl.name}"
      kernelAddOrThrow (kernelOfDecl item.decl scratchName)
    unless family == "PU" || state.fallbacks.isEmpty do throwError "{family}: unexpected fallback {state.fallbacks}"
    say s!"POSITIVE {family}/P{presentation}: exact={exact}/{out.decls.size}, kernel={out.decls.size}/{out.decls.size}, fallbacks={state.fallbacks.size}"
  ) env

def actualProbe (env : Environment) : IO Unit := _root_.runMeta (do
  let first ← getDecl env (fx "actualFirst")
  let second ← getDecl env (fx "actualSecond")
  let packed ← getDecl env (fx "actualFirst.mutual")
  let layout ← ofExcept "actual layout"
    (_root_.Ix.Compile.Pass.Clique.pfLayout #[first, second] packed #[1, 0] packed.name)
  say s!"ACTUAL layout fixed={layout.numFixed}, leaves={layout.leaves.size}"
  say s!"ACTUAL source packed: {← ppExpr (toLeanExpr packed.value)}"
  let userFns := mkConst (fx "userFns")
  let evaluate (value : IxExpr) (component : Nat) : MetaM Expr := do
    let body := (mkApp (toLeanExpr value) userFns).headBeta
    let some functional := body.getAppArgs.find? Expr.isLambda
      | throwError "actual packed body has no functional lambda"
    return mkApp (mkProj ``PProd component (mkApp functional userFns)) (mkNatLit 0)
  let source ← evaluate packed.value 0
  -- the deleted shape route's output on this clique: the user's selector
  -- became `fun p => p.snd` (frozen data, see `frozenOldPFSelector`)
  let some frozenSel := (env.find? (fx "frozenOldPFSelector")).bind (·.value?)
    | throwError "missing frozen PF selector"
  let changed := mkApp3 (mkConst (fx "applyUserProjection")) userFns frozenSel (mkNatLit 0)
  let expected := mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)
  let expected := mkApp expected (mkNatLit 17)
  let wrong := mkApp (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Nat)) (mkNatLit 29)
  unless ← isDefEq source expected do throwError "actual source functional does not return some 17"
  let same ← isDefEq changed expected
  let swapped ← isDefEq changed wrong
  say s!"FROZEN OLD PF ROUTE: functional at n=0: source=some17, old target17={same}, old target29={swapped}"
  let body := (mkApp (toLeanExpr packed.value) userFns).headBeta
  say s!"FIX HEAD {body.getAppFn.constName?} ARITY {body.getAppArgs.size}"
  for arg in body.getAppArgs do say s!"FIX ARG {← ppExpr arg}"
  for (n, ci) in env.constants.toList do
    if n.getPrefix == fx "actualFirst.mutual" then
      say s!"PROOF {n}: {← ppExpr ci.type}"
      if let .thmInfo info := ci then say s!"PROOF VALUE {← ppExpr info.value}"
  let some functional := body.getAppArgs.find? Expr.isLambda
    | throwError "actual functional missing"
  let conjugated ← match _root_.Ix.Compile.Pass.Clique.conjugatePF 2 #[1, 0] (toIxExpr functional) with
    | .ok e => pure (toLeanExpr e)
    | .error e => throwError "conjugation declined: {e}"
  let conjugatedValue := mkApp (mkProj ``PProd 1 (mkApp conjugated userFns)) (mkNatLit 0)
  unless ← isDefEq conjugatedValue expected do throwError "conjugation changed the user value"
  say s!"CONJUGATED actual functional: value=some17; {← ppExpr conjugated}"
  let twin ← getDecl env (fx "actualSecondTwin.mutual")
  let twinBody := (mkApp (toLeanExpr twin.value) userFns).headBeta
  let some twinFunctional := twinBody.getAppArgs.find? Expr.isLambda
    | throwError "missing twin functional"
  unless ← isDefEq conjugated twinFunctional do throwError "conjugation disagrees with the canonical source twin"
  say "CONJUGATED canonical source twin: definitionally equal"
  let some control := (env.find? (fx "binderMentionControl")).bind (·.value?)
    | throwError "missing binder-mention control"
  let control' ← match _root_.Ix.Compile.Pass.Clique.conjugatePF 2 #[1, 0] (toIxExpr control) with
    | .ok e => pure (toLeanExpr e)
    | .error e => throwError "control conjugation: {e}"
  let controlValue := mkApp (mkProj ``PProd 1 (mkApp control' userFns)) (mkNatLit 0)
  unless ← isDefEq controlValue expected do throwError "binder mention or shadowing changed a user value"
  say "CONJUGATED recursive-binder mention + shadowing control: some17"
  let sourceProof ← getDecl env (fx "actualFirst.mutual" ++ `_proof_1)
  let proofBody := (mkApp (toLeanExpr sourceProof.value) userFns).headBeta
  let composeInfo ← getConstInfo ``Lean.Order.monotone_compose
  let layout := { layout with composeLevels := composeInfo.levelParams.toArray.map ixName }
  let mono ← match _root_.Ix.Compile.Pass.Clique.conjugatePFMono layout (toIxExpr proofBody) with
    | .ok e => pure (toLeanExpr e)
    | .error e => throwError "proof conjugation declined: {e}"
  let fixArgs := body.getAppArgs
  let whole := mkAppN body.getAppFn #[fixArgs[0]!, fixArgs[1]!, conjugated, mono]
  kernelAddOrThrow (.defnDecl {
    name := `RecognitionScratch.conjugated, levelParams := [], type := fixArgs[0]!,
    value := whole, hints := .opaque, safety := .safe })
  say "CONJUGATED packed fixpoint + composed monotonicity proof: Lean kernel accepted"
  let const? := constOf env
  let (checkedMono, checkedState) ← ofExcept "owned proof transport"
    ((_root_.Ix.Compile.Pass.Clique.conjugatePFMonoChecked layout const? (toIxExpr proofBody)).run {})
  let checkedWhole := mkAppN body.getAppFn #[fixArgs[0]!, fixArgs[1]!, conjugated, toLeanExpr checkedMono]
  kernelAddOrThrow (.defnDecl {
    name := `RecognitionScratch.ownedProof, levelParams := [], type := fixArgs[0]!,
    value := checkedWhole, hints := .opaque, safety := .safe })
  let twinProof ← getDecl env (fx "actualSecondTwin.mutual" ++ `_proof_1)
  let twinProofBody := (mkApp (toLeanExpr twinProof.value) userFns).headBeta
  say s!"OWNED proof: kernel accepted; fallbacks={checkedState.fallbacks}; exact twin={alphaEqSkipMdata checkedMono (toIxExpr twinProofBody)}"
  unless checkedState.fallbacks.isEmpty do throwError "ordinary generated proof fell back"
  unless alphaEqSkipMdata checkedMono (toIxExpr twinProofBody) do
    throwError "owned proof transport changed canonical generated syntax"
  let firstEquationName ← realizeGlobalConstNoOverloadCore (fx "actualFirst" ++ `eq_def)
  let secondEquationName ← realizeGlobalConstNoOverloadCore (fx "actualSecond" ++ `eq_def)
  let equationEnv ← getEnv
  let equationOf (name : Name) := (equationEnv.find? name).bind fun c =>
    Decl.ofConstantInfo? (toIxConst c)
  let some firstEquation := equationOf firstEquationName | throwError "missing first equation"
  let some secondEquation := equationOf secondEquationName | throwError "missing second equation"
  let equations := #[(firstEquation, firstEquation.name), (secondEquation, secondEquation.name)]
  let (repaired, repairState) ← ofExcept "production PF routing"
    ((_root_.Ix.Compile.Pass.Clique.transportPF #[first, second] packed #[sourceProof]
      #[1, 0] (ixName `RecognitionScratch.packed) const? equations).run {})
  unless repairState.fallbacks.isEmpty do throwError "production repair unexpectedly fell back"
  let repairedValue ← evaluate repaired.decls[0]!.decl.value 1
  unless ← isDefEq repairedValue expected do throwError "production PF routing changed the user's value"
  let renamed (name : IxName) : Option IxName := do
    let index ← repaired.decls.findIdx? (·.decl.name == name)
    if index < 2 then some name else some (ixName (Name.str `RecognitionScratch s!"decl{index}"))
  for index in #[1, 0, 2, 3, 4, 5] do
    kernelAddOrThrow (kernelOfDecl repaired.decls[index]!.decl renamed)
  say "PRODUCTION PF routing: source value preserved; all six declarations including equation lemmas kernel accepted"
  match _root_.Ix.Compile.Pass.Clique.recoverPF #[first, second] packed with
  | .ok (components, _) =>
    unless components.size == 2 do throwError "PF recovery lost a component"
  | .error reason => throwError "PF recovery rejected the decoded source: {reason}"
  let foreignRoot := renameConsts
    (fun name => if name == _root_.Ix.Compile.Pass.Clique.nOrderFix then some (ixName `Unowned.fix) else none)
    packed.value
  match _root_.Ix.Compile.Pass.Clique.recoverPF #[first, second] { packed with value := foreignRoot } with
  | .error _ => pure ()
  | .ok _ => throwError "PF recovery accepted a functional under an unowned root"
  say "PF recovery: decoded root accepted; unowned root rejected"
  unless !same && swapped do throwError "the frozen old-route PF output no longer means some 29"
  ) env

/-! ## Adversarial negatives: names of encoding constants on other bodies

The library identifies a below matcher by its declaration (`matcherShape?`),
the `below`/`brecOn` family by authentication (`familyCandidates`,
`Ix.AuxGen.SourceFamily.filterHeads`, `blockOf`), and a member's functional
by the `brecOn` applications (`StructLayout.fNames`, checked by
`recoverStructural`). Each case gives a user declaration the name of an
encoding constant, or an encoding constant's name another body, and requires
a refusal or an ordinary constant. -/

/-- Lean's `all` of `member`, and the clique's members. -/
def cliqueOf (env : Environment) (member : Name) : MetaM (Array IxName × Array Decl) := do
  let const? := constOf env
  let some ci := const? (ixName member) | throwError "missing clique member {member}"
  let all := _root_.Ix.Compile.Pass.Clique.allOf ci
  let members ← all.mapM fun n => getDecl env (toLeanName n)
  pure (all, members)

/-- What a decoy `m._f` holds. -/
inductive DecoyKind where
  /-- a functional's body (the next member's when the types agree, else the
  member's own behind a `(fun x => x)` redex): it binds a `below` dictionary
  of its own -/
  | body
  /-- a bare reference to `m.otherF`, another copy of Lean's functional (the
  next member's when the types agree, else the member's own) that the
  members do not pass -/
  | ref
  deriving BEq

def DecoyKind.tag : DecoyKind → String
  | .body => "body" | .ref => "ref"

/-- The decoy input of a structural clique (`members`, Lean's order, each
with its functional `m._f`): the members pass copies of Lean's functionals
under the names `m.realF`, and every name `m._f` holds a user declaration of
the same type with another body (`DecoyKind`). Returns the overlay (the
rewritten members, the decoys, the copies `m.realF` and `m.otherF`), the
rewritten members, the decoys, and the two sets of copies. -/
def decoyInput (const? : IxName → Option IxConst) (kind : DecoyKind) (members fs : Array Decl) :
    Std.HashMap IxName IxConst × Array Decl × Array Decl × Array Decl × Array Decl := Id.run do
  let copy (s : String) := fs.zipWith (fun f m => { f with name := _root_.Ix.Name.mkStr m.name s }) members
  let copies := copy "realF"
  let others := copy "otherF"
  let ren (n : IxName) : Option IxName := (fs.findIdx? (·.name == n)).bind fun i => copies[i]?.map (·.name)
  let members' := members.map fun d => { d with value := renameConsts ren d.value }
  let decoys := fs.zipIdx.map fun (f, i) =>
    let j := if alphaEqSkipMdata f.type fs[(i + 1) % fs.size]!.type then (i + 1) % fs.size else i
    match kind with
    | .body =>
      let redex := _root_.Ix.Expr.mkApp
        (_root_.Ix.Expr.mkLam (ixName `x) f.type (_root_.Ix.Expr.mkBVar 0) .default) f.value
      if j != i then { f with value := fs[j]!.value } else { f with value := redex }
    | .ref =>
      { f with value := _root_.Ix.Expr.mkConst others[j]!.name (f.levelParams.map _root_.Ix.Level.mkParam) }
  let mut overlay : Std.HashMap IxName IxConst := {}
  for d in decoys ++ copies ++ others do overlay := overlay.insert d.name (constOfDecl d)
  -- the members keep their own constants (Lean's `all`), with the new values
  for d in members' do
    if let some ci := const? d.name then
      overlay := overlay.insert d.name (_root_.Ix.Compile.Pass.Clique.withValue ci d.value)
  return (overlay, members', decoys, copies, others)

/-- The library gaps the decoy plans found, recorded rather than silenced:
each listed case must still fail the kernel (a listed case that no longer
fails is stale and fails the suite), and any other failing case fails it.

Empty. The one gap these cases found, `ref SP P1`, is fixed in the
library: `planClique` takes the clique's encoding constants from the names
`m._f` (`encodingOf`), while the structural transport reorders the calls of
the functionals the members' `brecOn` applications pass
(`StructLayout.fNames`); with the members passing `m.realF` and user
declarations under `m._f`, the plan transported the members over
`fa.realF`, which kept Lean's telescope (the kernel: application type
mismatch). `structLayout` now refuses a functional that is not one of the
encoding's constants, so the case is not transported. An entry here needs
its reason. -/
def knownDecoyPlanGaps : List String := []

/-- Add a transported plan's constants with the kernel: `extra` (the
constants the input adds, when the environment does not have them yet), the
canonical constants under their names, the members under `scratch`. The
rejections. -/
private def checkPlan (scratch : Name) (extra : Array Decl) (cp : _root_.Ix.Compile.Pass.Clique.CliquePlan) :
    MetaM (Array (IxName × String)) := do
  let ren (n : IxName) : Option IxName :=
    if cp.all.contains n then some (ixName (scratch ++ toLeanName n)) else none
  let mut rejected := #[]
  for d in extra do
    unless (← getEnv).contains (toLeanName d.name) do
      if let some why ← kernelAdd (kernelOfDecl d) then rejected := rejected.push (d.name, why)
  for (d, _) in cp.canon do
    if let some why ← kernelAdd (kernelOfDecl d ren) then rejected := rejected.push (d.name, why)
  for m in cp.all do
    if let some d := cp.members.get? m then
      if let some why ← kernelAdd (kernelOfDecl d ren) then rejected := rejected.push (d.name, why)
  return rejected

def adversarialNegatives (env : Environment) : IO Unit := _root_.runMeta (do
  let const? := constOf env
  let adv (s : String) : Name := fx ("Adversarial." ++ s)
  let addr (n : IxName) : Option Address := some (Address.blake3 (toLeanName n).toString.toUTF8)
  let isBaseline : _root_.Ix.Compile.Pass.Clique.CliqueOutcome → Bool
    | .baseline .. => true
    | _ => false
  -- (1) a below matcher is its declaration, not its name
  let helper ← getDecl env (adv "helper.match_1")
  let good ← getDecl env (adv "Shape.good.match_1")
  let bad ← getDecl env (adv "Shape.bad.match_1")
  let shape? (lookup : IxName → Option IxConst) (k : Nat) (d : Decl) :=
    _root_.Ix.Compile.Pass.Clique.matcherShape? lookup (fun _ => false) k d
  for k in [1, 2] do
    if (shape? const? k helper).isSome then
      throwError "a user match_1 with an ordinary body was read as a below matcher ({k})"
    if (shape? const? k bad).isSome then
      throwError "a matcher-shaped match_1 whose body applies a user function was read as a below matcher ({k})"
    if (shape? const? k good).isNone then
      throwError "control: the matcher-shaped match_1 with a casesOn body was not read as a below matcher ({k})"
  unless alphaEqSkipMdata good.type bad.type do throwError "the two matcher-shaped fixtures differ in type"
  -- the accepted matcher's name on the other body (same name, same type)
  let sameName : Decl := { bad with name := good.name }
  let renamedEnv := ixEnvOf env (({} : Std.HashMap IxName IxConst).insert good.name (constOfDecl sameName))
  if (shape? renamedEnv.get? 2 sameName).isSome then
    throwError "an accepted matcher's name on a body that is not an eliminator was read as a below matcher"
  say "ADVERSARIAL matcher by declaration: a user match_1 (ordinary body) and a matcher-shaped match_1 whose body applies a user function: refused; the same type with a casesOn body: accepted; the accepted name on the other body: refused"
  -- (1b) the same declarations beside Lean's below matchers of an
  -- inductive-predicate clique: Lean's are matchers, the user's are
  -- ordinary constants, left unchanged, and nothing else moves
  let (_, ipMembers) ← cliqueOf env `Tests.Ix.Compile.Twins.Cliques.IP.P0.evM
  let ipMatcherNames := (ipMembers.foldl (init := #[]) fun acc d =>
      acc ++ _root_.Ix.Compile.Pass.Clique.constOccurrences
        _root_.Ix.Compile.Pass.Clique.isMatcherName d.value).foldl (init := #[]) fun acc n =>
    if acc.contains n then acc else acc.push n
  let ipAux ← ipMatcherNames.mapM fun n => getDecl env (toLeanName n)
  let ipFamily ← ofExcept "IP family" (_root_.Ix.Compile.Pass.Clique.authenticatedFamily (ixEnvOf env) ipMembers)
  let ipSigma := (List.range ipMembers.size).toArray.reverse
  let layout ← ofExcept "IP layout"
    (_root_.Ix.Compile.Pass.Clique.structLayout ipMembers ipAux ipSigma const? ipFamily)
  unless !ipAux.isEmpty && ipAux.all (layout.matchers.contains ·.name) do
    throwError "control: Lean's below matchers of IP are not all read as matchers ({ipMatcherNames})"
  let withUser := ipAux ++ #[helper, bad]
  let layout' ← ofExcept "IP layout with user match_1s"
    (_root_.Ix.Compile.Pass.Clique.structLayout ipMembers withUser ipSigma const? ipFamily)
  if layout'.matchers.contains helper.name || layout'.matchers.contains bad.name then
    throwError "a user match_1 beside Lean's below matchers was read as a below matcher"
  let clean ← ofExcept "IP transport" (_root_.Ix.Compile.Pass.Clique.transportStructural
    ipMembers ipAux ipSigma const? ipFamily).run'
  let dirty ← ofExcept "IP transport with user match_1s" (_root_.Ix.Compile.Pass.Clique.transportStructural
    ipMembers withUser ipSigma const? ipFamily).run'
  let find (out : Array Transported) (n : IxName) := out.find? (·.decl.name == n)
  for u in #[helper, bad] do
    let some t := find dirty u.name | throwError "the transport dropped the user declaration {u.name}"
    unless t.decl.type == u.type && t.decl.value == u.value do
      throwError "the transport rewrote the user declaration {u.name}"
  for t in clean do
    let some t' := find dirty t.decl.name | throwError "the user match_1s dropped {t.decl.name}"
    unless t'.decl.type == t.decl.type && t'.decl.value == t.decl.value do
      throwError "the user match_1s changed the transport of {t.decl.name}"
  say s!"ADVERSARIAL IP with user match_1s: Lean's below matchers {ipMatcherNames.map (·.pretty)} read as matchers, the user's as ordinary constants (unchanged); the other {clean.size} constants as without them"
  -- (1c) Lean's own below matcher's name on another body (same name, same
  -- type): the body applies a user copy of the matcher instead of an
  -- eliminator, so it is no below matcher; the transport refuses, or treats
  -- it as an ordinary constant (unchanged) with a kernel-accepted result
  let some m := ipAux[0]? | throwError "IP has no below matcher"
  let (mBinders, mConcl) := _root_.Ix.Compile.Canon.peelForalls
    (_root_.Ix.Compile.Image.forallArity m.type) m.type #[]
  if mConcl matches .letE .. then throwError "IP's below matcher has a let in its type"
  let copyName := _root_.Ix.Name.mkStr m.name "userCopy"
  let copy : Decl := { m with name := copyName }
  let callCopy := _root_.Ix.Compile.Canon.mkAppN
    (_root_.Ix.Expr.mkConst copyName (m.levelParams.map _root_.Ix.Level.mkParam))
    ((List.range mBinders.size).toArray.reverse.map _root_.Ix.Expr.mkBVar)
  let m' : Decl := { m with value := _root_.Ix.Compile.Pass.Clique.mkLams mBinders callCopy }
  let some mInfo := const? m.name | throwError "missing {m.name}"
  let sameEnv := ixEnvOf env ((({} : Std.HashMap IxName IxConst).insert m.name
    (_root_.Ix.Compile.Pass.Clique.withValue mInfo m'.value)).insert copyName (constOfDecl copy))
  if (shape? sameEnv.get? layout.numFunTypes m').isSome then
    throwError "Lean's below matcher name on a body that applies a user copy was read as a below matcher"
  let ipAux' := ipAux.map fun d => if d.name == m.name then m' else d
  if let .ok layoutS := _root_.Ix.Compile.Pass.Clique.structLayout ipMembers ipAux' ipSigma sameEnv.get? ipFamily then
    if layoutS.matchers.contains m.name then
      throwError "the structural layout read the same-name matcher as a below matcher"
  let sameNameNote ← match (_root_.Ix.Compile.Pass.Clique.transportStructural
      ipMembers ipAux' ipSigma sameEnv.get? ipFamily).run' with
    | .error why => pure s!"the transport refused ({why})"
    | .ok out =>
      let some t := find out m.name | throwError "the transport dropped the same-name matcher"
      unless t.decl.type == m'.type && t.decl.value == m'.value do
        throwError "the transport rewrote the same-name matcher"
      kernelAddOrThrow (kernelOfDecl copy)
      let moved := (out.filter (·.decl.name != m.name)).map (·.decl.name)
      let ren (n : IxName) : Option IxName :=
        if moved.contains n then some (ixName (`RecognitionSameNameMatcher ++ toLeanName n)) else none
      for t in out do
        unless t.decl.name == m.name do kernelAddOrThrow (kernelOfDecl t.decl ren)
      pure s!"transport treats it as an ordinary constant (unchanged); the other {moved.size} transported constants kernel accepted"
  say s!"ADVERSARIAL IP with {m.name.pretty} on a body that applies a user copy: not a below matcher; {sameNameNote}"
  -- (2) `below`/`brecOn` outside the authenticated family: a non-recursive
  -- structure's user definitions under those names
  let pair := ixName (adv "Pair")
  let pairBelow := ixName (adv "Pair.below")
  let pairBrecOn := ixName (adv "Pair.brecOn")
  if (_root_.Ix.Compile.Pass.Clique.familyCandidates const? pairBrecOn).isSome then
    throwError "a non-recursive structure's user brecOn has family candidates"
  let kept := _root_.Ix.AuxGen.SourceFamily.filterHeads (ixEnvOf env) #[pair] #[pairBelow, pairBrecOn]
  unless kept.isEmpty do
    throwError "the user below/brecOn of a non-recursive structure were authenticated: {kept.map (·.pretty)}"
  let named : Std.HashSet IxName := ({} : Std.HashSet IxName).insert pairBelow |>.insert pairBrecOn
  match _root_.Ix.Compile.Pass.Clique.blockOf const? named pairBrecOn with
  | .ok _ => throwError "blockOf accepted the user brecOn of a non-recursive structure named into the family"
  | .error why => unless why.contains "not recursive" do throwError "blockOf refused for another reason: {why}"
  say "ADVERSARIAL below/brecOn of a non-recursive structure: no family candidates, not authenticated, and refused by blockOf even when named into the family"
  -- (3) the block's `brecOn` with another body (same name, same type): not
  -- authenticated, so the structural transport and the plan refuse
  let natBrecOn := ixName ``Nat.brecOn
  let some (.defnInfo brecOnVal) := const? natBrecOn | throwError "Nat.brecOn is not a definition"
  let alteredValue := _root_.Ix.Expr.mkApp
    (_root_.Ix.Expr.mkLam (ixName `x) brecOnVal.cnst.type (_root_.Ix.Expr.mkBVar 0) .default) brecOnVal.value
  let alteredBrecOn : IxConst := .defnInfo { brecOnVal with value := alteredValue }
  let alteredEnv := ixEnvOf env (({} : Std.HashMap IxName IxConst).insert natBrecOn alteredBrecOn)
  let mut transportedPlans := 0
  for p in ["P0", "P1"] do
    let (all, members) ← cliqueOf env (`Tests.Ix.Compile.Twins.Cliques.SA ++ p.toName ++ `ev)
    let aux ← members.mapM fun m => getDecl env (toLeanName m.name ++ `_f)
    let family ← ofExcept "SA family" (_root_.Ix.Compile.Pass.Clique.authenticatedFamily (ixEnvOf env) members)
    let alteredFamily ← ofExcept "SA family (altered brecOn)"
      (_root_.Ix.Compile.Pass.Clique.authenticatedFamily alteredEnv members)
    unless family.contains natBrecOn && !alteredFamily.contains natBrecOn do
      throwError "SA {p}: the altered Nat.brecOn was authenticated (or the original was not)"
    let some all0 := all[0]? | throwError "SA {p}: no member"
    let inp : Input := { encoding := .structural, members, aux, sigma := #[1, 0], newEncName := all0,
                         const? := alteredEnv.get?, family := alteredFamily }
    let out := _root_.Ix.Compile.Pass.Clique.transport inp
    unless out.baseline && out.causes.all (fun (_, c, why) => c == .shape && why.contains "authenticated") do
      throwError "SA {p}: the structural transport accepted an altered brecOn: {out.causes.map (·.2.2)}"
    let control := _root_.Ix.Compile.Pass.Clique.transport { inp with const? := const?, family }
    if control.baseline then throwError "control: SA {p} kept Lean's form with the authenticated family"
    let cleanPlan := _root_.Ix.Compile.Pass.Clique.planClique (ixEnvOf env) addr all #[]
    let alteredPlan := _root_.Ix.Compile.Pass.Clique.planClique alteredEnv addr all #[]
    if let .transported _ := cleanPlan then transportedPlans := transportedPlans + 1
    unless isBaseline alteredPlan do
      throwError "SA {p}: the plan over an altered brecOn is not the baseline: {alteredPlan.tag}"
    say s!"ADVERSARIAL SA {p} with an altered Nat.brecOn: transport baseline ({out.causes[0]!.2.2}); plan {alteredPlan.tag}; with Lean's brecOn: plan {cleanPlan.tag}"
  unless transportedPlans ≥ 1 do throwError "control: no SA presentation was transported with Lean's brecOn"
  -- (4) a decoy `f._f` beside the real functional: the members pass Lean's
  -- functionals under other names (`m.realF`), and `m._f` holds a user
  -- declaration of the same type with another body. A decoy that binds a
  -- dictionary of its own is refused by the ownership rules (a `below`
  -- binder that is not the recursion's); a decoy without one is refused by
  -- the recovery's functional check (`L.fNames`).
  let combos := [DecoyKind.body, DecoyKind.ref].flatMap fun kind =>
    [("SA", "P0"), ("SA", "P1"), ("SP", "P0"), ("SP", "P1")].map fun (fam, p) => (kind, fam, p)
  for (kind, fam, p) in combos do
    let label := s!"{kind.tag} {fam} {p}"
    let ns := `Tests.Ix.Compile.Twins.Cliques ++ fam.toName ++ p.toName
    let (all, members) ← cliqueOf env (ns ++ (if fam == "SA" then `ev else `fa))
    let fs ← members.mapM fun m => getDecl env (toLeanName m.name ++ `_f)
    let family ← ofExcept s!"{label} family"
      (_root_.Ix.Compile.Pass.Clique.authenticatedFamily (ixEnvOf env) members)
    let sigma := (List.range members.size).toArray.reverse
    -- control: Lean's functionals are recovered
    discard <| ofExcept s!"control: {label} recovery"
      (_root_.Ix.Compile.Pass.Clique.recoverStructural members fs const? family).run'
    let (overlay, members', decoys, copies, others) := decoyInput const? kind members fs
    let decoyEnv := ixEnvOf env overlay
    -- the decoys are refused by the ownership rule (body) or the recovery's
    -- functional check (ref), or first by the
    -- transport's check that every functional the members pass is one of the
    -- encoding's constants (the decoys are not the members' functionals)
    let expectedRefusals : List String := match kind with
      | .body => ["of a below type that is not the recursion's dictionary",
                  "is not one of the encoding's constants"]
      | .ref => ["is not a functional of the members' brecOn applications",
                 "is not one of the encoding's constants"]
    let recoveryRefusal ← match
        (_root_.Ix.Compile.Pass.Clique.recoverStructural members' decoys decoyEnv.get? family).run' with
      | .ok _ => throwError "{label}: the recovery read a decoy m._f as the member's functional"
      | .error why =>
        unless expectedRefusals.any (why.contains ·) do
          throwError "{label}: the decoy recovery refused for another reason: {why}"
        pure why
    let inp0 : Input := { encoding := .structural, members := members', aux := decoys,
                          sigma := _root_.Ix.Compile.Pass.Clique.idPerm members.size,
                          newEncName := members[0]!.name, const? := decoyEnv.get?, family }
    match _root_.Ix.Compile.Pass.Clique.cliqueOrder addr inp0 with
    | .ok (_, _, .specification) => throwError "{label}: the order was read from a decoy's body"
    | _ => pure ()
    -- the transport with Lean's functionals in the encoding beside the
    -- decoys: refused (a decoy with its own dictionary), or the decoys are
    -- ordinary constants, unchanged, and the transported constants are
    -- kernel-accepted
    let transportNote ← match (_root_.Ix.Compile.Pass.Clique.transportStructural
        members' (decoys ++ copies) sigma decoyEnv.get? family).run' with
      | .error why =>
        unless kind == .body && expectedRefusals.any (why.contains ·) do
          throwError "{label}: the transport with the decoys refused: {why}"
        pure "refused"
      | .ok out =>
        if kind == .body then throwError "{label}: the transport accepted a decoy that binds a dictionary"
        for u in decoys do
          let some t := out.find? (·.decl.name == u.name) | throwError "{label}: the transport dropped a decoy"
          unless t.decl.type == u.type && t.decl.value == u.value do
            throwError "{label}: the transport rewrote the decoy {u.name}"
        let scratch := Name.str `RecognitionDecoy s!"{kind.tag}{fam}{p}"
        let moved := (copies ++ members').map (·.name)
        let scratchName (n : IxName) : Option IxName :=
          if moved.contains n then some (ixName (scratch ++ (toLeanName n).replacePrefix ns .anonymous)) else none
        for c in copies ++ members' do
          let some t := out.find? (·.decl.name == c.name) | throwError "{label}: the transport dropped {c.name}"
          kernelAddOrThrow (kernelOfDecl t.decl scratchName)
        pure s!"decoys unchanged, {copies.size + members'.size} transported constants kernel accepted"
    -- the plan over the decoy input (what the hook computes: its encoding
    -- constants are the `m._f` names): the baseline, or a transport whose
    -- constants the kernel accepts
    let plan := _root_.Ix.Compile.Pass.Clique.planClique decoyEnv addr all #[]
    let recorded := knownDecoyPlanGaps.contains label
    let rejected ← match plan with
      | .transported cp =>
        checkPlan (Name.str `RecognitionDecoyPlan s!"{kind.tag}{fam}{p}") (copies ++ others) cp
      | _ => pure #[]
    if rejected.isEmpty then
      if recorded then
        throwError "{label}: the recorded library gap no longer occurs ({plan.tag}): remove it from knownDecoyPlanGaps"
    else
      for (n, why) in rejected do
        say s!"ADVERSARIAL decoy plan {label}: KERNEL-REJECT {n.pretty}: {(why.take 300).toString}"
      unless recorded do
        throwError "{label}: the plan over the decoy input transported constants the kernel rejects ({plan.tag})"
      say s!"ADVERSARIAL decoy plan {label}: KNOWN LIBRARY GAP (recorded in knownDecoyPlanGaps, reported): the plan transports the members over functionals outside its encoding constants"
    say s!"ADVERSARIAL decoy _f ({label}): recovery refused ({recoveryRefusal}); order not read from the decoys; transport with Lean's functionals: {transportNote}; plan {plan.tag}"
  ) env

/-! ## The suite -/

/-- The repeated-parameter and permutation controls, on the environment's
fixtures. -/
def repeatedControls (env : Environment) : IO Unit := do
  let declOf' (name : Name) : IO Decl := do
    let some declaration := declOf env name
      | throw (IO.userError s!"missing repeated-parameter control {name}")
    pure declaration
  let pfPacked ← declOf' (fx "repeatedPFPacked")
  let wfPacked ← declOf' (fx "repeatedWFPacked")
  let pfMembers ← #[fx "repeatedPFFirst", fx "repeatedPFSecond"].mapM declOf'
  -- The elaborator's generated members use primitive projections, whereas
  -- these ordinary source definitions elaborate through PProd.fst/snd.
  let pfMembers := pfMembers.mapIdx fun index declaration =>
    { declaration with value := toIxExpr (mkLambda `a .default (mkConst ``Nat)
      (mkProj ``PProd index (mkApp2 (mkConst (fx "repeatedPFPacked")) (mkBVar 0) (mkBVar 0)))) }
  let wfMembers ← #[fx "repeatedWFFirst", fx "repeatedWFSecond"].mapM declOf'
  for invalid in #[#[], #[0], #[0, 0], #[0, 2]] do
    let input : Input := {
      encoding := .wellFounded, members := wfMembers, aux := #[wfPacked],
      sigma := invalid, newEncName := wfPacked.name }
    let rejected := _root_.Ix.Compile.Pass.Clique.transport input
    let originals := input.aux ++ input.members
    unless rejected.baseline && rejected.decls.size == originals.size &&
        rejected.causes.size == originals.size &&
        rejected.causes.all (fun (_, cause, reason) => cause == .shape && reason.contains "bad permutation") &&
        (rejected.decls.zip originals).all (fun (actual, expected) =>
          actual.name == expected.name && alphaEqSkipMdata actual.type expected.type &&
          alphaEqSkipMdata actual.value expected.value) do
      throw (IO.userError s!"public transport accepted or lost source input for invalid permutation {invalid}")
  say "Public transport rejects empty/truncated/duplicate/out-of-range permutations before identity shortcut"
  match _root_.Ix.Compile.Pass.Clique.pfLayout pfMembers pfPacked #[1, 0] pfPacked.name with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throw (IO.userError s!"PF repeated-parameter control failed for another reason: {reason}")
  | .ok _ => throw (IO.userError "PF layout accepted two fixed slots sharing one source binder")
  match _root_.Ix.Compile.Pass.Clique.wfLayout wfMembers wfPacked #[1, 0] wfPacked.name with
  | .error reason => unless reason.contains "distinct fixed parameters alias" do
      throw (IO.userError s!"WF repeated-parameter control failed for another reason: {reason}")
  | .ok _ => throw (IO.userError "WF layout accepted two fixed slots sharing one source binder")
  say "Repeated same-typed fixed arguments: PF and WF both rejected"

def run : IO UInt32 := do
  let env ← fixturesEnv
  let parts : List (String × (Environment → IO Unit)) := [
    ("repeated-parameter controls", repeatedControls),
    ("partial_fixpoint actual probe", actualProbe),
    ("partial_fixpoint positive probes", positiveProbes),
    ("WF matcher controls", wfMatcherControls),
    ("structural identity control", structuralIdentityControl),
    ("WF actual probe", actualWFProbe),
    ("WF positive probes", wfPositiveProbes),
    ("adversarial negatives", adversarialNegatives)]
  let mut failures : Array String := #[]
  for (label, part) in parts do
    try part env
    catch e =>
      say s!"FAIL {label}: {e}"
      failures := failures.push label
  say s!"{failures.size} failures"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Clique.Recognition
