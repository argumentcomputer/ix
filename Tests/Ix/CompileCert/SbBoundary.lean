import Ix.CompileCert.TypeRows
import Ix.CompileCert.StrongCertifier
import Tests.Ix.CompileCert.Changed
import Tests.Ix.CompileCert.Strong

/-! Diagnostic only: complete installed-row observations after actual cone-local
W+ admission and source installation. No S verdict is produced or modified.
The Mathlib mode is one explicitly named cone, not the global S pass. -/

namespace Tests.Ix.CompileCert.SbBoundary

open _root_.Ix _root_.Ix.CompileCert _root_.Ix.CompileCert.Certifier
open _root_.Ix.CompileCert.Strong
open Benchmarks.Kernel.CheckIxeStep

def j (s : String) : Lean.Json := .str s
def n (v : Nat) : Lean.Json := Lean.toJson v
def b (v : Bool) : Lean.Json := Lean.toJson v
def obj (xs : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj xs

structure Output where
  handle : IO.FS.Handle

def Output.row (o : Output) (kind : String) (xs : List (String × Lean.Json)) : IO Unit := do
  o.handle.putStrLn (obj (("kind", j kind) :: xs)).compress
  o.handle.flush

def kind : Kernel.ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo .. => "definition"
  | .thmInfo .. => "theorem" | .recInfo .. => "recursor"
  | .indInfo .. => "inductive" | .ctorInfo .. => "constructor" | .projInfo _ => "projection"

/-- Non-recursive node description; comparison below retains binder annotations.
No expression is printed by expanding its entire shared tree. -/
def node : Kernel.Expr → String
  | .bvar i => s!"bvar {i}" | .fvar i _ => s!"fvar {i}"
  | .sort u => s!"sort {reprStr u}" | .const c us => s!"const {c} {reprStr us}"
  | .app .. => "app" | .lam _ _ m => s!"lam {reprStr m}"
  | .forallE _ _ m => s!"forallE {reprStr m}" | .letE .. => "letE"
  | .lit l => s!"lit {reprStr l}" | .proj c i _ => s!"proj {c} {i}"

/-- Exact first differing node in a fixed preorder, including annotations.
The full equality is decided before reporting; no expression-size sampling. -/
def difference (path : String) (a c : Kernel.Expr) : Lean.Json :=
  if decide (a = c) then .null else
  let leaf := obj [("path", j path), ("left", j (node a)), ("right", j (node c))]
  match a, c with
  | .app f x, .app g y =>
    if decide (f = g) then difference (path ++ ".arg") x y else difference (path ++ ".fn") f g
  | .lam d x m, .lam e y q | .forallE d x m, .forallE e y q =>
    if decide (m ≠ q) then leaf else
    if decide (d = e) then difference (path ++ ".body") x y else difference (path ++ ".domain") d e
  | .letE t v x, .letE u w y =>
    if decide (t ≠ u) then difference (path ++ ".type") t u else
    if decide (v ≠ w) then difference (path ++ ".value") v w else difference (path ++ ".body") x y
  | .fvar i t, .fvar k u => if i == k then difference (path ++ ".type") t u else leaf
  | .proj s i x, .proj t k y =>
    if decide (s = t ∧ i = k) then difference (path ++ ".subject") x y else leaf
  | _, _ => leaf
termination_by sizeOf a

def comparison (a c : Kernel.Expr) : Lean.Json :=
  obj [("literalEqual", b (decide (a = c))), ("firstDifference", difference "$" a c)]

def capsJson (c : Kernel.IndCaps) : Lean.Json :=
  obj [("eta", b c.eta), ("etaCtor", j (toString c.etaCtor)), ("etaParams", n c.etaParams),
    ("etaFields", n c.etaFields), ("unitlike", b c.unitlike), ("unitParams", n c.unitParams),
    ("ruleK", b c.ruleK), ("sortZ", j (reprStr c.sortZ))]

def ruleJson (r : Kernel.RecRule) : Lean.Json :=
  obj [("ctor", j (toString r.ctor)), ("nfields", n r.nfields), ("ctorParams", n r.ctorParams),
    ("fire", j (match r.fire with | .inert => "inert" | .plain => "plain" | .nested .. => "nested")),
    ("k", b r.k), ("eta", b r.eta), ("paramsBlind", b r.paramsBlind)]

def resultSort : Kernel.Expr → Option Kernel.Level
  | .forallE _ body _ => resultSort body
  | .sort u => some u
  | _ => none

/-- An independent symbolic equation assembled from the actual installed frame.
`motivePosition` is printed source metadata, not an assumed theorem. All needed
syntactic arities and installed constructor counts are checked here. The output
does not assert typedness or the semantic rule law. -/
def frameStatement {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (f : InstalledRuleFrame env name index) (motivePosition : Nat) : Except String Kernel.Expr := do
  unless f.rulePrefix ≤ f.major do throw "major before rule prefix"
  unless f.rule.nfields == f.constructorFields && f.rule.ctorParams == f.constructorParams do
    throw "installed constructor/rule arities disagree"
  let p := f.rulePrefix
  let ni := f.major - p
  let nf := f.constructorFields
  let some (pre, rest) := f.header.type.stripPis p | throw "installed recursor prefix"
  let some (motive, _) := pre[motivePosition]? | throw "installed motive position"
  let some level := resultSort motive | throw "installed motive result sort"
  let preVars := (List.range p).map fun i => Kernel.Expr.bvar (p - 1 - i)
  let (us, parameters) := Kernel.recFireComparands f.rule f.header.levelParams
    (f.header.levelParams.map .param) f.constructor.levelParams preVars p
  unless us.length == f.constructor.levelParams.length && parameters.length == f.constructorParams do
    throw "installed firing recipe arity"
  let ctorType := f.constructor.type.instantiateLevelParams f.constructor.levelParams us
  let some fieldsType := ctorType.instPis parameters | throw "installed constructor parameter telescope"
  let some (fields, result) := fieldsType.stripPis nf | throw "installed constructor field telescope"
  let indices := result.getAppArgs.drop f.constructorParams
  unless indices.length == ni do throw "installed constructor result index count"
  let fieldVars := (List.range nf).map fun i => Kernel.Expr.bvar (nf - 1 - i)
  let leading := preVars.map (Kernel.Expr.liftLooseBVars nf 0)
  let major := Kernel.Expr.mkAppN (.const f.constructor.name us)
    (parameters.map (Kernel.Expr.liftLooseBVars nf 0) ++ fieldVars)
  let lhs := Kernel.Expr.mkAppN (.const name (f.header.levelParams.map .param)) (leading ++ indices ++ [major])
  let rhs := Kernel.Expr.mkAppN f.rule.rhs (leading ++ fieldVars)
  let some carrier := (Kernel.Expr.liftLooseBVars nf 0 rest).instPis (indices ++ [major])
    | throw "installed result carrier"
  let body := kernelEq level carrier lhs rhs
  return (pre ++ fields).foldr (fun (ty, binderData) body => .forallE ty body binderData) body

def fourChecks (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : List Bool :=
  [checkInstalledTypesF source fS fT names, checkInstalledCapabilitiesF source fS fT names,
   checkInstalledRecursorsF source fS fT names, checkInstalledConstructorsF source fS fT names]

def checkNames : List String := ["types", "capabilities", "recursors", "constructors"]

def installedRows (o : Output) (label : String) (source target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) (rows : Array Kernel.Declaration)
    (owners : Array Lean.Name) : IO Unit := do
  let fS := envFind source
  let fT := envFind target
  let mut conjunction := [true, true, true, true]
  for (entry, ordinal) in source.consts.zipIdx do
    let targetEntry := fT (names entry.name)
    let one : Kernel.Env := ⟨[entry]⟩
    let checks := fourChecks one fS fT names
    conjunction := (conjunction.zip checks).map fun (a, c) => a && c
    let typeCheck := targetEntry.bind fun t =>
      checkInstalledMemberExprF fS fT names entry.name entry.toConstantVal.type t.toConstantVal.type
    let typeDiff := targetEntry.map fun t => comparison entry.toConstantVal.type t.toConstantVal.type
    o.row "installed" [("cone", j label), ("ordinal", n ordinal), ("source", j (toString entry.name)),
      ("target", j (toString (names entry.name))), ("sourceKind", j (kind entry)),
      ("targetKind", j ((targetEntry.map kind).getD "missing")),
      ("sourceOwnsLookup", b (decide (fS entry.name = some entry))),
      ("sourceLevels", j (reprStr entry.toConstantVal.levelParams)),
      ("targetLevels", j (reprStr (targetEntry.map (·.toConstantVal.levelParams)))),
      ("telescope", b (checkTelescopesF one fT names)), ("typeComparison", j (reprStr typeCheck)),
      ("typeLiteralDifferenceDifferentNamespaces", typeDiff.getD .null),
      ("checks", obj ((checkNames.zip checks).map fun (s, c) => (s, b c))),
      ("etaAssociations", j (reprStr (checkInstalledEtaAssociationsF one fS fT names))),
      ("ruleLevelLinks", j (reprStr (checkInstalledRuleLevelLinksF one fS fT names)))]
    match entry with
    | .indInfo header caps =>
      o.row "capabilities" [("cone", j label), ("source", j (toString header.name)),
        ("sourceCaps", capsJson caps), ("targetCaps", match targetEntry with
          | some (.indInfo _ c) => capsJson c | _ => .null),
        ("mappedEtaCtor", j (toString (names caps.etaCtor))),
        ("headerComparison", b (match targetEntry with
          | some (.indInfo _ c) => decide (InstalledCapsHeader names header.name caps c) | _ => false)),
        ("sortDatumComparison", j (reprStr (match targetEntry with
          | some (.indInfo _ c) => checkInstalledMemberExprF fS fT names header.name
            (capabilityDatumExpr caps) (capabilityDatumExpr c) | _ => none)))]
    | .ctorInfo header params fields =>
      o.row "constructor" [("cone", j label), ("source", j (toString header.name)),
        ("params", n params), ("fields", n fields), ("targetArity", match targetEntry with
          | some (.ctorInfo _ p q) => obj [("params", n p), ("fields", n q)] | _ => .null)]
    | .recInfo header major rp rules =>
      o.row "recursor" [("cone", j label), ("source", j (toString header.name)),
        ("major", n major), ("rulePrefix", n rp), ("rules", n rules.length),
        ("targetHeader", match targetEntry with
          | some (.recInfo _ m p rs) => obj [("major", n m), ("rulePrefix", n p), ("rules", n rs.length)]
          | _ => .null)]
      for (rule, i) in rules.zipIdx do
        let tr := match targetEntry with | some (.recInfo _ _ _ rs) => rs[i]? | _ => none
        o.row "installed-rule" [("cone", j label), ("source", j (toString header.name)),
          ("ordinal", n i), ("sourceRule", ruleJson rule), ("targetRule", (tr.map ruleJson).getD .null),
          ("headerComparison", b ((tr.map fun r => decide (InstalledRuleHeader names rule r)).getD false)),
          ("fireComparison", j (reprStr (tr.bind fun r => checkInstalledFireF fS fT names header.name rule.fire r.fire))),
          ("rhsComparison", j (reprStr (tr.bind fun r => checkInstalledMemberExprF fS fT names header.name rule.rhs r.rhs))),
          ("rhsLiteralDifferenceDifferentNamespaces", (tr.map fun r => comparison rule.rhs r.rhs).getD .null)]
    | _ => pure ()
    -- All owner rows are tried. No alias fiber is collapsed and no guessed row
    -- position is used as evidence that a type certificate exists.
    for i in [0:rows.size] do
      if (owners[i]?).map sourceName != some entry.name then continue
      let row := rows[i]!
      for rowName in row.names do
        let rowsFn : Kernel.Name → Kernel.Name := fun _ => rowName
        let via := installedTypeRowF fS fT names rowsFn entry.name entry.toConstantVal.type
        let parts := (fT rowName).bind fun row => eqParts row.toConstantVal.type
        o.row "type-row-candidate" [("cone", j label), ("source", j (toString entry.name)),
          ("supportOrdinal", n i), ("row", j (toString rowName)), ("accepted", b via),
          ("installedKind", j (((fT rowName).map kind).getD "missing")),
          ("rowLevels", j (reprStr ((fT rowName).map (·.toConstantVal.levelParams)))),
          ("equation", match parts, targetEntry with
            | some (level, carrier, left, right), some t => obj [
                ("level", j (reprStr level)), ("carrier", j (node carrier)),
                ("leftVsActualTargetType", comparison left t.toConstantVal.type),
                ("rightImageComparison", j (reprStr (checkInstalledMemberExprF fS fT names entry.name
                  entry.toConstantVal.type right)))]
            | _, _ => .null)]
  let whole := fourChecks source fS fT names
  let original := [checkInstalledTypes source target names, checkInstalledCapabilities source target names,
    checkInstalledRecursors source target names, checkInstalledConstructors source target names]
  o.row "installed-summary" [("cone", j label), ("rows", n source.consts.length),
    ("whole", obj ((checkNames.zip whole).map fun (s, c) => (s, b c))),
    ("rowConjunction", obj ((checkNames.zip conjunction).map fun (s, c) => (s, b c))),
    ("originalChecks", obj ((checkNames.zip original).map fun (s, c) => (s, b c))),
    ("same", b (whole == conjunction && whole == original)), ("certification", j "none: diagnostic only")]
  unless whole == conjunction && whole == original do throw (IO.userError "row observer disagrees with whole installed checks")

def ruleRows (o : Output) (label : String) (cx : ExportContext) (source target : Kernel.Env)
    (rows : Array Kernel.Declaration) (rowsOf : Std.HashMap Lean.Name (Array Nat)) : IO Unit := do
  let mut count := 0
  for ci in cx.source.declarations do
    let .recInfo r := ci | continue
    let targetStatements := ruleStatements cx r
    for (rule, ordinal) in r.rules.zipIdx do
      count := count + 1
      let rawSource := do
        let some (.ctorInfo c) := cx.source.find rule.ctor | throw "source constructor missing"
        exportSourceExpr r.levelParams (← leanRuleStatement r c rule)
      let frame := readInstalledRuleFrame source (sourceName r.name) ordinal
      let actualStatement := match frame with
        | some f => frameStatement f r.numParams
        | none => .error "no firing installed source frame (inert/missing/kind/constructor)"
      let frameDifference := match rawSource, actualStatement with
        | .ok a, .ok c => comparison a c | _, _ => .null
      let rawRule := exportSourceRule r.levelParams rule
      let rawRhsDifference := match rawRule, frame with
        | .ok rr, some f => comparison rr.rhs f.rule.rhs | _, _ => .null
      o.row "source-rule-frame" [("cone", j label), ("source", j (toString r.name)),
        ("ordinal", n ordinal), ("constructor", j (toString rule.ctor)),
        ("numParams", n r.numParams), ("numMotives", n r.numMotives),
        ("numMinors", n r.numMinors), ("numIndices", n r.numIndices), ("fields", n rule.nfields),
        ("sourceExportError", j (match rawSource with | .ok _ => "" | .error e => e)),
        ("frameRecipeError", j (match actualStatement with | .ok _ => "" | .error e => e)),
        ("rawVsInstalledEquation", frameDifference), ("rawVsInstalledRhs", rawRhsDifference),
        ("installedRule", (frame.map fun f => ruleJson f.rule).getD .null),
        ("installedLevels", j (reprStr (frame.map (·.universeComparands))))]
      let expected := do
        let statements ← targetStatements
        match statements[ordinal]? with
        | some statement => pure statement | none => throw "target rule ordinal missing"
      o.row "target-rule-export" [("cone", j label), ("source", j (toString r.name)),
        ("ordinal", n ordinal), ("error", j (match expected with | .ok _ => "" | .error e => e)),
        ("ownerSupportRows", n (rowsOf.getD r.name #[]).size)]
      for pos in rowsOf.getD r.name #[] do
        let some row := rows[pos]? | throw (IO.userError "owner row index out of range")
        let .thmDecl header _ := row | throw (IO.userError "owner support row is not a theorem")
        let installed := target.find? header.name
        o.row "target-rule-row" [("cone", j label), ("source", j (toString r.name)),
          ("ruleOrdinal", n ordinal), ("supportOrdinal", n pos), ("row", j (toString header.name)),
          ("levels", j (reprStr header.levelParams)),
          ("exportVsProposed", match expected with | .ok e => comparison e header.type | .error _ => .null),
          ("proposedVsInstalled", (installed.map fun v => comparison header.type v.toConstantVal.type).getD .null),
          ("installedKind", j ((installed.map kind).getD "missing"))]
      -- Sensitivity control: changing the applied installed RHS changes the
      -- literal equation. This is not a semantic counterexample or W+ verdict.
      if let .ok statement := actualStatement then
        let forged := Kernel.Expr.app statement (.sort .zero)
        o.row "rule-difference-control" [("cone", j label), ("source", j (toString r.name)),
          ("ordinal", n ordinal), ("validNeighbour", comparison statement statement),
          ("malformedNeighbour", comparison statement forged)]
  o.row "rule-summary" [("cone", j label), ("originalRules", n count)]

def witnesses (env : Lean.Environment) (source : Source) : IO LoweringWitnesses := do
  let functions := LoweringLean.projectionFunctionsIn env source.declarations
  let mut out := []
  for name in functions do
    let witness ← IO.ofExcept (← LoweringLean.runMeta env (LoweringLean.buildLoweringWitness name .none))
    match ← LoweringLean.admitLoweringWitness env witness with
    | .ok _ => out := out ++ [witness]
    | .error why => throw (IO.userError s!"lowering witness refused: {name}: {why}")
  return out

/-- Returns false on an operationally incomplete cone. Installed-check failures
are complete diagnostic results, not a short circuit or an S refusal verdict. -/
def inspectCone (o : Output) (w : WState) (root : Lean.Name) (limit : Nat)
    (familyRoots : Array Lean.Name := #[]) : IO Bool := do
  let label := toString root
  try
    let pins ← IO.ofExcept Kernel.Reader.defaultPins
    let known : Lean.Name → Bool := w.namedAddr.contains
    let pinGround := natOpPinGround w.env w.store w.namedAddr pins w.names known
    let requested := (#[root] ++ familyRoots).toList.eraseDups.toArray
    let mut seeds := requested
    o.row "cone-request" [("cone", j label), ("roots", Lean.toJson (requested.toList.map toString))]
    -- Bounded closure, with a final fixed-point requirement. Exceeding it is
    -- reported incomplete, never silently discarded support or certification.
    for round in [0:8] do
      let (members, missing) := coneMembersOf w.refs known pinGround seeds
      o.row "cone-round" [("cone", j label), ("round", n round), ("members", n members.size),
        ("missing", Lean.toJson (missing.toList.map toString))]
      unless missing.isEmpty do throw (IO.userError "source closure has missing names")
      unless members.size ≤ limit do throw (IO.userError s!"cone over {limit} limit; not executed")
      let input ← IO.ofExcept (coneInput w.env w.produced w.store w.namedAddr requested.toList members)
      let ⟨artifact, staged⟩ ← match prepareArtifactStaged input.toArtifactInput with
        | .ok a => pure a | .error _ => throw (IO.userError "target artifact admission refused")
      let images := imageClaims w.env w.store members w.namedAddr
      let imagesFn : Lean.Name → Bool := images.contains
      let entries := input.map.foldl (fun m e => m.insert e.source e) ({} : Std.HashMap Lean.Name MapEntry)
      let pre ← wPrePass w.env entries input images artifact (queriesFor w.env w.refs) 4
        (fun s => o.row "prepass-log" [("cone", j label), ("text", j s)])
        (fun s => o.row "prepass-row" [("cone", j label), ("text", j s)])
        (rowBudget := fun _ _ => defaultRowBudget) (produced? := some w.produced)
      for ci in input.source.declarations do
        o.row "route" [("cone", j label), ("round", n round), ("source", j (toString ci.name)),
          ("route", j (pre.routes.getD ci.name "missing")),
          ("failure", j (match pre.failed[ci.name]? with | none => "" | some v => v.word ++ ": " ++ v.cause))]
      let (rows, owners, rowsOf) := finalSupport input.source.names.toArray pre
      let localW := { w with support := rows, rowsOf }
      let ground := rowGround localW pins known
      let present : Std.HashSet Lean.Name := members.foldl (·.insert ·) {}
      let extra := (members.flatMap fun m => ground.getD m #[]).filter (!present.contains ·)
      if !extra.isEmpty then
        seeds := seeds ++ extra
        continue
      let association (support : Array Kernel.Declaration) :=
        let sh := SharedW.ofArtifact input imagesFn artifact support
        let pos := entryPositions sh.entries
        let hints := buildHintsW input sh pos (queriesFor w.env w.refs) 4
          (rowsAtWith entries pos sh.reader rowsOf sh.entries.size)
        checkIndexed' input imagesFn artifact support hints (some staged)
      let accepted ← match association rows with
        | .ok a => pure a | .error e => throw (IO.userError s!"W+ association: {Changed.declineLabel e}")
      let ws ← witnesses w.env input.source
      let installed ← match installSourceNormalizedComplete accepted.domain.1 (sourcePins input accepted.pins) ws with
        | .ok a => pure a | .error e => throw (IO.userError s!"source installation: {(sourceErrorLabel e).1}")
      let proposal ← IO.ofExcept (proposeWith accepted.pins imagesFn accepted.env installed)
      let inspect (target : Kernel.Env) : IO Unit := do
        o.row "installation" [("cone", j label), ("members", n members.size), ("records", n input.records.length),
          ("sourceRows", n installed.env.consts.length), ("targetRows", n target.consts.length),
          ("wRows", n rows.size), ("sourceSupport", n proposal.support.size), ("witnesses", n ws.length),
          ("originalRules", n (input.source.declarations.foldl (fun total ci => match ci with
            | .recInfo r => total + r.rules.length | _ => total) 0)),
          ("sourceOriginals", Lean.toJson (input.source.names.map toString))]
        installedRows o label installed.env target proposal.names rows owners
        ruleRows o label ⟨input.source, input.map, accepted.pins, imagesFn⟩ installed.env target rows rowsOf
      if proposal.support.isEmpty then inspect accepted.folded.env else
        match association (rows ++ proposal.support) with
        | .ok final => inspect final.folded.env
        | .error e => throw (IO.userError s!"W+ with source-owned support: {Changed.declineLabel e}")
      o.row "cone-complete" [("cone", j label), ("installed", b true), ("certification", j "none")]
      return true
    throw (IO.userError "support closure did not stabilize within eight rounds; incomplete")
  catch e =>
    o.row "cone-incomplete" [("cone", j label), ("reason", j e.toString), ("certification", j "none")]
    return false

def fixture (o : Output) : IO Bool := do
  let (env, source, compiled) ← Changed.compile
  let built ← Changed.build env source compiled.env
  let w : WState := { env, produced := compiled.env, store := built.store,
    namedAddr := built.namedAddr, refs := built.refs, names := source.names.toArray,
    verdicts := {}, wRun := false }
  let roots := [(`Reord, `Reord.viaRec_zero), (`ReordProp, `ReordProp.even_true),
    (`Split, `Split.viaRec_nil), (`Collapse, `Collapse.f_ab), (`Evap, `Evap.useRec_ex)]
  let mut complete := 0
  for (family, root) in roots do
    let familyName := Changed.prefixName ++ family
    -- Every declaration of this family in the original complete fixture cone,
    -- including every captured rec_N. Do not keep only the representative root.
    let familyRoots := source.declarations.toArray.filterMap fun ci =>
      if familyName.isPrefixOf ci.name then some ci.name else none
    o.row "fixture-family" [("family", j (toString familyName)),
      ("roots", Lean.toJson (familyRoots.toList.map toString))]
    if ← inspectCone o w (Changed.prefixName ++ root) 50000 familyRoots then complete := complete + 1
  o.row "fixture-summary" [("requestedFamilies", n 5), ("completedFamilies", n complete),
    ("scope", j "all source rows of each complete cone; unchanged dependencies included")]
  return complete == 5

/-- Controls use real folded fixture declarations. Mutation changes only the
target definition's type to a convertible beta-redex; no arbitrary axiom. -/
def controls (o : Output) : IO Bool := do
  let fx ← Strong.fixture
  let first := Tests.Ix.CompileCert.Compiled.prefixName ++ `first
  let p ← fx.pieces first []
  let source := p.installed.env
  let names := p.proposal.names
  let targetName := names (sourceName first)
  let base := Kernel.Frontend.preparePrelude p.accepted.prelude.ix p.accepted.declarations
  let pins ← IO.ofExcept Kernel.Reader.builtinNatOpPins
  let fold (ds : Array Kernel.Declaration) := Kernel.Cached.checkDecls .verified pins ds
  let some (header, value, hint) := base.findSome? fun d => match d with
    | .defnDecl h v k => if h.name == targetName then some (h, v, k) else none | _ => none
    | throw (IO.userError "TypeRows control target definition missing")
  let sortLevel ← IO.ofExcept (checkerSortLevel (Kernel.mkFEnv p.accepted.env) header.type)
  let changed := Kernel.Expr.app (.lam (.sort sortLevel) (.bvar 0) default) header.type
  let ds := base.map fun d => if d.names.contains targetName then
      Kernel.Declaration.defnDecl { header with type := changed } value hint else d
  let target0 ← match fold ds with
    | .ok a => pure a | .error (e, i) => throw (IO.userError s!"convertible type control refused at {i}: {(checkOutcome e).2}")
  let some actual := target0.find? targetName | throw (IO.userError "mutated target missing")
  let never : Kernel.Name → Kernel.Name := fun name => name.str "_sb_missing_type_row"
  let mut results : List Bool := []
  let record (label : String) (actual expected : Bool) : IO Bool := do
    o.row "control" [("name", j label), ("actual", b actual), ("expected", b expected), ("pass", b (actual == expected))]
    return actual == expected
  results := (← record "direct-valid-neighbour" (checkInstalledTypesRows source p.accepted.env names never) true) :: results
  results := (← record "convertible-type-without-row" (checkInstalledTypesRows source target0 names never) false) :: results
  let makeRow (tag : String) (left right : Kernel.Expr) :=
    supportRow (targetName.str tag) header.levelParams (kernelEq (.succ sortLevel) (.sort sortLevel) left right)
  for (tag, left, right, expected) in
      [("honest", actual.toConstantVal.type, header.type, true),
       ("wrong-left", header.type, header.type, false),
       ("wrong-right", actual.toConstantVal.type, actual.toConstantVal.type, false)] do
    let some row := makeRow tag left right | throw (IO.userError "type row shape")
    let folded ← match fold (ds.push row) with
      | .ok a => pure a | .error (e, i) => throw (IO.userError s!"true row {tag} refused at {i}: {(checkOutcome e).2}")
    let rowName := targetName.str tag
    let rows : Kernel.Name → Kernel.Name := fun name => if name == sourceName first then rowName else never name
    results := (← record tag (checkInstalledTypesRows source folded names rows) expected) :: results
    if tag == "honest" then
      let some original := source.find? (sourceName first) | throw (IO.userError "source first missing")
      let shadow := Kernel.ConstantInfo.axiomInfo { original.toConstantVal with type := .sort .zero }
      let shadowed : Kernel.Env := ⟨shadow :: source.consts⟩
      results := (← record "shadowed-source-owner" (checkInstalledTypesRows shadowed folded names rows) false) :: results
      let some extra := supportRow (targetName.str "extra") header.levelParams
        (kernelEq (.succ sortLevel) (.sort sortLevel) header.type header.type)
        | throw (IO.userError "extra support shape")
      let withExtra ← match fold ((ds.push row).push extra) with
        | .ok a => pure a | .error _ => throw (IO.userError "extra true support refused")
      results := (← record "extra-support-valid-neighbour" (checkInstalledTypesRows source withExtra names rows) true) :: results
  let some falseRow := makeRow "false-row" (.sort .zero) (.sort (.succ .zero))
    | throw (IO.userError "false row shape")
  results := (← record "false-row-fold-refusal" (match fold (ds.push falseRow) with | .ok _ => false | .error _ => true) true) :: results
  o.row "controls-summary" [("count", n results.length), ("allPassed", b (results.all id))]
  return results.all id

def mathlib (o : Output) (ixe benchmark : String) : IO Bool := do
  let (rc, state) ← runW { lean := .file benchmark, ixe, out := "unused-sb-loader",
    strongOnly := true, workers := 4 }
  unless rc == 0 do throw (IO.userError s!"artifact loader returned {rc}")
  let some w := state | throw (IO.userError "artifact loader returned no state")
  unless !w.wRun do throw (IO.userError "unexpected global W pass")
  o.row "mathlib-loader" [("namedDeclarations", n w.names.size), ("globalWRun", b w.wRun)]
  unless w.names.size == 783115 do throw (IO.userError "pinned Mathlib named universe changed")
  inspectCone o w `Lean.Meta.Grind.Arith.Linear.DiseqCnstr.h 50000

def main (args : List String) : IO UInt32 := do
  let (mode, output, artifact, benchmark) ← match args with
    | [mode, output] => pure (mode, output, "", "")
    | [mode, output, artifact, benchmark] => pure (mode, output, artifact, benchmark)
    | _ => throw (IO.userError "usage: sb-boundary-diag controls|fixture OUT.jsonl; mathlib OUT.jsonl MATHLIB.ixe CompileMathlib.lean")
  unless mode == "controls" || mode == "fixture" || (mode == "mathlib" && artifact != "" && benchmark != "") do
    throw (IO.userError "invalid mode/arguments")
  unless !(← (System.FilePath.mk output).pathExists) do throw (IO.userError "output already exists")
  let handle ← IO.FS.Handle.mk output .write
  let o : Output := ⟨handle⟩
  try
    o.row "start" [("mode", j mode), ("residualUnsupported", n 205), ("residualBlocked", n 2234),
      ("claim", j "diagnostic only; no S+b acceptance, no global rerun")]
    let ok ← match mode with
      | "controls" => controls o | "fixture" => fixture o | _ => mathlib o artifact benchmark
    o.row "terminal" [("mode", j mode), ("complete", b ok), ("certification", j "none")]
    handle.flush
    (← IO.getStdout).flush
    -- The row pre-screen can own tasks after it reports a timeout. As with
    -- compile-certify, exit only after the complete diagnostic is flushed.
    IO.Process.exit (if ok then 0 else 1)
  catch e =>
    o.row "terminal" [("mode", j mode), ("complete", b false), ("error", j e.toString)]
    handle.flush
    IO.Process.exit 1

end Tests.Ix.CompileCert.SbBoundary

def main (args : List String) : IO UInt32 := Tests.Ix.CompileCert.SbBoundary.main args
