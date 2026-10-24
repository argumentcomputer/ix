/- A checked answer capability for generation from a safe Source-unaccepted
family. The logical Source snapshot is immutable. Checked tier/sigma updates
are private, every resulting oracle stays failClosed and every generated
row retains the original non-acceptance reason. The production retry provider
requests this factory lazily. Actual supplied safe dependencies may be checked privately; absent or
unsupported records refuse. Supplied safe opaques are checked with their
actual logical bodies and stay opaque in both private views. No logical group is discovered/folded and no
missing recursor is synthesized. Char alone has a guarded full-check route. -/
module
public import Ix.AuxGen.IxcScope

namespace Ix.AuxGen.GenerationOnly

open Source (Service SourceEnv TierEntry)

private structure Context where
  baseline : Service
  tier : Array TierEntry
  sigma : Flat.ClassMap
  reason : String

private def Context.env (g : Context) : SourceEnv :=
  { g.baseline.env with tier := g.tier, sigma := g.sigma }

private theorem logical_frame (g : Context) : g.env.fold = g.baseline.env.fold := rfl
private theorem evidence_frame (g : Context) : g.env.ev = g.baseline.env.ev := rfl

private def Context.update (g : Context) (env : SourceEnv) : Context :=
  { g with tier := env.tier, sigma := env.sigma }

private theorem update_frame (g : Context) (env : SourceEnv) :
    (g.update env).baseline = g.baseline ∧ (g.update env).reason = g.reason := ⟨rfl, rfl⟩

/-- Input shadowing is deliberate: an unaccepted input name cannot fall
through to a prelude copy. The checker validates any absent-input reference. -/
private def Context.ready (g : Context) (refs : Std.HashSet Name)
    (owned : Array Name := #[]) : Except String Unit := do
  for name in refs.toArray do
    if owned.any (Ix.Compile.ExactKey.nameEq · name) then continue
    if g.tier.any (fun t => t.check.any (·.name == g.env.key name)) then continue
    match g.baseline.statusOf? name with
    | some s => unless s.isAccepted || s.isTier do throw s!"generation: unaccepted dependency {name.pretty}"
    | none => if (g.baseline.input.get? name).isSome then throw s!"generation: dependency not folded {name.pretty}"

private def blockRefs (types : Array InductiveVal) (ctors : Array (Array ConstructorVal))
    (recs : Array RecursorVal) : Std.HashSet Name := Id.run do
  let mut refs := {}
  for t in types do refs := collectLeanConstRefs t.cnst.type refs
  for cs in ctors do for c in cs do refs := collectLeanConstRefs c.cnst.type refs
  for r in recs do
    refs := collectLeanConstRefs r.cnst.type refs
    for rule in r.rules do refs := collectLeanConstRefs rule.rhs refs
  return refs

private def suppliedInductive (input : Source.Input) (firstName : Name) : Except String Ix.LeanIngress.Group := do
  let some (.inductInfo first) := input.get? firstName | throw s!"generation: missing former {firstName.pretty}"
  unless Ix.Compile.ExactKey.nameEq first.cnst.name firstName &&
      (first.all[0]?).any (Ix.Compile.ExactKey.nameEq · firstName) do throw "generation: original family head differs"
  let types ← first.all.mapM fun n => do
    let some (.inductInfo v) := input.get? n | throw s!"generation: missing former {n.pretty}"
    unless Ix.Compile.ExactKey.nameEq v.cnst.name n && v.all.isEqv first.all Name.beqRaw do
      throw s!"generation: former family differs at {n.pretty}"
    if v.isUnsafe then throw s!"generation: unsafe supplied former {n.pretty}"
    return v
  let ctors ← types.mapM fun v => v.ctors.zipIdx.mapM fun (n, i) => do
    let some (.ctorInfo c) := input.get? n | throw s!"generation: missing constructor {n.pretty}"
    unless Ix.Compile.ExactKey.nameEq c.cnst.name n && Ix.Compile.ExactKey.nameEq c.induct v.cnst.name && c.cidx == i do
      throw s!"generation: constructor family/index differs at {n.pretty}"
    if c.isUnsafe then throw s!"generation: unsafe supplied constructor {n.pretty}"
    return c
  let slots := first.all.map (·.mkStr "rec") ++ (Array.range first.numNested).map (fun i => firstName.mkStr s!"rec_{i + 1}")
  let mut recs := #[]
  for n in slots do
    match input.get? n with
    | none => pure ()
    | some (.recInfo r) =>
      unless Ix.Compile.ExactKey.nameEq r.cnst.name n && r.all.isEqv first.all Name.beqRaw do
        throw s!"generation: supplied recursor family/name differs at {n.pretty}"
      if r.isUnsafe then throw s!"generation: unsafe supplied recursor {n.pretty}"
      recs := recs.push r
    | some _ => throw s!"generation: supplied recursor slot has another kind at {n.pretty}"
  return .inductive types ctors recs

private def actualGroup (input : Source.Input) (name : Name) : Except String Ix.LeanIngress.Group := do
  let some ci := input.get? name | throw s!"generation: missing input record {name.pretty}"
  unless Ix.Compile.ExactKey.nameEq ci.getCnst.name name do throw s!"generation: input name differs at {name.pretty}"
  let first? := match ci with
    | .inductInfo v => v.all[0]?
    | .ctorInfo c => match input.get? c.induct with | some (.inductInfo v) => v.all[0]? | _ => none
    | .recInfo r => r.all[0]?
    | _ => none
  if let some first := first? then
    let group ← suppliedInductive input first
    unless group.names.any (Ix.Compile.ExactKey.nameEq · name) do throw s!"generation: family does not claim {name.pretty}"
    return group
  if let .opaqueInfo v := ci then
    if v.isUnsafe then throw s!"generation: unsafe supplied opaque {name.pretty}"
    let some lo := input.blocks.lowLinks.get? name | throw s!"generation: opaque is unplaced {name.pretty}"
    let some members := input.blocks.blocks.get? lo | throw s!"generation: opaque unit is absent {name.pretty}"
    let #[member] := members.toArray | throw s!"generation: opaque unit is not singleton {name.pretty}"
    unless Ix.Compile.ExactKey.nameEq member name do
      throw s!"generation: opaque unit member differs at {name.pretty}"
    return .definitions #[ci]
  let .defnInfo _ := ci | throw s!"generation: unsupported supplied dependency {name.pretty}"
  let some lo := input.blocks.lowLinks.get? name | throw s!"generation: definition is unplaced {name.pretty}"
  let some members := input.blocks.blocks.get? lo | throw s!"generation: definition unit is absent {name.pretty}"
  unless members.contains name do throw s!"generation: definition unit does not claim {name.pretty}"
  let names := members.toArray.qsort (fun a b => Ix.LeanIngress.nameCmp a b == .lt)
  let defs ← names.mapM fun n => do
    let some (.defnInfo v) := input.get? n | throw s!"generation: missing or non-definition unit member {n.pretty}"
    unless Ix.Compile.ExactKey.nameEq v.cnst.name n do throw s!"generation: definition name differs at {n.pretty}"
    unless v.safety == .safe do throw s!"generation: non-safe definition unit member {n.pretty}"
    return ConstantInfo.defnInfo v
  return .definitions defs

private def refsOf : Ix.LeanIngress.Group → Std.HashSet Name
  | .inductive ts cs rs => blockRefs ts cs rs
  | .definitions ms => ms.foldl (init := {}) fun refs ci => match ci with
      | .defnInfo v => collectLeanConstRefs v.value (collectLeanConstRefs v.cnst.type refs)
      | .opaqueInfo v => collectLeanConstRefs v.value (collectLeanConstRefs v.cnst.type refs)
      | _ => refs
  | _ => {}

private def charInputKeys : List (Ix.Kernel.Key .source) :=
  [.role .char, Ix.LeanIngress.ingressKey (Name.fromLeanName `Char.mk), Ix.LeanIngress.ingressKey (Name.fromLeanName `Char.rec)]
private def charDeltaKeys : List (Ix.Kernel.Key .source) := charInputKeys ++ [.aux (.role .char) .projTable]

private def checkOnly (ci : Ix.Kernel.ConstantInfo .source) : Ix.Kernel.ConstantInfo .source :=
  match ci with
  | .indInfo cv _ => .indInfo cv {}
  | .recInfo cv major rulePrefix _ => .recInfo cv major rulePrefix []
  | _ => ci

private def sealCharDelta (old new : Ix.Kernel.FEnv .source) : Except String Source.TierEntry := do
  unless charDeltaKeys.all (fun k => (old.find? k).isNone) do throw "Char adapter: role/key collision"
  let delta := new.env.consts.take 4
  unless delta.length == 4 && decide (new.env.consts.drop 4 = old.env.consts) do
    throw "Char adapter: extra/overwritten entry or nonexact old suffix"
  unless old.env.consts.all (fun ci => decide (new.find? ci.name = some ci)) do
    throw "Char adapter: old lookup changed"
  let keys := delta.map (·.name)
  unless decide keys.Nodup && keys.all charDeltaKeys.contains && charDeltaKeys.all keys.contains do
    throw "Char adapter: duplicate/unexpected/missing delta key"
  unless delta.all (fun ci => decide (new.find? ci.name = some ci)) do
    throw "Char adapter: delta index disagrees"
  for ci in delta do
    let proper : Bool := match ci with
      | .indInfo cv _ => cv.name == .role .char
      | .ctorInfo cv _ _ => cv.name == charInputKeys[1]!
      | .recInfo cv _ _ _ => cv.name == charInputKeys[2]!
      | .projInfo t => t.structName == .role .char && ci.name == .aux (.role .char) .projTable
      | _ => false
    unless proper do throw "Char adapter: wrong delta record kind"
  let pushOrder := delta.reverse
  return ⟨2, pushOrder.map checkOnly, .infos pushOrder⟩

private def checkedCharUnit (g : Context) : Except String (Ix.Kernel.FEnv .source × Ix.Kernel.FEnv .source) := do
  let char := Name.fromLeanName `Char
  let group ← actualGroup g.baseline.input char
  unless group.names.toList.map Ix.LeanIngress.ingressKey == charInputKeys do
    throw "Char adapter: original key layout differs"
  unless g.env.key char == .role .char && (g.sigma.misfit Source.roleBound).isNone do
    throw "Char adapter: role binding moved"
  g.ready (refsOf group) group.names
  let c ← (Ix.LeanIngress.convert group).mapError (fun e => s!"Char adapter: conversion: {Source.renderRead e}")
  let .inductive rb := c | throw "Char adapter: not an inductive unit"
  let some (cv, _, _) := rb.types[0]? | throw "Char adapter: former missing"
  let pin : Ix.Kernel.ConstantVal .source := { name := .role .char, levelParams := [], type := .sort (.succ .zero) }
  unless cv.matchesPin pin do throw "Char adapter: anchor header mismatch"
  let r : Ix.Kernel.Reader.Read .source ← (Ix.LeanIngress.lower g.baseline.reader c).mapError (fun e => s!"Char adapter: lowering: {Source.renderRead e}")
  unless r.generated == 0 && r.decls.size == 1 do throw "Char adapter: extra/generated-prefix declaration"
  let some (Ix.Kernel.Declaration.indDecl infos _) := r.decls[0]? | throw "Char adapter: no original inductive declaration"
  unless infos.map (·.name) == charInputKeys do throw "Char adapter: lowered key layout differs"
  let work : Source.Fold := { fe := g.env.checkView 2 }
  unless charDeltaKeys.all (fun k => (work.fe.find? k).isNone) do throw "Char adapter: role/key collision"
  let result ← (work.steps g.baseline.env.ev r.decls).mapError (fun e => s!"Char adapter: complete check: {Source.renderCheck e}")
  return (work.fe, result.fe)

private def installCheckedChar (g : Context) : Except String Source.SourceEnv := do
  let (old, checked) ← checkedCharUnit g
  let entry ← sealCharDelta old checked
  return { g.env with tier := g.tier.push entry }

/-- Dependency preparation has its own bound; the public fuel still counts
oracle install successors. The original Source snapshot is never folded. -/
private def dependencyDepth : Nat := 256

/-- A supplied opaque is checked before its key is visible. Its header has
the normal opaque declaration guards and sort check; its actual logical
body is annotated and typed using only prior checked answers. Neither this
key nor any current body is pushed while these checks run. -/
private def checkedOpaqueHeader (s : SourceEnv)
    (cv : Ix.Kernel.ConstantVal .source) (body : Ix.Kernel.Expr .source) :
    Except (Ix.Kernel.CheckError .source) (Ix.Kernel.ConstantVal .source) := do
  let view := s.checkView 2
  let (header, _) ← Ix.Kernel.Tier.runC
    (Ix.Kernel.Cached.checkConstantValC .verified view cv)
  let knot := (s.answers 2).knot
  unless Ix.Kernel.Expr.looseBVarsBounded 0 body do
    throw (.invalid msg!"loose bound variable in value of {header.name}")
  if body.hasFvar then
    throw (.invalid msg!"unexpected free variable in value of {header.name}")
  let annotated ← Ix.Kernel.Tier.runC (knot.annotate 0 body)
  unless Ix.Kernel.Expr.allLevelParamsDefinedC header.levelParams annotated do
    throw (.invalid msg!"undeclared universe parameter in value of {header.name}")
  unless Ix.Kernel.Cached.constsResolveFC view annotated do
    throw (Ix.Kernel.unresolvedConstsError msg!"value of {header.name}" annotated)
  let inferred ← Ix.Kernel.Tier.runC (knot.infer 0 annotated)
  unless ← Ix.Kernel.Tier.runC (knot.defeq 0 inferred header.type) do
    throw (.invalid (Ix.Kernel.Msg.withTerms
      msg!"type mismatch in generation opaque {header.name}"
      [("has type", inferred), ("but is expected to have type", header.type)]))
  return header

/-- Only the actual supplied safe opaque body is checked. On success its
header is opaque in BOTH private views; no runtime companion is looked up
and no transparent definition or logical acceptance is produced. -/
private def installPreparedOpaque (s : SourceEnv) (v : OpaqueVal) : Except String SourceEnv := do
  if v.isUnsafe then throw s!"generation: unsafe supplied opaque {v.cnst.name.pretty}"
  let key := Ix.LeanIngress.ingressKey v.cnst.name
  let .id _ := key | throw "generation: opaque must have an input key"
  s.tierFresh [key]
  let numbering := Ix.LeanIngress.Numbering.mk v.cnst.levelParams false
  let terms ← (Ix.LeanIngress.ingressExprs numbering.pos [v.cnst.type, v.value]).mapError
    (fun error => s!"generation: opaque ingress: {error}")
  let [type, body] := terms | throw "generation: opaque ingress arity"
  let header ← (checkedOpaqueHeader s ⟨key, numbering.params, type⟩ body).mapError Source.renderCheck
  let info := Ix.Kernel.ConstantInfo.axiomInfo header
  return { s with tier := s.tier.push ⟨2, [info], .infos [info]⟩ }

/-- A supplied definition's annotation may need a previously checked alias
to unfold (for example a monad abbreviation in an instance argument).
Headers retain the opaque check view. Current bodies are never installed
while any member is being checked; only prior answers and opaque current
headers are available to the verified knot. -/
private def checkedDefinitionAnswers (s : SourceEnv)
    (members : List (Ix.Kernel.ConstantVal .source × Ix.Kernel.Expr .source))
    (hints : List Ix.Kernel.ReducibilityHint) :
    Except (Ix.Kernel.CheckError .source) (List (Ix.Kernel.ConstantInfo .source)) := do
  let view := s.checkView 2
  Ix.Kernel.Tier.blockShape members
  let headers ← Ix.Kernel.Tier.headersC view members
  for header in headers do Ix.Kernel.Tier.sortC view header
  let opaqueHeaders := headers.map Ix.Kernel.ConstantInfo.axiomInfo
  let knot := ((s.answers 2).pushInfos opaqueHeaders).knot
  let present := Ix.Kernel.Tier.pushHeaders view headers
  (headers.zip members).zipIdx.mapM fun ((header, (_, value)), i) => do
    unless Ix.Kernel.Expr.looseBVarsBounded 0 value do
      throw (.invalid msg!"loose bound variable in value of {header.name}")
    if value.hasFvar then
      throw (.invalid msg!"unexpected free variable in value of {header.name}")
    let annotated ← Ix.Kernel.Tier.runC (knot.annotate 0 value)
    unless Ix.Kernel.Expr.allLevelParamsDefinedC header.levelParams annotated do
      throw (.invalid msg!"undeclared universe parameter in value of {header.name}")
    unless Ix.Kernel.Cached.constsResolveFC present annotated do
      throw (Ix.Kernel.unresolvedConstsError msg!"value of {header.name}" annotated)
    let inferred ← Ix.Kernel.Tier.runC (knot.infer 0 annotated)
    unless ← Ix.Kernel.Tier.runC (knot.defeq 0 inferred header.type) do
      throw (.invalid (Ix.Kernel.Msg.withTerms
        msg!"type mismatch in generation dependency {header.name}"
        [("has type", inferred), ("but is expected to have type", header.type)]))
    pure (.defnInfo header annotated (hints.getD i (.regular 0)))

/-- Preserve the ordinary install, then retry only supplied safe definition
dependencies over prior checked answers. Freshness and the complete block
are checked before appending an opaque check entry and its answer records.
A failed retry preserves the original refusal. No logical field changes. -/
private def installPreparedDefinitions (s : SourceEnv)
    (members : List (Ix.Kernel.ConstantVal .source × Ix.Kernel.Expr .source))
    (hints : List Ix.Kernel.ReducibilityHint) : Except String SourceEnv :=
  match s.installTierDecl (.defs .unsaf members) hints with
  | .ok installed => .ok installed
  | .error original =>
    let retry : Except String SourceEnv := do
      s.tierFresh (members.map (·.1.name))
      let infos ← (checkedDefinitionAnswers s members hints).mapError Source.renderCheck
      let headers := infos.map fun info => Ix.Kernel.ConstantInfo.axiomInfo info.toConstantVal
      return { s with tier := s.tier.push ⟨2, headers, .infos infos⟩ }
    retry.mapError fun _ => original

private def prepare : Nat → Context → Array Name → Name → Except String Context
  | 0, g, _, name =>
    if (g.ready (({} : Std.HashSet Name).insert name)).isOk then .ok g
    else .error s!"generation: dependency depth exhausted at {name.pretty}"
  | fuel + 1, g, active, name => do
    if (g.ready (({} : Std.HashSet Name).insert name)).isOk then return g
    if active.any (Ix.Compile.ExactKey.nameEq · name) then throw s!"generation: dependency cycle at {name.pretty}"
    let group ← actualGroup g.baseline.input name
    let names := group.names
    let refs := refsOf group
    let deps := (refs.toArray.filter fun n => !names.any (Ix.Compile.ExactKey.nameEq · n)).qsort
      (fun a b => Ix.LeanIngress.nameCmp a b == .lt)
    let mut next := g
    for dep in deps do next ← prepare fuel next (active ++ names) dep
    next.ready refs names
    let env ← match group with
      | .inductive ts cs rs =>
        if ts.any (fun t => Ix.LeanIngress.ingressKey t.cnst.name == .role .char) then installCheckedChar next
        else do
          let b ← (Ix.LeanIngress.convertTierInductive ts cs rs).mapError Source.renderRead
          next.env.installTierInd b
      | .definitions #[.opaqueInfo v] => installPreparedOpaque next.env v
      | .definitions ms => do
        let staged ← ms.mapM fun ci => do
          let .defnInfo v := ci | throw "generation: non-definition escaped extraction"
          unless v.safety == .safe do throw "generation: non-safe definition escaped extraction"
          return ConstantInfo.defnInfo { v with safety := .unsafe }
        let d ← (Ix.LeanIngress.convertTier (.definitions staged)).mapError Source.renderRead
        let hints := ms.toList.map fun ci => ((Ix.LeanIngress.definitionShape ci).map (·.2.2)).getD (.regular 0)
        let .defs .unsaf members := d | throw "generation: supplied definition staging differs"
        installPreparedDefinitions next.env members hints
      | _ => throw "generation: unsupported group escaped extraction"
    return next.update env

private def start (svc : Service) (owner : Name) : Except String Context := do
  let some why := Ixc.blockStatus? svc #[owner] | throw "generation: Source-accepted block is ineligible"
  let some (.inductInfo _) := svc.input.get? owner | throw "generation: incomplete original group"
  let _ ← actualGroup svc.input owner
  prepare dependencyDepth ⟨svc, svc.env.tier, svc.env.sigma, why⟩ #[] owner

private def Context.definition (g : Context) (name : Name) (lps : Array Name)
    (ty value : Expr) (thm : Bool) : Except String Context := do
  g.ready (collectLeanConstRefs value (collectLeanConstRefs ty {}))
  return g.update (← g.env.admitTierDefinition name lps ty value thm)

private def Context.flat (g : Context) (b : Flat.FlatBlock) : Except String Context := do
  g.ready (blockRefs b.types b.ctors b.recs) (b.consts.map (·.1))
  let converted ← (Ix.LeanIngress.convertTierInductive b.types b.ctors b.recs).mapError Source.renderRead
  return g.update (← g.env.installTierInd converted b.sigma)

private def Context.family (g : Context) (types : Array (InductiveVal × Array ConstructorVal))
    (recs : Array (Name × RecursorVal)) : Except String Context := do
  let own (n : Name) : Option ConstantInfo :=
    match types.find? (fun (v, _) => Ix.Compile.ExactKey.nameEq v.cnst.name n) with
    | some (v, _) => some (.inductInfo v)
    | none => (types.findSome? fun (_, cs) => cs.find? fun c => Ix.Compile.ExactKey.nameEq c.cnst.name n).map .ctorInfo
  let lookup n := (own n).orElse fun _ => g.baseline.input.get? n
  let fb ← (Flat.build lookup (types.map fun (v, _) => #[v.cnst.name]) recs g.sigma).mapError (·.render)
  g.flat fb

private def Context.bare (g : Context) (types : Array (InductiveVal × Array ConstructorVal)) : Except String Context := do
  let mut own : Flat.ClassMap := {}
  for (v, cs) in types do
    own ← (own.insert v.cnst.name (Flat.fresh v.cnst.name)).mapError (·.render)
    for c in cs do own ← (own.insert c.cnst.name (Flat.fresh c.cnst.name)).mapError (·.render)
  g.ready (blockRefs (types.map (·.1)) (types.map (·.2)) #[])
    ((types.map (·.1.cnst.name)) ++ types.flatMap (fun (_, cs) => cs.map (·.cnst.name)))
  let sigma ← (g.sigma.union own).mapError (·.render)
  let rename e := Flat.renameExpr sigma e
  let names := types.map fun (v, _) => Flat.fresh v.cnst.name
  let converted : StateM Flat.RenameCache (Array (InductiveVal × Array ConstructorVal)) := types.mapM fun (v, cs) => do
    let ty ← rename v.cnst.type
    let cs' ← cs.mapM fun c => do
      pure { c with cnst := { c.cnst with name := Flat.fresh c.cnst.name, type := ← rename c.cnst.type }, induct := Flat.fresh v.cnst.name }
    let v' : InductiveVal := { v with cnst := { v.cnst with name := Flat.fresh v.cnst.name, type := ty }, all := names, ctors := v.ctors.map Flat.fresh }
    pure (v', cs')
  let entries := converted.run' {}
  let b ← (Ix.LeanIngress.convertTierInductive (entries.map (·.1)) (entries.map (·.2)) #[]).mapError Source.renderRead
  return g.update (← g.env.installTierInd b own)

private def oracle (trace : Bool) (g : Context) : Nat → AuxOracle
  | 0 =>
    let bad {α} : Except String α := .error "generation oracle fuel exhausted"
    .mk .failClosed trace (fun _ _ => bad) (fun _ _ _ => bad) (fun _ => bad) true true
      (fun overlay _ locals => Ixc.ofLazy (Ixc.overlaid overlay g.baseline.input.get?) Ixc.scopeFuel locals (Thunk.pure bad))
      (fun _ => bad) (fun _ => some g.reason) none (fun _ => bad)
  | fuel + 1 =>
    let scope lps locals := do
      let s ← Ixc.Scope.new g.env lps (some g.env.answers)
      s.push locals
    .mk .failClosed trace
      (fun lps locals => do pure (Ixc.ofScope g.baseline.input.get? Ixc.scopeFuel (← scope lps locals)))
      (fun classes originals recs => do
        let aux := (recs.extract classes.size recs.size).map (·.1)
        let nested := match originals[0]?.bind g.baseline.input.get? with | some (.inductInfo v) => v.numNested | _ => 0
        unless Flat.needed classes originals aux nested do return none
        let fb ← (Flat.build g.baseline.input.get? classes recs g.sigma).mapError (·.render)
        return some (oracle trace (← g.flat fb) fuel))
      (fun defs => do
        let next ← defs.foldlM (fun s d => s.definition d.name d.levelParams d.typ d.value false) g
        return (oracle trace next fuel, defs.size, 0))
      true true
      (fun overlay lps locals => Ixc.ofLazy (Ixc.overlaid overlay g.baseline.input.get?) Ixc.scopeFuel locals
        (Thunk.mk fun _ => scope lps locals))
      (fun decls => do
        let mut next := g
        let mut rows := #[]
        for decl in decls do
          match decl with
          | .defn n lps ty value thm =>
            next ← next.definition n lps ty value thm
            rows := rows.push (n, some g.reason)
          | .family types recs =>
            next ← next.family types recs
            rows := rows ++ types.map fun (v, _) => (v.cnst.name, some g.reason)
        return (oracle trace next fuel, rows))
      (fun _ => some g.reason) none
      (fun types => return oracle trace (← g.bare types) fuel)

/-- Check and expose a private generation view of a safe Source-unaccepted
original family. The original owner must already have an unaccepted reason.
Safe supplied definition, opaque and inductive dependency groups may be
checked in a private overlay; opaque bodies remain unavailable after checking. Their
logical statuses are never changed. Only supplied recursors are used.
The result and every install successor are failClosed, have no fallback,
retain the original refusal and never report logical acceptance. -/
public def ofService (svc : Service) (owner : Name) (fuel : Nat := Ixc.oracleFuel)
    (trace : Bool := false) : Except String AuxOracle := do
  return oracle trace (← start svc owner) fuel

end Ix.AuxGen.GenerationOnly
