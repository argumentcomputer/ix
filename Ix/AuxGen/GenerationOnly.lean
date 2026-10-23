/- A checked answer capability for generation from a safe Source-unaccepted
family. The logical Source snapshot is immutable. Checked tier/sigma updates
are private, every resulting oracle stays failClosed and every generated
row retains the original non-acceptance reason. This factory is not wired
into the production retry provider. Missing external dependencies refuse;
it neither discovers new logical groups nor synthesizes missing recursors. -/
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

private def start (svc : Service) (owner : Name) : Except String Context := do
  let some why := Ixc.blockStatus? svc #[owner] | throw "generation: Source-accepted block is ineligible"
  let some (.inductive ts cs rs) := svc.input.blockGroupOf? owner | throw "generation: incomplete original group"
  if ts.any (·.isUnsafe) then throw "generation: safe original block required"
  let g : Context := ⟨svc, svc.env.tier, svc.env.sigma, why⟩
  g.ready (blockRefs ts cs rs) (ts.map (·.cnst.name) ++ cs.flatten.map (·.cnst.name) ++ rs.map (·.cnst.name))
  let b ← (Ix.LeanIngress.convertTierInductive ts cs rs).mapError Source.renderRead
  return g.update (← g.env.installTierInd b)

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
original family. `svc` must already contain its logical dependency statuses;
this function does not fold/discover them. Only supplied recursors are used.
The result and every install successor are failClosed, have no fallback,
retain the original refusal and never report logical acceptance. -/
public def ofService (svc : Service) (owner : Name) (fuel : Nat := Ixc.oracleFuel)
    (trace : Bool := false) : Except String AuxOracle := do
  return oracle trace (← start svc owner) fuel

end Ix.AuxGen.GenerationOnly
