import Tests.Ix.AuxGen.TierService
import Tests.Ix.Compile.AuxCert.NestedSortUK

/-! Isolated M7 spike. Nothing calls this from production. A generation
context stores only checked tier/sigma extensions of an immutable Source
snapshot; its logical fold, reader and statuses cannot be replaced. -/

namespace Tests.Ix.AuxGen.GenerationOnlySpike

open _root_.Ix _root_.Ix.AuxGen
open _root_.Ix.AuxGen.Source (Service SourceEnv TierEntry)

structure Generation where
  baseline : Service
  tier : Array TierEntry
  sigma : Flat.ClassMap
  reason : String

def Generation.env (g : Generation) : SourceEnv :=
  { g.baseline.env with tier := g.tier, sigma := g.sigma }

theorem Generation.logical_frame (g : Generation) : g.env.fold = g.baseline.env.fold := rfl
theorem Generation.evidence_frame (g : Generation) : g.env.ev = g.baseline.env.ev := rfl

def Generation.update (g : Generation) (env : SourceEnv) : Generation :=
  { g with tier := env.tier, sigma := env.sigma }

/-- Never discover/fold a new dependency here. Explicit checked tier entries
may be used despite their original logical refusal; other input refusals may not. -/
def Generation.ready (g : Generation) (refs : Std.HashSet Name) (owned : Array Name := #[]) : Except String Unit := do
  for name in refs.toArray do
    if owned.any (Ix.Compile.ExactKey.nameEq · name) then continue
    if g.tier.any (fun t => t.check.any (·.name == g.env.key name)) then continue
    match g.baseline.statusOf? name with
    | some s => unless s.isAccepted || s.isTier do throw s!"generation: unaccepted dependency {name.pretty}"
    | none => if (g.baseline.input.get? name).isSome then throw s!"generation: dependency not folded {name.pretty}"

def blockRefs (types : Array InductiveVal) (ctors : Array (Array ConstructorVal)) (recs : Array RecursorVal) : Std.HashSet Name := Id.run do
  let mut refs := {}
  for t in types do refs := collectLeanConstRefs t.cnst.type refs
  for cs in ctors do for c in cs do refs := collectLeanConstRefs c.cnst.type refs
  for r in recs do
    refs := collectLeanConstRefs r.cnst.type refs
    for rule in r.rules do refs := collectLeanConstRefs rule.rhs refs
  return refs

def start (svc : Service) (owner : Name) : Except String Generation := do
  let some why := Ixc.blockStatus? svc #[owner] | throw "generation: Source-accepted block is ineligible"
  let some (.inductive ts cs rs) := svc.input.blockGroupOf? owner | throw "generation: incomplete original group"
  if ts.any (·.isUnsafe) then throw "generation spike: safe original block required"
  let g : Generation := ⟨svc, svc.env.tier, svc.env.sigma, why⟩
  g.ready (blockRefs ts cs rs) (ts.map (·.cnst.name) ++ cs.flatten.map (·.cnst.name) ++ rs.map (·.cnst.name))
  let b ← (Ix.LeanIngress.convertTierInductive ts cs rs).mapError Source.renderRead
  return g.update (← g.env.installTierInd b)

def Generation.definition (g : Generation) (name : Name) (lps : Array Name) (ty value : Expr) (thm : Bool) : Except String Generation := do
  g.ready (collectLeanConstRefs value (collectLeanConstRefs ty {}))
  return g.update (← g.env.admitTierDefinition name lps ty value thm)

def Generation.flat (g : Generation) (b : Flat.FlatBlock) : Except String Generation := do
  g.ready (blockRefs b.types b.ctors b.recs) (b.consts.map (·.1))
  let converted ← (Ix.LeanIngress.convertTierInductive b.types b.ctors b.recs).mapError Source.renderRead
  return g.update (← g.env.installTierInd converted b.sigma)

def Generation.family (g : Generation) (types : Array (InductiveVal × Array ConstructorVal))
    (recs : Array (Name × RecursorVal)) : Except String Generation := do
  let own (n : Name) : Option ConstantInfo :=
    match types.find? (fun (v, _) => Ix.Compile.ExactKey.nameEq v.cnst.name n) with
    | some (v, _) => some (.inductInfo v)
    | none => (types.findSome? fun (_, cs) => cs.find? fun c => Ix.Compile.ExactKey.nameEq c.cnst.name n).map .ctorInfo
  let lookup n := (own n).orElse fun _ => g.baseline.input.get? n
  let fb ← (Flat.build lookup (types.map fun (v, _) => #[v.cnst.name]) recs g.sigma).mapError (·.render)
  g.flat fb

def Generation.bare (g : Generation) (types : Array (InductiveVal × Array ConstructorVal)) : Except String Generation := do
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

/-- Every callback remains generation-only, including callbacks returned by
an install. Successful typing is reported as non-acceptance, never `none`. -/
def oracle (mode : IxcMode) (g : Generation) : Nat → AuxOracle
  | 0 =>
    let bad {α} : Except String α := .error "generation oracle fuel exhausted"
    .mk mode false (fun _ _ => bad) (fun _ _ _ => bad) (fun _ => bad) true true
      (fun overlay _ locals => Ixc.ofLazy (Ixc.overlaid overlay g.baseline.input.get?) Ixc.scopeFuel locals (Thunk.pure bad))
      (fun _ => bad) (fun _ => some g.reason) none (fun _ => bad)
  | fuel + 1 =>
    let scope lps locals := do
      let s ← Ixc.Scope.new g.env lps (some g.env.answers)
      s.push locals
    .mk mode false
      (fun lps locals => Ixc.ofScope g.baseline.input.get? Ixc.scopeFuel <$> scope lps locals)
      (fun classes originals recs => do
        let aux := (recs.extract classes.size recs.size).map (·.1)
        let nested := match originals[0]?.bind g.baseline.input.get? with | some (.inductInfo v) => v.numNested | _ => 0
        unless Flat.needed classes originals aux nested do return none
        let fb ← (Flat.build g.baseline.input.get? classes recs g.sigma).mapError (·.render)
        return some (oracle mode (← g.flat fb) fuel))
      (fun defs => do
        let next ← defs.foldlM (fun s d => s.definition d.name d.levelParams d.typ d.value false) g
        return (oracle mode next fuel, defs.size, 0))
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
        return (oracle mode next fuel, rows))
      (fun _ => some g.reason) none
      (fun types => return oracle mode (← g.bare types) fuel)

end Tests.Ix.AuxGen.GenerationOnlySpike
