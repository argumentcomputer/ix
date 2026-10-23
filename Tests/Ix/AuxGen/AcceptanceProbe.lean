import LSpec
import Ix.Meta
import Ix.CompileDriver
import Tests.Ix.AuxGen.BelowIxc
import Tests.Ix.AuxGen.CheckedKernel

/-! # Generated auxiliaries accepted by Source mode (`lake exe IxTests --ignored auxgen-acceptance-probe`)

AuxGen M5a's library check, before its wiring (`auxgen-m5.md` §2). For every
block that holds an inductive, on the fixtures and on Init+Std: the aux
tail's patches (`generateAuxPatches` on the checked IxC capability), then, over the block's
oracle (a run-ahead with production's asks, the block folded):
- a block whose layout is Lean's (no flat block) is left to the identity
  verdict (the input's own acceptance); its patches are counted against
  Lean's by term, for information;
- a flat or nested block: its canonical flat block installed (the generated
  recursors checked, `AuxOracle.withFlat`), then every other patch admitted
  in generation order (`AuxOracle.admit`): `casesOn`, `recOn`, the `.below`
  definitions, a Prop-level `.below` family as a block with its generated
  recursors, the `.brecOn` family (`go`, `brecOn`, `eq`); theorems as
  theorems;
- an unsafe block is exempt.
Printed: verdicts by route and kind, and the refusals. Asserts nothing (the
stop rule is M5a's gate). -/

namespace Tests.Ix.AuxGen.AcceptanceProbe

open Tests.Ix.AuxGen.FlatBlockSource (inductiveBlocks)

def kindOf : Ix.AuxGen.PatchedConstant → String
  | .recr _ => "rec"
  | .recOnDef _ => "recOn"
  | .casesOnDef _ => "casesOn"
  | .belowDef _ => "below (def)"
  | .belowIndc _ => "below (Prop family)"
  | .brecOnDef d => if d.isProp then "brecOn (Prop)" else "brecOn/go/eq"

/-- A block's route: unsafe, nested, a flat block (its layout not Lean's), or
Lean's layout. -/
def routeOf (get? : Ix.Name → Option Ix.ConstantInfo) (classes : Array (Array Ix.Name))
    (originalAll : Array Ix.Name) : String :=
  let inds := originalAll.filterMap fun n => match get? n with
    | some (.inductInfo v) => some v
    | _ => none
  if inds.any (·.isUnsafe) then "unsafe"
  else if inds.any (·.numNested > 0) then "nested"
  else if Ix.AuxGen.Flat.needed classes originalAll #[] 0 then "flat"
  else "lean"

/-- The generation order of a block's non-recursor patches: `casesOn`,
`recOn`, the `.below` definitions, the Prop family, then the `.brecOn`
family (`go`, `brecOn`, `eq`). -/
def order : Ix.AuxGen.PatchedConstant → Nat
  | .casesOnDef _ => 0
  | .recOnDef _ => 1
  | .belowDef _ => 2
  | .belowIndc _ => 3
  | .brecOnDef d => match d.name with
    | .str _ "go" _ => 4
    | .str _ "eq" _ => 6
    | _ => 5
  | .recr _ => 7

/-- One block's checked IxC generation: its classes, Lean's `all`, the
patches, and the Prop family's generated recursors (as CompileAux generates
them, over an overlay). -/
structure Gen where
  classes : Array (Array Ix.Name)
  originalAll : Array Ix.Name
  out : Ix.AuxGen.AuxPatchesOutput
  family : Array (Ix.InductiveVal × Array Ix.ConstructorVal)
  familyRecs : Array (Ix.Name × Ix.RecursorVal)

def generate (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (all : Array Ix.Name) :
    Except String (Option Gen) :=
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let act : Ix.CompileM.CompileM (Option Gen) := do
    let mut cs : Array Ix.MutConst := #[]
    for n in all do
      match (← Ix.AuxGen.lookupConst? n) with
      | some (.inductInfo val) => cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
      | some (.defnInfo val) => cs := cs.push (Ix.MutConst.fromDefinitionVal val)
      | some (.opaqueInfo val) => cs := cs.push (Ix.MutConst.fromOpaqueVal val)
      | some (.thmInfo val) => cs := cs.push (Ix.MutConst.fromTheoremVal val)
      | some (.recInfo val) => cs := cs.push (.recr val)
      | _ => pure ()
    let sorted ← Ix.CompileM.sortConsts cs.toList
    let classNames : Array (Array Ix.Name) := (sorted.map fun c => (c.map (·.name)).toArray).toArray
    let originalAll : Array Ix.Name := Id.run do
      for c in cs do
        if let .indc ind := c then return ind.all
      return #[]
    if originalAll.isEmpty then return none
    let inAll (n : Ix.Name) := originalAll.any (Ix.Compile.ExactKey.nameEq · n)
    let classes := (classNames.map (·.filter inAll)).filter (!·.isEmpty)
    if classes.isEmpty then return none
    let maps := Ix.AuxGen.AddrMaps.ofCompileEnv (← Ix.CompileM.getCompileEnv)
    let kernel ← checkedFamilyKernel cenv maps originalAll
    let (out, ctx) ← (Ix.AuxGen.generateAuxPatches classes originalAll maps kernel).run
      Ix.AuxGen.AuxKernelCtx.new
    -- the Prop family, as CompileAux builds its overlay
    let belowRaw : Array Ix.AuxGen.BelowIndc := out.patches.fold (init := #[]) fun acc _ p =>
      match p with
      | .belowIndc bi => acc.push bi
      | _ => acc
    let names := belowRaw.map (·.name)
    let mut family : Array (Ix.InductiveVal × Array Ix.ConstructorVal) := #[]
    let mut overlay : Std.HashMap Ix.Name Ix.ConstantInfo := {}
    for bi in belowRaw do
      if let .indc ind := Ix.AuxGen.belowIndcToMutConst bi names then
        let v : Ix.InductiveVal :=
          { cnst := { name := ind.name, levelParams := ind.levelParams, type := ind.type }
            numParams := ind.numParams, numIndices := ind.numIndices, all := ind.all
            ctors := ind.ctors.map (·.cnst.name), numNested := ind.numNested
            isRec := ind.isRec, isUnsafe := ind.isUnsafe, isReflexive := ind.isReflexive }
        family := family.push (v, ind.ctors)
        overlay := overlay.insert ind.name (.inductInfo v)
        for c in ind.ctors do overlay := overlay.insert c.cnst.name (.ctorInfo c)
    let familyRecs ← if family.isEmpty then pure #[] else do
      let (recs, _) ← (do
        let base := match ctx.canonical, ctx.canonicalOracle with
          | some .installed, some oracle => Ix.AuxGen.AuxKernel.ixc maps oracle
          | _, _ => kernel
        let familyKernel ← base.withFamily family
        Ix.AuxGen.generateCanonicalRecursorsWithOverlay
          (family.map fun (p : Ix.InductiveVal × Array Ix.ConstructorVal) => #[p.1.cnst.name])
          (some overlay) none familyKernel).run ctx
      pure recs.1
    return some { classes, originalAll, out, family, familyRecs }
  match Ix.CompileM.CompileM.run cenv blockEnv {} act with
  | .ok (r, _) => .ok r
  | .error e => .error (toString e)

/-- The declarations to admit, in generation order. -/
def decls (g : Gen) : Array Ix.AuxGen.GeneratedDecl := Id.run do
  let ps := g.out.patches.toArray.qsort fun (a, p) (b, q) =>
    order p < order q || (order p == order q && Ix.LeanIngress.nameCmp a b == .lt)
  let mut out : Array Ix.AuxGen.GeneratedDecl := #[]
  let mut familyDone := false
  for (n, p) in ps do
    match p with
    | .recr _ => pure ()
    | .casesOnDef d | .recOnDef d => out := out.push (.defn n d.levelParams d.typ d.value false)
    | .belowDef d => out := out.push (.defn n d.levelParams d.typ d.value false)
    | .belowIndc _ =>
      if !familyDone then
        out := out.push (.family g.family g.familyRecs)
        familyDone := true
    | .brecOnDef d =>
      let thm := !d.isUnsafe && (d.isProp || (match n with | .str _ "eq" _ => true | _ => false))
      out := out.push (.defn n d.levelParams d.typ d.value thm)
  return out

def measureOn (label : String) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (width : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (_, _, cenv) ← IO.ofExcept (← IO.lazyPure fun _ =>
    Ix.CompileM.compileEnvFold env blocks (width := width))
  let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
  let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks levels
    ({} : Ix.CompileM.AuxIxcOptions).asks
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: production fold {t1 - t0} ms"
  let mut counts : Std.HashMap String Nat := {}
  let mut samples : Array String := #[]
  let mut failures : Array String := #[]
  let bump (m : Std.HashMap String Nat) (k : String) := m.insert k (m.getD k 0 + 1)
  for (lo, members) in inductiveBlocks env blocks do
    let key := Ix.CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})
    let some t := ra.runFor key | do failures := failures.push s!"{lo.pretty}: no level"; continue
    match ← IO.lazyPure fun _ => generate cenv lo members with
    | .error e => failures := failures.push s!"{lo.pretty}: generation: {e.take 200}"
    | .ok none => pure ()
    | .ok (some g) =>
      let route := routeOf env.get? g.classes g.originalAll
      if route == "unsafe" then
        counts := bump counts s!"{route} | exempt (blocks)"
        continue
      if route == "lean" then
        counts := bump counts s!"{route} | identity (blocks)"
        continue
      let o := Ix.AuxGen.Ixc.oracleOfRun .fallback false (fun _ => t.get) (ra.membersFor key)
        { recursors := true, lookup := env.get? }
      let mut o := o
      -- the canonical flat block (the generated recursors checked)
      match o.withFlat g.classes g.originalAll g.out.canonicalRecs with
      | .ok (some o') =>
        o := o'
        counts := bump counts s!"{route} | rec (flat block) | accepted"
      | .ok none => counts := bump counts s!"{route} | rec (flat block) | not needed"
      | .error e =>
        counts := bump counts s!"{route} | rec (flat block) | refused"
        samples := samples.push s!"{lo.pretty}: flat block: {e.take 240}"
      match o.admit (decls g) with
      | .error e => failures := failures.push s!"{lo.pretty}: admit: {e.take 200}"
      | .ok (_, verdicts) =>
        for (n, why) in verdicts do
          let kind := match g.out.patches.get? n with
            | some p => kindOf p
            | none => "below (Prop family)"
          match why with
          | none => counts := bump counts s!"{route} | {kind} | accepted"
          | some r =>
            counts := bump counts s!"{route} | {kind} | refused"
            if samples.size < 40 then samples := samples.push s!"{n.pretty}: {r.take 240}"
  for (k, n) in counts.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"{label}: {k}: {n}"
  for s in samples do IO.println s!"{label}:   refused: {s}"
  for f in failures.extract 0 10 do IO.println s!"{label}:   failure: {f}"
  IO.println s!"{label}: {failures.size} harness failures"

def run : IO UInt32 := do
  let (env, blocks) ← Tests.Ix.AuxGen.BelowIxc.fixtureInput
  measureOn "fixtures" env blocks 16
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let consts := leanEnv.constants.toList.toArray
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts 32
  let blocks ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.condense env (parallel := true)
  measureOn "Init+Std" env blocks 128
  return 0

end Tests.Ix.AuxGen.AcceptanceProbe
