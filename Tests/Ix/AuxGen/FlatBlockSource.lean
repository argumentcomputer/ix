import LSpec
import Ix.Meta
import Ix.CompileDriver
import Ix.AuxGen.SourceService
import Ix.Cert.Statement
import Tests.Ix.Kernel.SourceIngress

/-! # The canonical flat block in Source mode (`lake test -- auxgen-flat-source`)

AuxGen on IxC, M1: the canonical flat blocks of the compiler's own blocks,
installed in the Source service environment (`Ix.AuxGen.Source.Service`)
and checked there by the verified fold, on the compiler's alias-collapse
fixtures (`Tests.Ix.Compile.Mutual`, `Tests.Ix.Compile.Canonicity`: twins,
over-merges, collapsed mutual and nested blocks, blocks that reference
collapsed ones):

1. **The flat blocks are accepted.** The fixtures' closure is compiled by the
   pure driver (`compileEnvAux`); each inductive block's canonical classes
   and canonical recursors are generated as the driver's aux tail generates
   them (`sortConsts`, the classes restricted to Lean's `all`,
   `generateAuxPatches`). Every block whose canonical layout is not Lean's
   (`Flat.needed`) gets its flat block, built over the σ of the blocks
   before it and installed in dependency order: Source mode accepts each.
2. **σ fits `Key.map`.** For every flat block, the Source ingress of each
   σ-renamed term equals `Key.map g` (`Ix.Cert.Rename.expr`) of the ingress
   of the term, where `g` is σ on Source names: σ is the renaming lemma's
   shape on the Source side (IXC-PLAN §12).
3. **The alias collapse is resolved.** The generated `casesOn`, `recOn`,
   `.below` and `.brecOn` definitions of every block with a flat block are
   accepted by Source mode through σ (each admitted under its fresh name,
   so the later ones read the earlier through σ), and the collapsed blocks'
   definitions read by Lean's names (σ empty) are refused: AuxGen's terms
   live in the α-quotient, which the flat block and σ make a checked object
   (AUXGEN-IXC §4.4). A definition over a Prop-level `.below` inductive
   waits for that inductive's install (`admitGenerated`'s inductive half,
   M2); its verdict is printed, not asserted. -/

namespace Tests.Ix.AuxGen.FlatBlockSource

open LSpec
open Ix.AuxGen.Source (Service Status)
open Ix.AuxGen.Flat (FlatBlock ClassMap)
open Tests.Ix.Kernel.SourceIngress (envOf)
open Tests.Ix.Kernel.SourceIngressStep (condense)

def fixtureModules : Array Lean.Name := #[`Tests.Ix.Compile.Mutual, `Tests.Ix.Compile.Canonicity]

/-! ## The compiler's canonical blocks -/

/-- A block's canonical classes (restricted to Lean's `all`), Lean's `all`,
and the aux generator's output, as the driver's aux tail computes them. -/
structure BlockAux where
  lo : Ix.Name
  classes : Array (Array Ix.Name)
  originalAll : Array Ix.Name
  out : Ix.AuxGen.AuxPatchesOutput

def blockAux (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (all : Array Ix.Name) :
    Except String (Option BlockAux) :=
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let act : Ix.CompileM.CompileM (Option BlockAux) := do
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
    let (out, _) ← (Ix.AuxGen.generateAuxPatches classes originalAll maps).run
      Ix.AuxGen.AuxKernelCtx.new
    return some { lo, classes, originalAll, out }
  match Ix.CompileM.CompileM.run cenv blockEnv {} act with
  | .ok (r, _) => .ok r
  | .error e => .error (toString e)

/-- The condensation's blocks that hold an inductive, in dependency order
(depth-first postorder over the blocks' references, roots and successors by
name), each with its members sorted by name. -/
def inductiveBlocks (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Array (Ix.Name × Array Ix.Name) := Id.run do
  let isInd (n : Ix.Name) := match env.consts.get? n with
    | some (.inductInfo _) => true
    | _ => false
  let byName (a b : Ix.Name) := Ix.LeanIngress.nameCmp a b == .lt
  let los := (blocks.blocks.toArray.map (·.1)).qsort byName
  let mut done : Std.HashSet Ix.Name := {}
  let mut out : Array (Ix.Name × Array Ix.Name) := #[]
  for root in los do
    let mut stack : Array (Ix.Name × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (lo, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if expanded then
        let members := ((blocks.blocks.get? lo).getD {}).toArray.qsort byName
        if members.any isInd then out := out.push (lo, members)
      else if !done.contains lo then
        done := done.insert lo
        stack := stack.push (lo, true)
        let refs := ((blocks.blockRefs.get? lo).getD {}).toArray.filterMap (blocks.lowLinks.get? ·)
        for r in (refs.qsort byName).reverse do
          if !done.contains r then stack := stack.push (r, false)
  return out

/-! ## σ fits `Key.map` -/

/-- σ on Source names: `ingressName n ↦ ingressName m` for each entry. -/
def kernelMap (σ : ClassMap) : Std.HashMap Ix.Kernel.Name Ix.Kernel.Name :=
  σ.entries.foldl (fun m (n, n') =>
    m.insert (Ix.LeanIngress.ingressName n) (Ix.LeanIngress.ingressName n')) {}

/-- The terms a flat block is built from, before σ, with each one's level
parameters and whether it belongs to a large eliminator. -/
def sourceTerms (lookup : Ix.Name → Option Ix.ConstantInfo) (b : BlockAux) :
    Array (Array Ix.Name × Bool × Ix.Expr) := Id.run do
  let mut out := #[]
  let firstLps : Nat := match b.classes[0]?.bind (·[0]?) |>.bind lookup with
    | some (.inductInfo v) => v.cnst.levelParams.size
    | _ => 0
  for cls in b.classes do
    if let some (.inductInfo v) := cls[0]?.bind lookup then
      out := out.push (v.cnst.levelParams, false, v.cnst.type)
      for c in v.ctors do
        if let some (.ctorInfo cv) := lookup c then out := out.push (cv.cnst.levelParams, false, cv.cnst.type)
  for (_, rv) in b.out.canonicalRecs do
    let large := rv.cnst.levelParams.size == firstLps + 1
    out := out.push (rv.cnst.levelParams, large, rv.cnst.type)
    for r in rv.rules do out := out.push (rv.cnst.levelParams, large, r.rhs)
  return out

/-- The Source ingress of each σ-renamed term is `Key.map g` of the ingress
of the term. `σ` is everything installed so far (the block's own entries
and the blocks' before it). -/
def fits (σ : ClassMap) (terms : Array (Array Ix.Name × Bool × Ix.Expr)) : Bool :=
  let g := kernelMap σ
  let keyMap := Ix.Kernel.Key.map (md := .source) (md' := .source) fun n => g.getD n n
  terms.all fun (lps, large, t) =>
    let pos := (Ix.LeanIngress.Numbering.mk lps large).pos
    match Ix.LeanIngress.ingressExprs pos [Ix.AuxGen.Flat.rename σ t],
        Ix.LeanIngress.ingressExprs pos [t] with
    | .ok [a], .ok [b] => decide (a = Ix.Cert.Rename.expr keyMap b)
    | _, _ => false

/-! ## Generated definitions through σ -/

/-- The generated definitions of a block, in dependency order (`casesOn`,
`recOn`, `.below`, `.brecOn.go`, `.brecOn`, `.brecOn.eq`): name, level
parameters, type, value, and whether it is a theorem. Prop-level `.below`
inductives are not definitions: their names and their constructors' names
are returned apart. Installing them (with their generated recursors) is
`admitGenerated`'s inductive half, AuxGen M2. -/
def generatedDefs (out : Ix.AuxGen.AuxPatchesOutput) :
    Array (Ix.Name × Array Ix.Name × Ix.Expr × Ix.Expr × Bool) × Array Ix.Name := Id.run do
  let rank (n : Ix.Name) : Nat := match n with
    | .str _ "go" _ => 3
    | .str _ "eq" _ => 5
    | _ => 4
  let mut defs : Array (Nat × Ix.Name × Array Ix.Name × Ix.Expr × Ix.Expr × Bool) := #[]
  let mut indcs : Array Ix.Name := #[]
  for (n, p) in out.patches.toArray do
    match p with
    | .casesOnDef d => if !d.isUnsafe then defs := defs.push (0, n, d.levelParams, d.typ, d.value, false)
    | .recOnDef d => if !d.isUnsafe then defs := defs.push (1, n, d.levelParams, d.typ, d.value, false)
    | .belowDef d => if !d.isUnsafe then defs := defs.push (2, n, d.levelParams, d.typ, d.value, false)
    | .brecOnDef d =>
      if !d.isUnsafe then
        let thm := d.isProp || rank n == 5
        defs := defs.push (rank n, n, d.levelParams, d.typ, d.value, thm)
    | .belowIndc i => indcs := indcs.push i.name ++ i.ctors.map (·.name)
    | .recr _ => pure ()
  let sorted := defs.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && Ix.LeanIngress.nameCmp a.2.1 b.2.1 == .lt)
  return (sorted.map (·.2), indcs)

/-- Whether a term mentions one of `names`. -/
def mentions (names : Array Ix.Name) (e : Ix.Expr) : Bool :=
  let refs := Ix.AuxGen.collectLeanConstRefs e {}
  names.any refs.contains

/-! ## The run -/

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def showCounts (m : Std.HashMap String Nat) : String :=
  ", ".intercalate ((m.toArray.qsort (·.1 < ·.1)).toList.map fun (k, v) => s!"{k} {v}")

def evaluate : IO (Array String × Array String) := do
  let t0 ← IO.monoMsNow
  let leanEnv ← getCompileEnv (fixtureModules ++ #[`IxC.Kernel.PinGen.Certs])
  let idxs := fixtureModules.filterMap leanEnv.getModuleIdx?
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    if (leanEnv.getModuleIdxFor? n).any idxs.contains then some n else none
  let certs := (Ix.RoleEvidence.certTheorems.flatMap (·.2)).toArray
  let env ← envOf leanEnv (seeds ++ certs)
  let blocks := condense env
  let (_, _, cenv) ← IO.ofExcept (← IO.lazyPure fun _ => Ix.CompileM.compileEnvAux env blocks)
  let t1 ← IO.monoMsNow
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let mut svc ← IO.lazyPure fun _ => Service.create pre env blocks (workers := 4)
  let t2 ← IO.monoMsNow
  let lookup := cenv.env.consts.get?
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let mut shapes : Std.HashMap String Nat := {}
  let mut installed := 0
  let mut generated : Std.HashMap String Nat := {}
  let mut controlRefused := 0
  let mut controlChecked := 0
  let mut indcs := 0
  let mut deferred : Std.HashMap String Nat := {}
  for (lo, members) in inductiveBlocks env blocks do
    match blockAux cenv lo members with
    | .error e => errors := errors.push s!"{lo.pretty}: aux generation: {e}"
    | .ok none => pure ()
    | .ok (some b) =>
      let nClasses := b.classes.size
      let auxNames := (b.out.canonicalRecs.extract nClasses b.out.canonicalRecs.size).map (·.1)
      let leanNested := match b.originalAll[0]?.bind lookup with
        | some (.inductInfo v) => v.numNested
        | _ => 0
      let collapsed := b.classes.any (·.size > 1)
      let shape := s!"{if nClasses == 1 then "single" else "mutual"}\
        {if auxNames.isEmpty then "" else "+nested"}{if collapsed then "+collapse" else ""}"
      unless Ix.AuxGen.Flat.needed b.classes b.originalAll auxNames leanNested do
        shapes := bump shapes s!"{shape}: Lean's layout"
        continue
      shapes := bump shapes s!"{shape}: flat block"
      match Ix.AuxGen.Flat.build lookup b.classes b.out.canonicalRecs svc.sigma with
      | .error e => errors := errors.push s!"{lo.pretty}: build: {e}"
      | .ok fb =>
        svc := svc.installFlat fb
        let first := fb.firstName.getD default
        match svc.flatStatus? first with
        | some .accepted =>
          installed := installed + 1
          unless fits svc.sigma (sourceTerms lookup b) do
            errors := errors.push s!"{lo.pretty}: σ does not fit Key.map"
        | some (.refused why) => errors := errors.push s!"{lo.pretty}: flat block refused: {why}"
        | _ => errors := errors.push s!"{lo.pretty}: flat block not recorded"
        -- the generated definitions, through σ; and, for a collapsed block,
        -- the same read by Lean's names
        let (defs, belowIndcs) := generatedDefs b.out
        indcs := indcs + belowIndcs.size
        for (n, lps, ty, v, thm) in defs do
          let control := ({ svc with env := { svc.env with sigma := {} } } : Service).admitDefinition n lps ty v thm
          let (svc', st) := svc.admitDefinition n lps ty v thm
          svc := svc'
          -- a definition over a Prop-level `.below` inductive waits for that
          -- inductive's install (M2): its verdict is recorded, not asserted
          if mentions belowIndcs ty || mentions belowIndcs v then
            deferred := bump deferred (if st.isAccepted then "accepted" else "refused")
            continue
          match st with
          | .accepted => generated := bump generated s!"{shape} accepted"
          | .refused why =>
            generated := bump generated s!"{shape} refused"
            errors := errors.push s!"{n.pretty}: generated definition refused through σ: {why.take 200}"
          | _ => pure ()
          if collapsed then
            controlChecked := controlChecked + 1
            match control.2 with
            | .accepted => pure ()
            | _ => controlRefused := controlRefused + 1
  let t3 ← IO.monoMsNow
  let (pending, acc, ref, blk) := svc.counts
  lines := lines.push s!"fixture closure: {env.consts.size} constants; compile {t1 - t0} ms; \
    service {t2 - t1} ms; flat blocks and checks {t3 - t2} ms"
  lines := lines.push s!"blocks: {showCounts shapes}"
  lines := lines.push s!"flat blocks installed and accepted: {installed}; σ entries {svc.sigma.entries.size}"
  lines := lines.push s!"generated definitions through σ: {showCounts generated}"
  lines := lines.push s!"definitions over a Prop-level .below inductive (its install is M2's; \
    {indcs} inductive and constructor names): {showCounts deferred}"
  lines := lines.push s!"collapsed blocks' definitions refused by Lean's names (control): \
    {controlRefused} of {controlChecked}"
  lines := lines.push s!"service groups: folded {acc} accepted, {ref} refused, {blk} blocked, \
    {pending} never asked for; prelude declarations synthesised {svc.synthesised}"
  if installed == 0 then errors := errors.push "no flat block was installed"
  if controlRefused == 0 then
    errors := errors.push "the control accepted every collapsed block's definition by Lean's names"
  return (errors, lines)

def fixtures : TestSeq :=
  .individualIO "auxgen flat blocks: accepted in Source mode, σ fits Key.map, collapse resolved"
    none (do
      let (errors, lines) ← evaluate
      for l in lines do IO.println l
      for e in errors do IO.println s!"  error: {e}"
      let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
      return (errors.isEmpty, 1, 0, msg)) .done

def suite : List TestSeq := [fixtures]

end Tests.Ix.AuxGen.FlatBlockSource
