import Ix.Meta
import Ix.CompileDriver
import Ix.AuxGen.Patches
import Ix.AuxGen.Nested
import Ix.LeanIngress
import Tests.Ix.Kernel.SourceIngressStep

/-! # nested-agreement: the compiler's nested expansion against IxC's nested modeller

The regression form of spike SP5 (`SP5-NESTED.md`, CQ3.3). For every
inductive block with `numNested > 0` among the fixtures (below), and every
compiler SCC of it:

* **Lean / IxC Source.** The block as Lean gives it (types, constructors,
  `T.rec`, `T₀.rec_j`) is converted by `Ix.LeanIngress.convertInductive` and
  turned into the modeller's `BlockRec` as `Reader.lowerInductive` does;
  IxC's `readMems` reads the members and mimics off the first recursor's
  motives (Lean's own nested→mutual order), the minors' field kinds are read
  as `readCtors` reads them, and `genNested` runs at the context the Source
  ingress builds over the closure.
* **Compiler.** In the `CompileEnv` of the pure-Lean compile of the closure
  (`compileLeanConsts`): `sortConsts`, the canonical expansion
  (`expandNestedBlock … (canonicalGroups := true)`, discovery order over the
  canonical members, external groups opened as their compiled classes, no
  sort), `computeAuxPerm`, the source walk (`expandNestedBlock originalAll
  {}`) and `generateAuxPatches` (the canonical recursors, restored to nested
  form).
* **Compiled / IxC.** The SCC's canonical block (class representatives,
  aliases renamed to them, the generated recursors in motive order) is read
  by the same Source-mode path.

Checked per SCC, each a failure:

1. **source order:** IxC's mimics of Lean's family are the compiler's source
   walk (the basis of `computeAuxPerm` and of `rec_N` naming);
2. **canonical order:** IxC's mimics of the compiled family are the
   compiler's canonical expansion;
3. **permutation:** the matching of the two readings is `computeAuxPerm`;
   and it is the identity wherever Lean's member order is canonical (every
   class a singleton, the SCC the whole block in Lean's order, and every
   external group the occurrences open compiled in its Lean order);
4. **field kinds:** per minor and field, IxC's reading equals the
   compiler's, on Lean's family against the source walk and on the compiled
   family against the canonical expansion;
5. **verdicts:** the modeller (or the direct route) accepts the compiled
   family exactly when it accepts Lean's;
6. **negative:** for a Lean block without nesting, the compiler's source
   walk finds no auxiliary.

The fixtures: the nested blocks of the test environment's fixture modules
(`fixtureModules`; at least `minFixtureBlocks` of them), `Tests.Ix.Compile.
Fixtures.NestedLevels` (loaded from its `.olean`, built by `TwinsFixtures`)
and `Tests/Ix/Compile/Fixtures/CanonSiblingNest.lean` (elaborated at run
time). `NestedLevels.Mixed` is the case CQ3.3's address-keyed deduplication
fixed: its two occurrences `List.{max 0 0} Right` and `List.{0} Right` are
one auxiliary of the compiled family. Not here: `Tests.Ix.Kernel.EntryCaseDefs`
(it holds an unchecked false theorem, so it stays out of the test binary's
environment) and the aux-cert files (refusals and IxC declines by design;
aux-cert checks them).

Run with `lake test -- nested-agreement` (landing tier).
`IX_NESTED_AGREEMENT_VERBOSE=1` prints every reading.
-/

namespace Tests.Ix.Compile.NestedAgreement

open Ix.Kernel.Frontend.InModel (BlockRec Ctx Mem readMems matchCarrier Family genNested)
open Ix.Kernel.Reader (BlockRead CName State ReadError)

abbrev KExpr := Ix.Kernel.Expr .source
abbrev KLevel := Ix.Kernel.Level

/-! ## Rendering -/

def rL : KLevel → String
  | .zero => "0"
  | .succ u => s!"{rL u}+1"
  | .max u v => s!"max({rL u},{rL v})"
  | .imax u v => s!"imax({rL u},{rL v})"
  | .param n => s!"u{n}"

def rK : KExpr → String
  | .bvar i => s!"#{i}"
  | .fvar i _ => s!"fv{i}"
  | .sort u => s!"Sort({rL u})"
  | .const n us => if us.isEmpty then toString n else s!"{n}.\{{",".intercalate (us.map rL)}}"
  | .app f a => s!"({rK f} {rK a})"
  | .lam t b _ => s!"(fun :{rK t} => {rK b})"
  | .forallE t b _ => s!"((:{rK t}) -> {rK b})"
  | .letE t v b _ => s!"(let :{rK t} := {rK v}; {rK b})"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s.quote
  | .proj s i e => s!"{rK e}.{s}.{i}"

def rMem (m : Mem .source) : String :=
  let head := if m.lv.isEmpty then toString m.I else s!"{m.I}.\{{",".intercalate (m.lv.map rL)}}"
  match m.real? with
  | some k => s!"real{k}:{head} idx{m.nIdx}"
  | none => s!"{head} {" ".intercalate (m.pins.map rK)} idx{m.nIdx}"

def rErr : ReadError → String
  | .malformed m => s!"reject: {m}"
  | .declined m => s!"decline: {m}"

/-! ## The modeller's records, as `Reader.lowerInductive` builds them -/

def blockRecOf (rb : BlockRead .source) : BlockRec .source :=
  let ⟨_, types, ctors, ctorNames, recs⟩ := rb
  let nTypes := types.size
  let numNested := match recs[0]? with
    | some (_, r, _) => r.motives - nTypes
    | none => 0
  let memberNames := types.toList.map (·.1.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (Ix.Kernel.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (Ix.Kernel.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := Ix.Kernel.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (Ix.Kernel.Frontend.headIs · body)
  ⟨types.toList.zip ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
      { cv, nP, nIdx, ctors := cs, isRec, isReflexive, numNested },
   ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
   recs.toList.map fun (cv, r, rules) =>
     { cv, nP := r.params, nM := r.motives, nm := r.minors, nI := r.indices, rules }⟩

/-- `nativeShape?` (the direct route's recogniser) on the block's records,
as `Reader.lowerInductive` lays them out. -/
def nativeOf (rb : BlockRead .source) : Bool :=
  let ⟨nPd, types, ctors, _, recs⟩ := rb
  let typeInfos : List (Ix.Kernel.ConstantInfo .source) := types.toList.map fun (cv, _, _) => .indInfo cv {}
  let ctorInfos : List (Ix.Kernel.ConstantInfo .source) := ctors.toList.map fun (cv, nP, nF) => .ctorInfo cv nP nF
  let recInfos : List (Ix.Kernel.ConstantInfo .source) := recs.toList.map fun (cv, r, rules) =>
    .recInfo cv (r.params + r.motives + r.minors + r.indices) (r.params + r.motives + r.minors) rules
  (Ix.Kernel.nativeShape? nPd (typeInfos ++ ctorInfos ++ recInfos)).isSome

/-- One minor premise as IxC reads it (`readCtors` without its declines):
its member (motive), constructor, per-field kind (`some tag` for a whole
carrier, `none` otherwise), whether a `none` field still mentions a real
member, and the inductive-hypothesis count. -/
structure MinorRead where
  mem : Nat
  cname : String
  kinds : List (Option Nat)
  other : List Bool
  nIh : Nat

instance : Inhabited MinorRead := ⟨⟨0, "", [], [], 0⟩⟩

def rKinds (kinds : List (Option Nat)) (other : List Bool) : String :=
  let ks := (kinds.zip other).map fun
    | (some t, _) => toString t
    | (none, true) => "x"
    | (none, false) => "-"
  s!"[{",".intercalate ks}]"

def MinorRead.render (m : MinorRead) : String := s!"{m.mem}:{rKinds m.kinds m.other}"

/-- What IxC reads off a block: the members and mimics, the minors, and the
modeller's verdict. -/
structure IxcRead where
  mems : Except String (List (Mem .source))
  minors : Except String (List MinorRead)
  gen : Except String Nat
  /-- whether the direct route's recogniser (`nativeShape?`) takes the block -/
  native : Bool := false
  /-- not the modeller's (`InModel.wants` false: one type, no nesting) -/
  direct : Bool := false
  deriving Inhabited

def readFamily' (ctx : Ctx .source) (b : BlockRec .source) : IxcRead := Id.run do
  let gen := if Ix.Kernel.Frontend.InModel.wants b then (genNested ctx b).map (·.length) else .ok 0
  let fam : Except String (List (Mem .source) × Nat × Nat × List KExpr) := do
    let t0 :: _ := b.types | throw "empty block"
    let lps := t0.cv.levelParams
    let nP := t0.nP
    let some r0 := b.recs[0]? | throw "no recursor"
    let M := r0.nM
    let n := r0.nm
    let some (_, afterP) := r0.cv.type.stripPis nP | throw "recursor: parameter telescope"
    let some (motiveBs, afterM) := afterP.stripPis M | throw "recursor: motive telescope"
    let some (minorBs, _) := afterM.stripPis n | throw "recursor: minor telescope"
    let mems ← readMems lps nP b.types (motiveBs.map (·.1))
    pure (mems, M, nP, minorBs.map (·.1))
  match fam with
  | .error e => return { mems := .error e, minors := .error e, gen }
  | .ok (mems, M, nP, minors) =>
    let t0 := b.types.headD default
    let r := b.types.length
    let famRec : Family .source :=
      ⟨t0.cv.name, t0.cv.levelParams, nP, [], .zero, r, mems, [], false, 0⟩
    let memberNames := mems.filterMap fun m => if m.real?.isSome then some m.I else none
    let nFOf : Ix.Kernel.Key .source → Nat → Except String Nat := fun cname mem => do
      let some memR := mems.find? (·.tag == mem) | throw "no member"
      match memR.real? with
      | some _ =>
        match b.ctors.find? (·.cv.name == cname) with
        | some c => pure c.nF
        | none => throw s!"constructor {cname} not in the block"
      | none =>
        match b.recs[memR.tag]? with
        | none => throw s!"no recursor at motive {memR.tag}"
        | some rr =>
          match rr.rules.find? (·.ctor == cname) with
          | some rule => pure rule.nfields
          | none => throw s!"no rule for {cname}"
    let minorsE : Except String (List MinorRead) := do
      let mut out : List MinorRead := []
      for J in List.range minors.length do
        let dom := minors.getD J default
        let (bs, body) := Ix.Kernel.Frontend.InModel.stripAllPis dom
        let .bvar mv := body.getAppFn | throw s!"minor {J}: codomain head is not a motive"
        unless mv ≥ bs.length + J && mv < bs.length + J + M do
          throw s!"minor {J}: codomain head is not a motive"
        let mem := M - 1 - (mv - bs.length - J)
        let margs := body.getAppArgs
        let some capp := margs.getLast? | throw s!"minor {J}: no major"
        let .const cname _ := capp.getAppFn | throw s!"minor {J}: major head is not a constructor"
        let nF ← nFOf cname mem
        unless nF ≤ bs.length do throw s!"minor {J}: fewer binders than fields"
        let doms : List KExpr := (List.range nF).map fun i =>
          let (d, _) := bs.getD i default
          Ix.Kernel.Frontend.InModel.betaHead (d.lowerBVars (M + J) i)
        let kinds := (List.range nF).map fun i => (matchCarrier famRec i (doms.getD i default)).map (·.1)
        let other := (List.range nF).map fun i =>
          (kinds.getD i none).isNone && Ix.Kernel.Frontend.InModel.mentionsAny memberNames (doms.getD i default)
        out := out ++ [⟨mem, toString cname, kinds, other, bs.length - nF⟩]
      pure out
    return { mems := .ok mems, minors := minorsE, gen }

def readFamily (ctx : Ctx .source) (b : BlockRec .source) : IxcRead :=
  { readFamily' ctx b with direct := !Ix.Kernel.Frontend.InModel.wants b }

/-- The verdict's class: accepted (by the modeller, or not the modeller's
block) or declined. -/
def IxcRead.accepted (r : IxcRead) : Bool := r.direct || r.gen.toBool

/-- The modeller's verdict, or the direct route's when the block is not the
modeller's (`InModel.wants`). -/
def IxcRead.render (r : IxcRead) : String :=
  if r.direct then s!"direct(nativeShape? {if r.native then "some" else "none"})" else
  match r.gen with
  | .ok k => s!"ok({k})"
  | .error e => s!"decline: {e}"

/-! ## The compiler's side -/

/-- A flat member's kind list per constructor (field heads), compiler side. -/
def compilerMinors (x : Ix.AuxGen.ExpandedBlock) : List (Nat × List (Option Nat) × List Bool) := Id.run do
  let names : Array Ix.Name := x.types.map (·.name)
  let nameSet : Std.HashSet Ix.Name := names.foldl (·.insert ·) {}
  let nP := (x.types[0]?.map (·.nParams)).getD 0
  let mut out := []
  for (mem, mi) in x.types.zipIdx do
    for c in mem.ctors do
      let (_, _, body) := Ix.AuxGen.forallTelescope c.typ nP "nested-agreement" 0
      let mut cur := body
      let mut kinds : List (Option Nat) := []
      let mut other : List Bool := []
      for _ in [0:c.nFields] do
        match cur with
        | .forallE _ d b _ _ =>
          let (h, _) := Ix.AuxGen.decomposeApps (Ix.AuxGen.betaReduce (Ix.AuxGen.stripMdata d))
          let k := match h with
            | .const n _ _ => names.findIdx? (· == n)
            | _ => none
          kinds := kinds ++ [k]
          other := other ++ [k.isNone && Ix.AuxGen.exprMentionsAnyName d nameSet]
          cur := b
        | .mdata _ e _ => cur := e
        | _ => break
      out := out ++ [(mi, kinds, other)]
  return out

def rCompilerMinor (m : Nat × List (Option Nat) × List Bool) : String :=
  s!"{m.1}:{rKinds m.2.1 m.2.2}"

/-- A compiler aux signature as IxC Source terms: the head's key, its levels
and the spec parameters with the block parameters abstracted to the
parameter frame. -/
structure Sig where
  head : Ix.Kernel.Key .source
  lv : List KLevel
  pins : List KExpr
  deriving BEq

def Sig.render (s : Sig) : String :=
  let head := if s.lv.isEmpty then toString s.head else s!"{s.head}.\{{",".intercalate (s.lv.map rL)}}"
  s!"{head} {" ".intercalate (s.pins.map rK)}"

def Sig.ofMem (m : Mem .source) : Sig := ⟨m.I, m.lv, m.pins⟩

def sigOf (levelParams : Array Ix.Name) (blockParamFvars : Array Ix.Expr)
    (head : Ix.Name) (levels : Array Ix.Level) (specs : Array Ix.Expr) : Except String Sig := do
  let σ : Ix.LeanIngress.Numbering := ⟨levelParams, false⟩
  let nP := blockParamFvars.size
  let mut fv : Std.HashMap Ix.Name Nat := {}
  for (e, i) in blockParamFvars.zipIdx do
    if let .fvar n _ := e then fv := fv.insert n i
  let lv ← levels.toList.mapM fun l => (Ix.LeanIngress.ingressLevel σ.pos l).mapError toString
  let pins ← specs.toList.mapM fun sp =>
    (Ix.LeanIngress.ingressExpr σ.pos (Ix.AuxGen.batchAbstract sp fv nP 0)).mapError toString
  pure ⟨Ix.LeanIngress.ingressKey head, lv, pins⟩

/-- Signatures of the aux members of an expanded block, in its order. -/
def sigsOf (x : Ix.AuxGen.ExpandedBlock) : Except String (List Sig) :=
  (Ix.AuxGen.auxSignaturesOfExpanded x).toList.mapM fun (h, ls, ss) =>
    sigOf x.levelParams x.blockParamFvars h ls ss

/-- Rename the block's alias members to their representatives in a Source
term (the matching the permutation is defined up to). -/
def renameK (f : Ix.Kernel.Key .source → Ix.Kernel.Key .source) : KExpr → KExpr
  | .const n us => .const (f n) us
  | .app g a => .app (renameK f g) (renameK f a)
  | .lam t b m => .lam (renameK f t) (renameK f b) m
  | .forallE t b m => .forallE (renameK f t) (renameK f b) m
  | .letE t v b l => .letE (renameK f t) (renameK f v) (renameK f b) l
  | .proj s i e => .proj s i (renameK f e)
  | e => e

/-! ## One SCC, compiler side -/

structure SccOut where
  lo : String
  classes : Array (Array Ix.Name)
  path : String
  srcSigs : Except String (List Sig) := .error "-"
  canonSigs : Except String (List Sig) := .error "-"
  perm : Except String (Array Nat) := .error "-"
  canonMinors : List (Nat × List (Option Nat) × List Bool) := []
  srcMinors : List (Nat × List (Option Nat) × List Bool) := []
  canonRecs : Except String (Array Ix.RecursorVal) := .error "-"
  canonTypes : Array Ix.InductiveVal := #[]
  canonCtors : Array (Array Ix.ConstructorVal) := #[]
  /-- every external group the source walk opens is compiled in its Lean
  order (each class a singleton, the representatives in `I.all` order) -/
  externalsInLeanOrder : Bool := false
  err : Option String := none

def permStr (p : Array Nat) : String :=
  " ".intercalate (p.toList.map fun i => if i == Ix.AuxGen.PERM_OUT_OF_SCC then "out" else toString i)

/-- The compiler's side of one SCC, in the compile's `CompileEnv`. -/
def compilerScc (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (sccInds : Array Ix.Name)
    (originalAll : Array Ix.Name) : SccOut := Id.run do
  let blockEnv : Ix.CompileM.BlockEnv := { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let maps := Ix.AuxGen.AddrMaps.ofCompileEnv cenv
  let res := Ix.CompileM.CompileM.run cenv blockEnv {} do
    let mut cs : Array Ix.MutConst := #[]
    for n in sccInds do
      match (← Ix.AuxGen.lookupConst? n) with
      | some (.inductInfo v) => cs := cs.push (← Ix.CompileM.MutConst.mkIndc v)
      | _ => pure ()
    let sorted ← Ix.CompileM.sortConsts cs.toList
    let classes : Array (Array Ix.Name) := (sorted.map fun c => (c.map (·.name)).toArray).toArray
    let reps := classes.filterMap (·[0]?)
    let mut aliasToRep : Std.HashMap Ix.Name Ix.Name := {}
    let mut o2c : Std.HashMap Ix.Name Ix.Name := {}
    for cls in classes do
      if let some rep := cls[0]? then
        for n in cls do
          o2c := o2c.insert n rep
          if n != rep then aliasToRep := aliasToRep.insert n rep
    let mut metaNested := false
    for n in originalAll do
      if let some (.inductInfo v) ← Ix.AuxGen.lookupConst? n then
        if v.numNested > 0 then metaNested := true
    -- the canonical expansion, as `generateAuxPatches` builds it
    let canon ← Ix.AuxGen.expandNestedBlock reps aliasToRep (canonicalGroups := true)
    let structNested : Bool := canon.types.size > canon.nOriginals
    let perm : Except String (Array Nat) ← tryCatch
      (Except.ok <$> Ix.AuxGen.computeAuxPerm canon originalAll o2c (fun n => some (maps.resolve n)))
      (fun e => pure (.error s!"computeAuxPerm: {e}"))
    let srcX ← Ix.AuxGen.expandNestedBlock originalAll {}
    -- the external groups the source walk opens, against their compiled classes
    let mut externalsInLeanOrder := true
    for (h, _, _) in Ix.AuxGen.auxSignaturesOfExpanded srcX do
      if let some (.inductInfo hv) ← Ix.AuxGen.lookupConst? h then
        if let some cls := cenv.blocks.get? h then
          let cls := cls.filter (!·.isEmpty)
          unless cls.all (·.size == 1) && cls.filterMap (·[0]?) == hv.all do
            externalsInLeanOrder := false
    -- the canonical block as the compiled environment holds it
    let mut types : Array Ix.InductiveVal := #[]
    let mut ctors : Array (Array Ix.ConstructorVal) := #[]
    let mut cache : Ix.AuxGen.ExprCache := {}
    for rep in reps do
      let some (.inductInfo v) ← Ix.AuxGen.lookupConst? rep | continue
      let (ty, c1) := (Ix.AuxGen.canonicalizeConstNames v.cnst.type aliasToRep).run cache
      cache := c1
      types := types.push { v with cnst := { v.cnst with type := ty }, all := reps }
      let mut cs' : Array Ix.ConstructorVal := #[]
      for cn in v.ctors do
        if let some (.ctorInfo c) ← Ix.AuxGen.lookupConst? cn then
          let (cty, c2) := (Ix.AuxGen.canonicalizeConstNames c.cnst.type aliasToRep).run cache
          cache := c2
          cs' := cs'.push { c with cnst := { c.cnst with type := cty } }
      ctors := ctors.push cs'
    let path := if metaNested && structNested then "expanded" else
      s!"flat(meta={metaNested},struct={structNested})"
    pure (classes, reps, canon, perm, srcX, types, ctors, path, externalsInLeanOrder)
  match res with
  | .error e => return { lo := lo.pretty, classes := #[], path := "error", err := some s!"{e}" }
  | .ok ((classes, reps, canon, perm, srcX, types, ctors, path, externalsInLeanOrder), _) =>
    -- the generated recursors (production entry point)
    let patchesE := Ix.CompileM.CompileM.run cenv blockEnv {}
      ((Ix.AuxGen.generateAuxPatches classes originalAll maps).run' Ix.AuxGen.AuxKernelCtx.new)
    let canonRecs : Except String (Array Ix.RecursorVal) :=
      match patchesE with
      | .error e => .error s!"generateAuxPatches: {e}"
      | .ok (out, _) => do
        let nCanon := canon.types.size - canon.nOriginals
        let some srcAll0 := originalAll[0]? | throw "empty block"
        let mut rs : Array Ix.RecursorVal := #[]
        for rep in reps do
          match out.patches.get? (Ix.Name.mkStr rep "rec") with
          | some (.recr rv) => rs := rs.push rv
          | _ => throw s!"no patch {rep.pretty}.rec"
        if nCanon > 0 then
          let some p := out.perm | throw "no perm"
          let mut canonRepr : Array Nat := Array.replicate nCanon Ix.AuxGen.PERM_OUT_OF_SCC
          for (ci, j) in p.zipIdx do
            if ci < nCanon && canonRepr[ci]? == some Ix.AuxGen.PERM_OUT_OF_SCC then
              canonRepr := canonRepr.set! ci j
          for j in canonRepr do
            let nm := Ix.Name.mkStr srcAll0 s!"rec_{j + 1}"
            match out.patches.get? nm with
            | some (.recr rv) => rs := rs.push rv
            | _ => throw s!"no patch {nm.pretty}"
        pure rs
    return {
      lo := lo.pretty, classes, path
      srcSigs := sigsOf srcX
      canonSigs := sigsOf canon, perm
      canonMinors := compilerMinors canon, srcMinors := compilerMinors srcX
      canonRecs, canonTypes := types, canonCtors := ctors, externalsInLeanOrder }

/-! ## The environment -/

/-- The reference closure of `seeds`, with every inductive's recursors. -/
def closure (env : Lean.Environment) (seeds : List Lean.Name) :
    Array (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  let mut work := seeds
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n <|> env.toKernelEnv.find? n | continue
      out := out.push (n, ci)
      let mut refs : Array Lean.Name := ci.type.getUsedConstants
      match ci with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants ++ v.all.toArray
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants ++ v.all.toArray
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants ++ v.all.toArray
      | .inductInfo v =>
        refs := refs ++ v.ctors.toArray ++ v.all.toArray ++ (v.all.toArray.map (· ++ `rec))
        if let some a0 := v.all.head? then
          for j in [1:v.numNested + 1] do refs := refs.push (a0.str s!"rec_{j}")
      | .ctorInfo v => refs := refs.push v.induct
      | .recInfo v =>
        refs := refs ++ v.all.toArray
        for rule in v.rules do refs := refs ++ rule.rhs.getUsedConstants
      | _ => pure ()
      for r in refs do
        if !seen.contains r then work := r :: work
  return out

/-- The constants the auxiliary generators name. -/
def auxPrereqs : List Lean.Name :=
  [`PUnit, `PUnit.unit, `PUnit.rec, `PProd, `PProd.mk, `PProd.rec, `Eq, `Eq.refl, `Eq.rec,
   `True, `True.intro, `True.rec, `OfNat, `OfNat.rec, `SizeOf, `SizeOf.rec, `Iff, `Iff.rec,
   `Add, `Add.rec, `HAdd, `HAdd.rec, `Nat, `Nat.rec, `PULift, `PULift.rec, `And, `And.rec]

/-- The inductive blocks (first member of each `all`) among the candidate
names: `(nested, other)`, by whether `numNested > 0`. -/
def blocksAmong (env : Lean.Environment) (cands : Array Lean.Name) :
    Array Lean.InductiveVal × Array Lean.InductiveVal := Id.run do
  let mut nested := #[]
  let mut other := #[]
  for n in cands do
    if let some (.inductInfo v) := env.find? n then
      if v.all.head? == some n then
        if v.numNested > 0 then nested := nested.push v else other := other.push v
  return (nested.qsort (·.name.toString < ·.name.toString), other.qsort (·.name.toString < ·.name.toString))

def safe (v : Ix.InductiveVal) : Ix.InductiveVal := { v with isUnsafe := false }

def sigsStr (xs : List Sig) : String :=
  "; ".intercalate ((xs.zipIdx).map fun (s, i) => s!"[{i}] {s.render}")

def memsStr (xs : List (Mem .source)) : String :=
  "; ".intercalate (xs.map fun m => s!"[{m.tag}] {rMem m}")

/-- One environment's result: the nested blocks seen, and the problems
(empty: every check holds). -/
structure EnvResult where
  nestedBlocks : Nat := 0
  rows : Nat := 0
  identities : Nat := 0
  problems : Array String := #[]

def EnvResult.add (r : EnvResult) (p : String) : EnvResult :=
  { r with problems := r.problems.push p }

/-- IxC's reading of a converted block (`Reader.lowerInductive`'s record). -/
def readConverted (ctxFor : BlockRec .source → Ctx .source) (rb : BlockRead .source) : IxcRead :=
  let b := blockRecOf rb
  { readFamily (ctxFor b) b with native := nativeOf rb }

/-- The checks over the nested blocks among `cands` in `env`. -/
def check (label : String) (env : Lean.Environment) (cands : Array Lean.Name)
    (verbose : Bool) : IO EnvResult := do
  let log := fun (s : String) => if verbose then IO.println s!"[nested-agreement] {s}" else pure ()
  let (blocks, plain) := blocksAmong env cands
  let mut res : EnvResult := { nestedBlocks := blocks.size }
  if blocks.isEmpty then return res
  let mut seeds : List Lean.Name := auxPrereqs.filter env.contains
  for v in blocks ++ plain do seeds := v.all ++ seeds
  let consts := closure env seeds
  let compiled ← Ix.CompileM.compileLeanConsts consts.toList (numWorkers := 16)
  if let .error e := compiled then
    return res.add s!"{label}: compile failed: {e}"
  let .ok out := compiled | return res
  for (n, e) in out.cenv.ungrounded.toList do
    res := res.add s!"{label}: compile failure {n.pretty}: {(e.take 200).toString}"
  let cenv := out.cenv
  -- the Source ingress over the closure
  let ixEnv := Tests.Ix.Kernel.SourceIngressStep.canon consts 8
  let condensed := Tests.Ix.Kernel.SourceIngressStep.condense ixEnv
  let groups := Ix.LeanIngress.groupsOf ixEnv condensed
  let converted := groups.map Ix.LeanIngress.convert
  let g := Ix.LeanIngress.graphOf condensed groups converted
  let sched := Ix.LeanIngress.scheduleOf g
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude (md := .source))
  let mut st : State .source := pre.state
  let mut allBlocks : Std.HashMap (CName .source) (BlockRec .source) := {}
  for (_, c) in sched do
    if let .ok (.inductive rb) := c then
      let b := blockRecOf rb
      for t in b.types do allBlocks := allBlocks.insert t.cv.name b
    if let .ok r := c >>= fun c => Ix.LeanIngress.lower st c then
      st := st.commit r
  let ctxFor (b : BlockRec .source) : Ctx .source :=
    let memberNames := b.types.map (·.cv.name)
    ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0,
     fun n => if memberNames.contains n then some b else allBlocks[n]?⟩
  let sccOf (n : Ix.Name) : Option (Ix.Name × Array Ix.Name) := do
    let lo ← condensed.lowLinks.get? n
    let ms ← condensed.blocks.get? lo
    pure (lo, ms.toArray)
  -- 6. the negative check
  for v in plain do
    let all := v.all.toArray.map Ix.Name.fromLeanName
    let some all0 := all[0]? | continue
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := all0, mutCtx := default, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv blockEnv {} (Ix.AuxGen.expandNestedBlock all {}) with
    | .ok (x, _) =>
      if x.types.size > x.nOriginals then
        res := res.add s!"{label}: {v.name}: Lean has no nested auxiliary, \
the compiler's source walk finds {x.types.size - x.nOriginals}"
    | .error e => res := res.add s!"{label}: {v.name}: source walk: {e}"
  for v in blocks do
    let all := v.all.toArray.map Ix.Name.fromLeanName
    let some all0 := all[0]? | continue
    let fail := fun (what : String) => s!"{label}: {v.name}: {what}"
    -- Lean / IxC Source
    let leanRead : Option IxcRead := do
      let gi ← groups.findIdx? fun
        | .inductive types _ _ => types.any (·.cnst.name == all0)
        | _ => false
      match groups[gi]? with
      | some (.inductive types ctors recs) =>
        let ctors' := ctors.map (·.map fun c => { c with isUnsafe := false })
        let recs' := recs.map fun r => { r with isUnsafe := false }
        match Ix.LeanIngress.convertInductive (types.map safe) ctors' recs' with
        | .ok (.inductive rb) => some (readConverted ctxFor rb)
        | _ => none
      | _ => none
    if leanRead.isNone then
      res := res.add (fail "Lean's block not converted")
      continue
    let some lr := leanRead | continue
    log s!"== {label}: {v.name} numNested={v.numNested}"
    match lr.mems with
    | .ok ms => log s!"lean.mems {memsStr ms}"
    | .error e => res := res.add (fail s!"IxC cannot read Lean's family: {e}")
    let leanMimics : List Sig := match lr.mems with
      | .ok ms => (ms.drop all.size).map Sig.ofMem
      | .error _ => []
    -- the SCCs among the block's members, in Lean's member order
    let mut sccs : Array (Ix.Name × Array Ix.Name) := #[]
    for n in all do
      if let some (lo, ms) := sccOf n then
        unless sccs.any (·.1 == lo) do
          let inds := ms.filter fun m => all.contains m
          let pos := fun (a : Ix.Name) => (all.findIdx? (· == a)).getD 0
          sccs := sccs.push (lo, inds.qsort (fun a b => pos a < pos b))
    for (lo, inds) in sccs do
      let s := compilerScc cenv lo inds all
      res := { res with rows := res.rows + 1 }
      let rowFail := fun (what : String) => fail s!"scc {s.lo}: {what}"
      if let some e := s.err then
        res := res.add (rowFail s!"compiler error: {(e.take 200).toString}")
        continue
      log s!"-- scc {s.lo}: classes {s.classes.map (·.map (·.pretty))} path {s.path}"
      -- 1. source order
      match s.srcSigs with
      | .error e => res := res.add (rowFail s!"source signatures: {e}")
      | .ok ss =>
        log s!"compiler.source {sigsStr ss}"
        unless ss == leanMimics do
          res := res.add (rowFail s!"source order: IxC on Lean's family \
{sigsStr leanMimics}; compiler {sigsStr ss}")
      -- the compiled family, read by IxC
      let readE : Except String IxcRead := do
        let recs ← s.canonRecs
        let types := s.canonTypes.map safe
        let ctors := s.canonCtors.map (·.map fun c => { c with isUnsafe := false })
        let recs := recs.map fun r => { r with isUnsafe := false }
        match Ix.LeanIngress.convertInductive types ctors recs with
        | .ok (.inductive rb) => pure (readConverted ctxFor rb)
        | .ok _ => throw "convert: not an inductive"
        | .error e => throw s!"convert: {rErr e}"
      if let .error e := readE then
        res := res.add (rowFail s!"the compiled family: {e}")
      let .ok cr := readE | continue
      let canonMimics : Option (List Sig) := match cr.mems with
        | .ok ms => some ((ms.drop s.canonTypes.size).map Sig.ofMem)
        | .error _ => none
      -- 2. canonical order
      match s.canonSigs, canonMimics with
      | .ok cs, some im =>
        log s!"compiler.canonical {sigsStr cs}"
        unless cs == im do
          res := res.add (rowFail s!"canonical order: IxC on the compiled family \
{sigsStr im}; compiler {sigsStr cs}")
      | .error e, _ => res := res.add (rowFail s!"canonical signatures: {e}")
      | _, none => res := res.add (rowFail "IxC cannot read the compiled family's members")
      -- 3. the permutation, matched up to the SCC's classes
      let o2c : Std.HashMap (Ix.Kernel.Key .source) (Ix.Kernel.Key .source) :=
        s.classes.foldl (init := {}) fun m cls =>
          match cls[0]? with
          | some rep => cls.foldl (init := m) fun m n =>
              m.insert (Ix.LeanIngress.ingressKey n) (Ix.LeanIngress.ingressKey rep)
          | none => m
      let ren := fun (k : Ix.Kernel.Key .source) => (o2c.get? k).getD k
      match s.perm, canonMimics with
      | .ok p, some im =>
        let implied : Array Nat := leanMimics.toArray.map fun sg =>
          let sg' : Sig := { sg with pins := sg.pins.map (renameK ren) }
          match im.findIdx? (· == sg') with
          | some i => i
          | none => match im.findIdx? (fun c => c.head == sg'.head && c.pins == sg'.pins) with
            | some i => i
            | none => Ix.AuxGen.PERM_OUT_OF_SCC
        let ident := p.zipIdx.all fun (c, j) => c == j
        log s!"perm compiler {permStr p}; IxC-implied {permStr implied}"
        unless implied == p do
          res := res.add (rowFail s!"permutation: computeAuxPerm {permStr p}; \
IxC's readings imply {permStr implied}")
        if ident then res := { res with identities := res.identities + 1 }
        let leanOrder := s.classes.all (·.size == 1) && s.classes.filterMap (·[0]?) == all
        if leanOrder && s.externalsInLeanOrder && !ident then
          res := res.add (rowFail s!"permutation {permStr p} is not the identity, but Lean's \
member order and every external group's are canonical")
      | .error e, _ => res := res.add (rowFail s!"permutation: {e}")
      | _, none => pure ()
      -- 4. field kinds
      let leanK : Option (List String) := lr.minors.toOption.map (·.map (·.render))
      let srcK := s.srcMinors.map rCompilerMinor
      unless leanK == some srcK do
        res := res.add (rowFail s!"field kinds on Lean's family: IxC {leanK.getD []}; \
compiler {srcK}")
      let canonK : Option (List String) := cr.minors.toOption.map (·.map (·.render))
      let ck := s.canonMinors.map rCompilerMinor
      unless canonK == some ck do
        res := res.add (rowFail s!"field kinds on the compiled family: IxC {canonK.getD []}; \
compiler {ck}")
      -- 5. verdicts
      log s!"verdicts: Lean's family {lr.render}; compiled family {cr.render}"
      unless lr.accepted == cr.accepted do
        res := res.add (rowFail s!"verdicts differ: Lean's family {lr.render}; \
compiled family {cr.render}")
  return res

/-! ## The suite -/

/-- The test environment's fixture modules with nested blocks (SP5's
fixture modules, without `Tests.Ix.Kernel.EntryCaseDefs`). -/
def fixtureModules : List Lean.Name :=
  [`Tests.Ix.Compile.Mutual, `Tests.Ix.Compile.Canonicity, `Tests.Ix.Fixtures, `Tests.Ix.IxVM,
   `Tests.Ix.Kernel.ReaderFidelityDefs, `Tests.Ix.Kernel.TutorialDefs]

/-- SP5's count of nested blocks in `fixtureModules` (2026-10-15: 64 with
`EntryCaseDefs`' 6): fewer means a fixture went missing. -/
def minFixtureBlocks : Nat := 58

/-- The constants of `mods` in `env`; an error names a missing module. -/
def moduleConstants (env : Lean.Environment) (mods : List Lean.Name) :
    Except String (Array Lean.Name) := do
  let mut cands : Array Lean.Name := #[]
  for m in mods do
    let some i := env.getModuleIdx? m | throw s!"module {m} is not in the environment"
    let some md := env.header.moduleData[i.toNat]? | throw s!"module {m} has no data"
    cands := cands ++ md.constNames
  return cands

def report (label : String) (r : EnvResult) : IO Unit :=
  IO.println s!"[nested-agreement] {label}: {r.nestedBlocks} nested blocks, {r.rows} SCC rows, \
{r.identities} identity permutations, {r.problems.size} problem(s)"

def run (env : Lean.Environment) : IO UInt32 := do
  let verbose := ((← IO.getEnv "IX_NESTED_AGREEMENT_VERBOSE").map (· != "0")).getD false
  let mut problems : Array String := #[]
  -- the test environment's fixture modules
  match moduleConstants env fixtureModules with
  | .error e => problems := problems.push s!"fixtures: {e}"
  | .ok cands =>
    let r ← check "fixtures" env cands verbose
    report "fixtures" r
    problems := problems ++ r.problems
    if r.nestedBlocks < minFixtureBlocks then
      problems := problems.push
        s!"fixtures: {r.nestedBlocks} nested blocks, expected at least {minFixtureBlocks}"
  -- `NestedLevels`, from its `.olean` (the `TwinsFixtures` library)
  let nlEnv ← getCompileEnv #[`Tests.Ix.Compile.Fixtures.NestedLevels]
  match moduleConstants nlEnv [`Tests.Ix.Compile.Fixtures.NestedLevels] with
  | .error e => problems := problems.push s!"NestedLevels: {e}"
  | .ok cands =>
    let r ← check "NestedLevels" nlEnv cands verbose
    report "NestedLevels" r
    problems := problems ++ r.problems
    if r.nestedBlocks != 4 then
      problems := problems.push s!"NestedLevels: {r.nestedBlocks} nested blocks, expected 4"
  -- `CanonSiblingNest`, elaborated at run time
  let csEnv := (← getFileEnvCore "Tests/Ix/Compile/Fixtures/CanonSiblingNest.lean").env
  let csCands := csEnv.constants.map₂.toList.toArray.map (·.1)
  let r ← check "CanonSiblingNest" csEnv csCands verbose
  report "CanonSiblingNest" r
  problems := problems ++ r.problems
  if r.nestedBlocks != 3 then
    problems := problems.push s!"CanonSiblingNest: {r.nestedBlocks} nested blocks, expected 3"
  for p in problems do IO.println s!"[nested-agreement] FAIL {p}"
  if problems.isEmpty then
    IO.println "[nested-agreement] every reading agrees"
    return 0
  return 1

end Tests.Ix.Compile.NestedAgreement
