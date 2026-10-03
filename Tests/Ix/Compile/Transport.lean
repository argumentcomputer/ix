/-
  clique-transport: the transport `Φ_σ` (`Ix.Compile.Clique`, design document
  §5) against the measured clique twins (`Tests/Ix/Compile/Twins/Cliques.lean`).

  For every clique family and every presentation `Pk` against the reference
  `P0`, with `σ` the permutation from `P0`'s Lean clique order to `Pk`'s:

  * **(a) the exact oracle.** `P0`'s encoding (the packed function and its
    proofs, the functionals, the fixpoint, the members) is transported onto
    `Pk`'s order and compared, constant by constant, with `Pk`'s own constants
    as `Ix.Expr`, the names of `Pk` mapped into `P0`'s namespace by the twins
    gate's name map, up to binder names and `mdata` (what Ixon addresses
    ignore). The count is reported against the non-canonical set's
    packing-order-only entries (cause `pendingTransport`, 93 at the head of
    wave 1): each such constant must be reproduced exactly, or the exception
    explained (logged, with both terms, in `out/clique-transport/`).
  * **(b) type-checking.** Every transported constant is added with
    `addDecl` (Lean's kernel, `Elab.async false`) to a scratch copy of the
    environment, under a fresh namespace: every one must be accepted.
  * **(c) GuessLex (`WG`).** Transport reproduces everything except the
    measures: equal once the measure arguments (`invImage`'s function,
    `WellFounded.Nat.fix`'s measure) are masked; recorded as `GUESSLEX`.
  * **(d) negative controls.** A wrong permutation fails the oracle; a proof
    with a term outside the grammar takes the fallback (kept verbatim,
    `SHAPE`) and still type-checks against the transported statement.
  * **(e) theorem cliques (Q6).** Each presentation is transported onto the
    order of its statements, or, when statements tie, of its recovered
    specifications (`Ix.Compile.Clique.recoveredOrder`); both must give the
    same constants. Where the statements decide, the recovered order must
    agree with them. The inductive-predicate route is not recovered: its
    recovery must fail (`NOSPEC`, the baseline).
  * **(f) residual causes.** Every `RECARG`, `TACTIC-ASYM` and `SHAPE` entry
    of the non-canonical set is a constant the transport does not reproduce;
    a `SHAPE` entry must have taken a fallback.
  * **(g) the position restriction.** `WU`'s user values of exactly the
    clique's packing type are not transported (the family is exact).

  The test may use `MetaM`/`CoreM` (it reads Lean's `EqnInfo`, converts terms
  and calls the kernel); the transport itself may not and does not.

  Invoked as `lake test -- --ignored clique-transport`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Canon
import Ix.Compile.Clique
import Ix.Compile.Clique.Transport
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.NonCanonical
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Lean Meta

namespace Tests.Ix.Compile.Transport

open Tests.Ix.Compile.Twins (Family Pres cliqueFamilies mapInto)
open Tests.Ix.Compile.NonCanonical
open _root_.Ix.Compile.Clique (Decl Encoding Input Output)

abbrev IxName := _root_.Ix.Name
abbrev IxExpr := _root_.Ix.Expr

def ixName (n : Name) : IxName := _root_.Ix.Name.fromLeanName n

def toLeanName : IxName → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (toLeanName p) s
  | .num p n _ => .num (toLeanName p) n

def toIxConst (c : ConstantInfo) : _root_.Ix.ConstantInfo := (_root_.Ix.CanonM.canonConst c).run' {}
def toLeanExpr (e : IxExpr) : Expr := (_root_.Ix.CanonM.uncanonExpr e).run' {}

def declOf (env : Environment) (n : Name) : Option Decl :=
  (env.find? n).bind fun ci => Decl.ofConstantInfo? (toIxConst ci)

/-! ## Lean's clique order -/

def mapExtEntries {α : Type} [Inhabited α] (ext : MapDeclarationExtension α)
    (env : Environment) : Array (Name × α) := Id.run do
  let mut out : Array (Name × α) := #[]
  for i in [0:env.allImportedModuleNames.size] do
    for level in [OLeanLevel.exported, .private] do
      for (n, a) in ext.toPersistentEnvExtension.getModuleEntries env i (level := level) do
        out := out.push (n, a)
  return out

/-- Every clique Lean recorded an `EqnInfo` for, by member. -/
def eqnCliques (env : Environment) : Std.HashMap Name (Encoding × Array Name) := Id.run do
  let mut m : Std.HashMap Name (Encoding × Array Name) := {}
  for (n, i) in mapExtEntries Lean.Elab.WF.eqnInfoExt env do
    m := m.insert n (.wellFounded, i.declNames)
  for (n, i) in mapExtEntries Lean.Elab.Structural.eqnInfoExt env do
    m := m.insert n (.structural, i.declNames)
  for (n, i) in mapExtEntries Lean.Elab.PartialFixpoint.eqnInfoExt env do
    m := m.insert n (.partialFixpoint, i.declNames)
  return m

def presConsts (env : Environment) (p : Pres) : Array (Name × ConstantInfo) :=
  env.constants.fold (init := #[]) fun acc n ci =>
    if p.ns.isPrefixOf n && n != p.ns then acc.push (n, ci) else acc

/-- A presentation's clique: encoding and members in Lean's clique order
(`EqnInfo.declNames`; for a theorem clique, which has none, `all`). -/
def presClique (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) (p : Pres) :
    Option (Encoding × Array Name) := Id.run do
  let cs := presConsts env p
  for (n, _) in cs do
    if let some r := eqn.get? n then return some r
  for (_, ci) in cs do
    if let .thmInfo v := ci then
      if v.all.length ≥ 2 && v.all.all (p.ns.isPrefixOf ·) then
        let all := v.all.toArray
        let enc : Encoding :=
          if env.contains (all[0]! ++ `_mutual) then .wellFounded else .structural
        return some (enc, all)
  return none

/-! ## Comparison -/


/-- Mask the measures: `invImage`'s function and `WellFounded.Nat.fix`'s
measure become a placeholder (GuessLex's choice lives there). -/
partial def maskMeasures (e : IxExpr) : IxExpr :=
  match e with
  | .app .. =>
    let (h, args) := _root_.Ix.Compile.Canon.getAppFnArgs e
    let args := args.map maskMeasures
    let placeholder := _root_.Ix.Expr.mkConst (ixName `_measure) #[]
    let args := match h with
      | .const c _ _ =>
        if (c == ixName ``invImage || c == ixName ``WellFounded.Nat.fix) && args.size ≥ 3 then
          args.set! 2 placeholder
        else if c == ixName ``InvImage && args.size ≥ 4 then args.set! 3 placeholder
        else args
      | _ => args
    _root_.Ix.Compile.Canon.mkAppN (maskMeasures h) args
  | .lam n t b bi _ => _root_.Ix.Expr.mkLam n (maskMeasures t) (maskMeasures b) bi
  | .forallE n t b bi _ => _root_.Ix.Expr.mkForallE n (maskMeasures t) (maskMeasures b) bi
  | .letE n t v b nd _ =>
    _root_.Ix.Expr.mkLetE n (maskMeasures t) (maskMeasures v) (maskMeasures b) nd
  | .proj s i x _ => _root_.Ix.Expr.mkProj s i (maskMeasures x)
  | .mdata d x _ => _root_.Ix.Expr.mkMData d (maskMeasures x)
  | e => e

/-- The first differing position of `a` and `b` (names of `b` mapped), for
the logs. -/
partial def firstDiff (mapB : IxName → IxName) (path : String) (a b : IxExpr) :
    Option (String × IxExpr × IxExpr) :=
  let a := _root_.Ix.Compile.Canon.stripMdata a
  let b := _root_.Ix.Compile.Canon.stripMdata b
  if _root_.Ix.Compile.Clique.eqUpTo mapB a b then none else
  match a, b with
  | .app .., .app .. =>
    let (fa, xs) := _root_.Ix.Compile.Canon.getAppFnArgs a
    let (fb, ys) := _root_.Ix.Compile.Canon.getAppFnArgs b
    if xs.size != ys.size then some (path, a, b) else
    match firstDiff mapB (path ++ ".fn") fa fb with
    | some r => some r
    | none => (List.range xs.size).findSome? fun i => firstDiff mapB (path ++ s!".@{i}") xs[i]! ys[i]!
  | .lam _ t e _ _, .lam _ t' e' _ _ | .forallE _ t e _ _, .forallE _ t' e' _ _ =>
    match firstDiff mapB (path ++ ".dom") t t' with
    | some r => some r
    | none => firstDiff mapB (path ++ ".body") e e'
  | .letE _ t v e _ _, .letE _ t' v' e' _ _ =>
    match firstDiff mapB (path ++ ".ty") t t' with
    | some r => some r
    | none => match firstDiff mapB (path ++ ".val") v v' with
      | some r => some r
      | none => firstDiff mapB (path ++ ".body") e e'
  | .proj s i x _, .proj s' i' y _ =>
    if s == mapB s' && i == i' then firstDiff mapB (path ++ s!".proj{i}") x y else some (path, a, b)
  | _, _ => some (path, a, b)

/-! ## The kernel -/

def kernelAdd (decl : Declaration) : CoreM (Option String) := do
  try
    withOptions (fun o => o.setBool `Elab.async false) do addDecl decl
    return none
  catch e =>
    return some (← e.toMessageData.toString)

/-- Add the transported constants under `scratch` (references among them
renamed), in dependency order; the verdict of each. -/
def checkDecls (scratch p0ns : Name) (decls : Array Decl) : CoreM (Array (Name × Option String)) := do
  let names : NameSet := decls.foldl (init := {}) fun s d => s.insert (toLeanName d.name)
  let rn (n : Name) : Name := if names.contains n then scratch ++ n.replacePrefix p0ns .anonymous else n
  let ren (e : Expr) : Expr := e.replace fun x => match x with
    | .const n us => some (.const (rn n) us)
    | _ => none
  let mut pending := decls.toList
  let mut added : NameSet := {}
  let mut out : Array (Name × Option String) := #[]
  let mut progress := true
  while progress && !pending.isEmpty do
    progress := false
    let mut rest := []
    for d in pending do
      let ty := toLeanExpr d.type
      let v := toLeanExpr d.value
      let deps := (ty.getUsedConstants ++ v.getUsedConstants).filter names.contains
      if deps.all fun x => added.contains x || x == toLeanName d.name then
        let n := rn (toLeanName d.name)
        let lps := d.levelParams.toList.map toLeanName
        let tv : TheoremVal := { name := n, levelParams := lps, type := ren ty, value := ren v }
        let dv : DefinitionVal := { name := n, levelParams := lps, type := ren ty, value := ren v, hints := .opaque, safety := .safe }
        let decl := if d.isThm then Declaration.thmDecl tv else Declaration.defnDecl dv
        let r ← kernelAdd decl
        out := out.push (toLeanName d.name, r)
        added := added.insert (toLeanName d.name)
        progress := true
      else rest := rest ++ [d]
    pending := rest
  for d in pending do out := out.push (toLeanName d.name, some "dependency cycle")
  return out

/-! ## One pair -/

structure Row where
  fam : String
  pair : String
  /-- the source constant (`P0`'s name, relative) -/
  src : Name
  /-- the transported constant's name (relative to `P0`) -/
  dst : Name
  /-- `EXACT`, `DIFF`, `GUESSLEX`, `MISSING`, `FALLBACK` -/
  verdict : String
  kernel : String := "-"
  note : String := ""

structure PairOut where
  rows : Array Row
  out : Output
  failures : Array String := #[]

def relName (ns n : Name) : Name := n.replacePrefix ns .anonymous

/-- The encoding constants of a presentation's clique (besides the members). -/
def auxNames (env : Environment) (p : Pres) (enc : Encoding) (members : Array Name) : Array Name :=
  match enc with
  | .wellFounded =>
    let packed := members[0]! ++ `_mutual
    let proofs := (presConsts env p).filterMap fun (n, _) => match n with
      | .str q s => if q == packed && s.startsWith "_proof_" then some n else none
      | _ => none
    #[packed] ++ proofs.qsort Name.quickLt
  | .structural =>
    -- the functionals, and the "below" matchers the members apply (IndPred route)
    let fs := members.filterMap fun m => if env.contains (m ++ `_f) then some (m ++ `_f) else none
    let used := members.foldl (init := ({} : NameSet)) fun s m => match env.find? m with
      | some (.defnInfo v) => v.value.getUsedConstants.foldl (·.insert ·) s
      | some (.thmInfo v) => v.value.getUsedConstants.foldl (·.insert ·) s
      | some _ => s
      | none => s
    let ms := (presConsts env p).filterMap fun (n, _) => match n with
      | .str _ s => if s.startsWith "match_" && used.contains n then some n else none
      | _ => none
    fs ++ ms.qsort Name.quickLt
  | .partialFixpoint =>
    let packed := members[0]! ++ `mutual
    let proofs := (presConsts env p).filterMap fun (n, _) => match n with
      | .str q s => if q == packed && s.startsWith "_proof_" then some n else none
      | _ => none
    #[packed] ++ proofs.qsort Name.quickLt

/-- The transport's input for `P0` against `Pk`'s order (or an explicit
permutation, for the negative control). -/
def pairInput (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (p0 pk : Pres) (σ? : Option (Array Nat) := none) :
    Except String (Input × Array Name × Array Name) := do
  let some (enc, ms0) := presClique env eqn p0 | throw s!"{p0.ns}: no clique"
  let some (_, msk) := presClique env eqn pk | throw s!"{pk.ns}: no clique"
  let mskMapped := msk.map (mapInto p0 pk)
  let σ ← match σ? with
    | some s => pure s
    | none => ms0.mapM fun m => match mskMapped.idxOf? m with
      | some j => pure j
      | none => throw s!"{m}: no counterpart in {pk.id}"
  let members ← ms0.mapM fun m => match declOf env m with
    | some d => pure d
    | none => throw s!"{m}: not a definition"
  let auxs := auxNames env p0 enc ms0
  let aux ← auxs.mapM fun m => match declOf env m with
    | some d => pure d
    | none => throw s!"{m}: not a definition"
  let newEncName := ixName (match enc with
    | .wellFounded => ms0[0]! ++ `_mutual
    | .partialFixpoint => ms0[0]! ++ `mutual
    | .structural => ms0[0]!)
  return ({ encoding := enc, members, aux, sigma := σ, newEncName
            const? := fun n => (env.find? (toLeanName n)).map toIxConst }, ms0, auxs)

/-- Compare the transport's output with `Pk`'s constants. -/
def compare (env : Environment) (fam : String) (p0 pk : Pres) (out : Output)
    (sources : Array Name) (guessLex : Bool) : IO (Array Row) := do
  let mapB (n : IxName) : IxName := ixName (mapInto p0 pk (toLeanName n))
  let pkMap : Std.HashMap Name Decl := (presConsts env pk).foldl (init := {}) fun m (n, _) =>
    match declOf env n with
    | some d => m.insert (mapInto p0 pk n) d
    | none => m
  let srcOf (dst : Name) : Name :=
    match out.renames.find? (fun (_, b) => toLeanName b == dst) with
    | some (a, _) => toLeanName a
    | none => dst
  let pair := s!"{p0.id}/{pk.id}"
  let mut rows := #[]
  for d in out.decls do
    let dst := toLeanName d.name
    let src := srcOf dst
    unless sources.contains src do continue
    let fb := out.causes.find? (fun (n, _, _) => n == d.name)
    let row : Row := { fam, pair, src := relName p0.ns src, dst := relName p0.ns dst, verdict := "" }
    match pkMap.get? dst with
    | none => rows := rows.push { row with verdict := "MISSING", note := "no counterpart in Pk" }
    | some dk =>
      let exact := d.levelParams.size == dk.levelParams.size &&
        _root_.Ix.Compile.Clique.eqUpTo mapB d.type dk.type &&
        _root_.Ix.Compile.Clique.eqUpTo mapB d.value dk.value
      -- up to the measures: a decreasing proof proves its measure's inequality, so only its
      -- statement is compared (its body is measure-dependent by construction)
      let isProof := match dst with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      let masked := _root_.Ix.Compile.Clique.eqUpTo mapB (maskMeasures d.type) (maskMeasures dk.type) &&
        (isProof || _root_.Ix.Compile.Clique.eqUpTo mapB (maskMeasures d.value) (maskMeasures dk.value))
      let verdict :=
        if exact then (if fb.isSome then "FALLBACK-EXACT" else "EXACT")
        else if guessLex && masked then "GUESSLEX"
        else if fb.isSome then "FALLBACK" else "DIFF"
      let note := match fb with
        | some (_, c, why) => s!"{c.tag}: {why}"
        | none => ""
      let mut note := note
      if !exact then
        let fd := (firstDiff mapB "type" d.type dk.type).orElse fun _ =>
          firstDiff mapB "value" d.value dk.value
        if let some (p, x, y) := fd then
          note := note ++ s!" first difference at {p}"
          let dir : System.FilePath := "out/clique-transport"
          IO.FS.createDirAll dir
          let file := dir / s!"{fam}.{p0.id}-{pk.id}.{relName p0.ns dst}.txt"
          let s := s!"# {fam} {pair} {src} -> {dst}: {verdict}\n# first difference at {p}\n\
            -- transported:\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr x) true}\n\
            -- {pk.id}:\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr y) true}\n\n\
            ## transported type\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr d.type)}\n\
            ## transported value\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr d.value)}\n\
            ## {pk.id} type\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr dk.type)}\n\
            ## {pk.id} value\n{← Tests.Ix.Compile.Twins.ppExprIO env (toLeanExpr dk.value)}\n"
          IO.FS.writeFile file s
      rows := rows.push { row with verdict, note }
  return rows

/-- Type-check the output in a scratch environment. -/
def kernelCheck (env : Environment) (fam : String) (p0 pk : Pres) (decls : Array Decl) :
    IO (Array (Name × Option String)) := do
  let scratch := `Tests.Ix.Compile.Transport.Checked ++ fam.toName ++ pk.id.toName
  let ctx : Core.Context := { fileName := "<clique-transport>", fileMap := default,
                              maxHeartbeats := 0 }
  let (r, _) ← (checkDecls scratch p0.ns decls).toIO ctx { env }
  return r

/-! ## Theorem cliques (Q6) -/

/-- A presentation whose clique is a theorem clique (no `EqnInfo`). -/
def isTheoremClique (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (p : Pres) : Bool :=
  match presClique env eqn p with
  | some (_, ms) => ms.all fun m => !eqn.contains m && (match env.find? m with
      | some (.thmInfo _) => true
      | _ => false)
  | none => false

/-- The canonical order of a theorem clique from its statements (Q6, first
source; `Ix.Compile.Canon.statementOrder`). -/
def stmtOrder (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) (p : Pres) :
    Except String (Option (Array Nat)) := do
  let some (_, ms) := presClique env eqn p | throw s!"{p.ns}: no clique"
  let members ← ms.mapM fun m => match declOf env m with
    | some d => pure ({ name := d.name, levelParams := d.levelParams, type := d.type,
                        value := d.value } : _root_.Ix.Compile.Canon.CliqueMember)
    | none => throw s!"{m}: not a theorem"
  _root_.Ix.Compile.Canon.statementOrder _root_.Ix.Compile.Canon.Rules.phaseA
    (fun n => some (Address.blake3 n.pretty.toUTF8)) members

/-- A content address for the comparator: a presentation's own constant by
its type and value with the presentation's namespace erased (so the same
matcher in two presentations has one address), any other constant by its
name (shared by every presentation). -/
def contentAddr (env : Environment) (p : Pres) (n : IxName) : Option Address :=
  let ln := toLeanName n
  if p.ns.isPrefixOf ln then
    match env.find? ln with
    | some ci =>
      let rel (e : Expr) : Expr := e.replace fun x => match x with
        | .const m us => if p.ns.isPrefixOf m then some (.const (m.replacePrefix p.ns `_pres) us) else none
        | _ => none
      let v := match ci.value? (allowOpaque := true) with
        | some v => toString (rel v)
        | none => ""
      some (Address.blake3 s!"{toString (rel ci.type)}|{v}".toUTF8)
    | none => none
  else some (Address.blake3 ln.toString.toUTF8)

/-- Q6's second source: the order of a theorem clique by its statements and
recovered specifications (`Ix.Compile.Clique.recoveredOrder`). -/
def recOrder (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) (p : Pres) :
    Except String (Array Nat × Array (Array IxName)) := do
  let some (_, ms) := presClique env eqn p | throw s!"{p.ns}: no clique"
  let (inp, _, _) ← pairInput env eqn p p (σ? := (List.range ms.size).toArray)
  _root_.Ix.Compile.Clique.recoveredOrder _root_.Ix.Compile.Canon.Rules.phaseA (contentAddr env p) inp

/-- Transport both presentations onto their canonical orders and compare. -/
def compareCanonical (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (p0 pk : Pres) (σ0 σk : Array Nat) : IO (Except String (Nat × Nat)) := do
  let .ok (inp0, _, _) := pairInput env eqn p0 p0 (σ? := σ0) | return .error "input"
  let .ok (inpk, _, _) := pairInput env eqn pk pk (σ? := σk) | return .error "input"
  let out0 := _root_.Ix.Compile.Clique.transport inp0
  let outk := _root_.Ix.Compile.Clique.transport inpk
  let mapB (n : IxName) : IxName := ixName (mapInto p0 pk (toLeanName n))
  let kMap : Std.HashMap Name Decl := outk.decls.foldl (init := {}) fun m d =>
    m.insert (mapInto p0 pk (toLeanName d.name)) d
  let mut same := 0
  let mut diff : Array Name := #[]
  for d in out0.decls do
    match kMap.get? (toLeanName d.name) with
    | some dk =>
      if _root_.Ix.Compile.Clique.eqUpTo mapB d.type dk.type &&
          _root_.Ix.Compile.Clique.eqUpTo mapB d.value dk.value then same := same + 1
      else diff := diff.push (relName p0.ns (toLeanName d.name))
    | none => diff := diff.push (relName p0.ns (toLeanName d.name))
  return if diff.isEmpty then .ok (same, out0.decls.size) else .error s!"DIFFERENT {diff}"

/-- (e) Both presentations of a theorem clique, each transported onto the
order of the statements (Q6's first source) or, when statements tie, of the
recovered specifications (the second source), must give the same constants;
a failed recovery is `NOSPEC`. -/
def theoremCanonicity (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (_fam : String) (p0 pk : Pres) : IO String := do
  match stmtOrder env eqn p0, stmtOrder env eqn pk with
  | .error e, _ | _, .error e => return s!"ERROR {e}"
  | .ok none, .ok none =>
    match recOrder env eqn p0, recOrder env eqn pk with
    | .error e, _ | _, .error e => return s!"NOSPEC ({e})"
    | .ok (σ0, cls0), .ok (σk, _) =>
      let tied := cls0.filter (·.size ≥ 2)
      let how := if tied.isEmpty then "recovered specifications distinct"
        else s!"recovered specifications tie in {tied.size} class(es), Pass 1's seed order"
      match ← compareCanonical env eqn p0 pk σ0 σk with
      | .ok (same, total) =>
        return s!"CANONICAL by the recovered specification ({how}; {same}/{total} identical; σ {p0.id} {σ0}, σ {pk.id} {σk})"
      | .error e => return e
  | .ok (some σ0), .ok (some σk) =>
    match ← compareCanonical env eqn p0 pk σ0 σk with
    | .ok (same, total) =>
      -- the recovered specification must agree with the statements where they decide
      let agree := match recOrder env eqn p0 with
        | .ok (σr, _) => if σr == σ0 then "recovered order agrees" else s!"RECOVERED ORDER DIFFERS {σr}"
        | .error e => s!"recovery: {e}"
      return s!"CANONICAL ({same}/{total} identical; σ {p0.id} {σ0}, σ {pk.id} {σk}; {agree})"
    | .error e => return e
  | _, _ => return "NOSPEC in one presentation only"

/-! ## Negative controls -/

def familyNamed (fam : String) : Option Family :=
  cliqueFamilies.find? (·.fixture.getString! == fam)

/-- (d1) A wrong permutation must fail the oracle. -/
def wrongPermutation (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (fam : String) : IO (Option String) := do
  let some f := familyNamed fam | return some s!"{fam}: no family"
  let some p0 := f.pres.head? | return some s!"{fam}: no presentation"
  let some pk := f.pres[1]? | return some s!"{fam}: one presentation"
  let .ok (inp, ms0, auxs) := pairInput env eqn p0 pk | return some s!"{fam}: no input"
  -- swap the images of the first two members
  let σ := inp.sigma
  let σ' := (σ.set! 0 σ[1]!).set! 1 σ[0]!
  let out := _root_.Ix.Compile.Clique.transport { inp with sigma := σ' }
  let rs ← compare env (fam ++ "-wrongσ") p0 pk out (ms0 ++ auxs) false
  let exact := (rs.filter (·.verdict == "EXACT")).size
  IO.println s!"[clique-transport] (d) wrong permutation {fam} {p0.id}/{pk.id}: σ' = {σ'}, \
    {exact}/{rs.size} exact{if out.baseline then " (BASELINE)" else ""}"
  return if exact < rs.size then none else some s!"{fam}: a wrong permutation reproduced {pk.id}"

/-- Wrap `v` as `(λ (_ : A → B). v) g`: a well-typed term with the same type
as `v` that carries `g`. -/
def carrying (v : IxExpr) (arrowDom arrowCod g : IxExpr) : IxExpr :=
  let ty := _root_.Ix.Expr.mkForallE (ixName `_a) arrowDom (_root_.Ix.Compile.Canon.liftLoose arrowCod 1) .default
  _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkLam (ixName `_g) ty (_root_.Ix.Compile.Canon.liftLoose v 1) .default) g

/-- (d2) A decreasing proof with a term outside the grammar (a partial
injection into the packing) keeps Lean's body under the transported
statement, records `SHAPE`, and is accepted by the kernel. -/
def strayProof (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) :
    IO (Option String) := do
  let some f := familyNamed "WD" | return some "WD: no family"
  let some p0 := f.pres.head? | return some "WD: no presentation"
  let some pk := f.pres[1]? | return some "WD: one presentation"
  let .ok (inp, _, _) := pairInput env eqn p0 pk | return some "WD: no input"
  let some packed := _root_.Ix.Compile.Clique.findPacked? inp.members inp.aux | return some "WD: no packed function"
  let some proof := inp.aux.find? (·.name != packed.name) | return some "WD: no proof"
  -- `@PSum.inl.{u,v} A B : A → α`, partially applied
  let ar := _root_.Ix.Compile.Image.forallArity packed.type
  let (bs, _) := _root_.Ix.Compile.Canon.peelForalls ar packed.type #[]
  let some (_, α, _) := bs[ar - 1]? | return some "WD: no packed domain"
  let some (_, us, #[a, b]) := _root_.Ix.Compile.Clique.constApp? α | return some "WD: packed domain"
  let inl := _root_.Ix.Compile.Canon.mkAppN (_root_.Ix.Expr.mkConst _root_.Ix.Compile.Clique.nPSumInl us) #[a, b]
  -- the proof's body, under its binders
  let n := _root_.Ix.Compile.Clique.lamArity proof.value
  let (ps, body) := _root_.Ix.Compile.Clique.peelLams n proof.value #[]
  let body' := carrying body a α inl
  let proof' := { proof with value := _root_.Ix.Compile.Clique.mkLams ps body' }
  let aux := inp.aux.map fun d => if d.name == proof.name then proof' else d
  let out := _root_.Ix.Compile.Clique.transport { inp with aux }
  let causes := out.causes.filter fun (_, c, _) => c == .shape
  let kept := out.decls.find? fun d => causes.any (·.1 == d.name)
  let verbatim := match kept with
    | some d => _root_.Ix.Compile.Clique.alphaEq d.value proof'.value
    | none => false
  let ks ← kernelCheck env "WD-stray" p0 pk out.decls
  let accepted := ks.all (·.2.isNone)
  IO.println s!"[clique-transport] (d) stray term in {proof.name.pretty}: causes {causes.map fun (n, c, w) => s!"{n.pretty} {c.tag} ({w})"}, \
    body kept verbatim: {verbatim}, kernel {(ks.filter (·.2.isNone)).size}/{ks.size}"
  for (n, r) in ks do
    if let some m := r then IO.println s!"[clique-transport]   KERNEL-REJECT {n}: {(m.take 300).toString}"
  return if causes.size == 1 && verbatim && accepted && !out.baseline then none
    else some "WD: the stray proof did not take the verbatim fallback"

/-- (d3) A `partial_fixpoint` monotonicity proof outside the grammar takes
the composition fallback `monotone_compose (mono φ) h`, records `SHAPE`, and
is accepted by the kernel. -/
def strayMonotonicity (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) :
    IO (Option String) := do
  let some f := familyNamed "PF" | return some "PF: no family"
  let some p0 := f.pres.head? | return some "PF: no presentation"
  let some pk := f.pres[1]? | return some "PF: one presentation"
  let .ok (inp, _, _) := pairInput env eqn p0 pk | return some "PF: no input"
  let some packed := _root_.Ix.Compile.Clique.findPacked? inp.members inp.aux | return some "PF: no packed fixpoint"
  let some proof := inp.aux.find? (·.name != packed.name) | return some "PF: no proof"
  let L : _root_.Ix.Compile.Clique.PFLayout ← IO.ofExcept
    (_root_.Ix.Compile.Clique.pfLayout inp.members packed inp.sigma inp.newEncName)
  let some (d, fs, hs) := _root_.Ix.Compile.Clique.decodeMonoTree L proof.value
    | return some "PF: the proof is not a monotone_mk tree"
  -- `λ x. x.2` is not a path into a three-component packing: outside the grammar
  let γ := d.spine.type
  let suf := d.spine.suffixes
  let some (s1, _) := suf[1]? | return some "PF: no suffix"
  let snd := _root_.Ix.Expr.mkLam (ixName `x) γ
    (_root_.Ix.Expr.mkProj _root_.Ix.Compile.Clique.nPProd 1 (_root_.Ix.Expr.mkBVar 0)) .default
  let h0 := carrying hs[0]! γ s1 snd
  let value := _root_.Ix.Compile.Clique.mkMonoTree d fs (hs.set! 0 h0)
  let proof' := { proof with value }
  let aux := inp.aux.map fun x => if x.name == proof.name then proof' else x
  let out := _root_.Ix.Compile.Clique.transport { inp with aux }
  let causes := out.causes.filter fun (_, c, _) => c == .shape
  let ks ← kernelCheck env "PF-stray" p0 pk out.decls
  let accepted := ks.all (·.2.isNone)
  IO.println s!"[clique-transport] (d) stray term in a monotonicity proof: causes {causes.map fun (n, c, w) => s!"{n.pretty} {c.tag} ({w})"}, \
    kernel {(ks.filter (·.2.isNone)).size}/{ks.size}{if out.baseline then " (BASELINE)" else ""}"
  for (n, r) in ks do
    if let some m := r then IO.println s!"[clique-transport]   KERNEL-REJECT {n}: {(m.take 300).toString}"
  return if causes.size == 1 && accepted && !out.baseline then none
    else some "PF: the stray monotonicity proof did not take the composition fallback"

/-! ## The suite -/

def isPendingTransport (e : NonCanonicalEntry) : Bool :=
  match e.cause with
  | .pendingTransport => true
  | _ => false

def isGuessLex (e : NonCanonicalEntry) : Bool :=
  match e.cause with
  | .guessLex => true
  | _ => false

/-- The families added by A5f (`plans/wave1/a5f.md`). -/
def a5fFamilies : List String := ["RF", "NS", "LI", "LC", "PU", "RA", "WH", "TR", "TQ", "WU"]

/-- Families the transport covers so far. -/
def supported (_ : Encoding) : Bool := true

def run : IO UInt32 := do
  let env ← get_env!
  let eqn := eqnCliques env
  let mut failures : Array String := #[]
  let mut rows : Array Row := #[]
  let mut kernelRows : Array (String × Name × Option String) := #[]
  let entries := Tests.Ix.Compile.NonCanonical.nonCanonical
  for fam in cliqueFamilies do
    let famName := fam.fixture.getString!
    let some p0 := fam.pres.head? | continue
    for pk in fam.pres.tail do
      let es := entries.filter fun e => e.fixture == fam.fixture && e.presA == p0.id && e.presB == pk.id
      match pairInput env eqn p0 pk with
      | .error err =>
        if es.any isPendingTransport then failures := failures.push s!"{famName} {pk.id}: {err}"
        IO.println s!"[clique-transport] {famName} {p0.id}/{pk.id}: skipped ({err})"
      | .ok (inp, ms0, auxs) =>
        if !supported inp.encoding then
          IO.println s!"[clique-transport] {famName} {p0.id}/{pk.id}: {reprStr inp.encoding} not covered yet"
          continue
        let out := _root_.Ix.Compile.Clique.transport inp
        if (← IO.getEnv "IX_TRANSPORT_LOG") == some famName then
          for l in out.log do IO.println s!"[clique-transport]   log: {l}"
        let guess := es.any isGuessLex
        let rs ← compare env famName p0 pk out (ms0 ++ auxs) guess
        rows := rows ++ rs
        let ks ← kernelCheck env famName p0 pk out.decls
        kernelRows := kernelRows ++ ks.map fun (n, r) => (s!"{famName} {p0.id}/{pk.id}", n, r)
        let nExact := (rs.filter (·.verdict == "EXACT")).size
        IO.println s!"[clique-transport] {famName} {p0.id}/{pk.id}: σ = {inp.sigma}, \
          {nExact}/{rs.size} exact, kernel {(ks.filter (·.2.isNone)).size}/{ks.size}\
          {if out.baseline then " (BASELINE)" else ""}"
        for r in rs do
          if r.verdict != "EXACT" then
            IO.println s!"[clique-transport]   {r.verdict} {r.src} → {r.dst} {r.note}"
        for (n, r) in ks do
          if let some msg := r then
            IO.println s!"[clique-transport]   KERNEL-REJECT {n}: {(msg.take 300).toString}"
  -- (a) the exact oracle over the packing-order-only set
  let pend := entries.filter isPendingTransport
  let mut exact := 0
  for e in pend do
    let famName := e.fixture.getString!
    let hit := rows.find? fun r => r.fam == famName && r.pair == s!"{e.presA}/{e.presB}" &&
      r.src == e.constant
    match hit with
    | some r =>
      if r.verdict == "EXACT" then exact := exact + 1
      else failures := failures.push s!"oracle: {famName} {e.presA}/{e.presB} {e.constant}: {r.verdict} {r.note}"
    | none => failures := failures.push s!"oracle: {famName} {e.presA}/{e.presB} {e.constant}: not transported"
  let isExact (e : NonCanonicalEntry) : Bool := rows.any fun r =>
    r.fam == e.fixture.getString! && r.pair == s!"{e.presA}/{e.presB}" && r.src == e.constant && r.verdict == "EXACT"
  let a5t (e : NonCanonicalEntry) : Bool := e.fixture.getString! == "WA"
  let a5f (e : NonCanonicalEntry) : Bool := a5fFamilies.contains e.fixture.getString!
  let wave1 (e : NonCanonicalEntry) : Bool := !a5t e && !a5f e
  let count (p : NonCanonicalEntry → Bool) : String :=
    s!"{(pend.filter fun e => p e && isExact e).length}/{(pend.filter p).length}"
  IO.println s!"[clique-transport] (a) exact oracle: {exact}/{pend.length} packing-order-only constants reproduced exactly \
    (the wave-1 measured set: {count wave1}; the A5t probe WA: {count a5t}; the A5f families: {count a5f})"
  for fam in a5fFamilies do
    let p (e : NonCanonicalEntry) : Bool := e.fixture.getString! == fam
    if (pend.filter p).length > 0 then
      IO.println s!"[clique-transport]   (a) {fam}: {count p} exact"
  -- (f) the residual causes: transport cannot remove them, and says how
  for e in entries do
    let fam := e.fixture.getString!
    unless cliqueFamilies.any (·.fixture == e.fixture) do continue
    let expected : Option String := match e.cause with
      | .recArg => some "RECARG"
      | .tacticAsym => some "TACTIC-ASYM"
      | .shape => some "SHAPE"
      | _ => none
    let some tag := expected | continue
    match rows.find? fun r => r.fam == fam && r.pair == s!"{e.presA}/{e.presB}" && r.src == e.constant with
    | some r =>
      IO.println s!"[clique-transport] (f) {tag} {fam} {e.presA}/{e.presB} {e.constant}: {r.verdict} {r.note}"
      if r.verdict == "EXACT" then
        failures := failures.push s!"{tag}: {fam} {e.constant} is reproduced exactly (stale cause)"
      if tag == "SHAPE" && !r.verdict.startsWith "FALLBACK" then
        failures := failures.push s!"SHAPE: {fam} {e.constant} did not take a fallback ({r.verdict})"
    | none =>
      -- a one-sided constant (e.g. RA's `_sparseCasesOn`) is outside the encoding
      IO.println s!"[clique-transport] (f) {tag} {fam} {e.presA}/{e.presB} {e.constant}: not an encoding constant"
  -- (g) the position restriction's negative control: user values of the packing type stay
  let wu := rows.filter (·.fam == "WU")
  let wuExact := (wu.filter (·.verdict == "EXACT")).size
  IO.println s!"[clique-transport] (g) position restriction: WU {wuExact}/{wu.size} exact (user values of exactly the packing type kept)"
  unless wu.size > 0 && wuExact == wu.size do failures := failures.push "WU: a user value of the packing type was transported"
  -- (c) GuessLex: everything but the measures reproduced
  let wg := rows.filter (·.fam == "WG")
  let wgGuess := (wg.filter (·.verdict == "GUESSLEX")).size
  let wgExact := (wg.filter (·.verdict == "EXACT")).size
  IO.println s!"[clique-transport] (c) WG: {wgExact} exact, {wgGuess} equal up to the measures (GUESSLEX), {wg.size - wgExact - wgGuess} other"
  unless wg.size > 0 && wgGuess > 0 && wgExact + wgGuess == wg.size do
    failures := failures.push "WG: not classified as GUESSLEX"
  -- (e) theorem cliques ordered by their statements (Q6)
  for fam in cliqueFamilies do
    let famName := fam.fixture.getString!
    let some p0 := fam.pres.head? | continue
    unless isTheoremClique env eqn p0 do continue
    for pk in fam.pres.tail do
      let v ← theoremCanonicity env eqn famName p0 pk
      IO.println s!"[clique-transport] (e) theorem clique {famName} {p0.id}/{pk.id}: {v}"
      let expectNoSpec := (entries.filter fun e => e.fixture == fam.fixture && e.cause matches .noSpec).length > 0
      if expectNoSpec then
        unless v.startsWith "NOSPEC" do failures := failures.push s!"Q6: {famName}: expected NOSPEC, got {v}"
      else unless v.startsWith "CANONICAL" && !((v.splitOn "RECOVERED ORDER DIFFERS").length > 1) do
        failures := failures.push s!"Q6: {famName}: {v}"
  -- the recovery's fallback: the inductive-predicate route is not recovered, so a tie there is NOSPEC
  if let some ip := familyNamed "IP" then
    if let some p0 := ip.pres.head? then
      match recOrder env eqn p0 with
      | .ok (σ, _) =>
        failures := failures.push s!"recovery: IP was recovered ({σ}); the control expects NOSPEC"
      | .error err => IO.println s!"[clique-transport] (e) recovery fallback IP {p0.id}: NOSPEC ({err})"
  -- (d) negative controls
  for fam in ["W3", "S3", "PF", "WD"] do
    if let some err ← wrongPermutation env eqn fam then failures := failures.push s!"control: {err}"
  if let some err ← strayProof env eqn then failures := failures.push s!"control: {err}"
  if let some err ← strayMonotonicity env eqn then failures := failures.push s!"control: {err}"
  -- (b) the kernel
  let rejected := kernelRows.filter (·.2.2.isSome)
  IO.println s!"[clique-transport] (b) kernel: {kernelRows.size - rejected.size}/{kernelRows.size} transported constants accepted"
  for (p, n, r) in rejected do failures := failures.push s!"kernel: {p} {n}: {r.getD ""}"
  -- results
  IO.FS.createDirAll "out/clique-transport"
  IO.FS.writeFile "out/clique-transport/results.tsv" <| String.join <| rows.toList.map fun r =>
    s!"{r.fam}\t{r.pair}\t{r.src}\t{r.dst}\t{r.verdict}\t{r.note}\n"
  IO.println s!"[clique-transport] {failures.size} failures"
  for f in failures do IO.println s!"[clique-transport] FAIL {f}"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Transport
