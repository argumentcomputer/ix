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

  The test may use `MetaM`/`CoreM` (it reads Lean's `EqnInfo`, converts terms
  and calls the kernel); the transport itself may not and does not.

  Invoked as `lake test -- --ignored clique-transport`.
-/
import Ix.Meta
import Ix.CanonM
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

/-! ## The suite -/

def isPendingTransport (e : NonCanonicalEntry) : Bool :=
  match e.cause with
  | .pendingTransport => true
  | _ => false

def isGuessLex (e : NonCanonicalEntry) : Bool :=
  match e.cause with
  | .guessLex => true
  | _ => false

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
  IO.println s!"[clique-transport] (a) exact oracle: {exact}/{pend.length} packing-order-only constants reproduced exactly"
  -- (c) GuessLex: everything but the measures reproduced
  let wg := rows.filter (·.fam == "WG")
  let wgGuess := (wg.filter (·.verdict == "GUESSLEX")).size
  let wgExact := (wg.filter (·.verdict == "EXACT")).size
  IO.println s!"[clique-transport] (c) WG: {wgExact} exact, {wgGuess} equal up to the measures (GUESSLEX), {wg.size - wgExact - wgGuess} other"
  unless wg.size > 0 && wgGuess > 0 && wgExact + wgGuess == wg.size do
    failures := failures.push "WG: not classified as GUESSLEX"
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
