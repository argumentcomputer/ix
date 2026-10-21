/-
  clique-ownership: value-sensitive regression tests for the clique
  transport `Φ_σ` (`Ix.Compile.Pass.Clique.transport`) and the plan
  (`Ix.Compile.Pass.Clique.planClique`) on ordinary Lean sources in which a
  user's value, binder or relation has the shape of the clique's own encoding
  (`Tests/Ix/Compile/Clique/Ownership/Sources.lean`), and the structural
  carried-lemma checks on `Tests/Ix/Compile/Clique/Ownership/Lemmas.lean`.
  Ported from the donor's `Tests/Ix/Compile/CliqueOwnership.lean`, library
  cases only: the library is not wired into the compiler (see "Left for the
  wiring step" below).

  The sources are loaded at run time with the twins (`Common.fixturesEnv`;
  the `TwinsFixtures` root imports them), so they stay out of `get_env!`.

  For each fixture clique (both member orders) and the permutation `σ = [1,0]`:

  1. the transport (`runCase`) either transports the clique or keeps Lean's
     form (`baseline`, a named cause);
  2. when it transports, every output constant is added to a scratch Lean
     environment under scratch names (the Lean kernel must accept it);
  3. **value**: each probe evaluates a member, in Lean's constants and in the
     transported ones, and compares the two values with each other and with
     the value written in the probe. Structural members compute directly
     (`brecOn` reduces). A `partial_fixpoint` or well-founded member is a
     fixpoint, which does not reduce; its value is compared one unfolding
     deep: the fixpoint `fix F` is replaced by `F` applied to an oracle that
     answers every recursive call to member `j` with the fixed function
     `oracle_j`, placed in Lean's packing at `j` and in the transported packing
     at `σ j`. A transport that moves a user's value changes this value;
     O16 (`FixPerm.fix_iso`) is what makes one unfolding enough for a correct
     transport.

  A clique left in Lean's form is faithful by construction (its value is
  Lean's); it is reported, and it fails the test only where the probe says
  the clique must be transported (the controls, which measure that the
  ownership rules do not decline ordinary code).

  The plan cases (`runPlanCase`, `R1`, `R2`) run the compiler's whole plan
  (`planClique`: recovery, order, O17 aliases, transport) on the clique with
  primitive projections in the functionals, then evaluate every member the
  plan replaces against Lean's, and kernel-check the plan's constants.

  The carried-lemma checks (D-M5-1) on `Lemmas.lean`: each clique's plan
  with its members' `eq_def`s carried (`runLemmaPlan`: transported with
  every carried lemma, regenerated where a group is repacked, and accepted by
  Lean's kernel, or unchanged), the structural memo keyed by the ownership
  mode (`memoByMode`), and the repacked `eq_def`s of `SC1` regenerated
  exactly as the canonical `SC0`'s, with the original refusal kept for every
  unsupported replacement (`equationRegenerationChecks`).

  **The donor's sections that compile through the pipeline** are wired
  since CQ5.2 (b): the compile units (every well-founded case without its
  equation lemmas, WF8's caller refused by name and its neighbour compiled,
  the clique's addresses independent of its callers) and the carried-lemma
  units (each `Lem` clique compiled with its `eq_def`s, the clique table
  carrying them, the plan the compiler made, the kernels and the Rust leg on
  every compiled name) are `clique-ownership-units`
  (`Tests.Ix.Compile.Clique.OwnershipUnits`), and every case compiled by both
  compilers is `pass3-rust-parity`'s `co-*` units. Under decision (ii) the
  compiler keeps a structural clique in Lean's form, so the donor's control
  `lemmaControl` (lemmas transported by `Φ_σ` as before the refusal,
  rejected where `σ` repacks a group) has no compiled counterpart; the plan
  with the lemmas transported is checked here (`runLemmaPlan`).

  Invoked as `lake test -- clique-ownership`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Canon
import Ix.Compile.Pass.Clique
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.Clique.Common
import Tests.Ix.Compile.Clique.Transport

open Lean Meta

namespace Tests.Ix.Compile.Clique.Ownership

open Tests.Ix.Compile.Clique.Common
open Tests.Ix.Compile.Clique.Transport (eqnCliques checkDecls)
open _root_.Ix.Compile.Pass.Clique (Decl Encoding Input)

def srcNs : Name := `Tests.Ix.Compile.Clique.Ownership.Src
def lemNs : Name := `Tests.Ix.Compile.Clique.Ownership.Lem
def checkedNs : Name := `Tests.Ix.Compile.Clique.Ownership.Checked

/-- One evaluation: `member args` (member relative to the fixture). -/
structure Probe where
  member : Name
  args : Array Expr
  /-- the value Lean's member has -/
  expected : Expr
  /-- compare with `expected` (off when Lean's value is itself a stuck fixpoint) -/
  checkExpected : Bool := true

structure Case where
  /-- the fixture namespace under `Src` (`PF1A`, …) -/
  name : String
  /-- member (relative) ↦ its oracle constant (fixpoints only) -/
  oracles : Array (Name × Name) := #[]
  probes : Array Probe
  /-- the transport must not keep Lean's form (a control) -/
  mustTransport : Bool := false
  /-- an alteration of the transport's input (kernel-checked as source) -/
  alter : Option (Array Decl → Array Decl) := none
  /-- a short description for the log -/
  what : String := ""
  /-- run the compiler's whole plan (`planClique`: order, O17 classes,
  transport) on the input with primitive projections in the functionals,
  instead of the transport alone -/
  plan : Bool := false

/-! ## The transport's input -/

/-- The encoding constants of a clique besides its members: the packed
constant and its abstracted proofs (well-founded, `partial_fixpoint`), the
functionals (structural). -/
def auxOf (env : Environment) (enc : Encoding) (ms : Array Name) : Array Name :=
  let proofsOf (packed : Name) : Array Name :=
    (env.constants.fold (init := #[]) fun acc n _ => match n with
      | .str q s => if q == packed && s.startsWith "_proof_" then acc.push n else acc
      | _ => acc).qsort Name.quickLt
  match enc with
  | .wellFounded => #[ms[0]! ++ `_mutual] ++ proofsOf (ms[0]! ++ `_mutual)
  | .partialFixpoint => #[ms[0]! ++ `mutual] ++ proofsOf (ms[0]! ++ `mutual)
  | .structural => ms.filterMap fun m => if env.contains (m ++ `_f) then some (m ++ `_f) else none

/-- The block's authenticated `below`/`brecOn` family of a structural clique
(`Input.family`; empty for the other encodings, which do not read it). -/
def familyOf (ixEnv : _root_.Ix.Environment) (enc : Encoding) (members : Array Decl) :
    Except String (Std.HashSet IxName) :=
  match enc with
  | .structural => (_root_.Ix.Compile.Pass.Clique.authenticatedFamily ixEnv members).mapError
      (s!"no authenticated family ({·})")
  | _ => pure {}

/-- The inverse of a permutation, as an error when it is not one. -/
def invPermM (π : Array Nat) : MetaM (Array Nat) := do
  let some inv := _root_.Ix.Compile.Pass.Clique.invPerm π | throwError "not a permutation: {π}"
  return inv

/-! ## Evaluation -/

/-- Unfold every application of the named constants (their definitions,
β-reduced), repeatedly. -/
def deltaNames (names : NameSet) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let step (e : Expr) : Expr := e.replace fun x =>
    match x.getAppFn with
    | .const c us =>
      if names.contains c then
        match env.find? c with
        | some ci => match ci.value? (allowOpaque := true) with
          | some v => some ((v.instantiateLevelParams ci.levelParams us).beta x.getAppArgs)
          | none => none
        | none => none
      else none
    | _ => none
  let mut e := e
  for _ in [0:8] do
    let e' := step e
    if e' == e then break
    e := e'
  return e

/-- The tuple `⟨c₀, …⟩` of the `PProd` packing `γ` (right nested). `partial`,
as in the donor. -/
partial def mkTupleOf (comps : List Expr) : MetaM Expr := do
  match comps with
  | [] => throwError "empty packing"
  | [c] => pure c
  | c :: rest => mkAppM ``PProd.mk #[c, ← mkTupleOf rest]

/-- `λ y. PSum.casesOn y f₀ f₁ …` over the right-nested packing `α`,
motive `C`. `partial`, as in the donor. -/
partial def mkCases (α C : Expr) (fs : List Expr) (y : Expr) : MetaM Expr := do
  match fs with
  | [] => throwError "empty packing"
  | [f] => pure (mkApp f y)
  | f :: rest =>
    let α ← whnfR α
    unless α.isAppOfArity ``PSum 2 do throwError "not a PSum: {α}"
    let a := α.appFn!.appArg!
    let b := α.appArg!
    let mot ← withLocalDeclD `t α fun t => mkLambdaFVars #[t] (mkApp C t)
    let Cb ← withLocalDeclD `z b fun z => do
      mkLambdaFVars #[z] (mkApp C (← mkAppOptM ``PSum.inr #[a, b, z]))
    let inrFn ← withLocalDeclD `r b fun r => do mkLambdaFVars #[r] (← mkCases b Cb rest r)
    mkAppOptM ``PSum.casesOn #[a, b, mot, y, f, inrFn]

/-- One unfolding of the clique's fixpoint in `e`: `fix F` ↦ `F oracle`
(`Lean.Order.fix`), `fix F x` ↦ `F x (λ y _. O y)` (`WellFounded.fix`,
`WellFounded.Nat.fix`); component `p` of the packing answers with
`comps[p]`. -/
def unfoldFix (comps : Array Expr) (e : Expr) : MetaM Expr := do
  let isFix (x : Expr) : Bool :=
    (x.isAppOfArity ``Lean.Order.fix 4) || (x.isAppOfArity ``WellFounded.fix 6) ||
    (x.isAppOfArity ``WellFounded.Nat.fix 5)
  let some fx := e.find? isFix | throwError "no fixpoint to unfold in {e}"
  let args := fx.getAppArgs
  let repl ← if fx.isAppOf ``Lean.Order.fix then do
      let y ← mkTupleOf comps.toList
      pure (mkApp args[2]! y)
    else do
      let α := args[0]!
      let C := args[1]!
      let F := args[args.size - 2]!
      let x := args[args.size - 1]!
      let O ← withLocalDeclD `y α fun y => do mkLambdaFVars #[y] (← mkCases α C comps.toList y)
      let Fty ← whnf (← inferType F)
      let .forallE _ _ body _ := Fty | throwError "functional type {Fty}"
      let Aty ← whnf (body.instantiate1 x)
      let .forallE _ A _ _ := Aty | throwError "recursion binder type {Aty}"
      let a ← forallBoundedTelescope A (some 2) fun ys _ => mkLambdaFVars ys (mkApp O ys[0]!)
      pure (mkAppN F #[x, a])
  return e.replace fun z => if z == fx then some repl else none

/-- Evaluate `member args` one fixpoint unfolding deep (structural members
are evaluated directly). -/
def evalMember (names : NameSet) (member : Name) (args : Array Expr) (comps? : Option (Array Expr)) :
    MetaM Expr := do
  let e ← deltaNames names (mkAppN (mkConst member) args)
  let e ← match comps? with
    | some comps => unfoldFix comps e
    | none => pure e
  let e ← deltaNames names e
  withTransparency .all (reduce e (skipTypes := false))

/-! ## One case -/

structure Outcome where
  name : String
  /-- `transported`, `baseline: <cause>`, `planned: …`, … -/
  outcome : String
  kernel : String := "-"
  values : Array String := #[]
  failures : Array String := #[]

def coreCtx : Core.Context :=
  { fileName := "<clique-ownership>", fileMap := default, maxHeartbeats := 0 }

/-- Transport `c`'s clique onto `σ = [1, 0]` and check it (see the module
docstring). The transported constants are written to `dumpDir`. -/
def runCase (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (dumpDir : System.FilePath) (c : Case) : IO Outcome := do
  let ns := srcNs ++ c.name.toName
  let some (enc, ms) := eqn.get? (ns ++ `first) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for first"] }
  let σ : Array Nat := #[1, 0]
  let members ← ms.mapM fun m => match declOf env m with
    | some d => pure d
    | none => throw (IO.userError s!"{m}: not a definition")
  let auxNames := auxOf env enc ms
  let aux ← auxNames.mapM fun m => match declOf env m with
    | some d => pure d
    | none => throw (IO.userError s!"{m}: not a definition")
  let aux := match c.alter with
    | some f => f aux
    | none => aux
  let some σinv := _root_.Ix.Compile.Pass.Clique.invPerm σ | throw (IO.userError "σ is not a permutation")
  let newEncName := ixName (match enc with
    | .wellFounded => ns ++ `canon._mutual
    | .partialFixpoint => ns ++ `canon.mutual
    | .structural => ms[σinv[0]!]!)
  -- a structural clique needs its block's authenticated family (R02-06)
  let family ← match familyOf (ixEnvOf env) enc members with
    | .ok f => pure f
    | .error e => return { name := c.name, outcome := "NO FAMILY", failures := #[s!"{c.name}: {e}"] }
  let inp : Input := { encoding := enc, members, aux, sigma := σ, newEncName, const? := constOf env, family }
  let out := _root_.Ix.Compile.Pass.Clique.transport inp
  let scratch := checkedNs ++ c.name.toName
  let srcComps (π : Array Nat) : MetaM (Array Expr) := do
    -- component `π j` answers for member `j` (Lean's order)
    let inv ← invPermM π
    (List.range ms.size).toArray.mapM fun p => do
      let m := ms[inv[p]!]!
      let rel := m.replacePrefix ns .anonymous
      let some (_, o) := c.oracles.find? (·.1 == rel) | throwError "no oracle for {rel}"
      pure (mkConst o)
  let isFixpoint := enc != .structural
  let idσ := _root_.Ix.Compile.Pass.Clique.idPerm ms.size
  let body : MetaM Outcome := do
    let mut failures : Array String := #[]
    -- an altered source must itself be accepted by the kernel
    if c.alter.isSome then
      let r ← checkDecls (checkedNs ++ (c.name ++ "Source").toName) ns aux
      for (n, m?) in r do
        if let some m := m? then failures := failures.push s!"{c.name}: altered source {n} rejected: {m.take 300}"
    let srcNames : NameSet := (ms ++ auxNames).foldl (·.insert ·) {}
    let srcVal (p : Probe) : MetaM Expr := do
      evalMember srcNames (ns ++ p.member) p.args (← if isFixpoint then some <$> srcComps idσ else pure none)
    if out.baseline then
      let why := (out.causes[0]?).map (·.2.2) |>.getD "?"
      let mut values := #[]
      for p in c.probes do
        let v ← srcVal p
        unless !p.checkExpected || (← isDefEq v p.expected) do
          failures := failures.push s!"{c.name}: Lean's {p.member} is not {← ppExpr p.expected}: {← ppExpr v}"
        values := values.push s!"{p.member} {p.args.map toString}: Lean {← ppExpr v} (kept)"
      if c.mustTransport then failures := failures.push s!"{c.name}: a control kept Lean's form: {why}"
      return { name := c.name, outcome := s!"baseline: {why}", values, failures }
    -- the kernel
    let ks ← checkDecls scratch ns out.decls
    let rejected := ks.filter (·.2.isSome)
    for (n, m?) in rejected do
      failures := failures.push s!"{c.name}: kernel rejects {n}: {(m?.getD "").take 300}"
    let kernel := s!"{ks.size - rejected.size}/{ks.size}"
    -- the transported constants, for the record (a temporary directory)
    let tag := if c.alter.isSome then "-raw" else ""
    let mut dump := s!"# {c.name}{if c.alter.isSome then " (raw proj)" else ""}: {c.what}\n"
    for d in out.decls do
      dump := dump ++ s!"\n## {toLeanName d.name}\n{← ppExpr (toLeanExpr d.type)}\n:=\n{← ppExpr (toLeanExpr d.value)}\n"
    IO.FS.writeFile (dumpDir / s!"{c.name}{tag}.txt") dump
    -- the transported constants under their scratch names
    let outNames : NameSet := out.decls.foldl (fun s d => s.insert (toLeanName d.name)) {}
    let rn (n : Name) : Name := if outNames.contains n then scratch ++ n.replacePrefix ns .anonymous else n
    let tgtNames : NameSet := outNames.foldl (fun s n => s.insert (rn n)) {}
    let mut values := #[]
    if rejected.isEmpty then
      for p in c.probes do
        let v ← srcVal p
        let tgtMember := rn (ns ++ p.member)
        let w ← evalMember tgtNames tgtMember p.args (← if isFixpoint then some <$> srcComps σ else pure none)
        let okSrc ← if p.checkExpected then isDefEq v p.expected else pure true
        let same ← isDefEq v w
        values := values.push s!"{p.member} {p.args.map toString}: Lean {← ppExpr v}, transported {← ppExpr w}{if same then "" else "  <-- DIFFERENT"}"
        unless okSrc do failures := failures.push s!"{c.name}: Lean's {p.member} is not {← ppExpr p.expected}: {← ppExpr v}"
        unless same do
          failures := failures.push s!"{c.name}: WRONG MEANING: {p.member} {p.args.map toString} is {← ppExpr v} in Lean, {← ppExpr w} transported"
    return { name := c.name, outcome := "transported", kernel, values, failures }
  let (r, _) ← (body.run' {} : CoreM Outcome).toIO coreCtx { env }
  return r

/-! ## The compiler's plan (recovery, order, O17) -/

/-- `PProd.fst`/`PProd.snd` applications ↦ primitive projections (a raw
`Expr.proj`, which Lean's own field notation does not produce), to the fixed
point (nested applications are reached once their heads are replaced).
`partial`, as in the donor. -/
partial def rawProjsDeep (e : IxExpr) : IxExpr :=
  let le := toLeanExpr e
  let le' := le.replace fun x =>
    if x.isAppOfArity ``PProd.fst 3 then some (.proj ``PProd 0 x.appArg!)
    else if x.isAppOfArity ``PProd.snd 3 then some (.proj ``PProd 1 x.appArg!)
    else none
  let e' := toIxExpr le'
  if _root_.Ix.Compile.Pass.Clique.alphaEqSkipMdata e e' then e else rawProjsDeep e'

/-- Content addresses for a fixture's own constants (two matchers with one
body have one address, as in the compiler), names for the rest. -/
def fixtureAddr (env : Environment) (ns : Name) (n : IxName) : Option Address :=
  let ln := toLeanName n
  if ns.isPrefixOf ln then
    (env.find? ln).map fun ci =>
      Address.blake3 s!"{ci.type}|{(ci.value? (allowOpaque := true)).map toString}".toUTF8
  else some (Address.blake3 ln.toString.toUTF8)

/-- Plan the clique as the compiler does (with the functionals' projections
primitive), then evaluate every member the plan replaces (a transported or an
O17-aliased member) against Lean's. -/
def runPlanCase (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (c : Case) : IO Outcome := do
  let ns := srcNs ++ c.name.toName
  let some (_, ms) := eqn.get? (ns ++ `first) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for first"] }
  -- the input: Lean's constants, each member's functional with primitive
  -- projections (an overlay of the lazy environment)
  let mut overlay : Std.HashMap IxName IxConst := {}
  for m in ms do
    if let some ci := env.find? (m ++ `_f) then
      if let .defnInfo v := toIxConst ci then
        overlay := overlay.insert (ixName (m ++ `_f)) (.defnInfo { v with value := rawProjsDeep v.value })
  let ixEnv := ixEnvOf env overlay
  let const? := ixEnv.get?
  let outcome := _root_.Ix.Compile.Pass.Clique.planClique ixEnv (fixtureAddr env ns) (ms.map ixName) #[]
  -- the recovered specifications the order compares, for the log
  let specMembers := ms.filterMap fun m => (const? (ixName m)).bind Decl.ofConstantInfo?
  let specs : Except String (Array IxExpr) := do
    let family ← familyOf ixEnv .structural specMembers
    let specInp : Input :=
      { encoding := .structural, members := specMembers
        aux := ms.filterMap fun m => (const? (ixName (m ++ `_f))).bind Decl.ofConstantInfo?
        sigma := _root_.Ix.Compile.Pass.Clique.idPerm ms.size, newEncName := ixName ms[0]!, const?, family }
    _root_.Ix.Compile.Pass.Clique.normalisedSpecs specInp
  let body : MetaM Outcome := do
    let mut failures : Array String := #[]
    let mut specLines : Array String := #[]
    match specs with
    | .ok ss => for (m, s) in ms.zip ss do specLines := specLines.push s!"recovered {m.replacePrefix ns .anonymous}: {← ppExpr (toLeanExpr s)}"
    | .error e => specLines := specLines.push s!"recovery: {e}"
    let srcVal (p : Probe) : MetaM Expr :=
      evalMember ((ms.foldl (fun (s : NameSet) m => s.insert m) {}).insert (ns ++ p.member)) (ns ++ p.member) p.args none
    match outcome with
    | .transported plan =>
      let decls := plan.members.toArray.map (·.2) ++ plan.canon.map (·.1)
      let scratch := checkedNs ++ (c.name ++ "Plan").toName
      let ks ← checkDecls scratch ns decls
      for (n, m?) in ks do
        if let some m := m? then failures := failures.push s!"{c.name}: kernel rejects {n}: {m.take 300}"
      let outNames : NameSet := decls.foldl (fun s d => s.insert (toLeanName d.name)) {}
      let rn (n : Name) : Name := if outNames.contains n then scratch ++ n.replacePrefix ns .anonymous else n
      let mut values := #[]
      for p in c.probes do
        let v ← srcVal p
        let m := ns ++ p.member
        let w ← if outNames.contains m then
            evalMember (outNames.foldl (fun s n => s.insert (rn n)) {}) (rn m) p.args none
          else pure v
        let same ← isDefEq v w
        values := values.push s!"{p.member} {p.args.map toString}: Lean {← ppExpr v}, planned {← ppExpr w}{if same then "" else "  <-- DIFFERENT"}"
        if p.checkExpected then
          unless ← isDefEq v p.expected do failures := failures.push s!"{c.name}: Lean's {p.member} is not {← ppExpr p.expected}"
        unless same do failures := failures.push s!"{c.name}: WRONG MEANING: {p.member} {p.args.map toString} is {← ppExpr v} in Lean, {← ppExpr w} as planned"
      let aliases := plan.aliases.map fun (a, b) => s!"{(toLeanName a).replacePrefix ns .anonymous} = {(toLeanName b).replacePrefix ns .anonymous}"
      return { name := c.name, outcome := s!"planned: sigma {plan.sigma}, aliases (O17) {aliases}, order by {plan.source.describe}",
               kernel := s!"{ks.size - (ks.filter (·.2.isSome)).size}/{ks.size}", values := specLines ++ values, failures }
    | .baseline _ cause why => return { name := c.name, outcome := s!"baseline {cause.tag}: {why}", values := specLines }
    | .unchanged _ src => return { name := c.name, outcome := s!"unchanged (order by {src.describe})", values := specLines }
    | .notEncoded why => return { name := c.name, outcome := s!"not encoded: {why}", failures := #[s!"{c.name}: not encoded: {why}"] }
  let (r, _) ← (body.run' {} : CoreM Outcome).toIO coreCtx { env }
  return r

/-! ## Carried lemmas (D-M5-1), library level

The donor's carried-lemma units compile each `Lem` clique through the
pipeline (left for the wiring step). Their plan is checked here at the
library level (`runLemmaPlan`), with the donor's two library checks. -/

open _root_.Ix.Compile.Pass.Clique in
/-- The structural memo is keyed by the ownership mode
(`Clique.phiSFix`; M6R-3's observation). `HC`'s functional's dictionary type
`Nat.below M x`, taken as a term outside an owned binder, keeps its motive
with ownership enforced and has it repacked without (`σ = [1, 0]`,
`M = fun _ => PProd Bool Nat`). Within one run, each mode must give its own
result whichever comes first; the valid neighbour: without a repacked group
(`σ` the identity) the modes agree. Returns the failures and a summary. -/
def memoByMode (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name)) :
    Except String (Array String × String) := do
  let ns := lemNs ++ `HC
  let some (_, ms) := eqn.get? (ns ++ `hb) | throw "HC: no clique"
  let const? := constOf env
  let some members := ms.mapM (declOf env ·) | throw "HC: a member is not a definition"
  let all := ms.map ixName
  let some (_, aux) := encodingOf const? all members | throw "HC: no encoding"
  let family ← (familyOf (ixEnvOf env) .structural members).mapError (s!"HC: {·}")
  let some f := aux.find? (·.name == ixName (ms[0]! ++ `_f)) | throw "HC: no functional"
  let (bs, _) := _root_.Ix.Compile.Canon.peelForalls 2 f.type #[]
  let some (_, natTy, _) := bs[0]? | throw "HC: the functional has no major"
  let some (_, belowTy, _) := bs[1]? | throw "HC: the functional has no dictionary"
  let ctx : Array (IxExpr × Bool) := #[(natTy, false)]
  let one (σ : Array Nat) : Except String (IxExpr × IxExpr × IxExpr × IxExpr × IxExpr × IxExpr) := do
    let L ← structLayout members aux σ const? family
    let Lp := { L with checkOwnership := false }
    let on ← TM.run' (phiS L ctx belowTy)
    let off ← TM.run' (phiS Lp ctx belowTy)
    let (onOff1, onOff2) ← TM.run' do pure (← phiS L ctx belowTy, ← phiS Lp ctx belowTy)
    let (offOn1, offOn2) ← TM.run' do pure (← phiS Lp ctx belowTy, ← phiS L ctx belowTy)
    pure (on, off, onOff1, onOff2, offOn2, offOn1)
  let mut failures : Array String := #[]
  let (on, off, a1, b1, a2, b2) ← one #[1, 0]
  unless on == belowTy do failures := failures.push "HC: ownership enforced, the user's below application lost its motive"
  if off == belowTy then failures := failures.push "HC: ownership off, the motive was not repacked"
  unless a1 == on && b1 == off do failures := failures.push "HC: run (enforced, off): the second mode took the first one's result"
  unless a2 == on && b2 == off do failures := failures.push "HC: run (off, enforced): the second mode took the first one's result"
  let (on', off', _, _, _, _) ← one #[0, 1]
  unless on' == off' do failures := failures.push "HC: without a repacked group the modes differ"
  return (failures, s!"memo by ownership mode: repacked {if on != off then "distinct" else "equal"} \
    results per mode in both orders; identity σ: modes agree {on' == off'}")

open _root_.Ix.Compile.Pass.Clique in
/-- A false, but well-typed, Bool unfolding statement for the refusal control. -/
def eqDefFalseRhs : IxExpr → IxExpr
  | .forallE n t b bi _ => _root_.Ix.Expr.mkForallE n t (eqDefFalseRhs b) bi
  | e => match constApp? e with
    | some (n, us, #[ty, lhs, _]) =>
      _root_.Ix.Compile.Canon.mkAppN (_root_.Ix.Expr.mkConst n us)
        #[ty, lhs, _root_.Ix.Expr.mkConst (ixName ``Bool.false) #[]]
    | _ => e

open _root_.Ix.Compile.Pass.Clique in
/-- Exact P1→P0 members/functionals and independently regenerated equations
(`SC1` transported onto `σ = [1, 0]` against the canonical `SC0`);
source-proof wrapping is irrelevant. Each failed replacement must still hit
the original structural refusal. -/
def equationRegenerationChecks (env : Environment)
    (eqn : Std.HashMap Name (Encoding × Array Name)) :
    Except String (Array String × String) := do
  let ns := lemNs ++ `SC1
  let canonical := lemNs ++ `SC0
  let const? := constOf env
  let some (_, ms) := eqn.get? (ns ++ `od) | throw "eq_def: SC1 clique missing"
  let some members := ms.mapM (declOf env ·) | throw "eq_def: SC1 member missing"
  let all := ms.map ixName
  let some (_, aux) := encodingOf const? all members | throw "eq_def: SC1 encoding missing"
  let family ← (familyOf (ixEnvOf env) .structural members).mapError (s!"eq_def: SC1 {·}")
  let some lemmas := ms.mapM (fun n => declOf env (n ++ `eq_def)) | throw "eq_def: SC1 lemma missing"
  let pairs := lemmas.map fun d => (d, d.name)
  let generate (lookup : IxName → Option IxConst) (pairs : Array (Decl × IxName)) :=
    TM.run' (transportStructural members aux #[1, 0] lookup family pairs)
  let produced ← generate const? pairs
  -- `SC1`'s names map to `SC0`'s, except a constant `SC0` shares with `SC1`:
  -- Lean reuses an existing matcher of the same type and body, so `SC0`'s
  -- functionals and `eq_def`s apply `SC1.od.match_1` (there is no
  -- `SC0.od.match_1`). The donor mapped every `SC1` name, which here sends
  -- that matcher to a constant that does not exist and fails four exact
  -- comparisons for a reason outside the library. A name that exists under
  -- `SC0` is still mapped, so the comparison stays exact.
  let ren (n : IxName) : Option IxName :=
    let name := toLeanName n
    let name' := name.replacePrefix ns canonical
    if ns.isPrefixOf name && env.contains name' then some (ixName name') else none
  let mut failures := #[]
  let mut equations := 0
  let mut declarations := 0
  for t in produced do
    let d := t.decl
    let name := (toLeanName d.name).replacePrefix ns canonical
    let some reference := declOf env name | throw s!"eq_def: canonical reference {name} missing"
    let reference ← if lemmas.any (fun l => eqDefNameEq l.name d.name) then do
        let .str owner _ := name | throw "eq_def: equation has no owner"
        let some member := declOf env owner | throw "eq_def: canonical owner missing"
        equations := equations + 1
        TM.run' (regenerateStructuralEq const? member reference reference.name 0)
      else pure reference
    unless eqDefExprEq (renameConsts ren d.type) reference.type &&
        eqDefExprEq (renameConsts ren d.value) reference.value do
      failures := failures.push s!"eq_def: canonical P1→P0 oracle differs at {name}"
    declarations := declarations + 1
  unless equations == 2 && declarations == produced.size && declarations ≥ 6 do
    failures := failures.push s!"eq_def: incomplete canonical oracle ({equations}/{declarations})"
  let wrapped := pairs.map fun (d, n) =>
    ({ d with value := (_root_.Ix.Compile.Canon.mkAppN
        (_root_.Ix.Expr.mkConst (ixName ``id) #[_root_.Ix.Level.mkZero]) #[d.type, d.value]) }, n)
  let wrappedOutput ← generate const? wrapped
  unless produced.size == wrappedOutput.size && (produced.zip wrappedOutput).all (fun (a, b) =>
      eqDefNameEq a.decl.name b.decl.name && eqDefExprEq a.decl.type b.decl.type &&
        eqDefExprEq a.decl.value b.decl.value) do
    failures := failures.push "eq_def: a harmless source proof wrapper changed regeneration"
  let falsePairs := pairs.map fun (d, n) =>
    (if eqDefNameEq d.name (ixName (ns ++ `ev.eq_def)) then { d with type := eqDefFalseRhs d.type } else d, n)
  let renamedPairs := pairs.map fun (d, n) => ({ d with name := _root_.Ix.Name.mkStr d.name "unsupported" }, n)
  let attempts := #[
    ("false equation", generate const? falsePairs),
    ("foreign lemma", generate const? renamedPairs),
    ("missing Eq.refl", generate (fun n => if eqDefNameEq n (ixName ``Eq.refl) then none else const? n) pairs),
    ("missing casesOn", generate (fun n => if eqDefNameEq n (ixName ``Nat.casesOn) then none else const? n) pairs)]
  for (label, result) in attempts do
    match result with
    | .error e =>
      unless e.startsWith "grammar: the carried equation lemma " &&
          (e.splitOn "of a repacked group").length == 2 do
        failures := failures.push s!"eq_def: {label} lost the original refusal: {e}"
    | .ok _ => failures := failures.push s!"eq_def: {label} was admitted"
  let z := _root_.Ix.Expr.mkBVar 0
  let one : IxExpr := .bvar 1 z.getHash
  let zOther : IxExpr := .bvar 0 (_root_.Ix.Expr.mkBVar 9).getHash
  unless !eqDefExprEq z one && eqDefExprEq z zOther && !eqDefConvertible const? 0 z z do
    failures := failures.push "eq_def: structural cache/fuel admission controls failed"
  return (failures, s!"equation regeneration: {declarations} exact canonical declarations, {equations} equations, \
    proof-wrapper neighbour, {attempts.size} original refusals, cache/fuel controls")

/-- The carried-lemma cliques: the namespace under `Lem`, a member, and the
expected plan with the members' `eq_def`s carried (`transported` with every
carried lemma, or `unchanged`), under the test's addresses (`fixtureAddr`).

The donor compiled each clique (its units, left for the wiring step) and
expected `SC1` transported and `SC0` unchanged: the compiler's order over
compiled addresses. `SC0` and `SC1` are one clique in its two member orders,
and the order between `od` and `ev` compares their specifications, which
differ in external constants (`Bool.false`, `Bool.true`) that the test's
addresses hash by name; under them the canonical order is `SC1`'s, so `SC1`
is `unchanged` and `SC0` is the transported one (its group of two repacked,
its `eq_def`s regenerated). The suite also requires that the two orders
split this way (one transported, one unchanged), whatever the addresses.
`MA`–`MD` are transported, as in the donor. -/
def lemmaCases : Array (String × Name × String) :=
  #[("SC1", `od, "unchanged"), ("SC0", `od, "transported"), ("MA", `sa, "transported"),
    ("MB", `sa, "transported"), ("MC", `f, "transported"), ("MD", `f, "transported")]

/-- Plan a `Lem` clique with its members' `eq_def`s carried (the clique
table's carried lemmas, given here directly), and add a transported plan's
constants (members, carried lemmas, canonical constants) with Lean's kernel
under scratch names. -/
def runLemmaPlan (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (nm : String) (member : Name) (expect : String) : IO Outcome := do
  let ns := lemNs ++ nm.toName
  let some (enc, ms) := eqn.get? (ns ++ member) |
    return { name := nm, outcome := "MISSING", failures := #[s!"{nm}: no clique recorded for {member}"] }
  let mut failures : Array String := #[]
  unless enc == .structural do failures := failures.push s!"{nm}: not a structural clique"
  let carried := (ms.map fun m => ixName (m ++ `eq_def)).qsort (·.pretty < ·.pretty)
  for c in carried do
    unless env.contains (toLeanName c) do failures := failures.push s!"{nm}: {c.pretty} is not in the input"
  let outcome := _root_.Ix.Compile.Pass.Clique.planClique (ixEnvOf env) (fixtureAddr env ns) (ms.map ixName) carried
  let (got, decls) : String × Array Decl := match outcome with
    | .transported p =>
      (if carried.all p.members.contains && p.causes.isEmpty then "transported"
       else "transported without its lemmas or with causes",
       p.members.toArray.map (·.2) ++ p.canon.map (·.1))
    | .unchanged _ _ => ("unchanged", #[])
    | o => (o.tag, #[])
  unless got == expect do failures := failures.push s!"{nm}: plan {got}, expected {expect}"
  let body : MetaM Outcome := do
    let mut failures := failures
    let ks ← checkDecls (checkedNs ++ (nm ++ "Lem").toName) ns decls
    for (n, m?) in ks do
      if let some m := m? then failures := failures.push s!"{nm}: kernel rejects the planned {n}: {m.take 300}"
    let sigma := match outcome with
      | .transported p => s!", sigma {p.sigma}"
      | _ => ""
    return { name := nm, outcome := s!"plan {got}{sigma}; carried {carried.size}",
             kernel := s!"{(ks.filter (·.2.isNone)).size}/{ks.size}", failures }
  let (r, _) ← (body.run' {} : CoreM Outcome).toIO coreCtx { env }
  return r

/-! ## The cases -/

def natLit (n : Nat) : Expr := mkNatLit n
def someNat (n : Nat) : Expr := mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Nat) (mkNatLit n)
def ltNat (a b : Nat) : Expr :=
  mkApp4 (mkConst ``LT.lt [.zero]) (mkConst ``Nat) (mkConst ``instLTNat) (mkNatLit a) (mkNatLit b)
def src (n : Name) : Expr := mkConst (srcNs ++ n)

def pfOracles : Array (Name × Name) :=
  #[(`first, srcNs ++ `pfOracle0), (`second, srcNs ++ `pfOracle1)]
def wfPropOracles : Array (Name × Name) :=
  #[(`first, srcNs ++ `wfPropOracle0), (`second, srcNs ++ `wfPropOracle1)]
def wfNatOracles : Array (Name × Name) :=
  #[(`first, srcNs ++ `wfNatOracle0), (`second, srcNs ++ `wfNatOracle1)]

def cases : Array Case :=
  let pf (nm : String) (what : String) (probes : Array Probe) (must := false) : Case :=
    { name := nm, oracles := pfOracles, probes, mustTransport := must, what }
  let wfP (nm : String) (what : String) (probes : Array Probe) (must := false) : Case :=
    { name := nm, oracles := wfPropOracles, probes, mustTransport := must, what }
  let wfN (nm : String) (what : String) (probes : Array Probe) (must := false) : Case :=
    { name := nm, oracles := wfNatOracles, probes, mustTransport := must, what }
  let st (nm : String) (what : String) (probes : Array Probe) (must := false) (alter := none) : Case :=
    { name := nm, probes, mustTransport := must, what, alter }
  let pfUser (p : Expr) : Array Probe :=
    #[{ member := `first, args := #[p, natLit 0], expected := someNat 17 },
      { member := `first, args := #[p, natLit 3], expected := someNat 2002 },
      { member := `second, args := #[p, natLit 0], expected := someNat 31 },
      { member := `second, args := #[p, natLit 2], expected := someNat 1001 }]
  let pfPlain : Array Probe :=
    #[{ member := `first, args := #[natLit 0], expected := someNat 5 },
      { member := `first, args := #[natLit 4], expected := someNat 2004 },
      { member := `second, args := #[natLit 4], expected := someNat 1005 }]
  let wfRel : Array Probe :=
    #[{ member := `first, args := #[natLit 0], expected := ltNat 0 1 }]
  #[pf "PF1A" "user lambda over the packed type, handed to a higher-order function (F1)" (pfUser (src `userFns)),
    pf "PF1B" "PF1, other member order" (pfUser (src `userFns)),
    pf "PF2A" "user value of the packed type under a let" (pfUser (src `userFns)),
    pf "PF2B" "PF2, other member order" (pfUser (src `userFns)),
    pf "PF3A" "user value of the packed type inside a proposition and its decision" #[
      { member := `first, args := #[src `userFns, natLit 0], expected := someNat 1 }],
    pf "PF3B" "PF3, other member order" #[
      { member := `first, args := #[src `userFns, natLit 0], expected := someNat 1 }],
    pf "PF4A" "user value of the packed type as a structure field" (pfUser (src `userBox)),
    pf "PF4B" "PF4, other member order" (pfUser (src `userBox)),
    pf "PF2CA" "PF2 with the packed type spelled out" (pfUser (src `userFns)),
    pf "PF2CB" "PF2C, other member order" (pfUser (src `userFns)),
    pf "PF3CA" "PF3 under a user lambda binder of the packed type" #[
      { member := `first, args := #[src `userFns, natLit 0], expected := someNat 1 }],
    pf "PF3CB" "PF3C, other member order" #[
      { member := `first, args := #[src `userFns, natLit 0], expected := someNat 1 }],
    pf "PF4CA" "PF4 with the structure built in place" (pfUser (src `userFns)),
    pf "PF4CB" "PF4C, other member order" (pfUser (src `userFns)),
    pf "PF6A" "user function returning the packed type, projected unapplied" (pfUser (src `userFns)),
    pf "PF6B" "PF6, other member order" (pfUser (src `userFns)),
    pf "PF7A" "nested cliques: another clique's packed fixpoint of the same type" #[
      { member := `first, args := #[natLit 0], expected := someNat 0, checkExpected := false },
      { member := `second, args := #[natLit 2], expected := someNat 1001 }],
    pf "PF7B" "PF7, other member order" #[
      { member := `first, args := #[natLit 0], expected := someNat 0, checkExpected := false },
      { member := `second, args := #[natLit 2], expected := someNat 1001 }],
    pf "PF5A" "recursive calls inside a user lambda (control)" pfPlain (must := true),
    pf "PF5B" "PF5, other member order (control)" pfPlain (must := true),
    wfP "WF1A" "user WellFoundedRelation over the packing type (F2)" wfRel,
    wfP "WF1B" "WF1, other member order" wfRel,
    wfP "WF2A" "user relation on a let-bound user value of the packing type" wfRel,
    wfP "WF2B" "WF2, other member order" wfRel,
    wfP "WF3A" "user relation as a structure field" wfRel,
    wfP "WF3B" "WF3, other member order" wfRel,
    wfP "WF4A" "user InvImage over the packing type" wfRel,
    wfP "WF4B" "WF4, other member order" wfRel,
    wfP "WF5A" "user relation passed whole to a user lambda" wfRel,
    wfP "WF5B" "WF5, other member order" wfRel,
    wfN "WF6A" "user data of the packing type, recursive calls (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 1 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }] (must := true),
    wfN "WF6B" "WF6, other member order (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 1 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }] (must := true),
    wfN "WF7A" "user record function field applied to injections of the packing type" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }],
    wfN "WF7B" "WF7, other member order" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }],
    wfN "WF8A" "ordinary clique with a caller that unfolds Lean's encoding (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 1 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }] (must := true),
    wfN "WF8B" "WF8, other member order (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 1 },
      { member := `first, args := #[natLit 5], expected := natLit 2005 },
      { member := `second, args := #[natLit 5], expected := natLit 1006 }] (must := true),
    st "S1A" "user Nat.brecOn with a packed-shaped motive, field notation" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 },
      { member := `first, args := #[natLit 2], expected := natLit 17 },
      { member := `second, args := #[natLit 1], expected := natLit 17 }],
    st "S1B" "S1, other member order" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 },
      { member := `second, args := #[natLit 1], expected := natLit 17 }],
    st "S2A" "user binder of a below type with a packed-shaped motive, field notation" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 },
      { member := `second, args := #[natLit 1], expected := natLit 17 }],
    st "S2B" "S2, other member order" #[
      { member := `first, args := #[natLit 0], expected := natLit 17 }],
    { name := "S2A", what := "S2 with primitive projections (F3: raw Expr.proj)",
      probes := #[{ member := `first, args := #[natLit 0], expected := natLit 17 },
                  { member := `second, args := #[natLit 1], expected := natLit 17 }],
      alter := some fun aux => aux.map fun d => { d with value := rawProjsDeep d.value } },
    st "S4A" "dictionary threaded through a match with an equation binder (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 5 },
      { member := `first, args := #[natLit 1], expected := natLit 8 },
      { member := `first, args := #[natLit 3], expected := natLit 13 },
      { member := `second, args := #[natLit 2], expected := natLit 11 }] (must := true),
    st "S4B" "S4, other member order (control)" #[
      { member := `first, args := #[natLit 3], expected := natLit 13 }] (must := true),
    { name := "R1A", plan := true,
      what := "recovery: a user below path read as a recursive call (F3b), whole plan with O17",
      probes := #[{ member := `first, args := #[natLit 1], expected := natLit 5 },
                  { member := `second, args := #[natLit 1], expected := natLit 29 },
                  { member := `second, args := #[natLit 0], expected := natLit 5 }] },
    { name := "R1B", plan := true, what := "R1, other member order",
      probes := #[{ member := `first, args := #[natLit 1], expected := natLit 5 },
                  { member := `second, args := #[natLit 1], expected := natLit 29 },
                  { member := `second, args := #[natLit 0], expected := natLit 5 }] },
    -- FIX-pfwf O2: a user's `below` application decided classically. Lean's
    -- value is a stuck classical decision, so the probes compare the two
    -- terms definitionally (`checkExpected := false`)
    st "S5A" "user below application with heterogeneous components, decided classically (O2)" #[
      { member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false },
      { member := `second, args := #[natLit 1], expected := natLit 17, checkExpected := false },
      { member := `second, args := #[natLit 0], expected := natLit 31 }],
    st "S5B" "S5, other member order (O2)" #[
      { member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false },
      { member := `second, args := #[natLit 1], expected := natLit 17, checkExpected := false }],
    st "S6A" "S5 with homogeneous components (valid neighbour of S5)" #[
      { member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false },
      { member := `second, args := #[natLit 0], expected := natLit 31 }] (must := true),
    st "S6B" "S6, other member order (valid neighbour)" #[
      { member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false }] (must := true),
    { name := "R2A", plan := true,
      what := "recovery: two members that differ only in a user below motive, whole plan with O17 (O2)",
      probes := #[{ member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false },
                  { member := `second, args := #[natLit 0], expected := natLit 17, checkExpected := false },
                  { member := `second, args := #[natLit 1], expected := natLit 17, checkExpected := false }] },
    { name := "R2B", plan := true, what := "R2, other member order (O2)",
      probes := #[{ member := `first, args := #[natLit 0], expected := natLit 17, checkExpected := false },
                  { member := `second, args := #[natLit 0], expected := natLit 17, checkExpected := false },
                  { member := `second, args := #[natLit 1], expected := natLit 17, checkExpected := false }] },
    st "S3A" "ordinary structural recursion (control)" #[
      { member := `first, args := #[natLit 0], expected := natLit 5 },
      { member := `first, args := #[natLit 3], expected := natLit 11 },
      { member := `second, args := #[natLit 3], expected := natLit 10 }] (must := true),
    st "S3B" "S3, other member order (control)" #[
      { member := `first, args := #[natLit 3], expected := natLit 11 }] (must := true)]

/-- The suite on `env` (the twins' fixtures environment, with the sources). -/
def runOn (env : Environment) : IO UInt32 := do
  let eqn := eqnCliques env
  let dumpDir ← IO.FS.createTempDir
  IO.println s!"[clique-ownership] transported constants: {dumpDir}"
  let mut failures : Array String := #[]
  let mut transported := 0
  let mut planned := 0
  let mut kept := 0
  for c in cases do
    let o ← try (if c.plan then runPlanCase env eqn c else runCase env eqn dumpDir c)
      catch e => pure { name := c.name, outcome := "ERROR", failures := #[s!"{c.name}: {e}"] }
    let tag := if c.alter.isSome then s!"{c.name}(raw proj)" else c.name
    IO.println s!"[clique-ownership] {tag} ({c.what}): {o.outcome}, kernel {o.kernel}"
    for v in o.values do IO.println s!"[clique-ownership]   {v}"
    for f in o.failures do IO.println s!"[clique-ownership]   FAIL {f}"
    if o.outcome == "transported" then transported := transported + 1
    else if o.outcome.startsWith "planned" then planned := planned + 1
    else kept := kept + 1
    failures := failures ++ o.failures
  -- the carried-lemma library checks
  let mut lemmaPlans : Array (String × String) := #[]
  for (nm, member, expect) in lemmaCases do
    let o ← try runLemmaPlan env eqn nm member expect
      catch e => pure { name := nm, outcome := "ERROR", failures := #[s!"{nm} (carried lemmas): {e}"] }
    IO.println s!"[clique-ownership] {nm} (carried lemmas): {o.outcome}, kernel {o.kernel}"
    for f in o.failures do IO.println s!"[clique-ownership]   FAIL {f}"
    lemmaPlans := lemmaPlans.push (nm, o.outcome)
    failures := failures ++ o.failures
  -- `SC0` and `SC1` are one clique in two orders: one is canonical
  let planOf (nm : String) : String := ((lemmaPlans.find? (·.1 == nm)).map (·.2)).getD ""
  let split := [planOf "SC0", planOf "SC1"]
  unless split.any (·.startsWith "plan unchanged") && split.any (·.startsWith "plan transported") do
    failures := failures.push s!"carried lemmas: SC0 and SC1 (one clique, two orders) do not split into one unchanged and one transported: {split}"
  match equationRegenerationChecks env eqn with
  | .error e =>
    IO.println s!"[clique-ownership]   FAIL equation regeneration: {e}"
    failures := failures.push s!"equation regeneration: {e}"
  | .ok (fs, summary) =>
    IO.println s!"[clique-ownership] {summary}"
    for f in fs do IO.println s!"[clique-ownership]   FAIL {f}"
    failures := failures ++ fs
  match memoByMode env eqn with
  | .error e =>
    IO.println s!"[clique-ownership]   FAIL memo: {e}"
    failures := failures.push s!"memo: {e}"
  | .ok (fs, summary) =>
    IO.println s!"[clique-ownership] {summary}"
    for f in fs do IO.println s!"[clique-ownership]   FAIL {f}"
    failures := failures ++ fs
  IO.println s!"[clique-ownership] {cases.size} cases: {transported} transported, {planned} planned (transported), \
    {kept} kept in Lean's form (baseline or unchanged), {failures.size} failure(s)"
  return if failures.isEmpty then 0 else 1

def run : IO UInt32 := do runOn (← fixturesEnv)

end Tests.Ix.Compile.Clique.Ownership
