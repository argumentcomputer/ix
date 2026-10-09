/-
  clique-ownership: value-sensitive regression tests for the clique
  transport `Φ_σ` (`Ix.Compile.Clique.transport`, design document §5) on
  ordinary Lean sources in which a user's value, binder or relation has the
  shape of the clique's own encoding (`Tests/Ix/Compile/CliqueOwnership/
  Sources.lean`).

  For each fixture clique (both member orders) and the permutation `σ = [1,0]`:

  1. the public transport (the function the compiler calls under
     Pass 3, `Ix.Compile.Pass.planClique`) either transports the
     clique or keeps Lean's form (`baseline`, a named cause);
  2. when it transports, every output constant is added to a scratch Lean
     environment (the Lean kernel must accept it);
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

  Run with: `lake test -- --ignored clique-ownership`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Clique.Transport
import Ix.Compile.Pass
import Tests.Ix.Compile.Transport
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.CliqueOwnership.Sources
import Tests.Ix.Compile.CliqueOwnership.Lemmas

open Lean Meta
open Tests.Ix.Compile.Transport (ixName toLeanName toIxConst toLeanExpr declOf eqnCliques checkDecls)

namespace Tests.Ix.Compile.CliqueOwnership

abbrev IxName := _root_.Ix.Name
abbrev Decl := _root_.Ix.Compile.Clique.Decl

def srcNs : Name := `Tests.Ix.Compile.CliqueOwnership.Src
def checkedNs : Name := `Tests.Ix.Compile.CliqueOwnership.Checked

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
  /-- run the compiler's whole plan (`Ix.Compile.Pass.planClique`: order, O17
  classes, transport) on the input with primitive projections in the
  functionals, instead of the transport alone -/
  plan : Bool := false

/-! ## The transport's input -/

def auxOf (env : Environment) (enc : _root_.Ix.Compile.Clique.Encoding) (ms : Array Name) : Array Name :=
  let proofsOf (packed : Name) : Array Name :=
    (env.constants.fold (init := #[]) fun acc n _ => match n with
      | .str q s => if q == packed && s.startsWith "_proof_" then acc.push n else acc
      | _ => acc).qsort Name.quickLt
  match enc with
  | .wellFounded => #[ms[0]! ++ `_mutual] ++ proofsOf (ms[0]! ++ `_mutual)
  | .partialFixpoint => #[ms[0]! ++ `mutual] ++ proofsOf (ms[0]! ++ `mutual)
  | .structural =>
    let fs := ms.filterMap fun m => if env.contains (m ++ `_f) then some (m ++ `_f) else none
    fs

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

/-- The tuple `⟨c₀, …⟩` of the `PProd` packing `γ` (right nested). -/
partial def mkTupleOf (comps : List Expr) : MetaM Expr := do
  match comps with
  | [] => throwError "empty packing"
  | [c] => pure c
  | c :: rest => mkAppM ``PProd.mk #[c, ← mkTupleOf rest]

/-- `λ y. PSum.casesOn y f₀ f₁ …` over the right-nested packing `α`,
motive `C`. -/
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
  /-- `transported`, `baseline: <cause>` -/
  outcome : String
  kernel : String := "-"
  values : Array String := #[]
  failures : Array String := #[]

def runCase (env : Environment) (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name))
    (c : Case) : IO Outcome := do
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
  let newEncName := ixName (match enc with
    | .wellFounded => ns ++ `canon._mutual
    | .partialFixpoint => ns ++ `canon.mutual
    | .structural => ms[(_root_.Ix.Compile.Clique.invPerm σ)[0]!]!)
  let inp : _root_.Ix.Compile.Clique.Input :=
    { encoding := enc, members, aux, sigma := σ, newEncName
      const? := fun n => (env.find? (toLeanName n)).map toIxConst }
  let out := _root_.Ix.Compile.Clique.transport inp
  let ctx : Core.Context := { fileName := "<clique-ownership>", fileMap := default, maxHeartbeats := 0 }
  let scratch := checkedNs ++ c.name.toName
  let srcComps (π : Array Nat) : MetaM (Array Expr) := do
    -- component `π j` answers for member `j` (Lean's order)
    let inv := _root_.Ix.Compile.Clique.invPerm π
    (List.range ms.size).toArray.mapM fun p => do
      let m := ms[inv[p]!]!
      let rel := m.replacePrefix ns .anonymous
      let some (_, o) := c.oracles.find? (·.1 == rel) | throwError "no oracle for {rel}"
      pure (mkConst o)
  let isFixpoint := enc != .structural
  let body : MetaM Outcome := do
    let mut failures : Array String := #[]
    -- an altered source must itself be accepted by the kernel
    if c.alter.isSome then
      let r ← checkDecls (checkedNs ++ (c.name ++ "Source").toName) ns aux
      for (n, m?) in r do
        if let some m := m? then failures := failures.push s!"{c.name}: altered source {n} rejected: {m.take 300}"
    let srcNames : NameSet := (ms ++ auxNames).foldl (·.insert ·) {}
    let srcVal (p : Probe) : MetaM Expr := do
      evalMember srcNames (ns ++ p.member) p.args (← if isFixpoint then some <$> srcComps (_root_.Ix.Compile.Clique.idPerm ms.size) else pure none)
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
    -- the transported constants, for the record (`out/clique-ownership/<case>.txt`)
    let dir : System.FilePath := "out/clique-ownership"
    IO.FS.createDirAll dir
    let mut dump := s!"# {c.name}{if c.alter.isSome then " (raw proj)" else ""}: {c.what}\n"
    for d in out.decls do
      dump := dump ++ s!"\n## {toLeanName d.name}\n{← ppExpr (toLeanExpr d.type)}\n:=\n{← ppExpr (toLeanExpr d.value)}\n"
    IO.FS.writeFile (dir / s!"{c.name}{if c.alter.isSome then "-raw" else ""}.txt") dump
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
  let (r, _) ← (body.run' {} : CoreM Outcome).toIO ctx { env }
  return r

/-! ## The compiler's plan (recovery, order, O17) -/

/-- `PProd.fst`/`PProd.snd` applications ↦ primitive projections, to the
fixed point (defined below the cases for the transport-only cases too). -/
partial def rawProjsDeep (e : _root_.Ix.Expr) : _root_.Ix.Expr :=
  let le := toLeanExpr e
  let le' := le.replace fun x =>
    if x.isAppOfArity ``PProd.fst 3 then some (.proj ``PProd 0 x.appArg!)
    else if x.isAppOfArity ``PProd.snd 3 then some (.proj ``PProd 1 x.appArg!)
    else none
  let e' := (_root_.Ix.CanonM.canonExpr le').run' {}
  if _root_.Ix.Compile.Clique.alphaEq e e' then e else rawProjsDeep e'

/-- Plan the clique as the compiler does (with the functionals' projections
primitive), then evaluate every member the plan replaces (a transported or an
O17-aliased member) against Lean's. -/
def runPlanCase (env : Environment) (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name))
    (c : Case) : IO Outcome := do
  let ns := srcNs ++ c.name.toName
  let some (_, ms) := eqn.get? (ns ++ `first) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for first"] }
  let altered : NameSet := ms.foldl (fun s m => s.insert (m ++ `_f)) {}
  let const? (n : IxName) : Option _root_.Ix.ConstantInfo :=
    let ln := toLeanName n
    (env.find? ln).map fun ci =>
      match toIxConst ci with
      | .defnInfo v => if altered.contains ln then .defnInfo { v with value := rawProjsDeep v.value } else .defnInfo v
      | ic => ic
  -- content addresses for the fixture's own constants (two matchers with one
  -- body have one address, as in the compiler), names for the rest
  let addr? (n : IxName) : Option Address :=
    let ln := toLeanName n
    if ns.isPrefixOf ln then
      (env.find? ln).map fun ci =>
        Address.blake3 s!"{ci.type}|{(ci.value? (allowOpaque := true)).map toString}".toUTF8
    else some (Address.blake3 ln.toString.toUTF8)
  let outcome := Ix.Compile.Pass.planClique const? addr? (ms.map ixName) #[]
  -- the recovered specifications the order compares, for the log
  let specInp : _root_.Ix.Compile.Clique.Input :=
    { encoding := .structural, members := ms.filterMap fun m => (const? (ixName m)).bind _root_.Ix.Compile.Clique.Decl.ofConstantInfo?
      aux := ms.filterMap fun m => (const? (ixName (m ++ `_f))).bind _root_.Ix.Compile.Clique.Decl.ofConstantInfo?
      sigma := _root_.Ix.Compile.Clique.idPerm ms.size, newEncName := ixName ms[0]!, const? }
  let specs := _root_.Ix.Compile.Clique.normalisedSpecs specInp
  let ctx : Core.Context := { fileName := "<clique-ownership>", fileMap := default, maxHeartbeats := 0 }
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
      return { name := c.name, outcome := s!"planned: sigma {plan.sigma}, aliases (O17) {aliases}, order by {plan.source.tag}",
               kernel := s!"{ks.size - (ks.filter (·.2.isSome)).size}/{ks.size}", values := specLines ++ values, failures }
    | .baseline _ cause why => return { name := c.name, outcome := s!"baseline {cause}: {why}", values := specLines }
    | .unchanged _ src => return { name := c.name, outcome := s!"unchanged (order by {src.tag})", values := specLines }
    | .notEncoded why => return { name := c.name, outcome := s!"not encoded: {why}", failures := #[s!"{c.name}: not encoded: {why}"] }
  let (r, _) ← (body.run' {} : CoreM Outcome).toIO ctx { env }
  return r

/-! ## Compile units (the compiler, not the transport alone)

A fixture clique compiled by the Lean pipeline (Pass 3), as a
compile unit made of its members (and, for some cases, constants of the
fixture namespace that use them) with their closure
(`Tests.Ix.Compile.Pass3.closureOf`):

* the members' equation lemmas are not in the unit (the closure of the
  members does not reach them), so no carried lemma's statement check
  (`Pass/Cliques.lean`, `planClique`: "does not have Lean's type") can be
  what stops a wrong transport (FIX-pfwf O4);
* the plan is the compiler's (`Ix.Compile.Pass.planClique` on the compile
  state, the clique table's carried lemmas), and when it transports, every
  member it replaces is evaluated one fixpoint unfolding deep against Lean's
  (`evalMember`), and the three kernels check the compiled members and
  canonical constants;
* **callers** (the block rule, design document §6.3, "callers adapt"): a
  constant outside the clique's unit that references a member and one of
  Lean's encoding constants must be refused by name when the clique is
  transported (a block failure naming the caller and the clique), and must
  compile when it is not; a **neighbour** that references only a member
  always compiles; and the clique compiles to the same addresses with and
  without its callers in the unit (the clique is never changed for a
  caller). -/

open Tests.Ix.Compile.Pass3 (CUnit kernelFailures) in
/-- The Rust leg of a compile unit (M6R slice 3): the same prepared input
compiled by the Rust compiler under Pass 3 (`rsCompileEnvBytesFFI`). The
clique's members and the hook's canonical constants under reserved names must
have the same `Named` entries (address, metadata incl. the decompile records
and the side-car record `_ix.clique`, original, hints) as in the Lean compile
whose values this suite checks, the failures must be the same names, and the
three kernels must accept the Rust file's compiled names. Returns the failures
and a summary. -/
def rustLeg (u : CUnit) (on : Ix.CompileM.LeanPipelineOut) (ms : Array Name) (names : Array String) :
    IO (Array String × String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv u.env u.closure).mapError toString)
  let constants ← IO.ofExcept input.prepare
  let dir ← IO.FS.createTempDir
  try
    let path := dir / "rust.ixe"
    let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
    let rust ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
    let mut failures : Array String := #[]
    let leanFailed := (on.cenv.ungrounded.toArray.map (·.1.pretty)).qsort (· < ·)
    let rustFailed := status.ungrounded.map (·.1)
    unless leanFailed == rustFailed do
      failures := failures.push s!"{u.name}: Rust failures {rustFailed} differ from Lean's {leanFailed}"
    let msIx := ms.map ixName
    let keys := on.env.named.toArray.filterMap fun (n, _) =>
      if msIx.contains n then some n
      else if Ix.Compile.Pass.hasReserved n && msIx.any (fun m => (Ix.Compile.Pass.stripPrefix? m n).isSome) then some n
      else none
    let mut same := 0
    for n in keys do
      match on.env.named.get? n, rust.named.get? n with
      | some a, some b =>
        if a.addr == b.addr && a.constMeta == b.constMeta && a.hints == b.hints &&
            (a.original.map (·.1)) == (b.original.map (·.1)) then same := same + 1
        else failures := failures.push s!"{u.name}: Rust's {n.pretty} differs from Lean's"
      | _, none => failures := failures.push s!"{u.name}: Rust has no {n.pretty}"
      | none, _ => pure ()
    let kf ← if names.isEmpty then pure #[] else kernelFailures dir path names
    for (leg, n, m) in kf do failures := failures.push s!"{u.name}: Rust-compiled {n} rejected by {leg}: {m.take 200}"
    if keys.isEmpty then failures := failures.push s!"{u.name}: the Rust leg compared nothing"
    return (failures, s!"rust: {same}/{keys.size} member and canonical entries identical to Lean's, \
failures {rustFailed.size}, {kf.size} kernel failure(s) on {names.size} names")
  finally IO.FS.removeDirAll dir

open Tests.Ix.Compile.Pass3 (CUnit closureOf compileUnit kernelFailures) in
/-- Compile `c`'s clique as a unit (members, plus `callers` and
`neighbours`, relative to the fixture namespace) and check it. -/
def runUnitCase (env : Environment) (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name))
    (c : Case) (callers neighbours : Array Name := #[]) : IO Outcome := do
  let ns := srcNs ++ c.name.toName
  let some (enc, ms) := eqn.get? (ns ++ `first) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for first"] }
  let extra := (callers ++ neighbours).map (ns ++ ·)
  let mkUnit (seeds : Array Name) : CUnit :=
    { name := s!"clique-ownership-{c.name}", env, seeds, closure := closureOf env seeds.toList }
  let u := mkUnit (ms ++ extra)
  let mut failures : Array String := #[]
  -- the unit carries no equation lemma of a member
  let eqLemmas := u.closure.filterMap fun (n, _) =>
    if ms.contains n.getPrefix && (match n with | .str _ s => s.startsWith "eq_" | _ => false) then some n else none
  unless eqLemmas.isEmpty do failures := failures.push s!"{c.name}: the unit carries equation lemmas {eqLemmas}"
  let on ← compileUnit u
  -- the Rust leg (M6R slice 3): the same input through the Rust compiler
  let rustNames := (ms.map (·.toString)) ++ (on.env.named.toArray.filterMap fun (n, _) =>
    if Ix.Compile.Pass.hasReserved n then some n.pretty else none)
  let (rustFailures, rustSummary) ← rustLeg u on ms rustNames
  failures := failures ++ rustFailures
  let key := ixName ms[0]!
  let some (all, carried) := on.cenv.p3Cliques.get? key |
    return { name := c.name, outcome := "not in the clique table", failures := failures.push s!"{c.name}: not in the clique table" }
  unless carried.isEmpty do failures := failures.push s!"{c.name}: carried lemmas {carried.map (·.pretty)} in a unit without them"
  let outcome := Ix.Compile.Pass.planClique on.cenv.env.get? (Ix.Compile.Pass.cliqueAddr on.cenv) all carried
  let refused := on.cenv.ungrounded.toList.filter fun (_, e) => (e.splitOn "caller refused").length > 1
  let refusedNames : Array Name := refused.toArray.map (toLeanName ·.1)
  let isTransported := match outcome with | .transported _ => true | _ => false
  -- callers and neighbours
  for k in callers do
    let n := ns ++ k
    if isTransported then
      match refused.find? (toLeanName ·.1 == n) with
      | none => failures := failures.push s!"{c.name}: caller {k} of a transported clique was not refused"
      | some (_, e) =>
        unless (e.splitOn n.toString).length > 1 && (e.splitOn ms[0]!.toString).length > 1 do
          failures := failures.push s!"{c.name}: the refusal of {k} does not name the caller and the clique: {e}"
    else if on.cenv.ungrounded.contains (ixName n) then
      failures := failures.push s!"{c.name}: caller {k} of a clique in Lean's form failed: {on.cenv.ungrounded.get? (ixName n)}"
  for k in neighbours do
    if on.cenv.ungrounded.contains (ixName (ns ++ k)) then
      failures := failures.push s!"{c.name}: neighbour {k} failed: {on.cenv.ungrounded.get? (ixName (ns ++ k))}"
  for (n, e) in on.cenv.ungrounded.toList do
    unless refusedNames.contains (toLeanName n) do
      failures := failures.push s!"{c.name}: unexpected block failure {n.pretty}: {e.take 300}"
  -- the clique does not depend on its callers
  if !extra.isEmpty then
    let alone ← compileUnit (mkUnit ms)
    for m in ms do
      let a := (on.env.named.get? (ixName m)).map (·.addr)
      let b := (alone.env.named.get? (ixName m)).map (·.addr)
      unless a.isSome && a == b do
        failures := failures.push s!"{c.name}: {m} compiles to {a} with its callers and {b} without"
  let ctx : Core.Context := { fileName := "<clique-ownership>", fileMap := default, maxHeartbeats := 0 }
  let srcComps (π : Array Nat) : MetaM (Array Expr) := do
    let inv := _root_.Ix.Compile.Clique.invPerm π
    (List.range ms.size).toArray.mapM fun p => do
      let m := ms[inv[p]!]!
      let rel := m.replacePrefix ns .anonymous
      let some (_, o) := c.oracles.find? (·.1 == rel) | throwError "no oracle for {rel}"
      pure (mkConst o)
  let isFixpoint := enc != .structural
  let tag := s!"unit: {refused.length} caller(s) refused; {rustSummary}"
  let refusalLines := refused.toArray.map fun (n, e) => s!"refused {n.pretty}: {e}"
  match outcome with
  | .transported plan =>
    let decls := plan.members.toArray.map (·.2) ++ plan.canon.map (·.1)
    let body : MetaM Outcome := do
      let mut failures := failures
      let scratch := checkedNs ++ (c.name ++ "Unit").toName
      let ks ← checkDecls scratch ns decls
      for (n, m?) in ks do
        if let some m := m? then failures := failures.push s!"{c.name}: Lean kernel rejects the planned {n}: {m.take 300}"
      let outNames : NameSet := decls.foldl (fun s d => s.insert (toLeanName d.name)) {}
      let rn (n : Name) : Name := if outNames.contains n then scratch ++ n.replacePrefix ns .anonymous else n
      let tgtNames : NameSet := outNames.foldl (fun s n => s.insert (rn n)) {}
      let srcNames : NameSet := (ms ++ auxOf env enc ms).foldl (·.insert ·) {}
      let mut values := #[]
      for p in c.probes do
        let m := ns ++ p.member
        let v ← evalMember srcNames m p.args (← if isFixpoint then some <$> srcComps (_root_.Ix.Compile.Clique.idPerm ms.size) else pure none)
        let w ← if outNames.contains m then
            evalMember tgtNames (rn m) p.args (← if isFixpoint then some <$> srcComps plan.sigma else pure none)
          else pure v
        let same ← isDefEq v w
        values := values.push s!"{p.member} {p.args.map toString}: Lean {← ppExpr v}, compiled {← ppExpr w}{if same then "" else "  <-- DIFFERENT"}"
        if p.checkExpected then
          unless ← isDefEq v p.expected do failures := failures.push s!"{c.name}: Lean's {p.member} is not {← ppExpr p.expected}"
        unless same do
          failures := failures.push s!"{c.name}: WRONG MEANING (compile unit): {p.member} {p.args.map toString} is {← ppExpr v} in Lean, {← ppExpr w} compiled"
      return { name := c.name, outcome := s!"{tag}; compiled: sigma {plan.sigma}, aliases (O17) {plan.aliases.size}",
               kernel := s!"{ks.size - (ks.filter (·.2.isSome)).size}/{ks.size}", values := refusalLines ++ values, failures }
    let (r, _) ← (body.run' {} : CoreM Outcome).toIO ctx { env }
    -- the three kernels on the compiled members and canonical constants
    let names := (ms.map (·.toString)) ++ (on.env.named.toArray.filterMap fun (n, _) =>
      if Ix.Compile.Pass.hasReserved n then some n.pretty else none) ++
      neighbours.map (fun k => (ns ++ k).toString)
    let dir ← IO.FS.createTempDir
    let kf ← try
        let p := dir / "on.ixe"
        IO.FS.writeBinFile p on.bytes
        kernelFailures dir p names
      finally IO.FS.removeDirAll dir
    let kfails := kf.toList.map fun (leg, n, m) => s!"{c.name}: compiled {n} rejected by {leg}: {m.take 200}"
    return { r with kernel := s!"{r.kernel} planned (Lean), {names.size} compiled names, {kf.size} kernel failure(s)",
                    failures := r.failures ++ kfails.toArray }
  | .baseline _ cause why => return { name := c.name, outcome := s!"{tag}; baseline {cause}: {why}", failures }
  | .unchanged _ src => return { name := c.name, outcome := s!"{tag}; unchanged (order by {src.tag})", failures }
  | .notEncoded why => return { name := c.name, outcome := s!"{tag}; not encoded: {why}", failures := failures.push s!"{c.name}: not encoded: {why}" }

/-! ## Carried-lemma units (D-M5-1)

A structural clique of `Tests/Ix/Compile/CliqueOwnership/Lemmas.lean` with its
`eq_def`s realised (`unfold_used`) compiled by the Lean pipeline with the
switch on, as a unit seeded by the members and `unfold_used` (the closure
carries the `eq_def`s):

* the clique table carries every member's `eq_def` (`scheduleCliques`);
* the plan is the expected one: transported (repacked eq_def proofs are
  regenerated over the target definitions), or unchanged (Lean's order is
  canonical). Separate malformed/missing-support controls must retain the
  exact refusal of an unsupported repacked proof;
* the three kernels (`check-rs`, `check-lean`, the certified checker) accept
  every compiled name of the case's namespace, the `eq_def`s and
  `unfold_used` included (before the refusal, the certified checker rejected
  the transported `eq_def`s of the repacked cliques: "application type
  mismatch");
* the Rust compiler gives the same entries for the members, the carried
  lemmas, `unfold_used` and the canonical constants (`rustLeg`);
* **control**: the carried lemmas transported by `Φ_σ` as before the refusal
  (`phiS` with ownership off, beside the members' and functionals'
  transport) are rejected by Lean's kernel exactly where the clique repacks
  a group, and accepted where it does not. -/

def lemNs : Name := `Tests.Ix.Compile.CliqueOwnership.Lem

/-- One carried-lemma unit: the namespace under `Lem`, a member, the expected
plan (`transported`, `unchanged`, `refused`), and whether a group is repacked
(the control's expectation). -/
structure LemmaCase where
  name : String
  member : Name
  expect : String
  repacks : Bool
  what : String

def lemmaCases : Array LemmaCase := #[
  { name := "SC1", member := `od, expect := "transported", repacks := true,
    what := "one group of two in a non-canonical order (D-M5-1's source)" },
  { name := "SC0", member := `od, expect := "unchanged", repacks := false,
    what := "the same clique in the canonical order (neighbour)" },
  { name := "MA", member := `sa, expect := "transported", repacks := false,
    what := "groups of one, non-canonical order (neighbour)" },
  { name := "MB", member := `sa, expect := "transported", repacks := false,
    what := "groups of one, fixed parameters reordered (neighbour)" },
  { name := "MC", member := `f, expect := "transported", repacks := true,
    what := "a group of two repacked beside a group of one" },
  { name := "MD", member := `f, expect := "transported", repacks := false,
    what := "a group of two in the canonical order, the clique's order not (neighbour)" }]

open _root_.Ix.Compile.Clique in
/-- The control: the members, functionals and carried lemmas of the clique
transported as before the refusal (the lemmas by `phiS` with ownership off),
added to Lean's kernel under `scratch`; the verdict of each carried lemma, and
the rejections among the other constants. -/
def lemmaControl (cenv : Ix.CompileM.CompileEnv) (all carried : Array IxName) (scratch ns : Name) :
    CoreM (Except String (Array (Name × Option String) × Array String)) := do
  let const? := cenv.env.get?
  let some members := all.mapM fun m => (const? m).bind Ix.Compile.Pass.cliqueDecl?
    | return .error "a member is not a definition"
  let some (enc, aux) := Ix.Compile.Pass.encodingOf const? all members | return .error "no encoding"
  unless enc == .structural do return .error "not structural"
  let some lemmas := carried.mapM fun c => (const? c).bind _root_.Ix.Compile.Clique.Decl.ofConstantInfo?
    | return .error "a carried lemma is not a theorem"
  let inp0 : Input := { encoding := enc, members, aux, sigma := idPerm all.size, newEncName := all[0]!, const? }
  let .ok (σ, _, _) := cliqueOrder Ix.Compile.Canon.Rules.phaseA (Ix.Compile.Pass.cliqueAddr cenv) inp0
    | return .error "no order"
  let r : Except String (Array Decl × Array Decl) := TM.run' do
    let ts ← transportStructural members aux σ const? #[]
    let L ← liftE (structLayout members aux σ const?)
    let Lp := { L with checkOwnership := false }
    let ls ← lemmas.mapM fun d => do
      pure { d with type := ← phiS Lp #[] d.type, value := ← phiS Lp #[] d.value }
    pure (ts.map (·.decl), ls)
  match r with
  | .error e => return .error e
  | .ok (ts, ls) =>
    let ks ← checkDecls scratch ns (ts ++ ls)
    let lemmaNames : NameSet := carried.foldl (fun s c => s.insert (toLeanName c)) {}
    let other := ks.filterMap fun (n, m?) =>
      if lemmaNames.contains n then none else m?.map fun m => s!"{n}: {m.take 200}"
    return .ok (ks.filter (lemmaNames.contains ·.1), other)

open _root_.Ix.Compile.Clique in
/-- The structural memo is keyed by the ownership mode
(`Clique.phiSFix`; M6R-3's observation, `FU-compiler-followups.md` item 3).
`HC`'s functional's dictionary type `Nat.below M x`, taken as a term outside
an owned binder, keeps its motive with ownership enforced and has it
repacked without (`σ = [1, 0]`, `M = fun _ => PProd Bool Nat`). Within one
run, each mode must give its own result whichever comes first (before the
fix the second mode took the first one's from the memo); the valid
neighbour: without a repacked group (`σ` the identity) the modes agree.
Returns the failures and a summary. -/
def memoByMode (env : Environment) (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name)) :
    Except String (Array String × String) := do
  let ns := lemNs ++ `HC
  let some (_, ms) := eqn.get? (ns ++ `hb) | throw "HC: no clique"
  let const? (n : IxName) : Option _root_.Ix.ConstantInfo := (env.find? (toLeanName n)).map toIxConst
  let some members := ms.mapM (declOf env ·) | throw "HC: a member is not a definition"
  let all := ms.map ixName
  let some (_, aux) := Ix.Compile.Pass.encodingOf const? all members | throw "HC: no encoding"
  let some f := aux.find? (·.name == ixName (ms[0]! ++ `_f)) | throw "HC: no functional"
  let (bs, _) := _root_.Ix.Compile.Canon.peelForalls 2 f.type #[]
  let some (_, natTy, _) := bs[0]? | throw "HC: the functional has no major"
  let some (_, belowTy, _) := bs[1]? | throw "HC: the functional has no dictionary"
  let ctx : Array (_root_.Ix.Expr × Bool) := #[(natTy, false)]
  let one (σ : Array Nat) : Except String (_root_.Ix.Expr × _root_.Ix.Expr × _root_.Ix.Expr × _root_.Ix.Expr × _root_.Ix.Expr × _root_.Ix.Expr) := do
    let L ← structLayout members aux σ const?
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

open Tests.Ix.Compile.Pass3 (CUnit closureOf compileUnit kernelFailures) in
/-- Compile one carried-lemma unit and check it (see the section's text). -/
def runLemmaUnit (env : Environment) (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name))
    (c : LemmaCase) : IO Outcome := do
  let ns := lemNs ++ c.name.toName
  let some (enc, ms) := eqn.get? (ns ++ c.member) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for {c.member}"] }
  let mut failures : Array String := #[]
  unless enc == .structural do failures := failures.push s!"{c.name}: not a structural clique"
  let used := ns ++ `unfold_used
  let derived := if env.contains (ns ++ `equations_used) then #[ns ++ `equations_used] else #[]
  let seeds := ms.push used ++ derived
  let u : CUnit := { name := s!"clique-lemmas-{c.name}", env, seeds,
                     closure := closureOf env seeds.toList }
  let on ← compileUnit u
  for (n, e) in on.cenv.ungrounded.toList do
    failures := failures.push s!"{c.name}: block failure {n.pretty}: {e.take 300}"
  -- the carried lemmas: every member's `eq_def`
  let key := ixName ms[0]!
  let some (all, carried) := on.cenv.p3Cliques.get? key |
    return { name := c.name, outcome := "not in the clique table", failures := failures.push s!"{c.name}: not in the clique table" }
  let expectCarried := (ms.map fun m => ixName (m ++ `eq_def)).qsort (·.pretty < ·.pretty)
  unless carried.map (·.pretty) == expectCarried.map (·.pretty) do
    failures := failures.push s!"{c.name}: carried {carried.map (·.pretty)}, expected {expectCarried.map (·.pretty)}"
  -- the plan
  let outcome := Ix.Compile.Pass.planClique on.cenv.env.get? (Ix.Compile.Pass.cliqueAddr on.cenv) all carried
  let got := match outcome with
    | .transported p =>
      if carried.all p.members.contains then "transported" else "transported without its lemmas"
    | .unchanged _ _ => "unchanged"
    | .baseline _ cause why =>
      if cause == "SHAPE" && (why.splitOn "carried equation lemma").length > 1 &&
          (why.splitOn "repacked group").length > 1 then "refused" else s!"baseline {cause}: {why}"
    | .notEncoded why => s!"not encoded: {why}"
  unless got == c.expect do failures := failures.push s!"{c.name}: plan {got}, expected {c.expect}"
  -- the kernels on every compiled name of the case
  let names := on.env.named.toArray.filterMap fun (n, _) =>
    if ns.isPrefixOf (toLeanName n) then some n.pretty else none
  let dir ← IO.FS.createTempDir
  let kf ← try
      let p := dir / "on.ixe"
      IO.FS.writeBinFile p on.bytes
      kernelFailures dir p names
    finally IO.FS.removeDirAll dir
  for (leg, n, m) in kf do failures := failures.push s!"{c.name}: compiled {n} rejected by {leg}: {m.take 200}"
  unless names.any (· == (ixName used).pretty) && carried.all (fun l => names.contains l.pretty) &&
      derived.all (fun n => names.contains (ixName n).pretty) do
    failures := failures.push s!"{c.name}: the kernels did not check unfold_used and every carried lemma"
  -- the Rust leg: members, carried lemmas, `unfold_used`, canonical constants
  let (rustFailures, rustSummary) ← rustLeg u on ((ms ++ carried.map toLeanName |>.push used) ++ derived) #[]
  failures := failures ++ rustFailures
  -- the control
  let ctx : Core.Context := { fileName := "<clique-ownership>", fileMap := default, maxHeartbeats := 0 }
  let scratch := checkedNs ++ (c.name ++ "Lem").toName
  let (ctl, _) ← ((lemmaControl on.cenv all carried scratch ns) : CoreM _).toIO ctx { env }
  let (ctlLine, ctlFails) : String × Array String := match ctl with
    | .error e => (s!"control: {e}", #[s!"{c.name}: control: {e}"])
    | .ok (ks, other) =>
      let rejected := ks.filter (·.2.isSome)
      let fs := other.map (s!"{c.name}: control: Lean's kernel rejects " ++ ·)
      let fs := if c.repacks then
          (if rejected.size == ks.size && !ks.isEmpty then fs
           else fs.push s!"{c.name}: control: the lemmas transported as before are not all rejected ({rejected.size}/{ks.size})")
        else fs ++ rejected.map fun (n, m?) =>
          s!"{c.name}: control: {n} rejected without a repacked group: {(m?.getD "").take 200}"
      let first := (rejected[0]?.bind (·.2)).map (fun m => s!" ({m.take 120})") |>.getD ""
      (s!"control: {rejected.size}/{ks.size} lemma(s) transported as before rejected by Lean's kernel{first}", fs)
  failures := failures ++ ctlFails
  return { name := c.name, outcome := s!"plan {got}; carried {carried.size}; {rustSummary}",
           kernel := s!"{names.size} compiled names, {kf.size} kernel failure(s)",
           values := #[ctlLine], failures }

open _root_.Ix.Compile.Clique in
/-- A false, but well-typed, Bool unfolding statement for the refusal control. -/
def eqDefFalseRhs : _root_.Ix.Expr → _root_.Ix.Expr
  | .forallE n t b bi _ => _root_.Ix.Expr.mkForallE n t (eqDefFalseRhs b) bi
  | e => match constApp? e with
    | some (n, us, #[ty, lhs, _]) =>
      _root_.Ix.Compile.Canon.mkAppN (_root_.Ix.Expr.mkConst n us)
        #[ty, lhs, _root_.Ix.Expr.mkConst (ixName ``Bool.false) #[]]
    | _ => e

open _root_.Ix.Compile.Clique in
/-- Exact P1→P0 members/functionals and independently regenerated equations;
source-proof wrapping is irrelevant. Each failed replacement must still hit
the old structural refusal. The old mixed-packing kernel control above stays. -/
def equationRegenerationChecks (env : Environment)
    (eqn : Std.HashMap Name (_root_.Ix.Compile.Clique.Encoding × Array Name)) :
    Except String (Array String × String) := do
  let ns := lemNs ++ `SC1
  let canonical := lemNs ++ `SC0
  let const? (n : IxName) := (env.find? (toLeanName n)).map toIxConst
  let some (_, ms) := eqn.get? (ns ++ `od) | throw "eq_def: SC1 clique missing"
  let some members := ms.mapM (declOf env ·) | throw "eq_def: SC1 member missing"
  let all := ms.map ixName
  let some (_, aux) := Ix.Compile.Pass.encodingOf const? all members | throw "eq_def: SC1 encoding missing"
  let some lemmas := ms.mapM (fun n => declOf env (n ++ `eq_def)) | throw "eq_def: SC1 lemma missing"
  let pairs := lemmas.map fun d => (d, d.name)
  let generate (lookup : IxName → Option _root_.Ix.ConstantInfo) (pairs : Array (Decl × IxName)) :=
    TM.run' (transportStructural members aux #[1, 0] lookup pairs)
  let produced ← generate const? pairs
  let ren (n : IxName) : Option IxName :=
    let name := toLeanName n
    if ns.isPrefixOf name then some (ixName (name.replacePrefix ns canonical)) else none
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
    ({ d with value := _root_.Ix.Compile.Canon.mkAppN
        (_root_.Ix.Expr.mkConst (ixName ``id) #[_root_.Ix.Level.mkZero]) #[d.type, d.value] }, n)
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
  let one : _root_.Ix.Expr := .bvar 1 z.getHash
  let zOther : _root_.Ix.Expr := .bvar 0 (_root_.Ix.Expr.mkBVar 9).getHash
  unless !eqDefExprEq z one && eqDefExprEq z zOther && !eqDefConvertible const? 0 z z do
    failures := failures.push "eq_def: structural cache/fuel admission controls failed"
  return (failures, s!"equation regeneration: {declarations} exact canonical declarations, {equations} equations, \
    proof-wrapper neighbour, {attempts.size} original refusals, cache/fuel controls")

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

/-- `PProd.fst`/`PProd.snd` applications ↦ primitive projections (a raw
`Expr.proj`, which Lean's own field notation does not produce). -/
def rawProjs (e : _root_.Ix.Expr) : _root_.Ix.Expr :=
  let le := toLeanExpr e
  let le' := le.replace fun x =>
    if x.isAppOfArity ``PProd.fst 3 then some (.proj ``PProd 0 x.appArg!)
    else if x.isAppOfArity ``PProd.snd 3 then some (.proj ``PProd 1 x.appArg!)
    else none
  (_root_.Ix.CanonM.canonExpr le').run' {}

/-- `rawProjs` all the way down (nested applications are reached once their
heads are replaced). -/
partial def rawProjsFix (e : _root_.Ix.Expr) : _root_.Ix.Expr :=
  let e' := rawProjs e
  if _root_.Ix.Compile.Clique.alphaEq e e' then e else rawProjsFix e'

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
      alter := some fun aux => aux.map fun d => { d with value := rawProjsFix d.value } },
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

def run : IO UInt32 := do
  let env ← get_env!
  let eqn := eqnCliques env
  let mut failures : Array String := #[]
  let mut transported := 0
  let mut kept := 0
  for c in cases do
    let o ← try (if c.plan then runPlanCase env eqn c else runCase env eqn c) catch e => pure { name := c.name, outcome := "ERROR", failures := #[s!"{c.name}: {e}"] }
    let tag := if c.alter.isSome then s!"{c.name}(raw proj)" else c.name
    IO.println s!"[clique-ownership] {tag} ({c.what}): {o.outcome}, kernel {o.kernel}"
    for v in o.values do IO.println s!"[clique-ownership]   {v}"
    for f in o.failures do IO.println s!"[clique-ownership]   FAIL {f}"
    if o.outcome == "transported" then transported := transported + 1 else kept := kept + 1
    failures := failures ++ o.failures
  -- the compile units: every well-founded case without its equation
  -- lemmas (FIX-pfwf O4), and the callers of WF8
  let mut units := 0
  let mut refusals := 0
  let mut compiledCallers := 0
  for c in cases do
    unless c.name.startsWith "WF" && c.alter.isNone do continue
    let (callers, neighbours) := if c.name.startsWith "WF8" then (#[`caller], #[`neighbour]) else (#[], #[])
    let o ← try runUnitCase env eqn c callers neighbours
      catch e => pure { name := c.name, outcome := "ERROR", failures := #[s!"{c.name} (unit): {e}"] }
    units := units + 1
    IO.println s!"[clique-ownership] {c.name} (compile unit): {o.outcome}, kernel {o.kernel}"
    for v in o.values do IO.println s!"[clique-ownership]   {v}"
    for f in o.failures do IO.println s!"[clique-ownership]   FAIL {f}"
    if !callers.isEmpty && o.failures.isEmpty then
      if (o.outcome.splitOn "unit: 1 caller(s) refused").length > 1 then refusals := refusals + 1
      else compiledCallers := compiledCallers + 1
    failures := failures ++ o.failures
  -- the caller check must have been exercised both ways
  unless refusals ≥ 1 && compiledCallers ≥ 1 do
    failures := failures.push s!"callers: {refusals} refused and {compiledCallers} compiled; the block-rule check needs a transported and a kept WF8 order"
  IO.println s!"[clique-ownership] compile units: {units}, WF8 callers refused {refusals}, compiled {compiledCallers}"
  -- All six original units and their full kernel/name/parity predicates stay.
  let mut lemmaPlans : Std.HashMap String Nat := {}
  for c in lemmaCases do
    let o ← try runLemmaUnit env eqn c
      catch e => pure { name := c.name, outcome := "ERROR", failures := #[s!"{c.name} (carried lemmas): {e}"] }
    IO.println s!"[clique-ownership] {c.name} (carried lemmas: {c.what}): {o.outcome}, kernel {o.kernel}"
    for v in o.values do IO.println s!"[clique-ownership]   {v}"
    for f in o.failures do IO.println s!"[clique-ownership]   FAIL {f}"
    if o.failures.isEmpty then lemmaPlans := lemmaPlans.insert c.expect (lemmaPlans.getD c.expect 0 + 1)
    failures := failures ++ o.failures
  unless lemmaPlans.getD "transported" 0 == 5 && lemmaPlans.getD "unchanged" 0 == 1 do
    failures := failures.push s!"carried lemmas: five transported and one unchanged must pass ({lemmaPlans.toList})"
  IO.println s!"[clique-ownership] carried-lemma units: {lemmaCases.size}, passing by plan {lemmaPlans.toList.mergeSort (fun a b => a.1 < b.1)}"
  match equationRegenerationChecks env eqn with
  | .error e => failures := failures.push s!"equation regeneration: {e}"
  | .ok (fs, summary) =>
    IO.println s!"[clique-ownership] {summary}"
    failures := failures ++ fs
  -- the structural memo is keyed by the ownership mode
  match memoByMode env eqn with
  | .error e =>
    IO.println s!"[clique-ownership]   FAIL memo: {e}"
    failures := failures.push s!"memo: {e}"
  | .ok (fs, summary) =>
    IO.println s!"[clique-ownership] {summary}"
    for f in fs do IO.println s!"[clique-ownership]   FAIL {f}"
    failures := failures ++ fs
  IO.println s!"[clique-ownership] {cases.size} cases: {transported} transported, {kept} kept in Lean's form, {failures.size} failure(s)"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.CliqueOwnership
