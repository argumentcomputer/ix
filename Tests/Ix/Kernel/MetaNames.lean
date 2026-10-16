import Ix.Meta
import Ix.CompileM
import Tests.Ix.Kernel.SourceIngressStep
import Benchmarks.Kernel.CheckIxeMeta
import Ix.KernelDisplay.MetaNames
import Ix.KernelDisplay.Peek
import Tests.Ix.Kernel.MetaNamesFixtures

/-! # `kernel-meta-names`: `.meta` and `.source` names against Lean (IxC step 6b)

The oracle of step 6b's names. A small Lean environment (`Init` and
`Tests.Ix.Kernel.MetaNamesFixtures`) and five ill-typed declarations built
here (they cannot be elaborated) are checked three ways:

* **Lean**: the kernel (`Environment.addDeclCore`) rejects each ill-typed
  declaration with an exception holding terms; Lean's `ppExpr` prints them in
  the exception's local context, under the renderer's options (`ppOpts`);
* **`.meta`**: the closure is compiled by Ix's compiler (Rust, through FFI;
  it does not type-check) with its metadata, read at `.meta`, named from the
  metadata (`Ix.KernelDisplay.nameRead`) and checked, as
  `kernel-check-ixe --meta` does;
* **`.source`**: the same constants through the Source ingress, which names
  binders from the Lean terms (`Ix.LeanIngress.nameExprs`), and checked group
  by group, as `kernel-source-ingress` does.

It compares, whitespace-normalized:

* **messages**: each failure's terms, printed with names
  (`Ix.KernelDisplay.renderFailure`), against the terms of Lean's exception
  in the same roles: an application type mismatch's argument type and expected
  domain (names flowing through inference, β and instantiation; a free
  variable named by the binder the failure was thrown under), a declaration
  type mismatch's inferred and declared types, and an "expected a sort"
  failure's type after δ (`Lean.Kernel.whnf`), whose binder names are the
  unfolded definition's;
* **terms**: every fixture's type and value as `.meta` and `.source` hold
  them, printed, against `ppExpr` of Lean's;
* **the CLI**: `kernel-check-ixe --meta` on the compiled closure, whose rows
  carry the same printed failures.

`unsafe`: it prints names through the display-only read
(`Ix.KernelDisplay.Peek`). Run with `lake exe kernel-meta-names` (it imports
`Init` and the fixtures from this toolchain's and the build's `.olean` files). -/

namespace Tests.Ix.Kernel.MetaNames

open Lean Meta
open Ix.Kernel.Reader (ReadError State Read CDecl CName Prelude DisplayTable)
open Benchmarks.Kernel.CheckIxeStep (Checker)

/-! ## Lean's side -/

/-- `ppExpr`'s options for the comparison: Lean's defaults, except what the
renderer cannot do without Lean's elaborator (`Ix.KernelDisplay.Render`). -/
def ppOpts : Options := ({} : Options)
  |>.setBool `pp.notation false |>.setBool `pp.fullNames true |>.setBool `pp.proofs true
  |>.setBool `pp.coercions false |>.setBool `pp.fieldNotation false
  |>.setBool `pp.structureInstances false |>.setBool `pp.match false
  |>.set `format.width (100000 : Nat)

/-- Whitespace runs as one space. -/
def norm (s : String) : String :=
  " ".intercalate (((s.map fun c => if c.isWhitespace then ' ' else c).splitOn " ").filter
    (!·.isEmpty))

/-- Lean's `ppExpr` of `e` in the local context `lctx`. -/
def pp (env : Environment) (lctx : LocalContext) (e : Expr) : IO String := do
  let ctx : Core.Context := { fileName := "<kernel-meta-names>", fileMap := default, options := ppOpts }
  let st : Core.State := { env }
  let (fmt, _) ← ((withLCtx lctx {} (PrettyPrinter.ppExpr e)).run' {} {}).toIO ctx st
  return norm (toString fmt)

def natE : Expr := mkConst ``Nat
def rflE (a : Expr) : Expr := mkApp2 (mkConst ``rfl [Level.one]) natE a
def eqE (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) natE a b
def fx (n : String) : Name := (`MetaNamesFixtures).str n

/-- **The ill-typed declarations**, each with the roles its failure is compared
in. -/
def bad (env : Environment) : List (Name × Expr × Expr) :=
  let succTy := match (env.find? (fx "needsSucc")).map (·.type) with
    | some (.forallE _ d _ _) => d
    | _ => mkConst ``True
  [ -- an argument's type through inference: `∀ (j : Nat), j = j` for `∀ k, k = k + 1`
    (`MetaNamesBad.app, mkConst ``True,
      mkApp (mkConst (fx "needsSucc")) (mkLambda `j .default natE (rflE (.bvar 0)))),
    -- through β: `(fun F => F) (fun s => rfl)` has `F`'s type, `∀ (r : Nat), r = r`
    (`MetaNamesBad.beta, mkConst ``True,
      mkApp (mkConst (fx "needsSucc"))
        (mkApp (mkLambda `F .default (mkForall `r .default natE (eqE (.bvar 0) (.bvar 0))) (.bvar 0))
          (mkLambda `s .default natE (rflE (.bvar 0))))),
    -- a free variable named by its binder: `cnt : Nat` where a `Bool` is wanted
    (`MetaNamesBad.fvar, mkForall `n .default natE (mkConst ``True),
      mkLambda `cnt .default natE (mkApp (mkConst (fx "needsBool")) (.bvar 0))),
    -- a declaration type mismatch: `∀ (q : Nat), q = q` for `∀ (k : Nat), k = k + 1`
    (`MetaNamesBad.type, succTy, mkLambda `q .default natE (rflE (.bvar 0))),
    -- a "type" whose type unfolds (δ) to a Π with the definition's names
    (`MetaNamesBad.sort, mkConst (fx "polyId"), mkNatLit 0)]

/-- A declaration's constant. -/
def defnOf (n : Name) (ty v : Expr) : ConstantInfo :=
  .defnInfo {
    name := n, levelParams := [], type := ty, value := v,
    hints := ReducibilityHints.opaque, safety := .safe, all := [n] }

/-- What Lean's kernel says of an ill-typed declaration: the roles and the
printed terms, in IxC's role names. -/
def leanRoles (env : Environment) (n : Name) (ty v : Expr) : IO (List (String × String)) := do
  let decl : Declaration := .defnDecl {
    name := n, levelParams := [], type := ty, value := v,
    hints := ReducibilityHints.opaque, safety := .safe }
  match env.addDeclCore 0 10000 decl none with
  | .ok _ => throw (IO.userError s!"{n}: Lean's kernel accepts it")
  | .error (.appTypeMismatch _ lctx e fnType argType) =>
    let dom := match fnType with | .forallE _ d _ _ => d | t => t
    return [("argument", ← pp env lctx e.appArg!), ("argument has type", ← pp env lctx argType),
      ("but is expected to have type", ← pp env lctx dom)]
  | .error (.declTypeMismatch _ _ given) =>
    return [("has type", ← pp env {} given), ("but is expected to have type", ← pp env {} ty)]
  | .error (.typeExpected _ lctx e) =>
    let t ← (((Meta.inferType e).run' {} {}).toIO
      { fileName := "<kernel-meta-names>", fileMap := default } { env }).map (·.1)
    match Lean.Kernel.whnf env lctx t with
    | .ok w => return [("got", ← pp env lctx w)]
    | .error _ => throw (IO.userError s!"{n}: Lean's whnf fails")
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    throw (IO.userError s!"{n}: unexpected kernel exception {msg}")

/-! ## IxC's side -/

/-- The roles and printed terms of a failure, from its rendering (a role line,
then its term indented). -/
def rolesOf (rendered : String) : List (String × String) :=
  let lines := (rendered.splitOn "\n").drop 1
  let rec go : List String → List (String × String)
    | role :: term :: rest => (role, norm term) :: go rest
    | _ => []
  go lines

/-- An `Ix.Kernel.Name` as Lean's. -/
def toLean (n : Ix.Kernel.Name) : Name := Ix.KernelDisplay.leanName n

/-- What a check produced: per Lean name, its failure rendered with names,
and the printed type and value of each declaration. -/
structure Seen where
  failures : Std.HashMap Name String := {}
  terms : Std.HashMap Name (String × Option String) := {}

/-- **`.meta`**: the compiled closure read with names and checked, record by
record (`kernel-check-ixe --meta`'s loop). -/
unsafe def metaSide (path : System.FilePath) (wanted : Name → Bool) : IO Seen := do
  let bytes ← IO.FS.readBinFile path
  let env ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let preA : Prelude .anon ← IO.ofExcept (Ix.Kernel.Reader.preludeFor table)
  let preM : Prelude .meta ← IO.ofExcept (Ix.Kernel.Reader.preludeFor table)
  let hints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store env.anonHints
  let s := Benchmarks.Kernel.CheckIxeStep.setup store (env.blobs[·]?) table preA hints.lookup
  let (cxM, evM) := Benchmarks.Kernel.CheckIxeMeta.metaContext s (env.blobs[·]?) table preM hints.lookup
  let display := Benchmarks.Kernel.CheckIxeMeta.displayTable env cxM
  let nc : Ix.KernelDisplay.NameCx := ⟨env.names, Ix.KernelDisplay.metaTable env cxM⟩
  let nameOf (k : Ix.Kernel.Key .meta) : Option Name :=
    display[k]? |>.bind fun (d, _) => d.names.head?.map toLean
  let mut st : State .meta := {}
  let mut cm : Checker .meta := {}
  let mut seen : Seen := {}
  let mut types : Std.HashMap (Ix.Kernel.Key .meta) (Ix.Kernel.Expr .meta) := {}
  for address in s.ordered do
    let some source := s.store[address]? | continue
    let rdE := Ix.Kernel.Reader.readRecord cxM st address source
    if let .error e := rdE then
      IO.println s!"  meta: record {address} ({(env.addrToName[address]?).map toString}) refused: {e}"
    let .ok rd := rdE | continue
    let rd := Benchmarks.Kernel.CheckIxeMeta.withDisplay display rd
    let (rd, _, _) := Ix.KernelDisplay.nameRead nc rd
    st := st.commit rd
    for (k, t) in Ix.KernelDisplay.declTypes rd.decls do types := types.insert k t
    let levelNames := match (rd.display.find? fun (_, d) => !d.levelNames.isEmpty) with
      | some (_, d) => d.levelNames
      | none => []
    let base := Ix.KernelDisplay.metaCx display cm.fe levelNames types
    let rcx := { base with peek := Ix.KernelDisplay.peekAll }
    for d in rd.decls do
      match d with
      | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
        if let some n := nameOf cv.name then
          if wanted n then
            let printed := (norm (Ix.KernelDisplay.renderTerm rcx cv.type),
              some (norm (Ix.KernelDisplay.renderTerm rcx v)))
            seen := { seen with terms := seen.terms.insert n printed }
      | _ => pure ()
    let (cm', e) := cm.steps evM rd.decls
    cm := cm'
    if let some e := e then
      let ns := (rd.decls.toList.flatMap Benchmarks.Kernel.CheckIxeMeta.declaredKeys).filterMap nameOf
      unless ns.any wanted do IO.println s!"  meta: {ns.take 3} fails: {e}"
      for k in rd.decls.toList.flatMap Benchmarks.Kernel.CheckIxeMeta.declaredKeys do
        if let some n := nameOf k then
          let base := Ix.KernelDisplay.metaCx display cm'.fe levelNames types
          let printed := Ix.KernelDisplay.renderFailure
            { base with peek := Ix.KernelDisplay.peekAll,
                        msgSpell := some (Ix.Kernel.Reader.spellWith display) } e
          seen := { seen with failures := seen.failures.insert n printed }
  return seen

/-- **`.source`**: the constants through the Source ingress, group by group
(`kernel-source-ingress`'s loop), every declaration checked. -/
unsafe def sourceSide (consts : Array (Name × ConstantInfo)) (leanEnv : Environment)
    (wanted : Name → Bool) : IO Seen := do
  let env := Tests.Ix.Kernel.SourceIngressStep.canon consts
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let groups := Ix.LeanIngress.groupsOf env blocks
  let converted := Tests.Ix.Kernel.SourceIngressStep.convertAll groups 1
  let g := Ix.LeanIngress.graphOf blocks groups converted
  let sched := Ix.LeanIngress.scheduleOf g
  let pre : Prelude .source ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let mut st : State .source := pre.state
  let mut lowered : Array (CDecl .source) := #[]
  for (gi, c) in sched do
    match c >>= fun c => Ix.LeanIngress.lower st c with
    | .ok r =>
      st := st.commit r
      lowered := lowered ++ r.decls
    | .error e => IO.println s!"  source: group {gi} ({groups[gi]!.names.toList.take 3}) refused: {e}"
  let prepared := Ix.Kernel.Frontend.preparePrelude pre.ix lowered
  let (ev, _) := Ix.LeanIngress.sourceEvidenceReport prepared
  let levelNamesOf (n : Name) : List Ix.Kernel.Name :=
    match leanEnv.find? n with
    | some ci => ci.levelParams.map Ix.Kernel.Name.ofLeanName
    | none => []
  let types : Std.HashMap (Ix.Kernel.Key .source) (Ix.Kernel.Expr .source) :=
    (Ix.KernelDisplay.declTypes prepared).foldl (fun m (k, t) => m.insert k t) {}
  let cxOf (fe : Ix.Kernel.FEnv .source) (n : Name) : Ix.KernelDisplay.Cx .source :=
    { peek := Ix.KernelDisplay.peekAll
      spell := fun k => Ix.KernelDisplay.nameStr (toLean k.toName)
      levelName := fun i => match (levelNamesOf n)[i]? with
        | some l => Ix.KernelDisplay.nameStr (toLean l)
        | none => s!"u_{i + 1}"
      constType := fun k => types[k]? <|> (fe.find? k).map (·.toConstantVal.type) }
  let mut checker : Checker .source := {}
  let mut seen : Seen := {}
  for d in prepared do
    let names := (Benchmarks.Kernel.CheckIxeMeta.declaredKeys d).map fun k => toLean k.toName
    for n in names do
      if wanted n then
        match d with
        | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
          let rcx := cxOf checker.fe n
          let printed := (norm (Ix.KernelDisplay.renderTerm rcx cv.type),
            some (norm (Ix.KernelDisplay.renderTerm rcx v)))
          seen := { seen with terms := seen.terms.insert n printed }
        | _ => pure ()
    let before := checker.fe
    let (c', err) := checker.step ev d
    checker := c'
    if let some e := err then
      unless names.any wanted do IO.println s!"  source: {names.take 3} fails: {e}"
      for n in names do
        let printed := Ix.KernelDisplay.renderFailure (cxOf before n) e
        seen := { seen with failures := seen.failures.insert n printed }
  return seen

/-- The dependency closure of `roots`, with every inductive's recursors (a
block is read with its recursors) and theirs. -/
def closure (env : Environment) (roots : Array Name) : List (Name × ConstantInfo) := Id.run do
  let mut deps := Lean.collectDependenciesMany roots env.constants
  for _ in [0:8] do
    let recs := deps.foldl (init := #[]) fun acc (_, ci) =>
      match ci with
      | .inductInfo v =>
        let names := (mkRecName v.name) ::
          (List.range v.numNested).map fun i => v.name.str s!"rec_{i + 1}"
        acc ++ (names.filter fun r => env.contains r && !deps.any (·.1 == r)).toArray
      | _ => acc
    if recs.isEmpty then break
    deps := Lean.collectDependenciesMany (roots ++ recs ++ (deps.map (·.1)).toArray) env.constants
  return deps

/-! ## The comparison -/

unsafe def main (_args : List String) : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Init, `Tests.Ix.Kernel.MetaNamesFixtures]
  let bads := bad leanEnv
  let fixtures := leanEnv.constants.toList.filterMap fun (n, ci) =>
    if (`MetaNamesFixtures).isPrefixOf n && !n.isInternal then some (n, ci) else none
  let roots := (fixtures.map (·.1)).toArray ++ #[``True, ``Nat, ``Bool, ``rfl, ``Eq]
  let deps := closure leanEnv roots
  let consts := deps.toArray ++ (bads.map fun (n, ty, v) => (n, defnOf n ty v)).toArray
  let wanted (n : Name) : Bool := (`MetaNamesFixtures).isPrefixOf n || (`MetaNamesBad).isPrefixOf n
  IO.println s!"kernel-meta-names: {fixtures.length} fixtures, {bads.length} ill-typed \
    declarations, {consts.size} constants"
  -- `.meta`: compiled with the metadata, read, named, checked
  let dir ← IO.FS.createTempDir
  let path := dir / "meta-names.ixe"
  let status ← Ix.CompileM.rsCompileEnvBytesFFI consts.toList path.toString true
  unless status.ungrounded.isEmpty do
    IO.println s!"kernel-meta-names: {status.ungrounded.size} constants not compiled: \
      {status.ungrounded.toList.take 5}"
  let metaSeen ← metaSide path wanted
  let sourceSeen ← sourceSide consts leanEnv wanted
  let mut failures := 0
  let mut checks := 0
  -- `.meta` keys are addresses: the members of an alias fiber (α-equivalent
  -- constants, one address) print as its first name (a known limitation)
  let ixe ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  let fibers := ixe.named.toList.foldl (init := ({} : Std.HashMap Address (List String)))
    fun m (n, named) => m.insert named.addr (toString n :: m.getD named.addr [])
  let aliases : List (String × String) := fibers.toList.flatMap fun (_, ns) =>
    let ns := ns.toArray.qsort (· < ·) |>.toList
    match ns with
    | first :: rest => rest.map (·, first)
    | [] => []
  let check (what ours lean : String) (isMeta : Bool) : StateT (Nat × Nat) IO Unit := do
    modify fun (c, f) => (c + 1, f)
    let leanAliased := aliases.foldl (fun s (m, f) => s.replace m f) lean
    if ours == lean then IO.println s!"  ok   {what}: {ours}"
    else if isMeta && ours == leanAliased then
      IO.println s!"  ok   {what} (alias fiber printed by its first name): {ours}\n         Lean {lean}"
    else
      IO.println s!"  FAIL {what}:\n         ours {ours}\n         Lean {lean}"
      modify fun (c, f) => (c, f + 1)
  let run : StateT (Nat × Nat) IO Unit := do
    -- messages
    for (n, ty, v) in bads do
      let lean ← leanRoles leanEnv n ty v
      for (mode, seen) in [("meta", metaSeen), ("source", sourceSeen)] do
        match seen.failures[n]? with
        | none => check s!"{mode} {n} fails" "accepted" "a failure" false
        | some r =>
          IO.println s!"  {mode} {n}: {r.replace "\n" " ⏎ "}"
          let ours := rolesOf r
          for (role, leanTerm) in lean do
            check s!"{mode} {n} [{role}]" ((ours.lookup role).getD "(no such role)") leanTerm
              (mode == "meta")
    -- terms
    for (n, ci) in fixtures do
      let leanTy ← pp leanEnv {} ci.type
      let leanV ← match ci.value? (allowOpaque := true) with
        | some v => some <$> pp leanEnv {} v
        | none => pure none
      for (mode, seen) in [("meta", metaSeen), ("source", sourceSeen)] do
        match seen.terms[n]? with
        | none => pure ()
        | some (ty, v) =>
          check s!"{mode} {n} type" ty leanTy (mode == "meta")
          if let (some v, some lv) := (v, leanV) then
            check s!"{mode} {n} value" v lv (mode == "meta")
  let ((), (c, f)) ← run.run (0, 0)
  checks := c
  failures := f
  -- the CLI prints the same failures
  let rows := dir / "meta-names.jsonl"
  let code ← Benchmarks.Kernel.CheckIxeMeta.run [path.toString, rows.toString]
  let text ← IO.FS.readFile rows
  let mut cli := 0
  for (n, _, _) in bads do
    if let some r := metaSeen.failures[n]? then
      checks := checks + 1
      let line := (text.splitOn "\n").find? fun l => (l.splitOn s!"\"{n}\"").length > 1
      let carried : Bool := match line with
        | some l => (l.splitOn (Lean.Json.compress (Lean.Json.str r))).length > 1
        | none => false
      if carried then
        cli := cli + 1
      else
        failures := failures + 1
        IO.println s!"  FAIL cli {n}: the row does not carry the printed failure; row {line}"
  IO.FS.removeDirAll dir
  IO.println s!"kernel-meta-names: {checks} checks, {failures} failed; CLI rows {cli}/{bads.length}, \
    erasure run exit {code}"
  return if failures == 0 && code == 0 then 0 else 1

end Tests.Ix.Kernel.MetaNames

unsafe def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.MetaNames.main args
