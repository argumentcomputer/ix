import Ix.CompileCert.StrongCertifier
import Ix.CompileDriver
import Tests.Ix.CompileCert.Strong
import Tests.Ix.CompileCert.ChangedValueDefs

/-! # S at the value level for changed constants (M7 S+a)

`compile-certify --strong` (`Strong.runStrong` with the default `strongChanged`) decides, after
the strong cones, the constants W certifies by a W+ route outside a changed inductive block and
their users, at the value level (`decideStrongCone'`, `StrongCone'.sound`,
`Ix/CompileCert/StrongChanged.lean`). Checks, run in-process on real compiler output:

1. **`ChangedValueDefs`** (a theorem clique in both member orders, compiled here under Pass 3 into
   `value-cones.ixe`): the transported clique's members are W-certified by the `theorem` route;
   with `strongChanged := false` (the control) they are S-unsupported with WP-C's class and
   their users S-blocked; with the default every one of them and every user is S-certified by a
   value cone, and every other verdict and cause is the control's. Nothing is S-rejected.
2. **`ChangedDefs`** (`changed.ixe`, the W+ fixture: changed blocks, image recursors, type rows,
   a transported well-founded clique): no W+ constant keeps WP-C's class; each one over a changed
   inductive block is S-unsupported with the S+b class, each transported member W certifies by its
   `eq_def` only with package V's class, and every W-certified constant they keep out is S-blocked
   by one of them with that class; each member W certifies by a value row (package V) is S-certified by
   a value cone; the strong verdicts are unchanged; nothing is S-rejected.
   **Negatives**, beside it, in two runs: the transported members claimed by value rows they do not
   have (routes forged to `equations:rfl`, rows dropped). Those with Lean's `eq_def` keep W+'s `eq_def`
   route, so their cone's W+ association accepts and the **value check** refuses it (definitions); those
   without one have no W+ route left, so their cone's **W+ association** refuses it. Each refusal is
   asserted at its stage, and none of them is S-certified.
3. **The value check on a cone's real environments** (`BlockDefs.first`, installed source and
   admitted target as the certifier builds them): the target's definition replaced by a
   convertible value (`(λ x. x) a` for `a`), folded by the certified checker: refused without a
   row; accepted with a theorem row `@Eq T first v` (`v` the export of Lean's value, proof
   `Eq.refl`, checked by the fold); **a forged row** (a true equation the fold accepts, stating the
   replaced value) refused; a row stating a value the definition does not have refused by the fold
   itself. The unmutated target is accepted without a row (the neighbour). -/

namespace Tests.Ix.CompileCert.StrongChangedValues

open _root_.Ix.CompileCert _root_.Ix.CompileCert.Certifier _root_.Ix.CompileCert.Strong
open Benchmarks.Kernel.CheckIxeStep

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"strong changed values check failed: {label}")
  IO.println s!"PASS: {label}"

/-- The rows of a TSV file without its header, split at tabs. -/
def rowsOf (path : System.FilePath) : IO (Array (Array String)) := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter (· ≠ "")
  return (lines.drop 1).toArray.map fun l => (l.splitOn "\t").toArray

def cell (row : Array String) (i : Nat) : String := row.getD i ""

/-- name ↦ (S verdict, cause) from `<prefix>.strong.tsv`. -/
def sVerdicts (pre : String) : IO (Std.HashMap String (String × String)) := do
  let rows ← rowsOf s!"{pre}.strong.tsv"
  return rows.foldl (fun m r => m.insert (cell r 0) (cell r 2, cell r 3)) {}

/-- W's certified constants and their routes from `<prefix>.tsv`. -/
def wRoutes (pre : String) : IO (Array (String × String)) := do
  let rows ← rowsOf s!"{pre}.tsv"
  return (rows.filter (cell · 2 == "certified")).map fun r => (cell r 0, cell r 3)

def isValueCone (v : String × String) : Bool := v.1 == "S-certified" && v.2.startsWith "value cone "

def valuePrefix : Lean.Name := `Tests.Ix.CompileCert.ChangedValueDefs

def valueRoots : List Lean.Name :=
  [`TC0.use_ta, `TC0.useInDef_eq, `TC1.use_ta, `TC1.useInDef_eq].map (valuePrefix ++ ·)

/-- Compile the theorem-clique fixture under Pass 3 and write `value-cones.ixe`. -/
def compileValues (dir : String) : IO String := do
  let env ← getCompileEnv #[valuePrefix]
  let captured ← IO.ofExcept (captureCone env.find? valueRoots 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  let path := s!"{dir}/value-cones.ixe"
  IO.FS.createDirAll dir
  IO.FS.writeBinFile path compiled.bytes
  IO.println s!"compiled {captured.source.declarations.length} declarations: {compiled.bytes.size} bytes"
  return path

/-- Check 1: the transported theorem clique and its users, S-certified at the value level. -/
def valuesFixture (dir : String) : IO String := do
  let ixe ← compileValues dir
  let base : Config :=
    { lean := .modules #[valuePrefix], ixe, out := s!"{dir}/strong-changed-values",
      strong := true, workers := 4, strongTasks := 4 }
  let (_, some w) ← runW base | throw (IO.userError "W produced no state")
  let routes ← wRoutes base.out
  let theoremRoute := (routes.filter (·.2 == "theorem")).map (·.1)
  require s!"the fixture has {theoremRoute.size} constants W certifies by the theorem route (the transported clique)"
    (theoremRoute.size > 0)
  let isTheorem : Std.HashSet String := theoremRoute.foldl (·.insert ·) {}
  -- the direct/raw-only control; the positive run below uses the default.
  let _ ← runStrong { base with strongChanged := false } w
  let s0 ← sVerdicts base.out
  require s!"control with strongChanged disabled: each of the {theoremRoute.size} is S-unsupported ({wPlusClass})"
    (theoremRoute.all fun n => s0.getD n ("", "") == ("S-unsupported", wPlusClass))
  let blocked0 := (routes.map (·.1)).filter fun n => match s0[n]? with
    | some ("S-blocked", cause) => match cause.splitOn s!": {wPlusClass}" with
      | [dep, ""] => isTheorem.contains dep
      | _ => false
    | _ => false
  require s!"control with strongChanged disabled: {blocked0.size} users S-blocked by them" (blocked0.size > 0)
  -- No explicit strongChanged override: this checks the shipped default.
  let on := { base with out := s!"{dir}/strong-changed-values-on" }
  let code ← runStrong on w
  let s1 ← sVerdicts on.out
  require s!"default value-level S: each of the {theoremRoute.size} S-certified by a value cone"
    (theoremRoute.all fun n => isValueCone (s1.getD n ("", "")))
  require s!"default value-level S: each of the {blocked0.size} users S-certified by a value cone"
    (blocked0.all fun n => isValueCone (s1.getD n ("", "")))
  let changedNames : Std.HashSet String := (theoremRoute ++ blocked0).foldl (·.insert ·) {}
  let others := s0.toList.filter fun (n, _) => !changedNames.contains n
  require s!"every other verdict and cause ({others.length}) is the control's"
    (others.all fun (n, v) => s1[n]? == some v)
  require "nothing S-rejected; exit 0" (code == 0 && s1.toList.all fun (_, v) => v.1 != "S-rejected")
  return s!"{theoremRoute.size} transported theorems and {blocked0.size} users S-certified at the value level \
    ({others.length} other verdicts unchanged)"

/-- Check 2: the W+ fixture: the classes that remain, and a forged route label refused. -/
def changedFixture (ixe dir : String) : IO String := do
  let base : Config :=
    { lean := .modules #[`Tests.Ix.CompileCert.ChangedDefs], ixe, out := s!"{dir}/strong-changed-values-cd",
      strong := true, workers := 4, strongTasks := 4 }
  let (_, some w) ← runW base | throw (IO.userError "W produced no state")
  let routes ← wRoutes base.out
  let wPlus := routes.filter fun (_, r) => !(r == "" || sRoute r)
  let isWPlus : Std.HashSet String := wPlus.foldl (fun s (n, _) => s.insert n) {}
  let _ ← runStrong { base with strongChanged := false } w
  let s0 ← sVerdicts base.out
  let on := { base with out := s!"{dir}/strong-changed-values-cd-on" }
  let code ← runStrong on w
  let s1 ← sVerdicts on.out
  require s!"the W+ fixture has {wPlus.size} W+ constants; none keeps the class {wPlusClass}"
    (wPlus.size > 0 && wPlus.all fun (n, _) => (s1.getD n ("", "")).2 != wPlusClass)
  let block := wPlus.filter fun (n, _) => s1.getD n ("", "") == ("S-unsupported", changedBlockClass)
  let member := wPlus.filter fun (n, _) => s1.getD n ("", "") == ("S-unsupported", valueRowClass)
  let value := wPlus.filter fun (n, _) => isValueCone (s1.getD n ("", ""))
  let blockedW := wPlus.filter fun (n, _) => (s1.getD n ("", "")).1 == "S-blocked"
  require s!"{block.size} over a changed inductive block (S+b) and {member.size} transported members by eq_def only \
    (package V) S-unsupported with their classes; {value.size} S-certified at the value level; {blockedW.size} \
    S-blocked; nothing else" (block.size > 0 &&
      block.size + member.size + value.size + blockedW.size == wPlus.size)
  require "every changed-block route and every recursor is in the S+b class, every eq_def route in package V's"
    (wPlus.all fun (n, r) =>
      let v := s1.getD n ("", "")
      if (r.splitOn "changed-block").length > 1 then v == ("S-unsupported", changedBlockClass)
      else if r.startsWith "equations:eq_def" then v == ("S-unsupported", valueRowClass)
      else true)
  let sbOrV (cause : String) : Bool :=
    match cause.splitOn s!": {changedBlockClass}", cause.splitOn s!": {valueRowClass}" with
    | [dep, ""], _ | _, [dep, ""] => isWPlus.contains dep
    | _, _ => false
  let blockedAll := s1.toList.filter fun (_, v) => v.1 == "S-blocked"
  let blockedByChanged := blockedAll.filter fun (_, v) => sbOrV v.2
  let blockedOther := blockedAll.filter fun (n, v) => !sbOrV v.2 && s0[n]? != some v
  require s!"{blockedByChanged.length} constants S-blocked by a W+ constant with its class named; every other \
    S-blocked verdict is the control's" (blockedByChanged.length > 0 && blockedOther.isEmpty)
  let strongBefore := s0.toList.filter fun (_, v) => v.1 == "S-certified"
  require s!"the {strongBefore.length} strong verdicts unchanged" (strongBefore.all fun (n, v) => s1[n]? == some v)
  require "nothing S-rejected; exit 0" (code == 0 && s1.toList.all fun (_, v) => v.1 != "S-rejected")
  -- package V's value rows: every member W certifies by its value row is S-certified by a value cone
  -- (the value check reads the row: the member's target value is not Lean's)
  let valueRowRoute := wPlus.filter fun (_, r) => r.startsWith "equations:value-row"
  require s!"{valueRowRoute.size} transported members W certifies by a value row (package V): each S-certified by a \
    value cone" (valueRowRoute.size > 0 && valueRowRoute.all fun (n, _) => isValueCone (s1.getD n ("", "")))
  -- negatives, beside it: the transported members claimed by value rows they do not have (their routes
  -- forged to `equations:rfl`, their rows dropped), in two runs, each refused at its own stage. A member
  -- with Lean's `eq_def` still has W+'s `eq_def` route, so its cone's W+ association accepts and the
  -- **value check** refuses it (definitions: the target value is not Lean's and no row states Lean's); a
  -- member without one has no W+ route left, so its cone's **W+ association** refuses it (the row is not
  -- in the fold). Each root's own cone after a refused value cone is refused too. None is S-certified.
  let leanOf : Std.HashMap String Lean.Name := w.names.foldl (fun m n => m.insert (toString n) n) {}
  let hasEqDef (n : String) : Bool := match leanOf[n]? with
    | some ln => (w.env.find? (ln.str "eq_def")).isSome
    | none => false
  let transported := (wPlus.filter fun (_, r) =>
    r.startsWith "equations:eq_def" || r.startsWith "equations:value-row").map (·.1)
  let withEqDef := transported.filter hasEqDef
  let withoutEqDef := transported.filter (!hasEqDef ·)
  require s!"the W+ fixture has {withEqDef.size} transported members with Lean's eq_def and {withoutEqDef.size} \
    without (certified by their value rows) to forge" (withEqDef.size > 0 && withoutEqDef.size > 0)
  let forgedRun (tag : String) (names : Array String) :
      IO (Std.HashMap String (String × String) × Array (Array String)) := do
    let forgedRoutes := w.names.foldl (fun m n =>
      if names.contains (toString n) then m.insert n "equations:rfl" else m) w.routes
    let forgedRows := w.names.foldl (fun m n => if names.contains (toString n) then m.erase n else m) w.rowsOf
    let cfg := { on with out := s!"{dir}/strong-changed-values-cd-forged-{tag}" }
    let _ ← runStrong cfg { w with routes := forgedRoutes, rowsOf := forgedRows }
    return (← sVerdicts cfg.out, ← rowsOf s!"{cfg.out}.strong.cones.tsv")
  let refusedAt (cones : Array (Array String)) (names : Array String) (stage : String) : Array String :=
    (cones.filter fun r => cell r 12 == "failed" && (cell r 13).startsWith stage && names.contains (cell r 14)).map
      fun r => s!"{cell r 13} at {cell r 14}"
  let neverCertified (s : Std.HashMap String (String × String)) (names : Array String) : Bool :=
    names.all fun n =>
      let v := s.getD n ("", "")
      (v.1 == "S-rejected" || v.1 == "S-blocked") && !isValueCone v
  let honest (names : Array String) : Bool :=
    names.all fun n => s1.getD n ("", "") == ("S-unsupported", valueRowClass) || isValueCone (s1.getD n ("", ""))
  let (sA, conesA) ← forgedRun "eqdef" withEqDef
  let atValueCheck := refusedAt conesA withEqDef "value check: definitions"
  require s!"forged (members with Lean's eq_def, {withEqDef.size}): their value cone refused by the value check \
    ({atValueCheck.toList.take 1}), none S-certified, each S-rejected or S-blocked; their honest neighbour: package \
    V's class or a value cone"
    (atValueCheck.size > 0 && neverCertified sA withEqDef && honest withEqDef)
  let (sB, conesB) ← forgedRun "noeqdef" withoutEqDef
  let atAssociation := refusedAt conesB withoutEqDef "cone W+ association refused"
  require s!"forged (members without an eq_def, {withoutEqDef.size}): their value cone refused by its W+ association \
    ({atAssociation.toList.take 1}), none S-certified, each S-rejected or S-blocked; their honest neighbour: a value \
    cone"
    (atAssociation.size > 0 && neverCertified sB withoutEqDef &&
      withoutEqDef.all fun n => isValueCone (s1.getD n ("", "")))
  return s!"{block.size} S+b and {member.size} package-V W+ constants classed, {valueRowRoute.size} value-row members \
    S-certified, {blockedByChanged.length} users S-blocked by them, strong verdicts unchanged; forged value-row claims \
    refused (by the value check with an eq_def, by the W+ association without)"

/-- `λ α a b, (λ x : α, x) a` for `λ α a b, a` (a convertible value). -/
def betaBody : _root_.Ix.Kernel.Expr → Option _root_.Ix.Kernel.Expr
  | .lam d1 (.lam d2 (.lam d3 (.bvar 1) m3) m2) m1 =>
    some (.lam d1 (.lam d2 (.lam d3 (.app (.lam (.bvar 2) (.bvar 0) m2) (.bvar 1)) m3) m2) m1)
  | _ => none

/-- Check 3: the value check on the cone of `BlockDefs.first`, its target mutated and folded. -/
def checkLevel : IO String := do
  let fx ← Tests.Ix.CompileCert.Strong.fixture
  let first := Tests.Ix.CompileCert.Compiled.prefixName ++ `first
  let p ← fx.pieces first []
  let source := p.installed.env
  let names := p.proposal.names
  let targetFirst := names (sourceName first)
  let never : _root_.Ix.Kernel.Name → _root_.Ix.Kernel.Name := fun n => n.str "_ix_no_row"
  let pins ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinNatOpPins
  let base := _root_.Ix.Kernel.Frontend.preparePrelude p.accepted.prelude.ix p.accepted.declarations
  let fold (decls : Array _root_.Ix.Kernel.Declaration) := _root_.Ix.Kernel.Cached.checkDecls .verified pins decls
  -- the neighbour: the real admitted target, no row needed
  require "value check: the real environments accepted with no row (the definitions' comparison)"
    (checkChangedAssociationF source p.accepted.env names never)
  -- the target's definition replaced by a convertible value
  let some (header, value) := base.findSome? fun d => match d with
      | .defnDecl h v _ => if h.name == targetFirst then some (h, v) else none
      | _ => none
    | throw (IO.userError s!"no target definition {targetFirst}")
  let some mutated := betaBody value | throw (IO.userError "unexpected shape of first's value")
  let decls := base.map fun d => match d with
    | .defnDecl h _ k => if h.name == targetFirst then .defnDecl h mutated k else d
    | _ => d
  let target1 ← match fold decls with
    | .ok env => pure env
    | .error (e, i) => throw (IO.userError s!"the mutated target was refused at {i}: {(checkOutcome e).2}")
  require "value check: the target definition replaced by a convertible value (folded): refused without a row"
    (!checkChangedAssociationF source target1 names never)
  let level ← IO.ofExcept (checkerSortLevel (_root_.Ix.Kernel.mkFEnv target1) header.type)
  let row (name : String) (right : _root_.Ix.Kernel.Expr) : Option _root_.Ix.Kernel.Declaration :=
    supportRow (targetFirst.str name) header.levelParams
      (kernelEq level header.type (.const targetFirst (header.levelParams.map .param)) right)
  let rowsFor (name : String) : _root_.Ix.Kernel.Name → _root_.Ix.Kernel.Name :=
    fun n => if n == sourceName first then targetFirst.str name else never n
  let some honest := row "_ix_value" value | throw (IO.userError "row shape")
  let target2 ← match fold (decls.push honest) with
    | .ok env => pure env
    | .error (e, i) => throw (IO.userError s!"the honest row was refused at {i}: {(checkOutcome e).2}")
  require "value check: with a theorem row `first = v` (v Lean's value, checked by the fold): accepted"
    (checkChangedAssociationF source target2 names (rowsFor "_ix_value"))
  let some forgedRow := row "_ix_forged" mutated | throw (IO.userError "row shape")
  let target3 ← match fold (decls.push forgedRow) with
    | .ok env => pure env
    | .error (e, i) => throw (IO.userError s!"the forged (true) row was refused at {i}: {(checkOutcome e).2}")
  require "value check: a forged row (`first = (λ x. x) a`-form, true, accepted by the fold): refused"
    (!checkChangedAssociationF source target3 names (rowsFor "_ix_forged"))
  let some wrongRow := row "_ix_wrong" (Tests.Ix.CompileCert.Strong.swapBody 1 0 value) | throw (IO.userError "row shape")
  let refusedByFold := match fold (decls.push wrongRow) with
    | .ok _ => false
    | .error _ => true
  require "value check: a row stating another value (`first = λ α a b, b`) is refused by the certified fold" refusedByFold
  return "value check on real environments: a convertible target value accepted through its row, refused without it, \
    a forged row refused, a false row refused by the fold"

def checks (ixe dir : String) : IO Unit := do
  let a ← valuesFixture dir
  let b ← changedFixture ixe dir
  let c ← checkLevel
  IO.println s!"strong changed values: {a}; {b}; {c}"

/-- The W+ pre-screen may leave tasks running past its report (as `compile-certify` does, the
process exits at once after its report). -/
def run (ixe dir : String) : IO Unit := do
  try
    checks ixe dir
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e =>
    IO.eprintln s!"{e}"
    (← IO.getStdout).flush
    IO.Process.exit 1

end Tests.Ix.CompileCert.StrongChangedValues
