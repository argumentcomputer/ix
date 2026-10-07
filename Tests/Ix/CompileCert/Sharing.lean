import Ix.CompileCert.Indexed

/-! The sharing-aware walks of M5 WP-B in compiled code: `exportExprWithShared`
and `exportExprShared` (substituted for `exportExprWith`/`exportExpr` by
`@[csimp]`), `refsInShared` (for `refsIn`), and the entry comparison
`DirectEntry.decEqShared` (for the derived `DecidableEq`, through
`Kernel.Expr.beqMemo`). Their equality with the tree functions is proved
(`exportExprWithShared_eq`, `exportExprShared_eq`, `refsInShared_eq`,
`DirectEntry.beqShared_iff`); these controls check what a proof cannot: that
compiled callers run the DAG walks (a tower whose tree has 2^66 nodes finishes
within a time limit only if every walk visits a shared node once), and that the
results are the expected terms, with valid neighbours for every negative; and
`treeControls` shows that the towers are huge trees: the derived tree decision on
the same pair does not finish. -/

namespace Tests.Ix.CompileCert.Sharing

open _root_.Ix.CompileCert

abbrev KExpr := _root_.Ix.Kernel.Expr

/-- `x₀ = Sort 0`, `xₖ₊₁ = (fun (_ : xₖ) => #0) xₖ`: 4 nodes per level as a DAG
(the child is the same object twice), a tree of about `2^(k+2)` nodes. -/
def towerL (base : Lean.Expr) : Nat → Lean.Expr
  | 0 => base
  | k + 1 => let x := towerL base k; .app (.lam `y x (.bvar 0) .default) x

/-- Its expected export, built directly (an independent construction). -/
def expectL (base : KExpr) : Nat → KExpr
  | 0 => base
  | k + 1 => let x := expectL base k; .app (.lam x (_root_.Ix.Kernel.Expr.mkBvar 0) ⟨.never⟩) x

/-- `xₖ₊₁ = f xₖ xₖ` over constants. -/
def towerC (leaf : Lean.Name) : Nat → Lean.Expr
  | 0 => .const leaf []
  | k + 1 => let x := towerC leaf k; .app (.app (.const `f []) x) x

def expectC (leaf : Lean.Name) : Nat → KExpr
  | 0 => .const (sourceName leaf) []
  | k + 1 => let x := expectC leaf k; .app (.app (.const (sourceName `f) []) x) x

/-- `xₖ₊₁ = mdata (xₖ xₖ)`: metadata on every shared node. -/
def towerM : Nat → Lean.Expr
  | 0 => .sort .zero
  | k + 1 => let x := towerM k; .mdata {} (.app x x)

def expectM : Nat → KExpr
  | 0 => .sort .zero
  | k + 1 => let x := expectM k; .app x x

/-- A context with empty source and map: enough for terms without constants. -/
def emptyContext : TermContext :=
  { context := { source := ⟨[]⟩, map := [], pins := {} }, sourceLevels := [], targetLevels := [] }

def okIs (r : ExportM KExpr) (expected : KExpr) : Bool :=
  match r with
  | .ok v => _root_.Ix.Kernel.Expr.beq v expected
  | .error _ => false

def errorIs (r : ExportM KExpr) (message : String) : Bool :=
  match r with
  | .ok _ => false
  | .error m => m == message

/-- A tree size beyond any walk: the controls marked "deep" finish only on the DAG. -/
def deep : Nat := 64

def cv (type : KExpr) : _root_.Ix.Kernel.ConstantVal := ⟨sourceName `t, [], type⟩

def controls : List (String × (Unit → Bool)) := [
  ("deep: exportExpr (csimp) of a tower of binders and sorts is the expected term", fun _ =>
    okIs (exportExpr emptyContext (towerL (.sort .zero) deep)) (expectL (.sort .zero) deep)),
  ("deep: exportExprShared directly, the same term", fun _ =>
    okIs (exportExprShared emptyContext (towerL (.sort .zero) deep)) (expectL (.sort .zero) deep)),
  ("deep: exportSourceExpr (exportExprWith, csimp) of a tower of constants", fun _ =>
    okIs (exportSourceExpr [] (towerC `c deep)) (expectC `c deep)),
  ("deep: metadata on shared nodes is erased", fun _ =>
    okIs (exportExpr emptyContext (towerM deep)) (expectM deep)),
  ("deep: a different leaf gives a different term (valid neighbour above)", fun _ =>
    match exportSourceExpr [] (towerC `c deep) with
    | .ok v => !_root_.Ix.Kernel.Expr.beq v (expectC `d deep)
    | .error _ => false),
  ("deep: a free variable at the bottom fails as the tree export does", fun _ =>
    errorIs (exportExpr emptyContext (towerL (.fvar ⟨`x⟩) deep)) "free source variable"),
  ("deep: a metavariable at the bottom fails as the tree export does", fun _ =>
    errorIs (exportSourceExpr [] (towerL (.mvar ⟨`m⟩) deep)) "source metavariable"),
  ("deep: refsIn (csimp) accepts a tower whose constants are all allowed", fun _ =>
    refsIn (fun n => n == `f || n == `c) (towerC `c deep)),
  ("deep: refsIn refuses the same tower without its leaf (valid neighbour above)", fun _ =>
    !refsIn (fun n => n == `f) (towerC `c deep)),
  ("deep: refsIn refuses the same tower without its head", fun _ =>
    !refsIn (fun n => n == `c) (towerC `c deep)),
  ("deep: declRefsIn over a theorem whose proof is the tower", fun _ =>
    declRefsIn (fun n => n == `f || n == `c || n == `t)
      (.thmInfo ⟨⟨`t, [], .sort .zero⟩, towerC `c deep, [`t]⟩)),
  ("deep: declRefsIn refuses it without the leaf", fun _ =>
    !declRefsIn (fun n => n == `f || n == `t)
      (.thmInfo ⟨⟨`t, [], .sort .zero⟩, towerC `c deep, [`t]⟩)),
  ("deep: an exported entry and one built directly compare equal (derived DecidableEq, csimp)", fun _ =>
    match exportSourceExpr [] (towerC `c deep) with
    | .ok v => decide (DirectEntry.thm (cv v) v = DirectEntry.thm (cv (expectC `c deep)) (expectC `c deep))
    | .error _ => false),
  ("deep: as `directAt` compares them (Option)", fun _ =>
    match exportSourceExpr [] (towerC `c deep) with
    | .ok v => decide (some (DirectEntry.thm (cv (.sort .zero)) v) =
      some (DirectEntry.thm (cv (.sort .zero)) (expectC `c deep)))
    | .error _ => false),
  ("deep: entries differing at the bottom leaf compare unequal", fun _ =>
    match exportSourceExpr [] (towerC `c deep) with
    | .ok v => !decide (DirectEntry.thm (cv (.sort .zero)) v =
      DirectEntry.thm (cv (.sort .zero)) (expectC `d deep))
    | .error _ => false),
  ("deep: entries differing in kind compare unequal", fun _ =>
    !decide (DirectEntry.thm (cv (.sort .zero)) (expectC `c deep) =
      DirectEntry.opaque (cv (.sort .zero)) (expectC `c deep))),
  ("recursor entries: rules compared field by field (equal)", fun _ =>
    let rule : _root_.Ix.Kernel.RecRule := ⟨sourceName `k, 2, 0, .inert, expectC `c 8, false, false, false⟩
    decide (DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule, rule] =
      DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule, rule])),
  ("recursor entries: a rule's field count differs", fun _ =>
    let rule : _root_.Ix.Kernel.RecRule := ⟨sourceName `k, 2, 0, .inert, expectC `c 8, false, false, false⟩
    !decide (DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule] =
      DirectEntry.recursor (cv (.sort .zero)) 3 2 [{ rule with nfields := 3 }])),
  ("recursor entries: a rule's right-hand side differs", fun _ =>
    let rule : _root_.Ix.Kernel.RecRule := ⟨sourceName `k, 2, 0, .inert, expectC `c 8, false, false, false⟩
    !decide (DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule] =
      DirectEntry.recursor (cv (.sort .zero)) 3 2 [{ rule with rhs := expectC `d 8 }])),
  ("recursor entries: a missing rule", fun _ =>
    let rule : _root_.Ix.Kernel.RecRule := ⟨sourceName `k, 2, 0, .inert, expectC `c 8, false, false, false⟩
    !decide (DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule, rule] =
      DirectEntry.recursor (cv (.sort .zero)) 3 2 [rule])),
  ("definition entries: hints compared", fun _ =>
    !decide (DirectEntry.defn (cv (.sort .zero)) (expectC `c 4) _root_.Ix.Kernel.ReducibilityHint.opaque =
      DirectEntry.defn (cv (.sort .zero)) (expectC `c 4) _root_.Ix.Kernel.ReducibilityHint.abbrev)),
  ("small: refsIn agrees with the list walk exprRefs", fun _ =>
    let es : List Lean.Expr := [towerC `c 5, towerL (.sort .zero) 5, towerM 5,
      .proj `S 0 (towerC `c 3), .lit (.natVal 3), .lit (.strVal "s"),
      .letE `x (.const `T []) (.const `v []) (.bvar 0) false]
    let ps : List (Lean.Name → Bool) := [fun _ => true, fun n => n != `c, fun n => n != `S,
      fun n => n != `Nat.succ, fun n => n != `Char.ofNat, fun n => n != `v]
    es.all fun e => ps.all fun p => refsIn p e == (exprRefs e).all p)]

/-- Controls that must *not* finish: the tree-walking decision on the same pair, which shows that the
towers above are huge trees (a valid neighbour for every "deep" control). -/
def treeControls : List (String × (Unit → Bool)) := [
  ("the derived tree decision of `Kernel.Expr` on the exported and the built tower does not finish", fun _ =>
    match exportSourceExpr [] (towerC `c deep) with
    | .ok v => @decide (v = expectC `c deep) (_root_.Ix.Kernel.instDecidableEqExpr _ _)
    | .error _ => false)]

/-- Run a control on its own task: its result, or `none` if it does not finish in time. -/
def finishes (ms : UInt32) (control : Unit → Bool) : IO (Option Bool) := do
  let work : Task (Option Bool) := Task.spawn fun _ => some (control ())
  let timer ← IO.asTask (IO.sleep ms)
  let expired : Task (Option Bool) := timer.map fun _ => none
  IO.waitAny [work, expired]

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := (← finishes 60000 control) == some true
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  for (label, control) in treeControls do
    let ok := (← finishes 5000 control).isNone
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label} (within 5 s)"
    unless ok do failed := failed + 1
  let total := controls.length + treeControls.length
  -- the controls that did not finish still run on their tasks: leave without waiting for them
  if failed != 0 then
    IO.eprintln s!"{failed}/{total} sharing controls failed"
    (← IO.getStdout).flush
    IO.Process.exit 1
  IO.println s!"sharing: {total}/{total} controls passed (tree sizes up to 2^{deep + 2})"
  (← IO.getStdout).flush
  IO.Process.exit 0

end Tests.Ix.CompileCert.Sharing
