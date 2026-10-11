import Ix.CompileCert.StrongCertifier

/-! The indexed, sharing-aware S decisions of M7 WP-F in compiled code
(`Ix/CompileCert/StrongFast.lean`, `SourceExportFast.lean`, `SourceInstallFast.lean`): their
equality with the list and tree functions is proved; these controls check what a proof cannot,
that the compiled callers run them and that they finish on the DAG, and they put every refusal
beside its valid neighbour:

* the comparison on the DAG (`checkInstalledExprShared`) accepts a source tower against its
  renamed target tower of 2^66 tree nodes, refuses it when the bottom leaf, a level or a binder
  datum differs, is unavailable (`none`) at a free variable, and agrees with the tree comparison
  `checkInstalledExprL` on every tower small enough to walk as a tree;
* the row checks as compiled code calls them (`checkInstalledTypes`, `checkInstalledDefinitions`,
  `checkInstalledAssociation`, all substituted by `@[csimp]`) on rows whose types and values are
  such towers: accepted; refused for a shadowed source row (two rows of one name: the list check's
  `find? n = some entry` fails for the second, and so must the index's), for a missing target row,
  for a different value; unavailable for a free variable; each beside the honest environment, and
  each verdict equal to the list-lookup decision (`…F` at `Kernel.Env.find?`);
* the source export (`exportSourceDeclarations`, substituted) of a theorem whose proof is a tower
  of 2^66 tree nodes finishes with the dependency list of the tree definition (`depsWalk` against
  `eraseDups` on every tower small enough), and refuses a source with a dangling reference with
  the list export's own error;
* `treeControls`: the tree versions of the same pairs do not finish in 5 s (the towers are huge
  trees, so every deep control above ran on the DAG). -/

namespace Tests.Ix.CompileCert.StrongIndexed

open _root_.Ix.CompileCert

abbrev KExpr := _root_.Ix.Kernel.Expr
abbrev KName := _root_.Ix.Kernel.Name

def kn (n : Lean.Name) : KName := sourceName n

/-- `x₀ = leaf`, `xₖ₊₁ = f xₖ xₖ`: three nodes per level as a DAG, `3·2^k` as a tree. -/
def tower (f : KName) (leaf : KExpr) : Nat → KExpr
  | 0 => leaf
  | k + 1 => let x := tower f leaf k; .app (.app (.const f []) x) x

/-- `x₀ = leaf`, `xₖ₊₁ = ∀ (_ : xₖ), xₖ` with a binder datum. -/
def binders (datum : _root_.Ix.Kernel.PropWhen) (leaf : KExpr) : Nat → KExpr
  | 0 => leaf
  | k + 1 => let x := binders datum leaf k; .forallE x x ⟨datum⟩

def deep : Nat := 64

def ax (n : Lean.Name) (type : KExpr := .sort .zero) : _root_.Ix.Kernel.ConstantInfo :=
  .axiomInfo ⟨kn n, [], type⟩

def defn (n : Lean.Name) (type value : KExpr) : _root_.Ix.Kernel.ConstantInfo :=
  .defnInfo ⟨kn n, [], type⟩ value .opaque

/-- The name map of the controls: `f`, `c`, `d`, `a`, `v` to their primed targets. -/
def names (n : KName) : KName :=
  if n == kn `f then kn `f' else if n == kn `c then kn `c' else if n == kn `d then kn `d'
  else if n == kn `a then kn `a' else if n == kn `v then kn `v' else n

def ground : List _root_.Ix.Kernel.ConstantInfo := [ax `f, ax `c, ax `d]
def groundT : List _root_.Ix.Kernel.ConstantInfo := [ax `f', ax `c', ax `d']

/-- The basis pins the installed association asks for, under their own names. -/
def pins : List _root_.Ix.Kernel.ConstantInfo :=
  [.axiomInfo ⟨_root_.Ix.Kernel.falseName, [], .sort .zero⟩,
   .axiomInfo ⟨_root_.Ix.Kernel.eqName, [kn `u], .sort .zero⟩]

def srcTower (k : Nat) : KExpr := tower (kn `f) (.const (kn `c) []) k
def tgtTower (k : Nat) : KExpr := tower (kn `f') (.const (kn `c') []) k

/-- The honest pair: a row `a` whose type is the tower, a definition `v` whose value is it. -/
def honestS (k : Nat) : _root_.Ix.Kernel.Env :=
  ⟨pins ++ ground ++ [ax `a (srcTower k), defn `v (.sort .zero) (srcTower k)]⟩
def honestT (k : Nat) : _root_.Ix.Kernel.Env :=
  ⟨pins ++ groundT ++ [ax `a' (tgtTower k), defn `v' (.sort .zero) (tgtTower k)]⟩

/-- The list-lookup decision of the installed association: the definition, with every lookup
`Kernel.Env.find?` (`…F` at `find?` is the check, `…F_env`). -/
def assocList (s t : _root_.Ix.Kernel.Env) : Option Bool :=
  bothChecks (checkInstalledComparisonAvailabilityF s s.find? t.find? names)
    (bothChecks (some (checkTelescopesF s t.find? names &&
      checkInstalledTypesF s s.find? t.find? names && checkInstalledDefinitionsF s s.find? t.find? names &&
      checkInstalledPin s names _root_.Ix.Kernel.falseName 0 && checkInstalledPin s names _root_.Ix.Kernel.eqName 1 &&
      checkInstalledCapabilitiesF s s.find? t.find? names && checkInstalledRecursorsF s s.find? t.find? names &&
      checkInstalledConstructorsF s s.find? t.find? names))
      (bothChecks (checkInstalledEtaAssociationsF s s.find? t.find? names)
        (checkInstalledRuleLevelLinksF s s.find? t.find? names)))

def cmpShared (s t : _root_.Ix.Kernel.Env) (a b : KExpr) : Option Bool :=
  checkInstalledExprShared s.find? t.find? names UniverseImage.identity a b

def cmpTree (s t : _root_.Ix.Kernel.Env) (a b : KExpr) : Option Bool :=
  checkInstalledExprL s.find? t.find? names UniverseImage.identity a b

/-- Target variants of the tower: another bottom constant, a free variable, a level. -/
def tgtLeafD (k : Nat) : KExpr := tower (kn `f') (.const (kn `d') []) k
def tgtFvar (k : Nat) : KExpr := tower (kn `f') (.fvar 0 (.sort .zero)) k
def srcSort (k : Nat) : KExpr := tower (kn `f) (.sort .zero) k
def tgtSortSucc (k : Nat) : KExpr := tower (kn `f') (.sort (.succ .zero)) k

def env0 : _root_.Ix.Kernel.Env := ⟨ground⟩
def envT0 : _root_.Ix.Kernel.Env := ⟨groundT⟩

/-! ### Lean-side towers for the source export -/

def towerL (leaf : Lean.Name) : Nat → Lean.Expr
  | 0 => .const leaf []
  | k + 1 => let x := towerL leaf k; .app (.app (.const `f []) x) x

def axL (n : Lean.Name) : Lean.ConstantInfo :=
  .axiomInfo { name := n, levelParams := [], type := .sort .zero, isUnsafe := false }

def thmL (n : Lean.Name) (value : Lean.Expr) : Lean.ConstantInfo :=
  .thmInfo { name := n, levelParams := [], type := .sort .zero, value, all := [n] }

/-- A source: `f`, `c` and a theorem `t` whose proof is the tower of depth `k`. -/
def sourceL (k : Nat) : Source := ⟨[thmL `t (towerL `c k), axL `f, axL `c]⟩

/-- The list export (`buildSourceGroupsP` at the originals is `buildSourceGroups` by `rfl`;
`validateSourceGroups` and `orderSourceGroups` are not substituted): the reference. -/
def exportList (s : Source) : ExportM (Array _root_.Ix.Kernel.Declaration) := do
  let groups ← buildSourceGroupsP (exportSourceInductive s) (sourceGroupDependencies s) s.declarations
  let groups ← validateSourceGroups s groups
  return (← orderSourceGroups (groups.length + 1) groups [] []).toArray

def sameExport (a b : ExportM (Array _root_.Ix.Kernel.Declaration)) : Bool :=
  match a, b with
  | .ok x, .ok y => decide (x.toList = y.toList)
  | .error e, .error e' => e == e'
  | _, _ => false

def exportNames (r : ExportM (Array _root_.Ix.Kernel.Declaration)) : List KName :=
  match r with
  | .ok ds => ds.toList.flatMap _root_.Ix.Kernel.Declaration.names
  | .error _ => []

def controls : List (String × (Unit → Bool)) := [
  ("deep: the comparison on the DAG accepts a tower against its renamed target", fun _ =>
    cmpShared env0 envT0 (srcTower deep) (tgtTower deep) == some true),
  ("deep: refused when the target's bottom constant differs (valid neighbour above)", fun _ =>
    cmpShared env0 envT0 (srcTower deep) (tgtLeafD deep) == some false),
  ("deep: unavailable (none) at a free variable at the bottom", fun _ =>
    cmpShared env0 envT0 (srcTower deep) (tgtFvar deep) == none),
  ("deep: refused when a level differs at the bottom", fun _ =>
    cmpShared env0 envT0 (srcSort deep) (tgtSortSucc deep) == some false),
  ("deep: binder towers with equal data accepted", fun _ =>
    cmpShared env0 envT0 (binders .never (.sort .zero) deep) (binders .never (.sort .zero) deep) == some true),
  ("deep: binder towers with a different datum refused (valid neighbour above)", fun _ =>
    cmpShared env0 envT0 (binders .never (.sort .zero) deep) (binders (.ifAllZero []) (.sort .zero) deep) == some false),
  ("the DAG comparison agrees with the tree comparison on towers of depth 0–10 (four pairs each)", fun _ =>
    (List.range 11).all fun k =>
      cmpShared env0 envT0 (srcTower k) (tgtTower k) == cmpTree env0 envT0 (srcTower k) (tgtTower k) &&
      cmpShared env0 envT0 (srcTower k) (tgtLeafD k) == cmpTree env0 envT0 (srcTower k) (tgtLeafD k) &&
      cmpShared env0 envT0 (srcTower k) (tgtFvar k) == cmpTree env0 envT0 (srcTower k) (tgtFvar k) &&
      cmpShared env0 envT0 (srcSort k) (tgtSortSucc k) == cmpTree env0 envT0 (srcSort k) (tgtSortSucc k)),
  ("deep: checkInstalledTypes (csimp) accepts rows whose types are towers", fun _ =>
    checkInstalledTypes (honestS deep) (honestT deep) names),
  ("deep: checkInstalledDefinitions (csimp) accepts a definition whose value is a tower", fun _ =>
    checkInstalledDefinitions (honestS deep) (honestT deep) names),
  ("deep: checkInstalledAssociation (csimp) accepts the honest pair (some true)", fun _ =>
    checkInstalledAssociation (honestS deep) (honestT deep) names == some true),
  ("forged: a shadowed source row (a second row `a` with another type) refused by the index \
    as by the list check; the honest neighbour accepted by both", fun _ =>
    let forged : _root_.Ix.Kernel.Env := ⟨(honestS 4).consts ++ [ax `a (.sort (.succ .zero))]⟩
    !checkInstalledTypes forged (honestT 4) names &&
      !checkInstalledTypesF forged forged.find? (honestT 4).find? names &&
      checkInstalledTypes (honestS 4) (honestT 4) names &&
      checkInstalledTypesF (honestS 4) (honestS 4).find? (honestT 4).find? names),
  ("forged: a missing target row refused, as by the list check", fun _ =>
    let missing : _root_.Ix.Kernel.Env := ⟨(honestT 4).consts.filter (·.name != kn `a')⟩
    !checkInstalledTypes (honestS 4) missing names &&
      !checkInstalledTypesF (honestS 4) (honestS 4).find? missing.find? names),
  ("forged: a different target value refused (some false), as by the list decision", fun _ =>
    let other : _root_.Ix.Kernel.Env :=
      ⟨(honestT 4).consts.map fun c => if c.name == kn `v' then defn `v' (.sort .zero) (tgtLeafD 4) else c⟩
    checkInstalledAssociation (honestS 4) other names == some false &&
      assocList (honestS 4) other == some false),
  ("a free variable in the target value: unavailable (none), as by the list decision", fun _ =>
    let other : _root_.Ix.Kernel.Env :=
      ⟨(honestT 4).consts.map fun c => if c.name == kn `v' then defn `v' (.sort .zero) (tgtFvar 4) else c⟩
    checkInstalledAssociation (honestS 4) other names == none && assocList (honestS 4) other == none),
  ("the indexed association equals the list decision on the honest pair at depths 0–8", fun _ =>
    (List.range 9).all fun k =>
      checkInstalledAssociation (honestS k) (honestT k) names == assocList (honestS k) (honestT k)),
  ("deep: the source export (csimp) of a theorem whose proof is a tower finishes, f and c before t", fun _ =>
    exportNames (exportSourceDeclarations (sourceL deep)) == [kn `f, kn `c, kn `t]),
  ("the source export equals the list export at depths 0–10", fun _ =>
    (List.range 11).all fun k => sameExport (exportSourceDeclarations (sourceL k)) (exportList (sourceL k))),
  ("the DAG dependency list is the tree definition's (eraseDups) at depths 0–10", fun _ =>
    (List.range 11).all fun k =>
      let ci := thmL `t (towerL `c k)
      decide (depsWalk [`t] [ci] =
        (([ci].map sourceTermRefs).flatten.filter (fun n => ![`t].contains n)).eraseDups)),
  ("a dangling reference (no `c` in the source) refused by the export with the list export's error", fun _ =>
    let dangling : Source := ⟨[thmL `t (towerL `c 3), axL `f]⟩
    sameExport (exportSourceDeclarations dangling) (exportList dangling) &&
      (match exportSourceDeclarations dangling with | .error _ => true | .ok _ => false)),
  ("deep: the dangling reference refused at depth 64 too (valid neighbour: the honest source above)", fun _ =>
    match exportSourceDeclarations ⟨[thmL `t (towerL `c deep), axL `f]⟩ with
    | .error _ => true | .ok _ => false)]

/-- A plain tree walk of a term's references (no memo, no allocation): what the source export's
`exprRefs` walk visits. -/
def treeRefs (p : Lean.Name → Bool) : Lean.Expr → Bool
  | .const n _ => p n
  | .app f a => treeRefs p f && treeRefs p a
  | _ => true

/-- Controls that must *not* finish in 5 s: the tree versions of deep controls above. -/
def treeControls : List (String × (Unit → Bool)) := [
  ("the tree comparison (checkInstalledExprL) of the deep tower pair does not finish", fun _ =>
    cmpTree env0 envT0 (srcTower deep) (tgtTower deep) == some true),
  ("a plain tree walk of the deep theorem's proof (its references, no memo) does not finish", fun _ =>
    treeRefs (fun n => n == `f || n == `c) (towerL `c deep))]

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
  if failed != 0 then
    IO.eprintln s!"{failed}/{total} strong-indexed controls failed"
    (← IO.getStdout).flush
    IO.Process.exit 1
  IO.println s!"strong indexed: {total}/{total} controls passed (DAG comparison, row checks, \
    association and source export on towers of 3·2^{deep} tree nodes; forged rows refused beside \
    their neighbours; agreement with the list and tree decisions)"
  (← IO.getStdout).flush
  IO.Process.exit 0

end Tests.Ix.CompileCert.StrongIndexed
