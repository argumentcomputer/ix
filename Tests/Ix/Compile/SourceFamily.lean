import Ix.AuxGen.SourceFamily
import Ix.CanonM
import Ix.EnvScope
import Ix.Meta
import Tests.Ix.Compile.SourceFamilyOracle

/-!
Source-family recognition of `below`/`brecOn` (`Ix.AuxGen.SourceFamily`),
`aux-source-family`: a dense validator-graph control, then the families of
`Fixtures/AuxiliaryFamilyIdentity.lean` (elaborated at run time). In each
mode the standard `Even` helper is recognized and kept by `filterHeads`; the
custom `Odd` helper, or a standard one that depends on a custom helper, is
not. The same recognizer guards the production image and clique paths.
-/

namespace Tests.Ix.Compile.SourceFamily

open _root_.Ix (Name)
open _root_.Ix.AuxGen.SourceFamily

private def need (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)

private def needError (result : Except String α) (expected : String) : IO Unit :=
  match result with
  | .error why => need (why == expected) s!"expected {expected}, got {why}"
  | .ok _ => throw (IO.userError s!"accepted instead of {expected}")

/-- The checked caller keeps failures visible; successful lazy reads retain
the same actual-source decisions. A provider cannot select a legacy mode. -/
def providerControls (source : _root_.Ix.Environment)
    (oracleFor : _root_.Ix.AuxGen.SourceFamilyOracle) (ind : _root_.Ix.InductiveVal) : IO Unit := do
  let owner := ind.cnst.name
  let heads := #[owner, owner.mkStr "below", owner.mkStr "brecOn"]
  let lazySource : _root_.Ix.Environment := { consts := {}, fallback? := some source.get? }
  let expected ← IO.ofExcept (filterHeadsChecked oracleFor source ind.all heads)
  need ((← IO.ofExcept (filterHeadsChecked oracleFor lazySource ind.all heads)) == expected)
    "lookup-only source changed the checked heads"
  let below ← IO.ofExcept (reconstruct oracleFor source ind.all false)
  need (!below.isEmpty && below.all (fun r => !isBRecOn r.name)) "below-only coverage"
  needError (reconstruct oracleFor source #[]) "source auxiliary family is empty"
  needError (reconstruct oracleFor { source with consts := source.consts.erase owner } ind.all)
    "source auxiliary owner is absent"
  needError (reconstruct oracleFor source ind.all.reverse) "source auxiliary mutual order differs"
  let recName := owner.mkStr "rec"
  needError (reconstruct oracleFor { source with consts := source.consts.erase recName } ind.all)
    s!"source recursor absent: {recName.pretty}"
  let unavailable : _root_.Ix.AuxGen.SourceFamilyOracle := fun _ => .error "planted provider failure"
  needError (filterHeadsChecked unavailable source ind.all heads) "planted provider failure"
  need (filterHeads unavailable source ind.all heads == #[owner]) "public filter accepted unavailable recipes"
  need ((← IO.ofExcept (filterHeadsChecked unavailable source ind.all #[owner])) == #[owner])
    "nonderived fast path queried the provider"
  let actual ← IO.ofExcept (oracleFor owner)
  let .mk _ trace scope flat below recs asked lazyScope admit status retry family := actual
  let unsafeModes := #[
    _root_.Ix.AuxGen.AuxOracle.mk .fallback trace scope flat below recs asked lazyScope admit status retry family,
    .mk .failClosed trace scope flat below false asked lazyScope admit status retry family,
    .mk .failClosed trace scope flat below true asked lazyScope admit status (some actual) family]
  for candidate in unsafeModes do
    needError (reconstruct (fun _ => .ok candidate) source ind.all)
      s!"source family {owner.pretty}: failClosed recursor capability without retry required"
  needError ((_root_.Ix.CompileM.CompileEnv.new source).familyOracle owner)
    s!"source family {owner.pretty}: original-source provider is absent"
  IO.println "[aux-source-family] 13 provider/lookup/negative controls"

/-- A validator graph control, separate from the checked source fixture.
Every member of a mutual below group names every other member. Traversing
all simple paths would make even this small family impractical. -/
def denseFamilyControls : IO Unit := do
  let names := (Array.range 32).map fun i => Name.mkStr .mkAnon s!"FamilyGraph{i}"
  let mut source : _root_.Ix.Environment := { consts := {} }
  let mut recipes : Array Recipe := #[]
  for name in names do
    let expected : _root_.Ix.AuxGen.BelowIndc := {
      name, levelParams := #[], nParams := 0, nIndices := 0
      isReflexive := false, isUnsafe := false, typ := _root_.Ix.Expr.mkSort .mkZero, ctors := #[] }
    let actual : _root_.Ix.InductiveVal := {
      cnst := { name, levelParams := #[], type := expected.typ }
      numParams := 0, numIndices := 0, all := names, ctors := #[], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false }
    source := { source with consts := source.consts.insert name (.inductInfo actual) }
    recipes := recipes.push (.inductiveDecl expected names)
  let some visited := authenticatedVisit source recipes (recipes.size + 1) #[] names[0]!
    | throw (IO.userError "dense family rejected")
  need (visited.size == names.size && names.all visited.contains)
    "dense family lost members or repeated visits"
  let badName := names[31]!
  let some (.inductInfo actual) := source.get? badName | throw (IO.userError "dense member missing")
  let altered := { actual with cnst := { actual.cnst with type := _root_.Ix.Expr.mkSort (.mkSucc .mkZero) } }
  source := { source with consts := source.consts.insert badName (.inductInfo altered) }
  need (!authenticated source recipes (recipes.size + 1) #[] names[0]!)
    "dense cycle hid an altered source declaration"
  need (!authenticated source recipes (recipes.size + 1) visited badName)
    "a visited name bypassed its actual source lookup"

/-- The derived-name classifier, and references walked once per shared
subterm (mirrors the Rust unit tests of `aux_gen/source_family.rs`). -/
def classifierControls : IO Unit := do
  let n (parts : List String) : Name := parts.foldl (fun acc s => Name.mkStr acc s) .mkAnon
  for derived in [["T", "below"], ["T", "below_2"], ["T", "brecOn"], ["T", "brecOn_1"],
      ["T", "brecOn", "go"], ["T", "brecOn_1", "eq"]] do
    need (isDerived (n derived)) s!"not derived: {derived}"
  need (isBRecOn (n ["T", "brecOn", "eq"]) && !isBRecOn (n ["T", "below"])) "brecOn classifier"
  for other in [["T", "casesOn"], ["T", "go"], ["T", "below", "go"]] do
    need (!isDerived (n other)) s!"derived: {other}"
  let c := _root_.Ix.Expr.mkConst (n ["c"]) #[]
  let shared := _root_.Ix.Expr.mkApp c c
  need (exprReferences (_root_.Ix.Expr.mkApp shared shared) == #[n ["c"]])
    "a shared subterm was walked twice"
  need (exprReferences (_root_.Ix.Expr.mkProj (n ["P"]) 0 c) == #[n ["P"], n ["c"]])
    "projection owners precede their subterm's references"

def fixture : System.FilePath := "Tests/Ix/Compile/Fixtures/AuxiliaryFamilyIdentity.lean"
def root : Lean.Name := `Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity

/-- Recognition on the actual source declarations of `env`'s fixture closure. -/
def check (env : Lean.Environment) : IO UInt32 := do
  denseFamilyControls
  classifierControls
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if root.isPrefixOf name then some name else none
  need (!seeds.isEmpty) "source auxiliary family fixture missing"
  let input := _root_.Ix.EnvScope.collectDeps env seeds
  let consts := (_root_.Ix.CanonM.canonChunk input.toArray).foldl
    (fun acc (n, ci) => acc.insert n ci) ({} : Std.HashMap Name _root_.Ix.ConstantInfo)
  let source : _root_.Ix.Environment := { consts }
  let oracleFor := SourceFamilyOracle.forInput source (consts.toArray.map (·.1))
  let mut checked := 0
  for mode in [`Main, `Go, `Below] do
    let ns := root ++ mode
    let even := Name.fromLeanName (ns ++ `Even)
    let odd := Name.fromLeanName (ns ++ `Odd)
    let some (.inductInfo ind) := source.get? even | throw (IO.userError "source member missing")
    if mode == `Main then providerControls source oracleFor ind
    let recipes ← IO.ofExcept (reconstruct oracleFor source ind.all (mode != `Below))
    let authentic := authenticated source recipes (recipes.size + 1) #[]
    let helper := if mode == `Below then "below" else "brecOn"
    let ordinary := even.mkStr helper
    let changed := odd.mkStr helper
    need (authentic ordinary) s!"{mode}: the standard helper was not recognized"
    need (!authentic changed) s!"{mode}: the custom helper was recognized"
    let heads := #[even, ordinary, changed]
    need (filterHeads oracleFor source ind.all heads == #[even, ordinary])
      s!"{mode}: filterHeads kept {(filterHeads oracleFor source ind.all heads).map (·.pretty)}"
    checked := checked + 2
    if mode == `Go then
      let some recipe := recipes.find? (fun r => r.name == changed)
        | throw (IO.userError "standard brecOn recipe missing")
      let some actual := source.get? changed | throw (IO.userError "standard brecOn missing")
      need (recipe.matches actual) "Go: brecOn itself must have the standard type and body"
      need (!authentic (changed.mkStr "go")) "Go: modified dependency was authenticated"
      need (authentic (ordinary.mkStr "go")) "Go: the standard go was not recognized"
      checked := checked + 3
  IO.println s!"[aux-source-family] dense, classifier and reference controls; \
    {checked} source-family checks (Main, Go, Below)"
  return 0

def run : IO UInt32 := do
  check (← getFileEnvCore fixture).env

end Tests.Ix.Compile.SourceFamily
