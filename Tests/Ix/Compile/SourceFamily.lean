import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity
import Ix.AuxGen.SourceFamily

namespace Tests.Ix.Compile.SourceFamily

open _root_.Ix (Name)

private def need (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)

/-- A validator graph control, separate from the checked source fixture.
Every member of a mutual below group names every other member. Traversing
all simple paths would make even this small family impractical. -/
def denseFamilyControls : IO Unit := do
  let names := (Array.range 32).map fun i => Name.mkStr .mkAnon s!"FamilyGraph{i}"
  let mut source : _root_.Ix.Environment := { consts := {} }
  let mut recipes : Array _root_.Ix.AuxGen.SourceFamily.Recipe := #[]
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
  let some visited := _root_.Ix.AuxGen.SourceFamily.authenticatedVisit source recipes
      (recipes.size + 1) #[] names[0]!
    | throw (IO.userError "dense family rejected")
  need (visited.size == names.size && names.all visited.contains)
    "dense family lost members or repeated visits"
  let badName := names[31]!
  let some (.inductInfo actual) := source.get? badName | throw (IO.userError "dense member missing")
  let altered := { actual with cnst := { actual.cnst with type := _root_.Ix.Expr.mkSort (.mkSucc .mkZero) } }
  source := { source with consts := source.consts.insert badName (.inductInfo altered) }
  need (!_root_.Ix.AuxGen.SourceFamily.authenticated source recipes (recipes.size + 1) #[] names[0]!)
    "dense cycle hid an altered source declaration"
  need (!_root_.Ix.AuxGen.SourceFamily.authenticated source recipes (recipes.size + 1) visited badName)
    "a visited name bypassed its actual source lookup"

def run (env : Lean.Environment) : IO UInt32 := do
  denseFamilyControls
  let root := `Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if root.isPrefixOf name then some name else none
  need (!seeds.isEmpty) "source auxiliary family fixture missing"
  let unit : Pass3.CUnit := {
    name := "AuxiliaryFamilyIdentity", env, seeds := seeds.toArray
    closure := Pass3.closureOf env seeds }
  let seq ← Twins.leanCompile env unit.closure (workers := 1)
  let par ← Twins.leanCompile env unit.closure (workers := 4)
  need (seq.cenv.ungrounded.isEmpty && par.cenv.ungrounded.isEmpty)
    "source family fixture refused"
  need (seq.bytes == par.bytes) "source family recognition depends on worker count"
  for name in seeds do
    need ((seq.env.getNamed? (Name.fromLeanName name)).isSome) s!"source declaration omitted: {name}"
  let source := { seq.cenv.env with overlay := {} }
  for mode in [`Main, `Go, `Below] do
    let ns := root ++ mode
    let even := Name.fromLeanName (ns ++ `Even)
    let odd := Name.fromLeanName (ns ++ `Odd)
    let some (.inductInfo ind) := source.get? even | throw (IO.userError "source member missing")
    let recipes ← IO.ofExcept (_root_.Ix.AuxGen.SourceFamily.reconstruct source ind.all (mode != `Below))
    let authentic := _root_.Ix.AuxGen.SourceFamily.authenticated source recipes (recipes.size + 1) #[]
    let ordinary := even.mkStr (if mode == `Below then "below" else "brecOn")
    let changed := odd.mkStr (if mode == `Below then "below" else "brecOn")
    need (authentic ordinary && seq.cenv.p3Heads.contains ordinary)
      s!"{mode}: ordinary helper lost the image/optimization route"
    need (!authentic changed && !seq.cenv.p3Heads.contains changed)
      s!"{mode}: custom helper entered the image/optimization route"
    if mode == `Go then
      let some recipe := recipes.find? (fun r => r.name == changed)
        | throw (IO.userError "standard brecOn recipe missing")
      let some actual := source.get? changed | throw (IO.userError "standard brecOn missing")
      need (recipe.matches actual) "Go: brecOn itself must have the standard type and body"
      need (!authentic (changed.mkStr "go")) "Go: modified dependency was authenticated"
  let (problems, summary) ← Pass3.decompileCheck unit seq
  need problems.isEmpty s!"source family recovery failed: {problems}"
  let dir : System.FilePath :=
    (← IO.getEnv "SOURCE_FAMILY_KEEP").getD "plans/tasks/lean-to-ixon-correctness/source-family-gate"
  IO.FS.createDirAll dir
  let leanPath := dir / "lean.ixe"
  let rustPath := dir / "rust.ixe"
  IO.FS.writeBinFile leanPath seq.bytes
  let input ← IO.ofExcept ((_root_.Ix.Compile.compileInputFromEnv env unit.closure).mapError toString)
  let constants ← IO.ofExcept input.prepare
  let status ← _root_.Ix.CompileM.rsCompileEnvBytesFFI constants rustPath.toString false
  need status.ungrounded.isEmpty "Rust source family fixture refused"
  need ((← IO.FS.readBinFile rustPath) == seq.bytes) "source family output differs between Lean and Rust"
  let sourceNames := unit.seeds.map Name.fromLeanName
  let requested := seq.env.named.toArray.filterMap fun (name, _) =>
    if sourceNames.contains name || _root_.Ix.Compile.Pass.hasReserved name then some name.pretty else none
  let checks := dir / "kernels"
  IO.FS.createDirAll checks
  let result ← Pass3.kernelRun checks leanPath requested
  need result.failed.isEmpty s!"source family kernel failures: {result.failed}"
  need (result.checked.all (fun (_, count) => count == result.targets.size))
    s!"source family kernel coverage differs: {result.checked} / {result.targets.size}"
  IO.println s!"[aux-source-family] {summary}; {seq.bytes.size} bytes identical (Lean 1/4 workers, Rust); \
{result.targets.size} declarations accepted by all three kernels; direct and transitive source-body controls passed"
  return 0

end Tests.Ix.Compile.SourceFamily
