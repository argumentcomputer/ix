import LSpec
import Ix.AuxGen.SourceIdentity
import Ix.Compile.Pass.Driver
import Ix.CanonM
import Ix.EnvScope
import Tests.Ix.Compile.Fixtures.AuxiliaryIdentity
import Tests.Ix.Compile.Pass.O3Cases
import Tests.Ix.Compile.Pass.O8Cases
import Tests.Ix.Compile.Pass.O5PropSplit

namespace Tests.Ix.Compile.SourceIdentity

open LSpec
open _root_.Ix (Name Level Expr)
open _root_.Ix.AuxGen.SourceIdentity

private def nm (s : String) : Name := Name.mkStr Name.mkAnon s

def controls : List (String × Bool) := Id.run do
  let u := nm "u"
  let v := nm "v"
  let p := Expr.mkSort (Level.mkParam u)
  let q := Expr.mkSort (Level.mkParam v)
  let body := Expr.mkBVar 0
  let f := Expr.mkLam (nm "left") p body .implicit
  let g := Expr.mkLam (nm "right") q body .default
  let h : Address := ⟨⟨Array.replicate 32 0⟩⟩
  let a := Name.str (.anonymous h) "a" h
  let b := Name.str (.anonymous h) "b" h
  return [
    ("universe binder renaming", agrees #[u] #[v] f g),
    ("universe positions differ", !agrees #[u, v] #[u, v] p q),
    ("undeclared parameters do not match", !agrees #[] #[] p p),
    ("level metavariables do not match", !agrees #[] #[]
      (Expr.mkSort (Level.mkMvar u)) (Expr.mkSort (Level.mkMvar u))),
    ("free variables do not match", !agrees #[] #[] (Expr.mkFVar u) (Expr.mkFVar u)),
    ("expression metavariables do not match", !agrees #[] #[] (Expr.mkMVar u) (Expr.mkMVar u)),
    ("same type, different body", !agrees #[u] #[v] f (Expr.mkLam (nm "right") q (Expr.mkBVar 1) .default)),
    ("constant name cache collision", !agrees #[] #[] (.const a #[] h) (.const b #[] h)),
    ("paired metadata", agrees #[u] #[v] (Expr.mkMData #[] f) (Expr.mkMData #[] g)),
    ("one-sided metadata remains conservative", !agrees #[u] #[v] (Expr.mkMData #[] f) g)
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"source auxiliary: {label}" ok

/-- Supply the old dispatch with an applicable recursor shape: refusal must
come from source-body recognition, not from an empty block/shape table. -/
def guardedDispatch (source : _root_.Ix.Environment) (name : Name) : Bool := Id.run do
  let .str parent _ _ := name | return false
  let some actual := source.get? name | return false
  let recName := Name.mkStr parent "rec"
  let ixRoot := Name.mkStr parent "_ix"
  let params := actual.getCnst.levelParams
  let shape : _root_.Ix.Compile.Pass.Opt.RecShape := {
    leanRec := recName, levelParams := params, np := 0, nm := 1, nmin := 1, ni := 0
    ixRec := Name.mkStr ixRoot "rec", ixLevels := params.map Level.mkParam
    motiveSrc := #[0], minorSrc := #[some 0], minorTerms := #[Expr.mkBVar 0] }
  let block : _root_.Ix.Compile.Pass.Opt.OptBlock := {
    all := #[parent], change := default, classOf := ({} : Std.HashMap _ _).insert parent #[parent]
    shapes := ({} : Std.HashMap _ _).insert recName shape }
  let blocks := ({} : Std.HashMap _ _).insert parent block
  let addresses := ({} : Std.HashMap _ Address).insert (Name.mkStr ixRoot "casesOn") name.getHash
    |>.insert (Name.mkStr ixRoot "recOn") name.getHash
  let cenv : _root_.Ix.CompileM.CompileEnv := { (default : _root_.Ix.CompileM.CompileEnv) with
    env := source, nameToAddr := addresses, p3Heads := ({} : Std.HashMap _ _).insert name parent }
  let optEnv : _root_.Ix.Compile.Pass.Opt.OptEnv := {
    ienv := source, resolves := addresses.contains, blockOf := fun _ => some block }
  let args := #[Expr.mkLam (nm "x") (Expr.mkConst parent #[])
      (Expr.mkConst (Name.fromLeanName `Nat) #[]) .default,
    Expr.mkConst (Name.mkStr parent "mk") #[], Expr.mkLit (.natVal 7)]
  let levels := #[Level.mkSucc Level.mkZero]
  let oldHit := (_root_.Ix.Compile.Pass.Opt.engineFull optEnv
    { head := name, us := levels, args }).isSome
  let guarded := (_root_.Ix.Compile.Pass.optLookup cenv blocks none name levels args).isNone
  let some candidate := wrapper? source name | return false
  let ordinary : _root_.Ix.ConstantInfo := .defnInfo {
    cnst := { name, levelParams := candidate.levelParams, type := candidate.typ }
    value := candidate.value, safety := .safe, hints := .abbrev, all := #[name] }
  let faithful := { source with consts := source.consts.insert name ordinary }
  let faithfulShape := { shape with
    levelParams := candidate.levelParams
    ixLevels := candidate.levelParams.map Level.mkParam }
  let faithfulBlocks := blocks.insert parent { block with
    shapes := ({} : Std.HashMap _ _).insert recName faithfulShape }
  let neighbor := (_root_.Ix.Compile.Pass.optLookup { cenv with env := faithful }
    faithfulBlocks none name levels args).isSome
  return oldHit && guarded && neighbor

/-- Check the real source declarations, including changed mutual families.
The custom fixtures are not expected to be compilable by the old publication
path: this test establishes recognition and production optimization refusal. -/
def run (env : Lean.Environment) : IO UInt32 := do
  let prefixes := [`Tests.Ix.Compile.Fixtures.AuxiliaryIdentity, `PassO3, `PassO8, `PassO5]
  let seeds := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (·.isPrefixOf n) then some n else none
  let input := _root_.Ix.EnvScope.collectDeps env seeds
  let consts := (_root_.Ix.CanonM.canonChunk input.toArray).foldl
    (fun acc (n, ci) => acc.insert n ci) ({} : Std.HashMap Name _root_.Ix.ConstantInfo)
  let source : _root_.Ix.Environment := { consts }
  let mut checks := suite
  let mut ordinary := 0
  for (n, _) in consts do
    let .str _ suffix _ := n | continue
    if suffix != "casesOn" && suffix != "recOn" then continue
    let leanName := _root_.Ix.Compile.Canon.keyName n
    if (`Tests.Ix.Compile.Fixtures.AuxiliaryIdentity).isPrefixOf leanName then continue
    ordinary := ordinary + 1
    checks := checks ++ [test s!"recognize actual source wrapper {n.pretty}"
      (checkedWrapper? source n).isSome]
  checks := checks ++ [test "ordinary wrapper controls are present" (ordinary ≥ 20)]
  let custom := [
    `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.DifferentType.Box.casesOn,
    `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.SameType.Box.casesOn,
    `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.SameType.Box.recOn,
    `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Unrelated.Box.casesOn]
  for leanName in custom do
    let n := Name.fromLeanName leanName
    checks := checks ++ [test s!"preserve custom source identity {n.pretty}"
      (source.get? n).isSome,
      test s!"decline custom source wrapper {n.pretty}" (!(checkedWrapper? source n).isSome)]
    if (`Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.SameType).isPrefixOf leanName then
      let sameType := do
        let expected ← wrapper? source n
        let actual ← source.get? n
        return agrees expected.levelParams actual.getCnst.levelParams expected.typ actual.getCnst.type
      checks := checks ++ [test s!"custom neighbor has the generated type {n.pretty}"
        (sameType == some true),
        test s!"production guard prevents applicable standard rewrite {n.pretty}" (guardedDispatch source n)]
  IO.println s!"[aux-source-identity] {ordinary} ordinary wrappers, {custom.length} custom wrappers"
  LSpec.lspecIO (.ofList [("aux-source-identity", checks)]) []

end Tests.Ix.Compile.SourceIdentity
