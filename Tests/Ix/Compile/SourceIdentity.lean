import LSpec
import Ix.AuxGen.SourceIdentity
import Ix.CanonM
import Ix.EnvScope
import Ix.Meta

/-!
Source-body recognition of `casesOn`/`recOn` (`Ix.AuxGen.SourceIdentity`).
`suite` (`aux-source-identity-unit`) holds the comparison controls; `run`
(`aux-source-identity`) elaborates `Fixtures/AuxiliaryIdentity.lean` at run
time and checks every wrapper of its source closure: each ordinary generated
wrapper is recognized and each custom declaration with a wrapper's name is
declined. Nothing on the compile path consults the recognizer yet.
-/

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
    ("a raw-equal level at another position", !agrees #[u, v] #[v, u] p p),
    ("universe arithmetic is not normalized",
      !agrees #[u] #[u] (Expr.mkSort (Level.mkMax (Level.mkParam u) (Level.mkParam u))) p),
    ("undeclared parameters do not match", !agrees #[] #[] p p),
    ("level metavariables do not match", !agrees #[] #[]
      (Expr.mkSort (Level.mkMvar u)) (Expr.mkSort (Level.mkMvar u))),
    ("free variables do not match", !agrees #[] #[] (Expr.mkFVar u) (Expr.mkFVar u)),
    ("free variables under a binder do not match",
      !agrees #[u] #[u] (Expr.mkLam (nm "x") p (Expr.mkFVar u) .default)
        (Expr.mkLam (nm "x") p (Expr.mkFVar u) .default)),
    ("expression metavariables do not match", !agrees #[] #[] (Expr.mkMVar u) (Expr.mkMVar u)),
    ("same type, different body", !agrees #[u] #[v] f (Expr.mkLam (nm "right") q (Expr.mkBVar 1) .default)),
    ("constant name cache collision", !agrees #[] #[] (.const a #[] h) (.const b #[] h)),
    ("paired metadata", agrees #[u] #[v] (Expr.mkMData #[] f) (Expr.mkMData #[] g)),
    ("one-sided metadata remains conservative", !agrees #[u] #[v] (Expr.mkMData #[] f) g)
  ]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"source auxiliary: {label}" ok

def fixture : System.FilePath := "Tests/Ix/Compile/Fixtures/AuxiliaryIdentity.lean"
def root : Lean.Name := `Tests.Ix.Compile.Fixtures.AuxiliaryIdentity

/-- The fixture's declarations that carry a wrapper's name but not its body. -/
def custom : List Lean.Name := [
  root ++ `DifferentType.Box.casesOn, root ++ `SameType.Box.casesOn,
  root ++ `SameType.Box.recOn, root ++ `Unrelated.Box.casesOn,
  root ++ `Changed.A.casesOn, root ++ `Changed.B.casesOn]

/-- Ordinary controls beside the fixture's own: the wrappers of these Prelude
families (indexed, universe-polymorphic, `Prop`, structures, recursive). -/
def standard : List Lean.Name := [
  `Nat, `List, `Option, `Prod, `PProd, `Sum, `PSum, `Sigma, `PSigma, `Subtype,
  `Eq, `HEq, `And, `Or, `Iff, `Exists, `True, `False, `Empty, `Bool, `PUnit,
  `Fin, `Decidable, `Acc]

/-- Recognition on the actual source declarations of `env`'s fixture closure,
including a changed mutual family. -/
def check (env : Lean.Environment) : IO UInt32 := do
  let fixtureNames := env.constants.toList.filterMap fun (n, _) =>
    if root.isPrefixOf n then some n else none
  let wrappers := standard.flatMap fun n => [n ++ `casesOn, n ++ `recOn]
  let seeds := fixtureNames ++ wrappers.filter env.contains
  let input := _root_.Ix.EnvScope.collectDeps env seeds
  let consts := (_root_.Ix.CanonM.canonChunk input.toArray).foldl
    (fun acc (n, ci) => acc.insert n ci) ({} : Std.HashMap Name _root_.Ix.ConstantInfo)
  let source : _root_.Ix.Environment := { consts }
  let mut checks := suite
  let mut ordinary := 0
  for (leanName, _) in input do
    let .str _ suffix := leanName | continue
    if suffix != "casesOn" && suffix != "recOn" || custom.contains leanName then continue
    let n := Name.fromLeanName leanName
    ordinary := ordinary + 1
    checks := checks ++ [
      test s!"recognize actual source wrapper {n.pretty}" (checkedWrapper? source n).isSome,
      test s!"permit the standard wrapper {n.pretty}" (permitsOptimization source n)]
  checks := checks ++ [test "ordinary wrapper controls are present"
    (wrappers.all env.contains && ordinary ≥ 50)]
  for leanName in custom do
    let n := Name.fromLeanName leanName
    checks := checks ++ [
      test s!"preserve custom source identity {n.pretty}" (source.get? n).isSome,
      test s!"decline custom source wrapper {n.pretty}" (checkedWrapper? source n).isNone,
      test s!"refuse the standard interpretation {n.pretty}" (!permitsOptimization source n)]
    -- The same name with the generated body is recognized: the refusal comes
    -- from the source body, not from a missing recursor or generator failure.
    if let some candidate := wrapper? source n then
      let generated : _root_.Ix.ConstantInfo := .defnInfo {
        cnst := { name := n, levelParams := candidate.levelParams, type := candidate.typ }
        value := candidate.value, safety := .safe, hints := .abbrev, all := #[n] }
      let faithful : _root_.Ix.Environment := { consts := consts.insert n generated }
      checks := checks ++ [test s!"the generated neighbor is recognized {n.pretty}"
        (checkedWrapper? faithful n).isSome]
    if (root ++ `SameType).isPrefixOf leanName then
      let sameType := do
        let expected ← wrapper? source n
        let actual ← source.get? n
        return agrees expected.levelParams actual.getCnst.levelParams expected.typ actual.getCnst.type
      checks := checks ++ [test s!"custom neighbor has the generated type {n.pretty}"
        (sameType == some true)]
  -- Heads that are not `casesOn`/`recOn` are not this recognizer's decision.
  let below := Name.fromLeanName (root ++ `Witness.below)
  checks := checks ++ [test "other heads are not decided here" (permitsOptimization source below)]
  IO.println s!"[aux-source-identity] {ordinary} ordinary wrappers, {custom.length} custom wrappers"
  LSpec.lspecIO (.ofList [("aux-source-identity", checks)]) []

def run : IO UInt32 := do
  check (← getFileEnvCore fixture).env

end Tests.Ix.Compile.SourceIdentity
