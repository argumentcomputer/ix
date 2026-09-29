module

public import Ix.Compile.SourceContract.Transport
public import Ix.CompileM

public section

namespace Tests.ContractTransport

open Ix.Compile

def source : Lean.ConstantInfo := .defnInfo {
  name := `contractIdentity, levelParams := []
  type := .forallE `x (.sort .zero) (.sort .zero) .default
  value := .lam `x (.sort .zero) (.bvar 0) .default
  hints := .abbrev, safety := .safe, all := [`contractIdentity] }

def block : Ix.CompileM.BlockEnv := ⟨{}, .mkAnon, {}, []⟩

def get (label : String) (result : Except α β) [ToString α] : IO β :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"contract transport {label}: {error}"

def compileMany (sources : Array Lean.Expr) (surgical : Bool := false) :
    Except Ix.CompileM.CompileError (Array Ixon.Expr) := do
  let ix := Id.run ((sources.mapM Ix.CanonM.canonExpr).run' {})
  let action := ix.mapM fun e => do
    let (result, _) ← if surgical then Ix.CompileM.compileExprSurgical e else Ix.CompileM.compileExpr e
    pure result
  let (output, _) ← Ix.CompileM.CompileM.run default block {} action
  return output

def run : IO Unit := do
  let mut sources := #[]
  let mut expected := #[]
  let mut allSources := #[]
  let mut allExpected := #[]
  for inputBits in [:16] do
    let some binder := Ixon.BinderContract.ofBits? inputBits.toUInt8
      | throw <| IO.userError "invalid test binder"
    for resultBits in [:4] do
      let some result := Ixon.ValueContract.ofBits? resultBits.toUInt8
        | throw <| IO.userError "invalid test result"
      let original ← get "telescope" (SourceContract.ofTelescope source #[{
        binder := .position 0, uses := binder.uses, value := binder.value, result := some result }])
      let resolved ← get "resolution" (original.resolve source)
      let decorated ← get "decoration" resolved.decorate
      allSources := allSources.push decorated.type
      allExpected := allExpected.push (.all binder result (.sort 0) (.sort 0))
      if resultBits == 0 then
        let some body := sourceBody? decorated | throw <| IO.userError "missing decorated body"
        sources := sources.push body
        expected := expected.push (.lam binder (.sort 0) (.var 0))
  for surgical in [false, true] do
    let output ← get "cached lambdas" (compileMany sources surgical)
    unless output == expected do throw <| IO.userError s!"lambda contracts collided during compilation (surgical={surgical}):\n{repr output}\nexpected {repr expected}"
    let output ← get "cached foralls" (compileMany allSources surgical)
    unless output == allExpected do throw <| IO.userError "arrow contracts collided during compilation"
  -- All occurrences share their unannotated inner binder. The complete
  -- metadata wrapper must distinguish them in both hash and equality paths.
  for i in [:sources.size] do
    for j in [:sources.size] do
      let equal := Id.run ((Ix.CanonM.exprEqCached sources[i]! sources[j]!).run' {})
      unless equal == (i == j) do throw <| IO.userError "semantic equality ignored a contract"
  let canonical := Id.run ((sources.mapM Ix.CanonM.canonExpr).run' {})
  for i in [:canonical.size] do
    for j in [:canonical.size] do
      let (comparison, _) ← get "ordering" <|
        Ix.CompileM.CompileM.run default block {} (Ix.CompileM.compareExpr {} [] [] canonical[i]! canonical[j]!)
      unless (comparison.ord == .eq) == (i == j) do
        throw <| IO.userError "canonical ordering merged distinct contracts"
  let rawLet := Lean.Expr.letE `view (.sort .zero) (.bvar 0) (.bvar 0) false
  let borrow : Ix.SemanticContract.Contract := {
    kind := .letE, binder := ⟨.affine, .localShared⟩, letKind := .borrowShared }
  let annotated := borrow.attach rawLet
  for surgical in [false, true] do
    let output ← get "borrow lowering" (compileMany #[rawLet, annotated, rawLet] surgical)
    let expectedBorrow := Ixon.Expr.letE ⟨false, .borrowShared, ⟨.affine, .localShared⟩⟩ (.sort 0) (.var 0) (.var 0)
    unless output == #[.leanLet false (.sort 0) (.var 0) (.var 0), expectedBorrow,
      .leanLet false (.sort 0) (.var 0) (.var 0)] do
      throw <| IO.userError "borrow contract contaminated a shared ordinary cache entry"
  let wrong := borrow.attach (.sort .zero)
  unless (compileMany #[wrong]).toOption.isNone do
    throw <| IO.userError "semantic metadata on a non-binder was discarded"
  let malformed := Lean.Expr.mdata (({} : Lean.MData).setNat `ix.contract 3) (.sort .zero)
  unless (compileMany #[malformed]).toOption.isNone do
    throw <| IO.userError "malformed semantic metadata was discarded"
  let inner := Lean.Expr.lam `x (.sort .zero) (.bvar 0) .default
  let nestedSource : Lean.ConstantInfo := .defnInfo {
    name := `nested, levelParams := [], type := .sort .zero
    value := .app inner inner, hints := .abbrev, safety := .safe, all := [`nested] }
  let nestedContract : SourceContract := {
    source := nestedSource
    binders := #[
      { site := ⟨.body, [.appFn]⟩, uses := .linear },
      { site := ⟨.body, [.appArg]⟩, uses := .affine, value := .localUnique }] }
  let nested ← get "nested resolution" (nestedContract.resolve nestedSource)
  let nested ← get "nested decoration" nested.decorate
  let some body := sourceBody? nested | throw <| IO.userError "missing nested body"
  let output ← get "nested lowering" (compileMany #[body])
  unless output == #[.app (.lam ⟨.linear, .shared⟩ (.sort 0) (.var 0))
      (.lam ⟨.affine, .localUnique⟩ (.sort 0) (.var 0))] do
    throw <| IO.userError "occurrence contracts merged before canonicalization"
  IO.println "Contract transport: every binder/arrow mode, cache ordering, nested occurrences, and borrow lowering passed"

end Tests.ContractTransport

end
