module

public import Ix.CompileCertified
public import Ix.ModeCheck

/-!
  Contract pipeline test suite (`Tests.ContractPipeline`).
-/

public section

namespace Tests.ContractPipeline

open Ix.Compile

def typeName : Lean.Name := `ContractA
def identityName : Lean.Name := `contractId

def typeSource : Lean.ConstantInfo := .axiomInfo {
  name := typeName, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }

def identitySource : Lean.ConstantInfo := .defnInfo {
  name := identityName, levelParams := []
  type := .forallE `x (.const typeName []) (.const typeName []) .default
  value := .lam `x (.const typeName []) (.bvar 0) .default
  hints := .abbrev, safety := .safe, all := [identityName] }

def input (result : Ixon.ValueContract := .localShared) : Except SourceContractError CompileInput := do
  let contract ← SourceContract.ofTelescope identitySource #[{
    binder := .position 0, uses := .many, value := .localShared, result := some result }]
  return { constants := [(typeName, typeSource), (identityName, identitySource)], contracts := #[contract] }

def get (label : String) (r : Except String α) : IO α :=
  match r with | .ok value => pure value | .error e => throw <| IO.userError s!"contract pipeline {label}: {e}"

def compileInput (input : CompileInput) : IO (Except String Ix.CompileM.CertifiedOut) := do
  match input.prepare >>= fun p => (Ix.CompileM.checkPreparedSource p).map (p, ·) with
  | .error e => return .error e
  | .ok (prepared, annotated) =>
    Ix.CompileM.compileCertifiedPrepared prepared annotated 1 (modeCheck := Ix.ModeCheck.checkArtifact)

def run : IO Unit := do
  let valid ← get "input" ((input).mapError toString)
  let lean ← compileInput valid >>= get "Lean compiler"
  let prepared ← get "preparation" valid.prepare
  let (certEnv, _) ← get "certified compiler" (Ix.Cert.compileReport (Ix.CompileM.canonInput prepared.toArray 1))
  unless (lean.env.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) ==
      (certEnv.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) do
    throw <| IO.userError "contract pipeline: Lean/certified address sets differ"
  let _ ← get "mode checking" (Ix.ModeCheck.checkArtifact lean.env)
  let invalid ← get "invalid input" ((input .shared).mapError toString)
  if (← compileInput invalid).toOption.isSome then
    throw <| IO.userError "contract pipeline: pure compiler emitted an escaping local value"
  IO.println "Contract pipeline: certified compiler preserves addresses, its modes check, and a borrowed result escaping is refused before emission"

end Tests.ContractPipeline

end
