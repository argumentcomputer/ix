module

public import Ix.CompileDriver

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
    binder := .position 0, uses := .linear, value := .localShared, result := some result }]
  return { constants := [(typeName, typeSource), (identityName, identitySource)], contracts := #[contract] }

def get (label : String) (r : Except String α) : IO α :=
  match r with | .ok value => pure value | .error e => throw <| IO.userError s!"contract pipeline {label}: {e}"

def run : IO Unit := do
  let valid ← get "input" ((input).mapError toString)
  let lean ← Ix.CompileM.compileLeanInput valid (numWorkers := 1) >>= get "Lean compiler"
  let prepared ← get "preparation" valid.prepare
  let rust ← Ix.CompileM.rsCompileEnvFFI prepared
  let rust := rust.toEnv
  unless (lean.env.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) ==
      (rust.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) do
    throw <| IO.userError "contract pipeline: Lean/Rust address sets differ"
  let profile : Ix.Resource.Profile := {}
  let explicit ← Ix.CompileM.rsCompileInput valid (some profile)
  unless (rust.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) ==
      (explicit.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) do
    throw <| IO.userError "contract pipeline: explicit profile changed constant addresses"
  let malformedRejected ← try
    let _ ← Ix.CompileM.rsCompileEnvProfileFFI prepared (profile.bytes.push 0)
    pure false
  catch _ => pure true
  unless malformedRejected do
    throw <| IO.userError "contract pipeline: malformed profile bytes accepted"
  let invalid ← get "invalid input" ((input .shared).mapError toString)
  if (← Ix.CompileM.compileLeanInput invalid (numWorkers := 1)).toOption.isSome then
    throw <| IO.userError "contract pipeline: pure compiler emitted an escaping local value"
  let prepared ← get "invalid preparation" invalid.prepare
  let rejected ← try
    let _ ← Ix.CompileM.rsCompileEnvFFI prepared
    pure false
  catch _ => pure true
  unless rejected do
    throw <| IO.userError "contract pipeline: native compiler emitted an escaping local value"
  IO.println "Contract pipeline: both compilers preserve addresses and reject local escape before emission"

end Tests.ContractPipeline

end
