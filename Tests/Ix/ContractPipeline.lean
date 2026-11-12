module

public import Ix.CompileCertified

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

/-- The identity under a telescope contract on its binder. -/
def input (uses : Ixon.Uses) (value result : Ixon.ValueContract) :
    Except SourceContractError CompileInput := do
  let contract ← SourceContract.ofTelescope identitySource #[{
    binder := .position 0, uses, value, result := some result }]
  return { constants := [(typeName, typeSource), (identityName, identitySource)], contracts := #[contract] }

def get (label : String) (r : Except String α) : IO α :=
  match r with | .ok value => pure value | .error e => throw <| IO.userError s!"contract pipeline {label}: {e}"

def compileInput (input : CompileInput) : IO (Except String Ix.CompileM.CertifiedOut) := do
  match input.prepare >>= fun p => (Ix.CompileM.checkPreparedSource p).map (p, ·) with
  | .error e => return .error e
  | .ok (prepared, annotated) => Ix.CompileM.compileCertifiedPrepared prepared annotated 1

def run : IO Unit := do
  -- The ordinary contract: the Lean and certified compilers agree.
  let valid ← get "input" ((input .many .shared .shared).mapError toString)
  let lean ← compileInput valid >>= get "Lean compiler"
  let prepared ← get "preparation" valid.prepare
  let (certEnv, _) ← get "certified compiler" (Ix.Cert.compileReport (Ix.CompileM.canonInput prepared.toArray 1))
  unless (lean.env.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) ==
      (certEnv.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) do
    throw <| IO.userError "contract pipeline: Lean/certified address sets differ"
  let profile : Ix.Resource.Profile := {}
  let _ ← get "explicit profile" (Ix.Resource.validate lean.env profile)
  let malformedRejected := (Ix.Resource.Profile.ofBytes (profile.bytes.push 0)).toOption.isNone
  unless malformedRejected do
    throw <| IO.userError "contract pipeline: malformed profile bytes accepted"
  -- An annotated contract is refused before emission.
  let annotated ← get "annotated input" ((input .linear .localShared .localShared).mapError toString)
  match ← compileInput annotated with
  | .ok _ => throw <| IO.userError "contract pipeline: annotated source compiled"
  | .error e =>
    unless (e.splitOn "annotated source is refused").length > 1 do
      throw <| IO.userError s!"contract pipeline: annotated source: unexpected error {e}"
  IO.println "Contract pipeline: an ordinary contract compiles to the same addresses through both \
    compilers; annotated source is refused before emission"

end Tests.ContractPipeline

end
