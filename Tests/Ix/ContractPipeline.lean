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
  | .ok (prepared, annotated) =>
    Ix.CompileM.compileCertifiedPrepared prepared annotated 1
      (binderData := annotated) (modeCheck := Ix.ModeCheck.checkArtifact)

def run : IO Unit := do
  -- The ordinary contract: the Lean and certified compilers agree.
  let valid ← get "input" ((input .many .shared .shared).mapError toString)
  let lean ← compileInput valid >>= get "Lean compiler"
  let prepared ← get "preparation" valid.prepare
  let (certEnv, _) ← get "certified compiler" (Ix.Cert.compileReport (Ix.CompileM.canonInput prepared.toArray 1))
  unless (lean.env.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) ==
      (certEnv.consts.toList.map Prod.fst).mergeSort (fun a b => Address.cmpBytes a b != .gt) do
    throw <| IO.userError "contract pipeline: Lean/certified address sets differ"
  let _ ← get "mode checking" (Ix.ModeCheck.checkArtifact lean.env)
  -- A valid annotated contract lowers modes into the record and passes mode checking.
  let annotated ← get "annotated input" ((input .linear .localShared .localShared).mapError toString)
  let annotatedOut ← compileInput annotated >>= get "annotated compile"
  unless annotatedOut.annotated do
    throw <| IO.userError "contract pipeline: annotated flag not set"
  let idKey := Ix.Name.fromLeanName identityName
  let some idNamed := annotatedOut.env.named.get? idKey
    | throw <| IO.userError "contract pipeline: annotated identity not published"
  let some idConst := annotatedOut.env.getConst? idNamed.addr
    | throw <| IO.userError "contract pipeline: annotated identity record missing"
  unless Ix.Compile.BinderData.hasModes idConst do
    throw <| IO.userError "contract pipeline: annotated identity carries no resource modes"
  -- An ill-moded annotated contract is refused by mode checking before emission.
  let escaping ← get "escaping input" ((input .linear .localShared .shared).mapError toString)
  match ← compileInput escaping with
  | .ok _ => throw <| IO.userError "contract pipeline: escaping borrow compiled"
  | .error e =>
    unless (e.splitOn "borrowEscape").length > 1 do
      throw <| IO.userError s!"contract pipeline: escaping borrow: unexpected error {e}"
  -- Compiling annotated source without a mode checker is refused.
  let preparedAnn ← get "annotated preparation" annotated.prepare
  match ← Ix.CompileM.compileCertifiedPrepared preparedAnn true 1 with
  | .ok _ => throw <| IO.userError "contract pipeline: annotated source accepted without a mode checker"
  | .error e =>
    unless (e.splitOn "annotated source is refused").length > 1 do
      throw <| IO.userError s!"contract pipeline: noModeChecker: unexpected error {e}"
  IO.println "Contract pipeline: ordinary and valid annotated contracts compile and pass mode checking; \
    escaping borrows and unchecked annotated compiles are refused"

end Tests.ContractPipeline

end
