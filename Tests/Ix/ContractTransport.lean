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

def block : Ix.CompileM.BlockEnv :=
  { all := {}, current := .mkAnon, mutCtx := {}, univCtx := [] }

def get (label : String) (result : Except α β) [ToString α] : IO β :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"contract transport {label}: {error}"

def compileMany (sources : Array Lean.Expr) :
    Except Ix.CompileM.CompileError (Array Ixon.Expr) := do
  let ix := Id.run ((sources.mapM Ix.CanonM.canonExpr).run' {})
  let action := ix.mapM fun e => do
    let (result, _) ← Ix.CompileM.compileExpr e
    pure result
  let (output, _) ← Ix.CompileM.CompileM.run default block {} action
  return output

/-- The unsupported-mode refusal's stable prefix. -/
def unsupportedModeRefusal : String := "unsupported semantic contract mode"

/-- The misplaced-frame refusal. -/
def misplacedRefusal : String :=
  "semantic contract is not attached to its original binder"

/-- A compile refusal whose message starts with `pre`. -/
def refusedWith (pre : String) : Ix.CompileM.CompileError → Bool
  | .unsupportedExpr desc => desc.startsWith pre
  | _ => false

/-- `source` compiled alone lowers to `expected`. -/
def expectLowering (label : String) (source : Lean.Expr) (expected : Ixon.Expr) : IO Unit := do
  match compileMany #[source] with
  | .ok output =>
    unless output == #[expected] do
      throw <| IO.userError s!"{label}: frame lowered to {repr output}, expected {repr expected}"
  | .error error => throw <| IO.userError s!"{label}: frame refused: {error}"

/-- `source` is refused with a message that starts with `message`. -/
def expectRefusal (label : String) (source : Lean.Expr) (message : String) : IO Unit :=
  match compileMany #[source] with
  | .ok output => throw <| IO.userError s!"{label}: compiled to {repr output}"
  | .error error =>
    unless refusedWith message error do
      throw <| IO.userError s!"{label}: unexpected refusal {error}"

def run : IO Unit := do
  let mut sources := #[]
  for inputBits in [:16] do
    let some binder := Ixon.BinderContract.ofBits? inputBits.toUInt8
      | throw <| IO.userError "invalid test binder"
    let validInput := (Ix.SemanticContract.toBinderMode? binder).isSome
    for resultBits in [:4] do
      let some result := Ixon.ValueContract.ofBits? resultBits.toUInt8
        | throw <| IO.userError "invalid test result"
      let original ← get "telescope" (SourceContract.ofTelescope source #[{
        binder := .position 0, uses := binder.uses, value := binder.value, result := some result }])
      let resolved ← get "resolution" (original.resolve source)
      if validInput then
        let decorated ← get "decoration" resolved.decorate
        -- Valid frames lower cleanly; lam/all modes live in the binder-data section.
        expectLowering s!"arrow {inputBits}/{resultBits}" decorated.type (.all (.sort 0) (.sort 0))
        if resultBits == 0 then
          let some body := sourceBody? decorated | throw <| IO.userError "missing decorated body"
          sources := sources.push body
          expectLowering s!"lambda {inputBits}" body (.lam (.sort 0) (.var 0))
      else
        match resolved.decorate with
        | .error e =>
          unless e == unsupportedModeRefusal do
            throw <| IO.userError s!"invalid binder {inputBits}/{resultBits} unexpected refusal: {e}"
        | .ok _ =>
          throw <| IO.userError s!"invalid binder {inputBits}/{resultBits} was not refused at decoration"
        let rawArrow : Ix.SemanticContract.Contract := { kind := .all, binder, result }
        expectRefusal s!"raw arrow {inputBits}/{resultBits}"
          (rawArrow.attach (.forallE `x (.sort .zero) (.sort .zero) .default)) unsupportedModeRefusal
  -- All valid occurrences share their unannotated inner binder. The complete
  -- metadata wrapper must distinguish them in both hash and equality paths.
  for i in [:sources.size] do
    for j in [:sources.size] do
      let equal := Id.run ((Ix.CanonM.exprEqCached sources[i]! sources[j]!).run' {})
      unless equal == (i == j) do throw <| IO.userError "semantic equality ignored a contract"
  let rawLet := Lean.Expr.letE `view (.sort .zero) (.bvar 0) (.bvar 0) false
  let plainLet := Ixon.Expr.leanLet false (.sort 0) (.var 0) (.var 0)
  let ordinaryLet : Ix.SemanticContract.Contract := { kind := .letE, binder := .many }
  let output ← get "ordinary let lowering" (compileMany #[rawLet, ordinaryLet.attach rawLet, rawLet])
  unless output == #[plainLet, plainLet, plainLet] do
    throw <| IO.userError "an ordinary let frame did not lower to the plain let"
  let borrow : Ix.SemanticContract.Contract := {
    kind := .letE, binder := ⟨.affine, .localShared⟩, letKind := .borrowShared }
  expectLowering "borrow" (borrow.attach rawLet) (.letE false .borrow (.sort 0) (.var 0) (.var 0))
  let uniqueLet : Ix.SemanticContract.Contract := {
    kind := .letE, binder := ⟨.linear, .localUnique⟩ }
  expectLowering "uniqueBorrowed let" (uniqueLet.attach rawLet)
    (.letE false (.value .uniqueBorrowed) (.sort 0) (.var 0) (.var 0))
  let badLet : Ix.SemanticContract.Contract := {
    kind := .letE, binder := ⟨.erased, .localShared⟩ }
  expectRefusal "erased local let" (badLet.attach rawLet) unsupportedModeRefusal
  expectRefusal "misplaced borrow" (borrow.attach (.sort .zero)) misplacedRefusal
  expectRefusal "misplaced ordinary frame" (ordinaryLet.attach (.sort .zero)) misplacedRefusal
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
  expectLowering "nested occurrences" body
    (.app (.lam (.sort 0) (.var 0)) (.lam (.sort 0) (.var 0)))
  IO.println "Contract transport: valid binder, arrow, let, borrow and nested frames lower; \
    unsupported erased-owned/local, misplaced and malformed frames are refused"

end Tests.ContractTransport

end
