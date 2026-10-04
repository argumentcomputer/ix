import LSpec
import Ix.AuxGen.Kernel

open LSpec Ix Ix.AuxGen Ix.CompileM

namespace Tests.Ix.Compile.BridgeProvenance

private def nm (s : String) : Ix.Name := Ix.Name.fromLeanName s.toName
private def shared : Address := Address.blake3 "bridge-provenance".toUTF8
private def wanted := nm "Wanted"
private def second := nm "Second"
private def ambient := nm "Ambient"

private def fixture : CompileEnv := Id.run do
  let mut env : CompileEnv := default
  for n in #[wanted, second, ambient] do
    let ci : ConstantInfo := .axiomInfo
      { cnst := { name := n, levelParams := #[], type := Expr.mkSort Level.mkZero }
        isUnsafe := false }
    env := { env with
      env := { env.env with consts := env.env.consts.insert n ci }
      nameToAddr := env.nameToAddr.insert n shared
      nameToNamed := env.nameToNamed.insert n { addr := shared } }
  return env

private def run (act : KBridgeM Bool) : Bool :=
  match CompileM.run fixture
      { all := {}, current := wanted, mutCtx := default, univCtx := [] }
      {} (act.run AuxKernelCtx.new) with
  | .ok ((result, _), _) => result
  | .error _ => false

private def maps : AddrMaps := AddrMaps.ofCompileEnv fixture

/-- A loaded alias is not the missing Meta KId, even at the same address. -/
private def maskedAlias : Bool := run do
  kenvInsert ⟨shared, ambient⟩
    (.axio ambient #[] false 0 (Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero))
  discard <| leanExprToKexpr (Expr.mkConst wanted #[]) #[] maps
  let scope ← TcScopeSt.new #[] #[] maps
  let loaded ← scope.faultInAddr shared
  return loaded && (← kenvGet? ⟨shared, wanted⟩).isSome
    && (← kenvGet? ⟨shared, ambient⟩).isSome

/-- All referenced aliases are ingressed; an unrelated ambient alias is not. -/
private def multipleAliases (reverse : Bool) : Bool := run do
  let names := if reverse then #[second, wanted] else #[wanted, second]
  for name in names do
    discard <| leanExprToKexpr (Expr.mkConst name #[]) #[] maps
  let scope ← TcScopeSt.new #[] #[] maps
  let loaded ← scope.faultInAddr shared
  return loaded && (← kenvGet? ⟨shared, wanted⟩).isSome
    && (← kenvGet? ⟨shared, second⟩).isSome
    && (← kenvGet? ⟨shared, ambient⟩).isNone

private def absentProvenance : Bool :=
  let action : KBridgeM Bool := do
    let scope ← TcScopeSt.new #[] #[] maps
    scope.faultInAddr shared
  match CompileM.run fixture
      { all := {}, current := wanted, mutCtx := default, univCtx := [] }
      {} (action.run AuxKernelCtx.new) with
  | .error (.unsupportedExpr msg) =>
    (msg.splitOn "no forward source provenance").length > 1
  | _ => false

private def localDomain : Bool := run do
  let localDecl : Ix.AuxGen.LocalDecl :=
    { fvarName := nm "x", binderName := nm "x",
      domain := Expr.mkConst wanted #[], info := .default }
  let scope ← TcScopeSt.new #[localDecl] #[] maps
  let loaded ← scope.faultInAddr shared
  return loaded && (← kenvGet? ⟨shared, wanted⟩).isSome
    && (← kenvGet? ⟨shared, ambient⟩).isNone

def suite : List TestSeq := [
  test "an already loaded alias cannot mask a missing referenced identity" maskedAlias
  ++ test "all forward aliases load without ambient aliases" (multipleAliases false)
  ++ test "reversing reference order preserves the loaded identities" (multipleAliases true)
  ++ test "ambient reverse aliases cannot supply absent provenance" absentProvenance
  ++ test "open local domains carry forward provenance" localDomain
]

end Tests.Ix.Compile.BridgeProvenance
