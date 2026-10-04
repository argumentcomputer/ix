import LSpec
import Ix.AuxGen.Kernel

open LSpec Ix Ix.AuxGen Ix.CompileM

namespace Tests.Ix.Compile.BridgeScopes

private def nm (s : String) := Ix.Name.fromLeanName s.toName
private def maps : AddrMaps := { nameToAddr := fun _ => none }
private def decl (s : String) (ty : Expr := Expr.mkSort Level.mkZero) : LocalDecl :=
  { fvarName := nm s, binderName := nm s, domain := ty, info := .default }

private def execute (act : KBridgeM α) : Except CompileError α := do
  let ((value, _), _) ← CompileM.run default
    { all := {}, current := nm "test", mutCtx := default, univCtx := [] } {}
    (act.run AuxKernelCtx.new)
  return value

private def refuses (act : KBridgeM α) (message : String) : Bool :=
  match execute act with
  | .error (.unsupportedExpr text) => (text.splitOn message).length > 1
  | _ => false

private def validDependentScope : Bool :=
  (execute do
    let a := decl "A" (Expr.mkSort (Level.mkSucc Level.mkZero))
    let x := decl "x" (Expr.mkFVar a.fvarName)
    let scope ← TcScopeSt.new #[a] #[] maps
    let scope ← scope.pushLocals #[x]
    let inferred ← scope.inferLean (Expr.mkFVar x.fvarName)
    let scope ← scope.popLocals #[x]
    return inferred == some (Expr.mkFVar a.fvarName)
      && scope.depth == 1 && scope.extraLocals == 0
      && (← get).tcState.ctx.size == 1
      && scope.fvarLevels[a.fvarName]? == some 0
      && !scope.fvarLevels.contains x.fvarName).toOption == some true

private def caughtFailureRestoresScope : Bool :=
  (execute do
    let scope ← TcScopeSt.new #[] #[] maps
    try
      discard <| scope.pushLocals #[decl "x", decl "x"]
      return false
    catch _ =>
      -- StateT's exception boundary restores the entry scope after a
      -- rejected telescope; the partially pushed local cannot leak.
      return (← get).tcState.ctx.isEmpty).toOption == some true

def suite : List TestSeq := [
  test "duplicate outer identities fail explicitly"
    (refuses (TcScopeSt.new #[decl "x", decl "x"] #[] maps) "duplicate outer")
  ++ test "duplicate universe parameters fail explicitly"
    (refuses (TcScopeSt.new #[] #[nm "u", nm "u"] maps) "duplicate universe")
  ++ test "a pushed identity cannot overwrite an outer identity"
    (refuses (do
      let scope ← TcScopeSt.new #[decl "x"] #[] maps
      scope.pushLocals #[decl "x"]) "duplicate pushed")
  ++ test "duplicate identities within a pushed telescope fail explicitly"
    (refuses (do
      let scope ← TcScopeSt.new #[] #[] maps
      scope.pushLocals #[decl "x", decl "x"]) "duplicate pushed")
  ++ test "pop cannot consume outer locals"
    (refuses (do
      let scope ← TcScopeSt.new #[decl "x"] #[] maps
      scope.popLocals #[decl "x"]) "exceeds pushed")
  ++ test "pop requires the actual LIFO telescope"
    (refuses (do
      let scope ← TcScopeSt.new #[] #[] maps
      let scope ← scope.pushLocals #[decl "x", decl "y"]
      scope.popLocals #[decl "x"]) "not LIFO")
  ++ test "a stale scope cannot push into another telescope"
    (refuses (do
      let scope ← TcScopeSt.new #[] #[] maps
      discard <| scope.pushLocals #[decl "x"]
      scope.pushLocals #[decl "y"]) "stale scope depth")
  ++ test "a stale scope cannot pop another telescope"
    (refuses (do
      let scope ← TcScopeSt.new #[] #[] maps
      discard <| scope.pushLocals #[decl "x"]
      scope.popLocals #[]) "stale scope depth")
  ++ test "valid dependent telescope inference and push/pop remain balanced"
    validDependentScope
  ++ test "caught invalid telescope restores its entry context"
    caughtFailureRestoresScope
]

end Tests.Ix.Compile.BridgeScopes
