module

public import Ix.DecompileM
public import Tests.Ix.ContractTransport

public section

namespace Tests.ContractDecompile

def get (label : String) (r : Except α β) [ToString α] : IO β :=
  match r with | .ok value => pure value | .error e => throw <| IO.userError s!"contract decompile {label}: {e}"

def context : Ix.DecompileM.BlockCtx := {
  refs := #[], univs := #[.zero], sharing := #[], mutCtx := #[], univParams := #[], arena := default }

def roundtrip (expression : Ixon.Expr) : IO Unit := do
  let (source, _) ← get "decode" <|
    Ix.DecompileM.DecompileM.run { ixonEnv := {} } context {} (Ix.DecompileM.decompileExpr expression UInt64.MAX)
  let ((result, _), _) ← get "encode" <|
    Ix.CompileM.CompileM.run default Tests.ContractTransport.block {} (Ix.CompileM.compileExpr source)
  unless result == expression do throw <| IO.userError s!"contract decompile roundtrip differs: {repr expression}"

def run : IO Unit := do
  -- Binders decompile without modes and compile back to the same terms.
  roundtrip (.lam (.sort 0) (.var 0))
  roundtrip (.all (.sort 0) (.sort 0))
  for nonDep in [false, true] do
    roundtrip (.leanLet nonDep (.sort 0) (.var 0) (.var 0))
  let key := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "ix") "contract"
  let env : Ixon.Env := { names := ({} : Std.HashMap Address Ix.Name).insert key.getHash key }
  let arena : Ixon.ExprMetaArena := { nodes := #[.leaf, .mdata #[#[(key.getHash, .ofBool true)]] 0] }
  let ctx := { context with arena }
  unless (Ix.DecompileM.DecompileM.run { ixonEnv := env } ctx {} (Ix.DecompileM.decompileExpr (.var 0) 1)).toOption.isNone do
    throw <| IO.userError "optional metadata injected a semantic contract"
  IO.println "Contract decompile: binders and lets roundtrip; contract frames from optional metadata reject"

end Tests.ContractDecompile

end
