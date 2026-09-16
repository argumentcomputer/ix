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
    Ix.DecompileM.DecompileM.run ⟨{}⟩ context {} (Ix.DecompileM.decompileExpr expression UInt64.MAX)
  let ((result, _), _) ← get "encode" <|
    Ix.CompileM.CompileM.run default Tests.ContractTransport.block {} (Ix.CompileM.compileExpr source)
  unless result == expression do throw <| IO.userError s!"contract decompile roundtrip differs: {repr expression}"

def run : IO Unit := do
  for inputBits in [:16] do
    let some binder := Ixon.BinderContract.ofBits? inputBits.toUInt8
      | throw <| IO.userError "invalid binder test"
    roundtrip (.lam binder (.sort 0) (.var 0))
    for resultBits in [:4] do
      let some result := Ixon.ValueContract.ofBits? resultBits.toUInt8
        | throw <| IO.userError "invalid arrow test"
      roundtrip (.all binder result (.sort 0) (.sort 0))
    for nonDep in [false, true] do
      roundtrip (.letE ⟨nonDep, .value, binder⟩ (.sort 0) (.var 0) (.var 0))
      if binder.value == .localShared then
        roundtrip (.letE ⟨nonDep, .borrowShared, binder⟩ (.sort 0) (.var 0) (.var 0))
  let nested := Ixon.Expr.lam ⟨.affine, .localUnique⟩ (.sort 0) (.var 0)
  let arena : Ixon.ExprMetaArena := { nodes := #[.callSite default #[] #[] none] }
  let ctx := { context with sharing := #[nested], arena }
  let expression := Ixon.Expr.app (.var 0) (.share 0)
  unless (Ix.DecompileM.DecompileM.run ⟨{}⟩ ctx {} (Ix.DecompileM.decompileExpr expression 0)).toOption.isNone do
    throw <| IO.userError "optional replay removed a contract behind sharing"
  let key := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "ix") "contract"
  let env : Ixon.Env := { names := ({} : Std.HashMap Address Ix.Name).insert key.getHash key }
  let arena : Ixon.ExprMetaArena := { nodes := #[.leaf, .mdata #[#[(key.getHash, .ofBool true)]] 0] }
  let ctx := { context with arena }
  unless (Ix.DecompileM.DecompileM.run ⟨env⟩ ctx {} (Ix.DecompileM.decompileExpr (.var 0) 1)).toOption.isNone do
    throw <| IO.userError "optional metadata injected a semantic contract"
  IO.println "Contract decompile: every binder, arrow, let, and borrow mode roundtrips; metadata attacks reject"

end Tests.ContractDecompile

end
