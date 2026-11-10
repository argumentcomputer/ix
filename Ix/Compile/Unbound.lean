module
public import Ix.CompileCertified

/-! `ix compile --unbound`: the certified compile published as it is, without
the role support, certificates and role binding that
`Ix.RoleBinding.Compile.finalize` adds. The artifact holds exactly the
selected closure and is written in the version-4 envelope (`0xE4`), which
consumers that do not read role bindings require; IxCC's corpus fixtures are
such closures. Consumers that admit through a role binding refuse it. -/

public section

namespace Ix.CompileM

/-- **The certified compile, unbound**: `compileCertified` (source contracts,
canonicalization, `Ix.Cert.compileReport` with its checks, the accounting and,
for an input with semantic contracts, the resource validation), then, unless a
constant failed and `allowPartial` is false, `strip` and `Ixon.serEnv` of its
artifact. The outer error is the compile's refusal; the result has the shape of
`compileAndFinalize`'s, so that the compile commands report both alike. -/
def compileUnbound (source : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat) (allowPartial : Bool)
    (log : String → IO Unit := fun _ => pure ())
    (strip : Ixon.Env → Ixon.Env := id) :
    IO (Except String (CertifiedOut × Finalization)) := do
  let out ← match ← compileCertified source constants workers log with
    | .ok out => pure out
    | .error e => return .error e
  if !allowPartial && !out.failures.isEmpty then return .ok (out, .refused)
  let artifact := strip out.env
  if artifact.roleBinding.isSome then
    return .ok (out, .failed "unbound compile: the compiled artifact carries a role binding")
  match Ixon.serEnv artifact with
  | .ok bytes => return .ok (out, .done artifact bytes)
  | .error e => return .ok (out, .failed e)

end Ix.CompileM

end
