import Tests.Ix.CompileCert.Compiled
import Tests.Ix.CompileCert.Direct

namespace Tests.Ix.CompileCert.SourceInstall

open _root_.Ix.CompileCert

def label : SourceInstallError → String
  | .incomplete => "incomplete source closure"
  | .exportFailure reason => s!"export: {reason}"
  | .checking error position => s!"checking at {position}: {error}"

def controls : List (String × (Unit → Bool)) := [
  ("source-only definition installation", fun _ =>
    (installSource Direct.choiceInput.source [`first]).isOk),
  ("source ordering ignores supplied declaration order", fun _ =>
    (installSource ⟨Direct.dependent.source.declarations.reverse⟩ [`root]).isOk),
  ("source body is checked independently", fun _ =>
    match installSource ⟨[Direct.sourceDef `first (.sort .zero)]⟩ [`first] with
    | .error (.checking (.notImplemented _) _) => false
    | .error (.checking _ _) => true
    | _ => false),
  ("source missing dependency is not repaired from target", fun _ =>
    match installSource ⟨[Direct.sourceDef `root (.const `missing [.param `u])]⟩ [`root] with
    | .error .incomplete => true
    | _ => false),
  ("source opaque body participates in verified checking", fun _ =>
    let opaqueCI : Lean.ConstantInfo := .opaqueInfo {
      name := `opaqueFirst, levelParams := [`u], type := Direct.sourceType,
      value := Direct.sourceValue true, isUnsafe := false, all := [`opaqueFirst] }
    (installSource ⟨[opaqueCI]⟩ [`opaqueFirst]).isOk)]

/-- Bounded independent source installation census. Every root has an
explicit outcome; this runner never substitutes target success. -/
def run : IO Unit := do
  for (name, control) in controls do
    unless control () do throw (IO.userError s!"FAIL source installation: {name}")
    IO.println s!"PASS: {name}"
  let env ← getCompileEnv #[Compiled.prefixName]
  let mut successful := 0
  let mut unsupported := 0
  for root in Compiled.roots do
    let captured ← IO.ofExcept (captureCone env.find? [root] 128)
    match installSource captured.source [root] with
    | .ok installed =>
      if root == Compiled.prefixName ++ `Node.val || root == Compiled.prefixName ++ `Node.kids then
        throw (IO.userError s!"unexpected source support change: {root}")
      successful := successful + 1
      IO.println s!"SOURCE-INSTALLED {root}: {installed.declarations.size} groups"
    | .error reason =>
      match reason with
      | .checking (.notImplemented _) _ =>
        unless root == Compiled.prefixName ++ `Node.val || root == Compiled.prefixName ++ `Node.kids do
          throw (IO.userError s!"unexpected unsupported source: {root}: {label reason}")
        unsupported := unsupported + 1
      | _ => throw (IO.userError s!"unexpected source rejection: {root}: {label reason}")
      IO.println s!"SOURCE-UNSUPPORTED {root}: {label reason}"
  unless successful == 6 && unsupported == 2 do throw (IO.userError "source outcome coverage changed")
  IO.println s!"source installation census: {successful} installed, {unsupported} unsupported, 0 rejected; {Compiled.roots.length}/8 roots covered"

end Tests.Ix.CompileCert.SourceInstall
