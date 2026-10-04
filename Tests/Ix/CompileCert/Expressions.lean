import Tests.Ix.CompileCert.Direct

namespace Tests.Ix.CompileCert.Expressions

open _root_.Ix.CompileCert
open Tests.Ix.Kernel.IxonFixtures (address)

def withContext (test : TermContext → Bool) : Bool :=
  match _root_.Ix.Kernel.Reader.defaultPins with
  | .error _ => false
  | .ok pins => test ⟨⟨⟨[]⟩, [], pins⟩, [], []⟩

def controls : List (String × (Unit → Bool)) := [
  ("Ix scope bridge exceeds packed bound saturation", fun _ => withContext fun cx =>
    match ixToKernel cx (.bvar 50000 (address 1)) with
    | .error _ => false
    | .ok result => result.bvarBound == 50001 && !result.looseBVarsBounded 50000),
  ("Ix closed binder scope survives arbitrary cached hashes", fun _ => withContext fun cx =>
    let source := Ix.Expr.lam (.anonymous (address 2))
      (.sort (.zero (address 3)) (address 4)) (.bvar 0 (address 5)) .default (address 6)
    match ixToKernel cx source with
    | .error _ => false
    | .ok result => result.looseBVarsBounded 0 && !result.hasFvar),
  ("open substitution avoids capture under a binder", fun _ => withContext fun cx =>
    let source := Lean.Expr.lam `x (.sort .zero) (.bvar 1) .default
    match exportExpr cx (sourceInstantiate (.bvar 0) 0 source) with
    | .error _ => false
    | .ok result => decide (result = .lam (.sort .zero) (.bvar 1) ⟨.never⟩)),
  ("substitution lowers higher loose indices", fun _ => withContext fun cx =>
    match exportExpr cx (sourceInstantiate (.bvar 7) 0 (.bvar 2)) with
    | .error _ => false
    | .ok result => decide (result = .bvar 1)),
  ("lifting respects the binder cutoff", fun _ => withContext fun cx =>
    let source := Lean.Expr.lam `x (.sort .zero) (.app (.bvar 0) (.bvar 1)) .default
    match exportExpr cx (sourceLift 3 0 source) with
    | .error _ => false
    | .ok result => decide (result = .lam (.sort .zero) (.app (.bvar 0) (.bvar 4)) ⟨.never⟩)),
  ("full renaming includes projection owner identities", fun _ =>
    let old := _root_.Ix.Kernel.Name.str .anonymous "Old"
    let fresh := _root_.Ix.Kernel.Name.str .anonymous "New"
    let source := _root_.Ix.Kernel.Expr.proj old 0 (.const old [])
    let rename := fun n => if n = old then fresh else n
    decide (kernelRenameAll rename source = .proj fresh 0 (.const fresh [])) &&
      decide (_root_.Ix.Kernel.Expr.renameConsts rename source = .proj old 0 (.const fresh []))),
  ("Ix free variables remain unsupported by the bridge", fun _ =>
    !(ixExpr (.fvar (.anonymous (address 1)) (address 2))).isOk)]

def run : IO Unit := do
  let mut failed := 0
  for (label, control) in controls do
    let ok := control ()
    IO.println s!"{if ok then "PASS" else "FAIL"}: {label}"
    unless ok do failed := failed + 1
  unless failed == 0 do throw (IO.userError s!"{failed} expression bridge controls failed")

end Tests.Ix.CompileCert.Expressions
